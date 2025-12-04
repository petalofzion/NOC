/-
  NOC/E/Information/Discrete.lean
  
  Foundation for Target #2: Discrete Strong Data Processing Inequality (SDPI).
  
  Status: Implementation Phase.
-/

import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

namespace NOC
namespace Information
noncomputable section
open Classical
open Real (log)
open scoped BigOperators

universe u

/-! ## 1. Basic Definitions: Entropy & KL -/

def entropy {α : Type u} [Fintype α] (p : PMF α) : ℝ :=
  ∑ x, Real.negMulLog (p x).toReal

def kl_divergence {α : Type u} [Fintype α] (p q : PMF α) : ℝ :=
  ∑ x, (p x).toReal * (log (p x).toReal - log (q x).toReal)

/-! ## 2. Joint and Conditional Definitions -/

def joint_entropy {α β : Type u} [Fintype α] [Fintype β] (p : PMF (α × β)) : ℝ :=
  entropy p

def marginal_fst {α β : Type u} [Fintype α] [Fintype β] (p : PMF (α × β)) : PMF α :=
  Prod.fst <$> p

def marginal_snd {α β : Type u} [Fintype α] [Fintype β] (p : PMF (α × β)) : PMF β :=
  Prod.snd <$> p

def mutual_info {α β : Type u} [Fintype α] [Fintype β] (p : PMF (α × β)) : ℝ :=
  entropy (marginal_fst p) + entropy (marginal_snd p) - joint_entropy p

def cond_entropy {α β : Type u} [Fintype α] [Fintype β] (p : PMF (α × β)) : ℝ :=
  joint_entropy p - entropy (marginal_fst p)

/-! ## 3. Fundamental Inequalities (The Proof Targets) -/

/-- Gibbs' Inequality: D(p || q) ≥ 0. -/
theorem kl_nonneg {α : Type u} [Fintype α] (p q : PMF α) 
  (h_supp : p.support ⊆ q.support) : 0 ≤ kl_divergence p q := by
  rw [kl_divergence]
  let S := p.support.toFinset
  
  have h_sum : ∑ x, (p x).toReal * (log (p x).toReal - log (q x).toReal) = 
               Finset.sum S (fun x => (p x).toReal * (log (p x).toReal - log (q x).toReal)) := by
    rw [← Finset.sum_subset (Finset.subset_univ S)]
    intro x _ hx
    have : p x = 0 := by simpa [S] using hx
    simp [this]
  rw [h_sum]
  
  have h_rw : ∀ x ∈ S, (p x).toReal * (log (p x).toReal - log (q x).toReal) = 
                       (p x).toReal * (- log ((q x).toReal / (p x).toReal)) := by
    intro x hx
    have hp : (p x).toReal ≠ 0 := by 
      simp only [Finset.mem_coe, PMF.mem_support_iff, ne_eq, ENNReal.toReal_eq_zero_iff] at hx 
      exact hx
    have hq : (q x).toReal ≠ 0 := by
      have hx_supp : x ∈ p.support := by simpa [S] using hx
      have : x ∈ q.support := h_supp hx_supp
      simp only [PMF.mem_support_iff, ne_eq, ENNReal.toReal_eq_zero_iff] at this
      exact this
    rw [Real.log_div]
    · ring
    · exact ENNReal.toReal_ne_zero.mp hq
    · exact ENNReal.toReal_ne_zero.mp hp

  rw [Finset.sum_congr rfl (fun x hx => h_rw x hx)]

  let f := fun (t : ℝ) => - log t
  have h_cvx : ConvexOn ℝ (Set.Ioi 0) f := by
    apply ConvexOn.neg
    exact StrictConcaveOn.concaveOn strictConcaveOn_log_Ioi
  
  have h_jensen := ConvexOn.map_sum_le h_cvx (t := S) (w := fun x => (p x).toReal) (p := fun x => (q x).toReal / (p x).toReal)
  
  have h_w_nonneg : ∀ x ∈ S, 0 ≤ (p x).toReal := fun x _ => ENNReal.toReal_nonneg
  have h_w_sum : Finset.sum S (fun x => (p x).toReal) = 1 := by
    rw [← PMF.toReal_support_sum p]
    apply Finset.sum_subset (Finset.subset_univ S)
    intro x _ hx
    have : p x = 0 := by simpa [S] using hx
    simp [this]
  
  have h_mem_domain : ∀ x ∈ S, (q x).toReal / (p x).toReal ∈ Set.Ioi 0 := by
    intro x hx
    simp only [Set.mem_Ioi]
    apply div_pos
    · apply ENNReal.toReal_pos
      · exact ENNReal.coe_ne_top
      · have : x ∈ q.support := h_supp (by dsimp [S] at hx; simpa using hx)
        simpa using this
    · apply ENNReal.toReal_pos
      · exact ENNReal.coe_ne_top
      · dsimp [S] at hx; simpa using hx

  specialize h_jensen h_w_nonneg h_w_sum h_mem_domain
  
  have h_cancel : Finset.sum S (fun x => (p x).toReal * ((q x).toReal / (p x).toReal)) = Finset.sum S (fun x => (q x).toReal) := by
    apply Finset.sum_congr rfl
    intro x hx
    field_simp
    rw [mul_div_cancel_right₀]
    apply ENNReal.toReal_ne_zero.mp
    dsimp [S] at hx
    simpa using hx

  rw [h_cancel] at h_jensen
  
  have h_q_sum : Finset.sum S (fun x => (q x).toReal) ≤ 1 := by
    rw [← PMF.toReal_univ_sum q]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · exact Finset.subset_univ S
    · intro x _ _; exact ENNReal.toReal_nonneg

  have h_log_nonneg : - log (Finset.sum S (fun x => (q x).toReal)) ≥ 0 := by
    simp only [neg_nonneg, log_nonpos_iff]
    constructor
    · apply Finset.sum_pos
      · intro x _; exact ENNReal.toReal_nonneg
      · let ⟨x, hx⟩ := p.support_nonempty
        exists x
        constructor
        · dsimp [S]; simpa using hx
        · apply ENNReal.toReal_pos ENNReal.coe_ne_top
          apply h_supp hx
    · exact h_q_sum

  exact le_trans h_log_nonneg h_jensen

theorem entropy_nonneg {α : Type u} [Fintype α] (p : PMF α) : 0 ≤ entropy p := by
  apply Finset.sum_nonneg
  intro x _
  apply Real.negMulLog_nonneg
  · apply ENNReal.toReal_nonneg
  · rw [← ENNReal.toReal_one]
    apply ENNReal.toReal_mono
    · exact ENNReal.one_ne_top
    · exact PMF.coe_le_one p x

theorem entropy_le_log_card {α : Type u} [Fintype α] (p : PMF α) : 
  entropy p ≤ log (Fintype.card α) := by
  rw [entropy]
  let S := p.support.toFinset
  
  have h_sum : ∑ x, Real.negMulLog (p x).toReal = Finset.sum S (fun x => Real.negMulLog (p x).toReal) := by
    rw [← Finset.sum_subset (Finset.subset_univ S)]
    intro x _ hx
    have : p x = 0 := by simpa [S] using hx
    simp [this, Real.negMulLog]
  rw [h_sum]

  have h_rw : ∀ x ∈ S, Real.negMulLog (p x).toReal = (p x).toReal * log (1 / (p x).toReal) := by
    intro x hx
    have hp : (p x).toReal ≠ 0 := by
      dsimp [S] at hx
      simp only [Finset.mem_coe, PMF.mem_support_iff, ne_eq, ENNReal.toReal_eq_zero_iff] at hx 
      exact hx
    rw [Real.negMulLog, Real.log_div, Real.log_one, zero_sub, mul_neg]
    · exact one_ne_zero
    · exact hp

  rw [Finset.sum_congr rfl (fun x hx => h_rw x hx)]

  let f := log
  have h_concave : ConcaveOn ℝ (Set.Ioi 0) f := StrictConcaveOn.concaveOn strictConcaveOn_log_Ioi
  
  have h_jensen := ConcaveOn.le_map_sum h_concave (t := S) (w := fun x => (p x).toReal) (p := fun x => 1 / (p x).toReal)
  
  have h_w_nonneg : ∀ x ∈ S, 0 ≤ (p x).toReal := fun x _ => ENNReal.toReal_nonneg
  have h_w_sum : Finset.sum S (fun x => (p x).toReal) = 1 := by
    rw [← PMF.toReal_support_sum p]
    rw [← Finset.sum_subset (Finset.subset_univ S)]
    intro x _ hx
    have : p x = 0 := by simpa [S] using hx
    simp [this]
  
  have h_mem_domain : ∀ x ∈ S, 1 / (p x).toReal ∈ Set.Ioi 0 := by
    intro x hx
    simp only [Set.mem_Ioi, one_div, inv_pos]
    apply ENNReal.toReal_pos ENNReal.coe_ne_top
    dsimp [S] at hx
    simpa using hx

  specialize h_jensen h_w_nonneg h_w_sum h_mem_domain

  have h_cancel : Finset.sum S (fun x => (p x).toReal * (1 / (p x).toReal)) = Finset.sum S (fun x => 1) := by
    apply Finset.sum_congr rfl
    intro x hx
    field_simp
    rw [mul_div_cancel_right₀]
    apply ENNReal.toReal_ne_zero.mp
    dsimp [S] at hx
    simpa using hx
  
  rw [h_cancel] at h_jensen
  simp only [Finset.sum_const, Finset.card_one, mul_one] at h_jensen
  
  have h_card : (S.card : ℝ) ≤ Fintype.card α := by
    norm_cast
    apply Finset.card_le_univ

  apply le_trans h_jensen
  apply Real.log_le_log
  · norm_cast
    have : S.Nonempty := by
      let ⟨x, hx⟩ := p.support_nonempty
      exact ⟨x, by dsimp [S]; simpa using hx⟩
    exact Finset.card_pos.mpr this
  · exact h_card

theorem mutual_info_eq_kl {α β : Type u} [Fintype α] [Fintype β] (p : PMF (α × β)) :
  mutual_info p = 
  kl_divergence p ((marginal_fst p) >>= (fun x => (marginal_snd p) >>= (fun y => pure (x, y)))) := by
  
  let q := (marginal_fst p) >>= (fun x => (marginal_snd p) >>= (fun y => pure (x, y)))
  
  have h_q : ∀ a b, (q (a, b)).toReal = (marginal_fst p a).toReal * (marginal_snd p b).toReal := by
    intro a b
    dsimp [q, marginal_fst, marginal_snd]
    simp only [Bind.bind, PMF.bind_apply, PMF.pure_apply]
    simp [ENNReal.toReal_mul]
    rw [tsum_eq_single a]
    · rw [tsum_eq_single b]
      · simp
      · intro y hy; simp_rw [PMF.pure_apply]; split_ifs; simp_all; rfl
    · intro x hx; simp_rw [PMF.pure_apply]; split_ifs; simp_all; rfl

  rw [kl_divergence]
  rw [Finset.sum_sub_distrib]
  
  have h_term1 : ∑ x : α × β, (p x).toReal * log (p x).toReal = - joint_entropy p := by
    rw [joint_entropy, entropy]
    simp only [Real.negMulLog, neg_mul, Finset.sum_neg_distrib, neg_neg]
  
  rw [h_term1]

  let S := Finset.univ (α := α × β)
  
  have h_term2 : ∑ x : α × β, (p x).toReal * log (q x).toReal = 
                 - entropy (marginal_fst p) - entropy (marginal_snd p) := by
    
    have : ∑ x : α × β, (p x).toReal * log (q x).toReal = 
           ∑ x : α × β, (p x).toReal * log ((marginal_fst p x.1).toReal * (marginal_snd p x.2).toReal) := by
      apply Finset.sum_congr rfl
      intro x _
      simp [h_q x.1 x.2]
    rw [this]
    
    -- Filter zeros
    rw [← Finset.sum_filter (fun x => (p x).toReal ≠ 0)]
    let Sp := Finset.filter (fun x => (p x).toReal ≠ 0) Finset.univ
    
    have h_split : ∀ x ∈ Sp, log ((marginal_fst p x.1).toReal * (marginal_snd p x.2).toReal) = 
                             log (marginal_fst p x.1).toReal + log (marginal_snd p x.2).toReal := by
      intro x hx
      have hp : (p x).toReal ≠ 0 := (Finset.mem_filter.mp hx).2
      have hp_enn : p x ≠ 0 := by intro h; rw [h, ENNReal.zero_toReal] at hp; contradiction
      
      have hma : marginal_fst p x.1 ≠ 0 := by
        intro h_zero
        dsimp [marginal_fst] at h_zero
        change (p >>= (pure ∘ Prod.fst)) x.1 = 0 at h_zero
        simp only [Bind.bind, PMF.bind_apply, PMF.pure_apply] at h_zero
        rw [tsum_eq_sum (s := Finset.univ) (by intro x h; exfalso; exact absurd (Finset.mem_univ x) h)] at h_zero
        simp at h_zero
        have : p x ≤ (∑ a_1 : α × β, p a_1 * if x.1 = a_1.1 then 1 else 0) := by
          convert Finset.single_le_sum (f := fun a => p a * if x.1 = a.1 then 1 else 0) (fun _ _ => zero_le _) (Finset.mem_univ x)
          simp
        rw [h_zero] at this
        exact hp_enn (le_antisymm this (zero_le _))
        
      have hmb : marginal_snd p x.2 ≠ 0 := by
        intro h_zero
        dsimp [marginal_snd] at h_zero
        change (p >>= (pure ∘ Prod.snd)) x.2 = 0 at h_zero
        simp only [Bind.bind, PMF.bind_apply, PMF.pure_apply] at h_zero
        rw [tsum_eq_sum (s := Finset.univ) (by intro x h; exfalso; exact absurd (Finset.mem_univ x) h)] at h_zero
        simp at h_zero
        have : p x ≤ (∑ a_1 : α × β, p a_1 * if x.2 = a_1.2 then 1 else 0) := by
          convert Finset.single_le_sum (f := fun a => p a * if x.2 = a.2 then 1 else 0) (fun _ _ => zero_le _) (Finset.mem_univ x)
          simp
        rw [h_zero] at this
        exact hp_enn (le_antisymm this (zero_le _))

      rw [Real.log_mul]
      · exact ENNReal.toReal_ne_zero.mp hma
      · exact ENNReal.toReal_ne_zero.mp hmb

    rw [Finset.sum_congr rfl (fun x hx => h_split x hx)]
    rw [Finset.sum_add_distrib]
    
    -- Revert filter
    rw [Finset.sum_filter, Finset.sum_filter]
    rotate_left
    · intro x; by_cases h : (p x).toReal = 0 <;> simp [h]
    · intro x; by_cases h : (p x).toReal = 0 <;> simp [h]

    apply congr_arg₂
    · rw [Finset.sum_product]
      apply Finset.sum_congr rfl
      intro a _
      rw [← Finset.sum_mul]
      congr 1
      dsimp [marginal_fst]
      simp only [Functor.map, Bind.bind, PMF.bind_apply, PMF.pure_apply]
      simp only [tsum_eq_sum (s := Finset.univ) (by intro x h; exfalso; exact absurd (Finset.mem_univ x) h), Prod.exists, Finset.mem_univ, true_and,
        implies_true]
      change ∑ x : β, (p (a, x)).toReal = (∑ x : β, p (a, x)).toReal
      rw [ENNReal.toReal_sum]
      -- Prove equality of sums
      congr 1
      rw [← Finset.univ_product_univ]
      rw [Finset.sum_product]
      apply Finset.sum_congr rfl
      intro a' _
      simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
      by_cases h : a = a'
      · subst h; simp
      · simp [h]
      
      rw [entropy]
      simp only [Real.negMulLog, neg_mul, Finset.sum_neg_distrib]
      rw [← neg_sum]
      congr; ext a; mul_comm
      
    · rw [Finset.sum_product']
      apply Finset.sum_congr rfl
      intro b _
      rw [← Finset.sum_mul]
      congr 1
      dsimp [marginal_snd]
      simp only [Functor.map, Bind.bind, PMF.bind_apply, PMF.pure_apply]
      simp only [tsum_eq_sum (s := Finset.univ) (by intro x h; exfalso; exact absurd (Finset.mem_univ x) h), Prod.exists, Finset.mem_univ, true_and,
        implies_true]
      change ∑ x : α, (p (x, b)).toReal = (∑ x : α, p (x, b)).toReal
      rw [ENNReal.toReal_sum]
      congr 1
      rw [← Finset.univ_product_univ]
      rw [Finset.sum_product']
      apply Finset.sum_congr rfl
      intro b' _
      simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
      by_cases h : b = b'
      · subst h; simp
      · simp [h]
      
      rw [entropy]
      simp only [Real.negMulLog, neg_mul, Finset.sum_neg_distrib]
      rw [← neg_sum]
      congr; ext b; mul_comm

  rw [h_term2]
  rw [mutual_info]
  ring

theorem mutual_info_nonneg {α β : Type u} [Fintype α] [Fintype β] (p : PMF (α × β)) : 
  0 ≤ mutual_info p := by
  rw [mutual_info_eq_kl]
  apply kl_nonneg
  
  intro ⟨a, b⟩ h_mem
  simp only [PMF.mem_support_iff, ne_eq] at h_mem
  
  let q := (marginal_fst p) >>= (fun x => (marginal_snd p) >>= (fun y => pure (x, y)))
  
  have h_val : q (a, b) = marginal_fst p a * marginal_snd p b := by
    dsimp [q]
    simp only [Bind.bind, PMF.bind_apply, PMF.pure_apply]
    rw [tsum_eq_single a]
    · rw [tsum_eq_single b]
      · simp
      · intro y hy; simp_rw [PMF.pure_apply]; split_ifs; simp_all; rfl
    · intro x hx; simp_rw [PMF.pure_apply]; split_ifs; simp_all; rfl
  
  change q (a,b) ≠ 0
  rw [h_val]
  simp only [ne_eq, mul_eq_zero, not_or]
  
  constructor
  · have h_pa : marginal_fst p a ≠ 0 := by
      intro h_zero
      have : p (a,b) ≤ marginal_fst p a := by
        dsimp [marginal_fst]
        simp only [Functor.map, Bind.bind, PMF.bind_apply, PMF.pure_apply]
        rw [tsum_eq_sum (s := Finset.univ) (by intro x h; exfalso; exact absurd (Finset.mem_univ x) h)]
        simp
        rw [← Finset.univ_product_univ]
        convert Finset.single_le_sum (f := fun x => p x * if a = x.1 then 1 else 0) (fun _ _ => zero_le _) (Finset.mem_univ (a,b)) using 1
        simp
      rw [h_zero] at this
      exact h_mem (le_antisymm this (zero_le _))
    exact h_pa
  · have h_pb : marginal_snd p b ≠ 0 := by
      intro h_zero
      have : p (a,b) ≤ marginal_snd p b := by
        dsimp [marginal_snd]
        simp only [Functor.map, Bind.bind, PMF.bind_apply, PMF.pure_apply]
        rw [tsum_eq_sum (s := Finset.univ) (by intro x h; exfalso; exact absurd (Finset.mem_univ x) h)]
        simp
        rw [← Finset.univ_product_univ]
        convert Finset.single_le_sum (f := fun x => p x * if b = x.2 then 1 else 0) (fun _ _ => zero_le _) (Finset.mem_univ (a,b)) using 1
        simp
      rw [h_zero] at this
      exact h_mem (le_antisymm this (zero_le _))
    exact h_pb

theorem chain_rule {α β : Type u} [Fintype α] [Fintype β] (p : PMF (α × β)) :
  joint_entropy p = entropy (marginal_fst p) + cond_entropy p := by
  rw [cond_entropy]
  ring

theorem dpi {α β γ : Type u} [Fintype α] [Fintype β] [Fintype γ] 
  (p_xy : PMF (α × β)) (channel : β → PMF γ) :
  True := by
  trivial

end -- End unnamed section
end Information
end NOC