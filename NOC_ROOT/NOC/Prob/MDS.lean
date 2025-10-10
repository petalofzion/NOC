import Mathlib
import Mathlib.Probability.Martingale.Basic
import Mathlib.Probability.Martingale.Convergence

/-!
Module: NOC.Prob.MDS
Status: scaffold + working partial‑sum API. This file hosts D1 (MDS
weighted‑sum convergence) and the supporting partial‑sum lemmas.

Mathlib toolkit we rely on (and will use when finishing D1):
- Conditional expectation API (real‑valued):
  * `MeasureTheory.condExp_smul`
  * `MeasureTheory.condExp_congr_ae`
  * `MeasureTheory.integral_condExp`
  * `MeasureTheory.condExp_mul_of_stronglyMeasurable_left`
    (file: MeasureTheory/Function/ConditionalExpectation/Real.lean)
- Martingale construction from zero conditional increment:
  * `ProbabilityTheory.martingale_of_condExp_sub_eq_zero_nat`
    (file: Probability/Martingale/Basic.lean)
- A.e. martingale/submartingale convergence (optional route for D1):
  * `MeasureTheory.Submartingale.ae_tendsto_limitProcess`
  * `MeasureTheory.Submartingale.exists_ae_tendsto_of_bdd`
    (file: Probability/Martingale/Convergence.lean)
- Chebyshev/Markov in Lp‑form (for tail bounds from L² or L¹):
  * `MeasureTheory.mul_meas_ge_le_pow_eLpNorm` and variants `'`
    (file: MeasureTheory/Function/LpSeminorm/ChebyshevMarkov.lean)
- Borel–Cantelli (first lemma, easy direction):
  * `MeasureTheory.measure_limsup_atTop_eq_zero`
    (file: MeasureTheory/OuterMeasure/BorelCantelli.lean)
- Standard Bochner integral utilities used throughout:
  * `Integrable.add`, `Integrable.smul`, `integrable_zero`
  * `integral_add`, `integral_sub'`, `integral_const_mul`, `integral_congr_ae`
  * `AEStronglyMeasurable.pow`

These are all available through `import Mathlib` plus the already imported
`Mathlib.Probability.Martingale.Basic`. No additional axioms are required.
-/

namespace NOC
namespace Prob
noncomputable section
open scoped BigOperators MeasureTheory ProbabilityTheory ENNReal
open Classical MeasureTheory Filter TopologicalSpace

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
variable {ℱ : MeasureTheory.Filtration ℕ m0}
variable [IsFiniteMeasure μ]

structure MDSData where
  seq : ℕ → Ω → ℝ
  adapted : Adapted ℱ seq
  integrable : ∀ n, Integrable (seq n) μ
  zero_condExp : ∀ n, μ[seq (n + 1) | ℱ n] =ᵐ[μ] 0
  variance_bound : ℝ
  variance_nonneg : 0 ≤ variance_bound
  second_moment_le : ∀ n, ∫ ω, (seq (n + 1) ω) ^ 2 ∂ μ ≤ variance_bound
  square_integrable : ∀ n, Integrable (fun ω => (seq (n + 1) ω) ^ 2) μ

namespace MDSData
variable (h : MDSData (μ:=μ) (ℱ:=ℱ))

-- (wrapper lemma removed; we directly use mathlib's Submartingale.exists_ae_tendsto_of_bdd at call sites)

-- (lemma removed; we perform the necessary pointwise identity inline where needed)

-- Helpers for exponent handling and `eLpNorm` at `p=2`.
private def half : ℝ := (1 / (2 : ℝ))

private lemma half_nonneg : 0 ≤ half := by
  simpa [half] using (by norm_num : 0 ≤ (1 / (2 : ℝ)))

/-- `eLpNorm` at `p = 2` in a convenient form (extended ℝ). -/
private lemma eLpNorm_two_eq_rpow
  (f : Ω → ℝ) :
  eLpNorm f (2 : ℝ≥0∞) μ
    = (∫⁻ ω, ‖f ω‖ₑ ^ (2 : ℝ) ∂ μ) ^ half := by
  have p_ne_zero : (2 : ℝ≥0∞) ≠ 0 := by simp
  have p_ne_top  : (2 : ℝ≥0∞) ≠ ∞ := by simp
  simpa [half] using
    (eLpNorm_eq_lintegral_rpow_enorm
      (μ := μ) (f := f) (p := (2 : ℝ≥0∞)) p_ne_zero p_ne_top)

-- (no pointwise helper lemma needed; we inline the identity for the concrete function `S` below)

@[simp] def partialSum (b : ℕ → ℝ) (n : ℕ) : Ω → ℝ :=
  fun ω => (Finset.range n).sum (fun k => b k * h.seq (k + 1) ω)

lemma partialSum_zero (b : ℕ → ℝ) : h.partialSum b 0 = 0 := by
  ext ω; simp [partialSum]

lemma partialSum_succ (b : ℕ → ℝ) (n : ℕ) :
    h.partialSum b (n + 1)
      = fun ω => h.partialSum b n ω + b n * h.seq (n + 1) ω := by
  classical
  ext ω; simp [partialSum, Finset.sum_range_succ, add_comm, add_left_comm, add_assoc]

lemma partialSum_adapted (b : ℕ → ℝ) :
    Adapted ℱ (fun n => h.partialSum b n) := by
  classical
  intro n
  induction' n with n ih
  · simpa [partialSum_zero] using
      (stronglyMeasurable_const : StronglyMeasurable[ℱ 0] (fun _ : Ω => (0 : ℝ)))
  · have ih' : StronglyMeasurable[ℱ (n + 1)] (h.partialSum b n) :=
      ih.mono (ℱ.mono (Nat.le_succ _))
    have hξ : StronglyMeasurable[ℱ (n + 1)] (h.seq (n + 1)) := h.adapted (n + 1)
    have hconst : StronglyMeasurable[ℱ (n + 1)] (fun _ : Ω => (b n : ℝ)) :=
      stronglyMeasurable_const
    have hscaled : StronglyMeasurable[ℱ (n + 1)] (fun ω => b n * h.seq (n + 1) ω) :=
      hconst.mul hξ
    simpa [partialSum_succ, mul_comm, mul_left_comm, mul_assoc] using ih'.add hscaled

lemma partialSum_integrable (b : ℕ → ℝ) :
    ∀ n, Integrable (h.partialSum b n) μ := by
  classical
  intro n
  induction' n with n ih
  · have hf : h.partialSum b 0 = fun _ : Ω => (0 : ℝ) := by
      ext ω; simp [partialSum]
    simpa [hf] using (MeasureTheory.integrable_zero : Integrable (fun _ : Ω => (0 : ℝ)) μ)
  · have hscaled : Integrable (fun ω => b n * h.seq (n + 1) ω) μ :=
      (h.integrable (n + 1)).smul (b n)
    have hsum := h.partialSum_succ (b := b) n
    simpa [hsum, smul_eq_mul] using ih.add hscaled

@[simp] lemma partialSum_diff (b : ℕ → ℝ) (n : ℕ) :
    (fun ω => h.partialSum b (n + 1) ω - h.partialSum b n ω)
      = fun ω => b n * h.seq (n + 1) ω := by
  classical
  funext ω
  simp [partialSum, Finset.sum_range_succ, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]

lemma scaled_condExp_zero (b : ℕ → ℝ) (n : ℕ) :
    μ[(fun ω => b n * h.seq (n + 1) ω) | ℱ n] =ᵐ[μ] 0 := by
  classical
  have hz := h.zero_condExp n
  have hsmul :
      μ[(fun ω => (b n) • h.seq (n + 1) ω) | ℱ n]
        =ᵐ[μ] (b n) • μ[(fun ω => h.seq (n + 1) ω) | ℱ n] :=
    condExp_smul (μ := μ) (m := ℱ n) (c := b n) (f := fun ω => h.seq (n + 1) ω)
  have hzero :
      μ[(fun ω => (b n) • h.seq (n + 1) ω) | ℱ n] =ᵐ[μ] 0 := by
    filter_upwards [hsmul, hz] with ω hω hzero
    simpa [Pi.zero_apply] using by simpa [hzero] using hω
  simpa [smul_eq_mul] using hzero

lemma partialSum_condExp_diff_zero (b : ℕ → ℝ) (n : ℕ) :
    μ[(fun ω => h.partialSum b (n + 1) ω - h.partialSum b n ω) | ℱ n]
      =ᵐ[μ] 0 := by
  classical
  have hdiffAE :
      (fun ω => h.partialSum b (n + 1) ω - h.partialSum b n ω)
        =ᵐ[μ] (fun ω => b n * h.seq (n + 1) ω) :=
    Filter.EventuallyEq.of_eq (partialSum_diff (h := h) (b := b) n)
  have hscaled := h.scaled_condExp_zero (b := b) n
  exact (MeasureTheory.condExp_congr_ae hdiffAE).trans hscaled

lemma partialSum_martingale (b : ℕ → ℝ) :
    Martingale (fun n => h.partialSum b n) ℱ μ := by
  classical
  refine martingale_of_condExp_sub_eq_zero_nat
    (hadp := h.partialSum_adapted b) (hint := h.partialSum_integrable b) ?_
  intro n
  simpa using h.partialSum_condExp_diff_zero (b := b) n

private def varianceTerm (b : ℕ → ℝ) (n : ℕ) : ℝ :=
  (Finset.range n).sum (fun k => (b k) ^ 2 * ∫ ω, (h.seq (k + 1) ω) ^ 2 ∂ μ)

private lemma varianceTerm_succ (b : ℕ → ℝ) (n : ℕ) :
    varianceTerm (h := h) (μ := μ) b (n + 1)
      = varianceTerm (h := h) (μ := μ) b n
        + (b n) ^ 2 * ∫ ω, (h.seq (n + 1) ω) ^ 2 ∂ μ := by
  classical
  unfold varianceTerm
  simp [Finset.sum_range_succ, add_comm, add_left_comm, add_assoc]

private lemma seq_sq_integrable (n : ℕ) :
    Integrable (fun ω => (h.seq (n + 1) ω) ^ 2) μ :=
  h.square_integrable n

private lemma diff_sq_integrable (b : ℕ → ℝ) (n : ℕ) :
    Integrable (fun ω => (b n * h.seq (n + 1) ω) ^ 2) μ := by
  classical
  have hsq := h.seq_sq_integrable n
  have hconst : Integrable (fun ω => (b n) ^ 2 * (h.seq (n + 1) ω) ^ 2) μ :=
    hsq.smul ((b n) ^ 2)
  have hcongr :
      (fun ω => (b n * h.seq (n + 1) ω) ^ 2)
        =ᵐ[μ] fun ω => (b n) ^ 2 * (h.seq (n + 1) ω) ^ 2 := by
    refine Filter.Eventually.of_forall ?_
    intro ω; simp [pow_two, mul_comm, mul_left_comm, mul_assoc]
  exact hconst.congr hcongr.symm

lemma partialSum_diff_sq_integral (b : ℕ → ℝ) (n : ℕ) :
    ∫ ω, (h.partialSum b (n + 1) ω - h.partialSum b n ω) ^ 2 ∂ μ
      = (b n) ^ 2 * ∫ ω, (h.seq (n + 1) ω) ^ 2 ∂ μ := by
  classical
  have hcongr :
      (fun ω => (h.partialSum b (n + 1) ω - h.partialSum b n ω) ^ 2)
        =ᵐ[μ] fun ω => (b n * h.seq (n + 1) ω) ^ 2 :=
    Filter.Eventually.of_forall (fun ω => by
      have hpoint := congrArg (fun f : Ω → ℝ => f ω)
          (partialSum_diff (h := h) (b := b) n)
      have := congrArg (fun t : ℝ => t ^ 2) hpoint
      simpa [pow_two])
  have hsq := h.seq_sq_integrable n
  have hcalc1 :
      ∫ ω, (h.partialSum b (n + 1) ω - h.partialSum b n ω) ^ 2 ∂ μ
        = ∫ ω, (b n * h.seq (n + 1) ω) ^ 2 ∂ μ :=
    integral_congr_ae hcongr
  have hrewrite :
      (fun ω => (b n * h.seq (n + 1) ω) ^ 2)
        = fun ω => (b n) ^ 2 * (h.seq (n + 1) ω) ^ 2 := by
    funext ω; simp [pow_two, mul_comm, mul_left_comm, mul_assoc]
  have hcalc2 :
      ∫ ω, (b n * h.seq (n + 1) ω) ^ 2 ∂ μ
        = (b n) ^ 2 * ∫ ω, (h.seq (n + 1) ω) ^ 2 ∂ μ := by
    simpa [hrewrite]
      using integral_const_mul (μ := μ) ((b n) ^ 2) (fun ω => (h.seq (n + 1) ω) ^ 2)
  exact hcalc1.trans hcalc2

private lemma add_sq_le_two_sq (x y : ℝ) :
    (x + y) ^ 2 ≤ 2 * (x ^ 2 + y ^ 2) := by
  have hx : (x - y) ^ 2 ≥ 0 := sq_nonneg _
  have hy : (x + y) ^ 2 ≥ 0 := sq_nonneg _
  nlinarith [hx, hy]

private lemma partialSum_sq_integrable_aux (b : ℕ → ℝ) :
    ∀ n, Integrable (fun ω => (h.partialSum b n ω) ^ 2) μ := by
  classical
  refine Nat.rec ?base ?step
  · have hz : h.partialSum b 0 = fun _ : Ω => (0 : ℝ) := by
      ext ω; simp [partialSum]
    simpa [hz] using
      (MeasureTheory.integrable_zero : Integrable (fun _ : Ω => (0 : ℝ)) μ)
  · intro n hn
    have hSn_sq : Integrable (fun ω => (h.partialSum b n ω) ^ 2) μ := hn
    have hΔ_sq : Integrable (fun ω => (b n * h.seq (n + 1) ω) ^ 2) μ :=
      h.diff_sq_integrable (b := b) n
    have hsum : Integrable
        (fun ω => (h.partialSum b n ω) ^ 2 + (b n * h.seq (n + 1) ω) ^ 2) μ := by
      simpa [pow_two] using hSn_sq.add hΔ_sq
    have hbound : ∀ᵐ ω ∂ μ,
        ‖(h.partialSum b (n + 1) ω) ^ 2‖
          ≤ (2 : ℝ) * ((h.partialSum b n ω) ^ 2 + (b n * h.seq (n + 1) ω) ^ 2) := by
      refine Filter.Eventually.of_forall ?_
      intro ω
      have hineq := add_sq_le_two_sq (x := h.partialSum b n ω)
        (y := b n * h.seq (n + 1) ω)
      have hineq' :
          (h.partialSum b (n + 1) ω) ^ 2
            ≤ (2 : ℝ) * ((h.partialSum b n ω) ^ 2
                + (b n * h.seq (n + 1) ω) ^ 2) := by
        simpa [partialSum, Finset.sum_range_succ, add_comm, add_left_comm, add_assoc]
          using hineq
      have hnonneg : 0 ≤ (h.partialSum b (n + 1) ω) ^ 2 := sq_nonneg _
      have hnorm :
          ‖(h.partialSum b (n + 1) ω) ^ 2‖
            = (h.partialSum b (n + 1) ω) ^ 2 := by
        simpa [Real.norm_eq_abs, abs_of_nonneg hnonneg]
      simpa [hnorm]
        using hineq'
    have hmeas : AEStronglyMeasurable
        (fun ω => (h.partialSum b (n + 1) ω) ^ 2) μ := by
      have hsm := (h.partialSum_adapted b) (n + 1)
      have hsm' : StronglyMeasurable (fun ω => h.partialSum b (n + 1) ω) :=
        (hsm.mono (ℱ.le (n + 1)))
      exact (hsm'.pow 2).aestronglyMeasurable
    refine Integrable.mono' ?_ hmeas hbound
    have : Integrable (fun ω => (2 : ℝ)
        * ((h.partialSum b n ω) ^ 2 + (b n * h.seq (n + 1) ω) ^ 2)) μ := by
      simpa using hsum.smul (2 : ℝ)
    exact this

lemma partialSum_sq_integrable (b : ℕ → ℝ) (n : ℕ) :
    Integrable (fun ω => (h.partialSum b n ω) ^ 2) μ :=
  partialSum_sq_integrable_aux (h := h) b n

private lemma abs_mul_le_half_sq_add_sq (x y : ℝ) :
    |x * y| ≤ (x ^ 2 + y ^ 2) / 2 := by
  have hsq : (|x| - |y|) ^ 2 ≥ 0 := sq_nonneg _
  have hineq1 : 0 ≤ |x| ^ 2 - 2 * |x| * |y| + |y| ^ 2 := by
    have hh : (|x| - |y|) ^ 2 = |x| ^ 2 - 2 * |x| * |y| + |y| ^ 2 := by
      ring
    simpa [hh] using hsq
  have hx : |x| ^ 2 = x ^ 2 := by simpa [pow_two]
  have hy : |y| ^ 2 = y ^ 2 := by simpa [pow_two]
  have hineq2 : 0 ≤ x ^ 2 - 2 * |x| * |y| + y ^ 2 := by
    simpa [hx, hy] using hineq1
  have hineq0 : 0 ≤ x ^ 2 + y ^ 2 - 2 * |x * y| := by
    simpa [abs_mul, mul_comm, mul_left_comm, mul_assoc, sub_eq_add_neg, add_comm,
      add_left_comm, add_assoc]
      using hineq2
  have hineq' : 2 * |x * y| ≤ x ^ 2 + y ^ 2 :=
    sub_nonneg.mp hineq0
  have hmul :=
    (mul_le_mul_of_nonneg_right hineq' (by norm_num : 0 ≤ (1 / 2 : ℝ)) :
      (2 * |x * y|) * (1 / 2 : ℝ) ≤ (x ^ 2 + y ^ 2) * (1 / 2 : ℝ))
  exact
    (by
      simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
        using hmul)

private lemma partialSum_mul_diff_integrable (b : ℕ → ℝ) (n : ℕ) :
    Integrable (fun ω => h.partialSum b n ω * (b n * h.seq (n + 1) ω)) μ := by
  classical
  have hSn_sq := partialSum_sq_integrable (h := h) b n
  have hΔ_sq : Integrable (fun ω => (b n * h.seq (n + 1) ω) ^ 2) μ :=
    h.diff_sq_integrable (b := b) n
  have hsum : Integrable (fun ω => (h.partialSum b n ω) ^ 2
      + (b n * h.seq (n + 1) ω) ^ 2) μ := by
    simpa [pow_two] using hSn_sq.add hΔ_sq
  have hmeasSn : AEStronglyMeasurable (fun ω => h.partialSum b n ω) μ :=
    (h.partialSum_integrable (b := b) n).aestronglyMeasurable
  have hmeasΔ : AEStronglyMeasurable (fun ω => b n * h.seq (n + 1) ω) μ :=
    ((h.integrable (n + 1)).smul (b n)).aestronglyMeasurable
  have hmeas : AEStronglyMeasurable
      (fun ω => h.partialSum b n ω * (b n * h.seq (n + 1) ω)) μ :=
    hmeasSn.mul hmeasΔ
  have hbound : ∀ᵐ ω ∂ μ,
      ‖h.partialSum b n ω * (b n * h.seq (n + 1) ω)‖
        ≤ ((h.partialSum b n ω) ^ 2 + (b n * h.seq (n + 1) ω) ^ 2) / 2 := by
    refine Filter.Eventually.of_forall ?_
    intro ω
    simpa [Real.norm_eq_abs, abs_mul, mul_comm, mul_left_comm, mul_assoc]
      using abs_mul_le_half_sq_add_sq (x := h.partialSum b n ω)
        (y := b n * h.seq (n + 1) ω)
  have : Integrable (fun ω =>
      ((h.partialSum b n ω) ^ 2 + (b n * h.seq (n + 1) ω) ^ 2) / 2) μ := by
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
      using hsum.smul (1 / 2 : ℝ)
  exact Integrable.mono' this hmeas hbound

private lemma partialSum_cross_integral_zero (b : ℕ → ℝ) (n : ℕ) :
    ∫ ω, h.partialSum b n ω * (b n * h.seq (n + 1) ω) ∂ μ = 0 := by
  classical
  have hmeas : AEStronglyMeasurable (fun ω => h.partialSum b n ω) μ :=
    (h.partialSum_integrable (b := b) n).aestronglyMeasurable
  have hmeasFil : AEStronglyMeasurable[ℱ n]
      (fun ω => h.partialSum b n ω) μ :=
    ((h.partialSum_adapted (b := b)) n).aestronglyMeasurable
  have hint_prod := h.partialSum_mul_diff_integrable (b := b) n
  have hint_g : Integrable (fun ω => b n * h.seq (n + 1) ω) μ :=
    (h.integrable (n + 1)).smul (b n)
  have hce :=
    (condExp_mul_of_aestronglyMeasurable_left
      (μ := μ) (m := ℱ n)
      (hf := hmeasFil) (hg := hint_g) (hfg := hint_prod))
  have hcond := h.scaled_condExp_zero (b := b) n
  have hce_zero :
      μ[
        fun ω => h.partialSum b n ω * (b n * h.seq (n + 1) ω)
        | ℱ n] =ᵐ[μ] 0 := by
    refine hce.trans ?_
    filter_upwards [hcond] with ω hω
    simp [hω]
  have hmono : ℱ n ≤ m0 := ℱ.le _
  have hcond_integral :=
    (integral_condExp (μ := μ) (m := ℱ n)
      (f := fun ω => h.partialSum b n ω * (b n * h.seq (n + 1) ω))
      hmono).symm
  have hzero :
      ∫ ω, (μ[
        fun ω => h.partialSum b n ω * (b n * h.seq (n + 1) ω)
        | ℱ n]) ω ∂ μ = 0 := by
    have :=
      integral_congr_ae (μ := μ) hce_zero
    simpa using this
  exact hcond_integral.trans hzero

private lemma partialSum_sq_integral_eq_varianceTerm (b : ℕ → ℝ) :
    ∀ n, ∫ ω, (h.partialSum b n ω) ^ 2 ∂ μ = varianceTerm (h := h) (μ := μ) b n := by
  classical
  refine Nat.rec ?base ?step
  · -- base case n = 0
    simp [varianceTerm, h.partialSum_zero (b := b)]
  · intro n hn
    -- Notation
    set S : Ω → ℝ := fun ω => h.partialSum b n ω
    set d : Ω → ℝ := fun ω => b n * h.seq (n + 1) ω
    -- Integrability of pieces
    have hintS2 : Integrable (fun ω => (S ω) ^ 2) μ :=
      by simpa [S] using partialSum_sq_integrable (h := h) (b := b) n
    have hintD2 : Integrable (fun ω => (d ω) ^ 2) μ :=
      by
        have := h.diff_sq_integrable (b := b) n
        simpa [d, pow_two, mul_comm, mul_left_comm, mul_assoc]
          using this
    have hintSD : Integrable (fun ω => S ω * d ω) μ :=
      by
        have := h.partialSum_mul_diff_integrable (b := b) n
        simpa [S, d] using this
    -- Expand the square and integrate
    have hpoint : ∀ ω, (S ω + d ω) ^ 2 = S ω ^ 2 + 2 * (S ω * d ω) + d ω ^ 2 := by
      intro ω; ring
    have hsum_int : Integrable (fun ω => S ω ^ 2 + 2 * (S ω * d ω)) μ :=
      by simpa using hintS2.add (hintSD.smul (2 : ℝ))
    have h1 : ∫ ω, (S ω + d ω) ^ 2 ∂ μ
        = ∫ ω, S ω ^ 2 ∂ μ + ∫ ω, 2 * (S ω * d ω) ∂ μ + ∫ ω, d ω ^ 2 ∂ μ := by
      have : ∫ ω, (S ω + d ω) ^ 2 ∂ μ
          = ∫ ω, (S ω ^ 2 + 2 * (S ω * d ω) + d ω ^ 2) ∂ μ := by
        have hcongr : (fun ω => (S ω + d ω) ^ 2)
            =ᵐ[μ] (fun ω => S ω ^ 2 + 2 * (S ω * d ω) + d ω ^ 2) :=
          Filter.Eventually.of_forall hpoint
        exact integral_congr_ae hcongr
      calc
        ∫ ω, (S ω + d ω) ^ 2 ∂ μ
            = ∫ ω, (S ω ^ 2 + 2 * (S ω * d ω) + d ω ^ 2) ∂ μ := this
        _ = (∫ ω, (S ω ^ 2 + 2 * (S ω * d ω)) ∂ μ)
              + ∫ ω, d ω ^ 2 ∂ μ := by
              simpa [add_comm, add_left_comm, add_assoc]
                using integral_add (hf := hsum_int) (hg := hintD2)
        _ = (∫ ω, S ω ^ 2 ∂ μ + ∫ ω, 2 * (S ω * d ω) ∂ μ)
              + ∫ ω, d ω ^ 2 ∂ μ := by
              simpa using integral_add (hf := hintS2) (hg := hintSD.smul (2 : ℝ))
    -- Cross term vanishes (conditional expectation zero)
    have hcross : ∫ ω, 2 * (S ω * d ω) ∂ μ = 0 := by
      have base := h.partialSum_cross_integral_zero (b := b) n
      have hcross0 : ∫ ω, S ω * d ω ∂ μ = 0 := by simpa [S, d] using base
      have hconst : ∫ ω, 2 * (S ω * d ω) ∂ μ = 2 * ∫ ω, S ω * d ω ∂ μ := by
        simpa [smul_eq_mul] using
          (integral_const_mul (μ := μ) (r := (2 : ℝ)) (f := fun ω => S ω * d ω))
      simpa [hcross0] using hconst
    -- Difference-square integral equals (b n)^2 times second moment
    have hd2 : ∫ ω, d ω ^ 2 ∂ μ = (b n) ^ 2 * ∫ ω, (h.seq (n + 1) ω) ^ 2 ∂ μ := by
      -- rewrite the integrand and pull out the constant
      have hrewrite : (fun ω => (d ω) ^ 2)
          = (fun ω => (b n) ^ 2 * (h.seq (n + 1) ω) ^ 2) := by
        funext ω
        simp [d, pow_two, mul_comm, mul_left_comm, mul_assoc]
      simpa [hrewrite] using
        (integral_const_mul (μ := μ) ((b n) ^ 2) (fun ω => (h.seq (n + 1) ω) ^ 2))
    -- Put everything together and use the inductive hypothesis and varianceTerm recursion
    -- Relate the target integral with the split using AE congruence
    have hfun_sq : (fun ω => (h.partialSum b (n + 1) ω) ^ 2)
          =ᵐ[μ] (fun ω => (h.partialSum b n ω + b n * h.seq (n + 1) ω) ^ 2) := by
      refine Filter.Eventually.of_forall ?_
      intro ω
      have := congrArg (fun f : Ω → ℝ => f ω) (h.partialSum_succ (b := b) n)
      -- Square both sides
      simpa using congrArg (fun t : ℝ => t ^ 2) this
    have hsum_eq : ∫ ω, (h.partialSum b (n + 1) ω) ^ 2 ∂ μ
          = ∫ ω, (S ω + d ω) ^ 2 ∂ μ := by
      have := integral_congr_ae hfun_sq
      simpa [S, d] using this
    have hsplit_main : ∫ ω, (S ω + d ω) ^ 2 ∂ μ
          = ∫ ω, S ω ^ 2 ∂ μ + ∫ ω, d ω ^ 2 ∂ μ := by
      calc
        ∫ ω, (S ω + d ω) ^ 2 ∂ μ
            = ∫ ω, S ω ^ 2 ∂ μ + ∫ ω, 2 * (S ω * d ω) ∂ μ + ∫ ω, d ω ^ 2 ∂ μ := h1
        _ = ∫ ω, S ω ^ 2 ∂ μ + 0 + ∫ ω, d ω ^ 2 ∂ μ := by simp [hcross]
        _ = ∫ ω, S ω ^ 2 ∂ μ + ∫ ω, d ω ^ 2 ∂ μ := by ring
    calc
      ∫ ω, (h.partialSum b (n + 1) ω) ^ 2 ∂ μ
          = ∫ ω, (S ω + d ω) ^ 2 ∂ μ := hsum_eq
      _ = ∫ ω, S ω ^ 2 ∂ μ + ∫ ω, d ω ^ 2 ∂ μ := hsplit_main
      _ = ∫ ω, S ω ^ 2 ∂ μ + (b n) ^ 2 * ∫ ω, (h.seq (n + 1) ω) ^ 2 ∂ μ := by
            simpa [hd2]
      _ = varianceTerm (h := h) (μ := μ) b n
            + (b n) ^ 2 * ∫ ω, (h.seq (n + 1) ω) ^ 2 ∂ μ := by
            simpa [S] using hn
      _ = varianceTerm (h := h) (μ := μ) b (n + 1) := by
            simpa [varianceTerm_succ (h := h) (μ := μ) b n]
end MDSData

end

/-!
## D1 — MDS weighted-sum convergence (scaffolding)

This section provides a lightweight, non-committal statement for the
convergence of weighted sums of a martingale-difference sequence (MDS).
It is a placeholder theorems layer designed to be consumed by the
ODE/SA meta-theorem. The concrete proof (via L2-bounds and
Chebyshev/Borel–Cantelli, or via mathlib’s martingale convergence)
will be added later.
-/

namespace NOC
namespace Prob

/-- Hypotheses for 1D weighted MDS sums. The fields are intentionally
lightweight `Prop`s to keep this module independent of a specific
measure-theory API. Downstream instances (when available) can refine
these to mathlib statements. -/
structure MDSWeightedSumHypotheses where
  steps_sq_summable : Prop     -- ∑ b_n^2 < ∞
  mds_zero_mean     : Prop     -- E[ξ_{n+1} | 𝓕_n] = 0
  variance_bounded  : Prop     -- E[ξ_{n+1}^2 | 𝓕_n] ≤ σ^2

/-- Conclusion shape for the weighted MDS convergence. -/
structure MDSWeightedSumConclusion where
  L2_converges : Prop
  asexists_sum : Prop    -- almost sure existence of the infinite series

/-- D1 scaffold: weighted MDS convergence (statement-only layer).
Populate with a real proof once the probability layer lands. -/
def mds_weighted_sum_converges (H : MDSWeightedSumHypotheses)
    : MDSWeightedSumConclusion :=
  { L2_converges := True, asexists_sum := True }

end Prob
end NOC

/-!
## D1 — Concrete weighted MDS convergence (AE limit via submartingale convergence)

We provide a concrete almost-everywhere convergence result for the weighted sum
`S n = ∑_{k<n} b k * ξ_{k+1}` under square–summable steps and a uniform second–moment
bound on the MDS `ξ`. The proof builds a martingale with square–summable increments,
derives a uniform L¹ bound via Hölder, and applies the a.e. submartingale convergence
theorem from mathlib.
-/

namespace NOC
namespace Prob

open Classical MeasureTheory Filter
open scoped BigOperators ProbabilityTheory ENNReal

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
variable {ℱ : MeasureTheory.Filtration ℕ m0}
variable [IsFiniteMeasure μ]

namespace MDSData
variable (h : MDSData (μ:=μ) (ℱ:=ℱ))

/-- If `(b n)^2` is summable, then the partial sums form an L¹–bounded submartingale,
and hence converge almost everywhere. -/
theorem weighted_sum_ae_converges
  (b : ℕ → ℝ)
  (hb2 : Summable (fun n => (b n) ^ 2)) :
  ∀ᵐ ω ∂ μ, ∃ c, Tendsto (fun n => h.partialSum b n ω) atTop (nhds c) := by
  classical
  -- Consider the martingale (and submartingale) of partial sums.
  have hmart : Martingale (fun n => h.partialSum b n) ℱ μ := h.partialSum_martingale b
  have hsub : Submartingale (fun n => h.partialSum b n) ℱ μ := hmart.submartingale

  -- Helper: nonnegativity of (b n)^2
  have h_nonneg_sq : ∀ n, 0 ≤ (b n) ^ 2 := fun _ => sq_nonneg _

  -- Real second-moment bound: ∫ (S n)^2 ≤ variance_bound * ∑_{k<n} (b k)^2
  have h_variance_bound_sum :
      ∀ n, ∫ ω, (h.partialSum b n ω) ^ 2 ∂ μ
          ≤ h.variance_bound * (Finset.range n).sum (fun k => (b k) ^ 2) := by
    intro n
    -- Expand by variance identity
    have hvar :
        ∫ ω, (h.partialSum b n ω) ^ 2 ∂ μ
          = (Finset.range n).sum (fun k => (b k) ^ 2 * ∫ ω, (h.seq (k + 1) ω) ^ 2 ∂ μ) := by
      simpa using h.partialSum_sq_integral_eq_varianceTerm (b := b) n
    -- Bound each term and pull out the constant
    have hsum_le :
        (Finset.range n).sum (fun k => (b k) ^ 2 * ∫ ω, (h.seq (k + 1) ω) ^ 2 ∂ μ)
          ≤ (Finset.range n).sum (fun k => (b k) ^ 2 * h.variance_bound) := by
      refine Finset.sum_le_sum ?_
      intro k hk
      have hk_nonneg : 0 ≤ (b k) ^ 2 := h_nonneg_sq k
      have := h.second_moment_le k
      have hx : (b k) ^ 2 * ∫ ω, (h.seq (k + 1) ω) ^ 2 ∂ μ
                ≤ (b k) ^ 2 * h.variance_bound := by
        exact mul_le_mul_of_nonneg_left this hk_nonneg
      simpa using hx
    have hpull :
        (Finset.range n).sum (fun k => (b k) ^ 2 * h.variance_bound)
          = h.variance_bound * (Finset.range n).sum (fun k => (b k) ^ 2) := by
      classical
      -- `∑ (b k)^2 * C = C * ∑ (b k)^2`.
      simpa [mul_comm, mul_left_comm, mul_assoc] using
        (Finset.sum_mul (s := Finset.range n)
          (f := fun k => (b k) ^ 2) (a := h.variance_bound)).symm
    -- Conclude the desired bound on the real second moment of `S`.
    have : ∫ ω, (h.partialSum b n ω) ^ 2 ∂ μ
          ≤ h.variance_bound * (Finset.range n).sum (fun k => (b k) ^ 2) := by
      calc
        ∫ ω, (h.partialSum b n ω) ^ 2 ∂ μ
            = (Finset.range n).sum (fun k => (b k) ^ 2 * ∫ ω, (h.seq (k + 1) ω) ^ 2 ∂ μ) := by
              simpa [hvar]
        _ ≤ (Finset.range n).sum (fun k => (b k) ^ 2 * h.variance_bound) := hsum_le
        _ = h.variance_bound * (Finset.range n).sum (fun k => (b k) ^ 2) := by
              simpa [hpull]
    exact this

  -- Compare finite sums to series: ∑_{k<n} (b k)^2 ≤ ∑' (b k)^2
  have hsum_le_tsum : ∀ n, (Finset.range n).sum (fun k => (b k) ^ 2)
      ≤ ∑' n, (b n) ^ 2 := by
    intro n
    -- order version works for nonnegative terms
    refine Summable.sum_le_tsum (s := Finset.range n)
      (f := fun k => (b k) ^ 2) (fun k _ => h_nonneg_sq k) ?_
    exact hb2

  -- L² bound on eLpNorm(S n): eLpNorm 2 ≤ const (independent of n)
  have hL2_bound : ∀ n,
      eLpNorm (h.partialSum b n) (2 : ℝ≥0∞) μ
        ≤ (ENNReal.ofReal (h.variance_bound * (∑' n, (b n) ^ 2))) ^ ((1 : ℝ) / 2) := by
    intro n
    -- convert lintegral of ‖·‖ₑ^2 to ofReal of the (Bochner) integral of (·)^2
    let S : Ω → ℝ := fun ω => h.partialSum b n ω
    have hint : Integrable (fun ω => (S ω) ^ 2) μ :=
      (NOC.Prob.MDSData.partialSum_sq_integrable (h := h) (b := b) n)
    have hnn : 0 ≤ᵐ[μ] (fun ω => (S ω) ^ 2) :=
      Filter.Eventually.of_forall (by intro ω; exact sq_nonneg _)
    have hpoint : ∀ ω, (‖S ω‖ₑ ^ 2) = ENNReal.ofReal ((S ω) ^ 2) := by
      intro ω
      have hx : 0 ≤ ‖S ω‖ := norm_nonneg _
      have hdef : ‖S ω‖ₑ = ENNReal.ofReal |S ω| := by
        simpa using (Real.enorm_eq_ofReal_abs (S ω))
      calc
        (‖S ω‖ₑ ^ 2) = ‖S ω‖ₑ * ‖S ω‖ₑ := by simp [pow_two]
        _ = ENNReal.ofReal |S ω| * ENNReal.ofReal |S ω| := by simpa [hdef]
        _ = ENNReal.ofReal (‖S ω‖ * ‖S ω‖) := by
          simpa [mul_comm] using
            ((ENNReal.ofReal_mul (hp := abs_nonneg _)
                : ENNReal.ofReal (|S ω| * |S ω|)
                  = ENNReal.ofReal |S ω| * ENNReal.ofReal |S ω|).symm)
        _ = ENNReal.ofReal ((|S ω|) ^ 2) := by simp [pow_two]
        _ = ENNReal.ofReal ((S ω) ^ 2) := by simpa [sq_abs]
    have hlin : ∫⁻ ω, ‖S ω‖ₑ ^ 2 ∂ μ = ENNReal.ofReal (∫ ω, (S ω) ^ 2 ∂ μ) := by
      have h₁ : ∫⁻ ω, ‖S ω‖ₑ ^ 2 ∂ μ
          = ∫⁻ ω, ENNReal.ofReal ((S ω) ^ 2) ∂ μ :=
        lintegral_congr_ae (Filter.Eventually.of_forall hpoint)
      have h₂ : ∫⁻ ω, ENNReal.ofReal ((S ω) ^ 2) ∂ μ
          = ENNReal.ofReal (∫ ω, (S ω) ^ 2 ∂ μ) :=
        (ofReal_integral_eq_lintegral_ofReal (μ := μ)
          (f := fun ω => (S ω) ^ 2) hint hnn).symm
      exact h₁.trans h₂
    -- push the real inequality via ofReal and take 1/2-power
    have hb_real : ∫ ω, (S ω) ^ 2 ∂ μ
        ≤ h.variance_bound * (Finset.range n).sum (fun k => (b k) ^ 2) :=
      h_variance_bound_sum n
    have hb_lint : ∫⁻ ω, ‖S ω‖ₑ ^ 2 ∂ μ
        ≤ ENNReal.ofReal (h.variance_bound * (Finset.range n).sum (fun k => (b k) ^ 2)) := by
      calc
        ∫⁻ ω, ‖S ω‖ₑ ^ 2 ∂ μ
            = ENNReal.ofReal (∫ ω, (S ω) ^ 2 ∂ μ) := hlin
        _ ≤ ENNReal.ofReal (h.variance_bound * (Finset.range n).sum (fun k => (b k) ^ 2)) :=
            ENNReal.ofReal_le_ofReal hb_real
    -- First bound with the finite sum inside `ofReal`.
    have hA : eLpNorm (h.partialSum b n) (2 : ℝ≥0∞) μ
        ≤ (ENNReal.ofReal (h.variance_bound
            * (Finset.range n).sum (fun k => (b k) ^ 2))) ^ ((1 : ℝ) / 2) := by
      have hpow := ENNReal.rpow_le_rpow hb_lint (by norm_num : 0 ≤ ((1 : ℝ) / 2))
      have p_ne_zero : (2 : ℝ≥0∞) ≠ 0 := by simp
      have p_ne_top  : (2 : ℝ≥0∞) ≠ ∞ := by simp
      have e2 :=
        (eLpNorm_eq_lintegral_rpow_enorm (μ := μ) (f := S)
          (p := (2 : ℝ≥0∞)) p_ne_zero p_ne_top)
      have e2' : eLpNorm (h.partialSum b n) (2 : ℝ≥0∞) μ
            = (∫⁻ ω, ‖S ω‖ₑ ^ 2 ∂ μ) ^ ((1 : ℝ) / 2) := by
        simpa [S] using e2
      -- Now rewrite the left side by `e2'`.
      simpa [e2'] using hpow
    -- Then upgrade finite sum to the full series by monotonicity.
    have hsum_le' :
      ENNReal.ofReal (h.variance_bound * (Finset.range n).sum (fun k => (b k) ^ 2))
        ≤ ENNReal.ofReal (h.variance_bound * (∑' n, (b n) ^ 2)) := by
      have hmul_mono :
          h.variance_bound * (Finset.range n).sum (fun k => (b k) ^ 2)
            ≤ h.variance_bound * (∑' n, (b n) ^ 2) := by
        exact mul_le_mul_of_nonneg_left (hsum_le_tsum n) h.variance_nonneg
      exact ENNReal.ofReal_le_ofReal hmul_mono
    have hB : (ENNReal.ofReal (h.variance_bound * (Finset.range n).sum (fun k => (b k) ^ 2))) ^ ((1 : ℝ) / 2)
        ≤ (ENNReal.ofReal (h.variance_bound * (∑' n, (b n) ^ 2))) ^ ((1 : ℝ) / 2) := by
      exact ENNReal.rpow_le_rpow hsum_le' (by norm_num : 0 ≤ ((1 : ℝ) / 2))
    exact hA.trans hB

  -- L¹ bound via exponent comparison (p = 1 ≤ 2 = q) and finite measure
  have hpq : (1 : ℝ≥0∞) ≤ (2 : ℝ≥0∞) := by norm_num
  have hL1_bound' : ∀ n,
      eLpNorm (h.partialSum b n) (1 : ℝ≥0∞) μ
        ≤ ((ENNReal.ofReal (h.variance_bound * (∑' n, (b n) ^ 2))) ^ ((1 : ℝ) / 2))
          * (μ Set.univ) ^ (1 / (1 : ℝ) - 1 / (2 : ℝ)) := by
    intro n
    have hsm : AEStronglyMeasurable (h.partialSum b n) μ :=
      (h.partialSum_integrable (b := b) n).aestronglyMeasurable
    have base :
        eLpNorm (h.partialSum b n) (1 : ℝ≥0∞) μ
          ≤ eLpNorm (h.partialSum b n) (2 : ℝ≥0∞) μ
              * (μ Set.univ) ^ (1 / (1 : ℝ) - 1 / (2 : ℝ)) := by
      simpa using
        (eLpNorm_le_eLpNorm_mul_rpow_measure_univ (μ := μ)
          (f := h.partialSum b n) hpq hsm)
    have step :
        eLpNorm (h.partialSum b n) (2 : ℝ≥0∞) μ
            * (μ Set.univ) ^ (1 / (1 : ℝ) - 1 / (2 : ℝ))
          ≤ (ENNReal.ofReal (h.variance_bound * (∑' n, (b n) ^ 2))) ^ ((1 : ℝ) / 2)
              * (μ Set.univ) ^ (1 / (1 : ℝ) - 1 / (2 : ℝ)) := by
      -- multiply both sides of the L² bound by a nonnegative constant
      have hnonneg : 0 ≤ (μ Set.univ) ^ (1 / (1 : ℝ) - 1 / (2 : ℝ)) := by
        simpa using (bot_le : (0 : ℝ≥0∞) ≤ (μ Set.univ) ^ (1 / (1 : ℝ) - 1 / (2 : ℝ)))
      exact (mul_le_mul_of_nonneg_right (hL2_bound n) hnonneg)
    exact base.trans step

  -- Package the bound into ℝ≥0 as expected by the convergence theorem
  set Rbound : ℝ≥0∞ :=
    ((ENNReal.ofReal (h.variance_bound * (∑' n, (b n) ^ 2))) ^ ((1 : ℝ) / 2))
      * (μ Set.univ) ^ (1 / (1 : ℝ) - 1 / (2 : ℝ))
  have hRfinite : Rbound < ⊤ := by
    have hne : ENNReal.ofReal (h.variance_bound * (∑' n, (b n) ^ 2)) ≠ (⊤ : ℝ≥0∞) := by
      simp
    have A : ((ENNReal.ofReal (h.variance_bound * (∑' n, (b n) ^ 2))) ^ ((1 : ℝ) / 2)) < ∞ := by
      refine ENNReal.rpow_lt_top_of_nonneg (by norm_num : 0 ≤ ((1 : ℝ) / 2)) hne
    have B : (μ Set.univ) ^ (1 / (1 : ℝ) - 1 / (2 : ℝ)) < ∞ := by
      exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) (measure_ne_top μ Set.univ)
    exact ENNReal.mul_lt_top_iff.2 (Or.inl ⟨A, B⟩)
  -- Provide an ℝ≥0 bound as required by the convergence lemma.
  -- Prepare the ℝ≥0 bound expected by the lemma
  have hRne_top : Rbound ≠ ⊤ := ne_of_lt hRfinite
  let Rnn : NNReal := ENNReal.toNNReal Rbound
  have hR_coe : (Rnn : ℝ≥0∞) = Rbound := ENNReal.coe_toNNReal hRne_top
  -- Option A: a.e. convergence via L¹-bounded submartingale
  have hbdd : ∀ n, eLpNorm (h.partialSum b n) (1 : ℝ≥0∞) μ ≤ (Rnn : ℝ≥0∞) := by
    intro n
    have hbd : eLpNorm (h.partialSum b n) (1 : ℝ≥0∞) μ ≤ Rbound := hL1_bound' n
    simpa [hR_coe] using hbd
  -- Apply a.e. convergence for submartingales. First get a.e. tendsto to the limitProcess,
  -- then package it as an existence statement.
  have h_tend : ∀ᵐ ω ∂ μ,
      Tendsto (fun n => h.partialSum b n ω) atTop
        (nhds (MeasureTheory.Filtration.limitProcess (fun n => h.partialSum b n) ℱ μ ω)) :=
    MeasureTheory.Submartingale.ae_tendsto_limitProcess
      (μ := μ) (ℱ := ℱ) (f := fun n => h.partialSum b n) (R := Rnn) hsub hbdd
  filter_upwards [h_tend] with ω hω
  exact ⟨(MeasureTheory.Filtration.limitProcess (fun n => h.partialSum b n) ℱ μ ω), hω⟩

end MDSData

end Prob
end NOC
