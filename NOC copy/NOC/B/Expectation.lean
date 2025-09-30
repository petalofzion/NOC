/-
  B_expectation.lean
  Finitary “expectation” (uniform average on a finite support) wrappers
  to lift the pointwise Lemma B bounds to an average statement.

  Intent wrt A2–A3 (see NOC doc):
  • A2 (“coverage”): the fraction of (task × seed) pairs that are in the HB/PL
    “good” regime is at least p₀.
  • A3 (“regularity outside”): Δ²U is bounded below by −M on the complement.
  • On the good regime, the determinant algebra (HB_CloseLoop + B_core mapping)
    gives Δ²U ≥ m₀ > 0 uniformly.

  This file turns those three facts into: average_{ω∈S} Δ²U(ω) > 0.
-/
import Mathlib
import NOC.B.Core
import NOC.HB.CloseLoop

/-!
Module: NOC.B.Expectation
Summary: Finitary expectation layer — lifts Lemma B pointwise/local bounds to uniform averages on finite supports.
Public entry points: `avg`, `lemmaB_expectation_finitary`, `lemmaB_expected_nonneg_finset`, `lemmaB_expected_nonneg_finset_abs`.
-/


namespace NOC
noncomputable section
open Classical
open scoped BigOperators


/-- Uniform arithmetic average of a function `x : Ω → ℝ` over a nonempty finite support `S`. -/
def avg {Ω : Type*} (S : Finset Ω) (x : Ω → ℝ) : ℝ :=
  S.sum (fun ω => x ω) / (S.card : ℝ)

@[simp] lemma avg_const {Ω} (S : Finset Ω) (hS : 0 < S.card) (c : ℝ) :
  avg S (fun _ => c) = c := by
  classical
  have h0 : (S.card : ℝ) ≠ 0 := by exact_mod_cast hS.ne'
  -- sum of a constant and divide
  simp [avg, Finset.sum_const, nsmul_eq_mul, h0]  -- no need for div_eq_iff/mul_comm


/-- Pointwise monotonicity lifts to averages. -/
lemma avg_mono {Ω : Type*} (S : Finset Ω) (hS : 0 < S.card)
  {x y : Ω → ℝ} (hxy : ∀ ω ∈ S, x ω ≤ y ω) :
  avg S x ≤ avg S y := by
  classical
  -- 1) Sum inequality from pointwise inequality on S
  have hsum : S.sum (fun ω => x ω) ≤ S.sum (fun ω => y ω) :=
    Finset.sum_le_sum (by intro ω hω; exact hxy ω hω)
  -- 2) Turn division by |S| into multiplication by its inverse, which is ≥ 0
  have hpos : 0 < (S.card : ℝ) := by exact_mod_cast hS
  have hinv_nonneg : 0 ≤ (S.card : ℝ)⁻¹ :=
    inv_nonneg.mpr (le_of_lt hpos)
  -- 3) Multiply both sides by the nonnegative scalar (|S|)⁻¹
  have h := mul_le_mul_of_nonneg_right hsum hinv_nonneg
  -- 4) Rewrite to the `avg` form
  simpa [avg, div_eq_mul_inv] using h

/-- Complement mass identity, convenient for split-average arguments.
For `G ⊆ S` and `S.card > 0`, we have `|S \ G| / |S| = 1 - |G| / |S|` (as reals). -/
lemma mass_sdiff_div
  {Ω : Type*} (S G : Finset Ω) (hGS : G ⊆ S) (hS : 0 < S.card) :
  ((S \ G).card : ℝ) / (S.card : ℝ) = 1 - (G.card : ℝ) / (S.card : ℝ) := by
  classical
  have hS_ne : (S.card : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hS)
  -- disjoint split and union
  have hdisj : Disjoint G (S \ G) := by
    refine Finset.disjoint_left.mpr ?_
    intro ω hωG hωSdiff
    exact (Finset.mem_sdiff.mp hωSdiff).2 hωG
  have hunion : G ∪ (S \ G) = S := Finset.union_sdiff_of_subset hGS
  -- sum of ones over the disjoint union gives a cardinality identity in ℝ
  have hsum :
      S.sum (fun _ => (1 : ℝ))
        = G.sum (fun _ => (1 : ℝ)) + (S \ G).sum (fun _ => (1 : ℝ)) := by
    -- Explicitly pass the summand to avoid typeclass inference sticking
    have :=
      (Finset.sum_union (s₁ := G) (s₂ := S \ G)
        (f := fun _ : Ω => (1 : ℝ)) hdisj)
    simpa [hunion, add_comm, add_left_comm, add_assoc] using this
  have hcard_add :
      (S.card : ℝ) = (G.card : ℝ) + ((S \ G).card : ℝ) := by
    simpa [Finset.sum_const, nsmul_eq_mul] using hsum
  -- rearrange and divide by |S|
  have hcomp :
      ((S \ G).card : ℝ) = (S.card : ℝ) - (G.card : ℝ) := by
    -- Use a + b = c ⇒ a = c − b, with a := |S\G|, b := |G|, c := |S|
    have hsum_cards : ((S \ G).card : ℝ) + (G.card : ℝ) = (S.card : ℝ) := by
      simpa [add_comm] using hcard_add.symm
    exact (eq_sub_iff_add_eq).mpr hsum_cards
  calc
    ((S \ G).card : ℝ) / (S.card : ℝ)
        = ((S.card : ℝ) - (G.card : ℝ)) / (S.card : ℝ) := by simpa [hcomp]
    _   = (S.card : ℝ) / (S.card : ℝ) - (G.card : ℝ) / (S.card : ℝ) := by
            simpa using (sub_div (S.card : ℝ) (G.card : ℝ) (S.card : ℝ))
    _   = 1 - (G.card : ℝ) / (S.card : ℝ) := by simp [div_self hS_ne]

/-- Split‑sum lower bound. If on a “good” subset `G ⊆ S` we have `x ≥ m₀`,
    and on the remaining `S \ G` we have `x ≥ −M`, then the sum over `S`
    is *at least* `G.card * m₀ + (S.card - G.card) * (−M)`. -/
lemma sum_lower_bound_split {Ω : Type*}
  (S G : Finset Ω) (x : Ω → ℝ) (hGS : G ⊆ S)
  {m0 M : ℝ}
  (hG  : ∀ ω ∈ G, x ω ≥ m0)
  (hBad : ∀ ω ∈ S \ G, x ω ≥ -M) :
  S.sum (fun ω => x ω) ≥ (G.card : ℝ) * m0 + ((S.card - G.card : ℕ) : ℝ) * (-M) := by
  classical
  -- Disjoint split and union
  have hdisj : Disjoint G (S \ G) := by
    classical
    refine Finset.disjoint_left.mpr ?_
    intro ω hωG hωSdiff
    -- unpack ω ∈ S \ G
    rcases Finset.mem_sdiff.mp hωSdiff with ⟨hωS, hωnotG⟩
    exact hωnotG hωG
  have hunion : G ∪ (S \ G) = S := Finset.union_sdiff_of_subset hGS
  -- Bound each part
  have hGsum : G.sum (fun ω => x ω) ≥ (G.card : ℝ) * m0 := by
    have : G.sum (fun ω => x ω) ≥ G.sum (fun _ => m0) :=
      Finset.sum_le_sum (by intro ω hω; exact hG ω hω)
    -- `∑ _∈G, m0 = (G.card) • m0 = (G.card : ℝ) * m0` on ℝ
    simpa [Finset.sum_const, nsmul_eq_mul, mul_comm] using this
  have hBsum : ((S \ G).sum (fun ω => x ω)) ≥ ((S \ G).card : ℝ) * (-M) := by
    have : (S \ G).sum (fun ω => x ω) ≥ (S \ G).sum (fun _ => (-M)) :=
      Finset.sum_le_sum (by intro ω hω; exact hBad ω hω)
    simpa [Finset.sum_const, nsmul_eq_mul, mul_comm] using this
  -- Combine the two pieces
  have hsplit :
      S.sum (fun ω => x ω) = G.sum (fun ω => x ω) + (S \ G).sum (fun ω => x ω) := by
    simpa [hunion, add_comm, add_left_comm, add_assoc] using
      (Finset.sum_union hdisj)
  -- Convert `((S \ G).card : ℝ)` to `S.card - G.card`
  have hcard :
      ((S \ G).card : ℝ) = (S.card - G.card : ℕ) := by
    -- standard cardinality: `card (S \ G) = S.card - G.card` since `G ⊆ S`
    have := Finset.card_sdiff hGS
    -- `card_sdiff` returns Nat; cast both sides to ℝ
    exact_mod_cast this
  -- Finish
  calc
    S.sum (fun ω => x ω)
        = G.sum (fun ω => x ω) + (S \ G).sum (fun ω => x ω) := hsplit
    _ ≥ (G.card : ℝ) * m0 + ((S \ G).card : ℝ) * (-M) := by
          exact add_le_add hGsum hBsum
    _ = (G.card : ℝ) * m0 + ((S.card - G.card : ℕ) : ℝ) * (-M) := by
          simp [hcard]

/-- Average lower bound obtained from the split‑sum inequality (no `div_le_div_right`). -/
lemma avg_lower_bound_split {Ω : Type*}
  (S G : Finset Ω) (x : Ω → ℝ) (hGS : G ⊆ S) (hS : 0 < S.card)
  {m0 M : ℝ}
  (hG  : ∀ ω ∈ G, x ω ≥ m0)
  (hBad : ∀ ω ∈ S \ G, x ω ≥ -M) :
  avg S x ≥ ((G.card : ℝ) / (S.card : ℝ)) * m0
         + (((S.card - G.card : ℕ) : ℝ) / (S.card : ℝ)) * (-M) := by
  classical
  -- Start from the split-sum lower bound (already proved)
  have hsum := sum_lower_bound_split S G x hGS hG hBad
  -- `|S| > 0` ⇒ its real cast is positive, so scaling preserves ≤
  have hpos : 0 < (S.card : ℝ) := by exact_mod_cast hS
  have hscale :
      (1 / (S.card : ℝ)) * S.sum (fun ω => x ω)
        ≥ (1 / (S.card : ℝ)) *
            ((G.card : ℝ) * m0 + ((S.card - G.card : ℕ) : ℝ) * (-M)) :=
    mul_le_mul_of_nonneg_left hsum (one_div_nonneg.mpr (le_of_lt hpos))
  -- Rewrite both sides into the desired "averages" shape
  -- (pure algebra: `a/b = a * (b)⁻¹`; distribute and rearrange)
  simpa [avg, div_eq_mul_inv, mul_add, add_comm, add_left_comm, add_assoc,
         mul_comm, mul_left_comm, mul_assoc] using hscale

/-- **Lemma B (Expectation, finitary form)**.
    Let `S` be a finite support of (task × noise) indices, and `G ⊆ S` the
    subset where the HB + PL conditions hold (A2). Assume:
      • inside `G`:  Δ²U(ω) ≥ m₀,
      • outside `S \ G`:  Δ²U(ω) ≥ −M,
      • slope nonnegativity `0 ≤ m₀ + M`,
      • and `p₀ ≤ |G| / |S|`.
    Then the uniform average of `Δ²U` on `S` is ≥ `p₀·m₀ − (1−p₀)·M`. -/
theorem lemmaB_expectation_finitary
  {Ω : Type*} (S G : Finset Ω) (Δ2U : Ω → ℝ)
  (hGS : G ⊆ S) (hS : 0 < S.card)
  {m0 M p0 : ℝ}
  (hG  : ∀ ω ∈ G, Δ2U ω ≥ m0)
  (hBad : ∀ ω ∈ S \ G, Δ2U ω ≥ -M)
  (hMm0 : 0 ≤ m0 + M)
  (hp0  : p0 ≤ (G.card : ℝ) / (S.card : ℝ)) :
  avg S Δ2U ≥ p0 * m0 - (1 - p0) * M := by
  classical
  -- Step 1: start from the split lower bound with the (Nat-sub) complement mass.
  have hsplit :=
    avg_lower_bound_split S G Δ2U hGS hS hG hBad
  have hpos : 0 < (S.card : ℝ) := by exact_mod_cast hS
  have hS_ne : (S.card : ℝ) ≠ 0 := ne_of_gt hpos

  -- Step 2: rewrite the complement mass using `(S \ G).card`.
  have hcard_nat : (S \ G).card = S.card - G.card := by
    simpa using Finset.card_sdiff hGS
  have hcast : ((S.card - G.card : ℕ) : ℝ) = ((S \ G).card : ℝ) := by
    simpa using (congrArg (fun n : ℕ => (n : ℝ)) hcard_nat).symm
  have hsplit' :
      avg S Δ2U
        ≥ ((G.card : ℝ) / (S.card : ℝ)) * m0
          + (((S \ G).card : ℝ) / (S.card : ℝ)) * (-M) := by
    simpa [hcast] using hsplit

  -- Step 3: prove the identity  |S\G|/|S| = 1 - |G|/|S|  without `field_simp`.
  have hmass :
      ((S \ G).card : ℝ) / (S.card : ℝ)
        = 1 - (G.card : ℝ) / (S.card : ℝ) := by
    -- disjointness and union
    have hdisj : Disjoint G (S \ G) := by
      refine Finset.disjoint_left.mpr ?_
      intro ω hωG hωSdiff
      exact (Finset.mem_sdiff.mp hωSdiff).2 hωG
    have hunion : G ∪ (S \ G) = S := Finset.union_sdiff_of_subset hGS
    -- sum of ones over a disjoint union
    have hsum1 :
        S.sum (fun ω => (1 : ℝ))
          = G.sum (fun ω => (1 : ℝ)) + (S \ G).sum (fun ω => (1 : ℝ)) := by
      have h :
          (G ∪ (S \ G)).sum (fun ω => (1 : ℝ))
            = G.sum (fun ω => (1 : ℝ)) + (S \ G).sum (fun ω => (1 : ℝ)) :=
        Finset.sum_union hdisj
      simpa [hunion, add_comm, add_left_comm, add_assoc] using h
    -- turn that into a cardinality identity in ℝ
    have hcard_add :
        (S.card : ℝ) = (G.card : ℝ) + ((S \ G).card : ℝ) := by
      simpa [Finset.sum_const, nsmul_eq_mul] using hsum1
    -- rearrange: ((S\G).card : ℝ) = (S.card : ℝ) - (G.card : ℝ)
    have hcomp :
        ((S \ G).card : ℝ) = (S.card : ℝ) - (G.card : ℝ) := by
      exact (eq_sub_iff_add_eq).2 (by simpa [add_comm] using hcard_add.symm)
    -- divide by |S| and expand (a-b)/a = a/a - b/a
    calc
      ((S \ G).card : ℝ) / (S.card : ℝ)
          = ((S.card : ℝ) - (G.card : ℝ)) / (S.card : ℝ) := by
              simp [hcomp]
      _ = (S.card : ℝ) / (S.card : ℝ) - (G.card : ℝ) / (S.card : ℝ) := by
              simpa using (sub_div (S.card : ℝ) (G.card : ℝ) (S.card : ℝ))
      _ = 1 - (G.card : ℝ) / (S.card : ℝ) := by
              simp [div_self hS_ne]

  -- Step 4: re‑express the split bound with q := |G|/|S|.
  -- Re‑express the split bound with q := |G|/|S|.
  set q : ℝ := (G.card : ℝ) / (S.card : ℝ)
  have hsplit_q :
      avg S Δ2U ≥ q * m0 - (1 - q) * M := by
    -- this line is exactly your earlier `hsplit'` with the 1−q rewrite
    simpa [q, hmass] using hsplit'

  -- Step 5: monotonicity of p ↦ p*m0 − (1−p)M when (m0+M)≥0.
  /- Monotonicity of φ(p) = p*m0 − (1−p)M in p when (m0+M) ≥ 0.
     We *avoid* any `simpa` gymnastics by working with the identity
     φ(p) = p*(m0+M) − M and a `calc` chain. -/
  set φ : ℝ → ℝ := fun p => p * m0 - (1 - p) * M
  have hp0' : p0 * (m0 + M) ≤ q * (m0 + M) :=
    mul_le_mul_of_nonneg_right hp0 hMm0

  have hq_ge_p0 : φ p0 ≤ φ q := by
    calc
      φ p0 = p0 * (m0 + M) - M := by ring
      _    ≤ q * (m0 + M) - M  := by
               -- subtract M on both sides of hp0'
               simpa using (sub_le_sub_right hp0' M)
      _    = φ q               := by ring

  -- Chain: φ(p0) ≤ φ(q) ≤ avg S Δ2U
  have hφq_le_avg : φ q ≤ avg S Δ2U := by
    -- `hsplit_q` is `avg ≥ φ q`
    simpa [φ, q] using hsplit_q
  have hchain : φ p0 ≤ avg S Δ2U := le_trans hq_ge_p0 hφq_le_avg

  -- Reorient to the goal (notation `≥` is just flipped `≤`).
  -- Goal: avg S Δ2U ≥ p0*m0 − (1−p0)M  ≡  φ p0 ≤ avg S Δ2U
  simpa [φ] using hchain


/-! ### Expectation layer (finite ensemble / empirical mean) -/

/--
**Lemma B (finite-ensemble expectation form).**
Let `S : Finset ι` index a finite batch. For every `i ∈ S`,
suppose the link and bounds hold with the same `c, κ, α, ε` (and `κ ε ≤ c α`).
If `S.card > 0` then the empirical mean of `Δ2U` over `S` is nonnegative:
`(1 / |S|) * (S.sum Δ2U) ≥ 0`.
-/
theorem lemmaB_expected_nonneg_finset
    {ι : Type*} (S : Finset ι)
    (Δ2U Δ2f dPrev dNext : ι → ℝ)
    {c κ α ε : ℝ}
    (hc : 0 ≤ c) (hκ : 0 ≤ κ) (htrade : κ * ε ≤ c * α)
    (hlink : ∀ i ∈ S, c * (-(Δ2f i)) - κ * ((dPrev i)^2 + (dNext i)^2) ≤ Δ2U i)
    (hΔ2f : ∀ i ∈ S, Δ2f i ≤ -α)
    (hsq   : ∀ i ∈ S, (dPrev i)^2 + (dNext i)^2 ≤ ε)
    (hSpos : 0 < (S.card)) :
    (1 / (S.card : ℝ)) * S.sum (fun i => Δ2U i) ≥ 0 := by
  classical
  -- Pointwise lower bound: Δ2U i ≥ c*α − κ*ε
  have hpoint : ∀ i ∈ S, c * α - κ * ε ≤ Δ2U i := by
    intro i hi
    have hneg : α ≤ -Δ2f i := by
      have := hΔ2f i hi
      simpa using (neg_le_neg this)
    have h1 : c * α ≤ c * (-Δ2f i) := mul_le_mul_of_nonneg_left hneg hc
    have h2 : κ * ((dPrev i)^2 + (dNext i)^2) ≤ κ * ε :=
      mul_le_mul_of_nonneg_left (hsq i hi) hκ
    have h2' : -(κ * ε) ≤ -(κ * ((dPrev i)^2 + (dNext i)^2)) := by
      simpa using (neg_le_neg h2)
    have hsum : c * α - κ * ε ≤ c * (-Δ2f i) - κ * ((dPrev i)^2 + (dNext i)^2) := by
      simpa [sub_eq_add_neg] using add_le_add h1 h2'
    exact le_trans hsum (hlink i hi)
  -- Pointwise nonnegativity from the tradeoff
  have hconst_nonneg : 0 ≤ c * α - κ * ε := sub_nonneg.mpr htrade
  have hterm_nonneg : ∀ i ∈ S, 0 ≤ Δ2U i := by
    intro i hi; exact le_trans hconst_nonneg (hpoint i hi)
  -- Sum of nonnegative terms is nonnegative
  have hsum_nonneg : 0 ≤ S.sum (fun i => Δ2U i) :=
    Finset.sum_nonneg (by intro i hi; exact hterm_nonneg i hi)
  -- Multiply by positive 1/|S|
  have hcardpos : 0 < (S.card : ℝ) := by exact_mod_cast hSpos
  have hone_div_nonneg : 0 ≤ (1 / (S.card : ℝ)) :=
    one_div_nonneg.mpr (le_of_lt hcardpos)
  exact mul_nonneg hone_div_nonneg hsum_nonneg

/--
**Lemma B (finite-ensemble expectation, δ‑form).**
Uniform per‑sample absolute bounds `|f - fprev| ≤ δ`, `|fnext - f| ≤ δ` with `δ ≥ 0`
imply the squared‑sum budget with `ε := 2*δ^2`. This feeds into
`lemmaB_expected_nonneg_finset`.
-/
theorem lemmaB_expected_nonneg_finset_abs
    {ι : Type*} (S : Finset ι)
    (Δ2U Δ2f : ι → ℝ)
    (fprev f fnext : ι → ℝ)
    {c κ α δ : ℝ}
    (hc : 0 ≤ c) (hκ : 0 ≤ κ)
    (htradeδ : κ * (2 * δ ^ 2) ≤ c * α)
    (hlink : ∀ i ∈ S,
        c * (-(Δ2f i)) - κ * ((f i - fprev i)^2 + (fnext i - f i)^2) ≤ Δ2U i)
    (hΔ2f : ∀ i ∈ S, Δ2f i ≤ -α)
    (hAbsPrev : ∀ i ∈ S, |f i - fprev i| ≤ δ)
    (hAbsNext : ∀ i ∈ S, |fnext i - f i| ≤ δ)
    (hδ : 0 ≤ δ)
    (hSpos : 0 < (S.card)) :
    (1 / (S.card : ℝ)) * S.sum (fun i => Δ2U i) ≥ 0 := by
  classical
  -- Build per-sample squared-step bounds from absolute bounds
  have hsq : ∀ i ∈ S, (f i - fprev i) ^ 2 + (fnext i - f i) ^ 2 ≤ 2 * δ ^ 2 := by
    intro i hi
    exact
      stepSquares_le_two_delta_sq
        (fprev := fprev i) (f := f i) (fnext := fnext i) (δ := δ)
        (hPrev := hAbsPrev i hi) (hNext := hAbsNext i hi) (hδ := hδ)
  -- Apply the generic finite-ensemble lemma with ε := 2 δ^2
  have := lemmaB_expected_nonneg_finset
    (S := S)
    (Δ2U := Δ2U) (Δ2f := Δ2f)
    (dPrev := fun i => (f i - fprev i))
    (dNext := fun i => (fnext i - f i))
    (c := c) (κ := κ) (α := α) (ε := 2 * δ ^ 2)
    (hc := hc) (hκ := hκ) (htrade := by simpa using htradeδ)
    (hlink := hlink) (hΔ2f := hΔ2f) (hsq := hsq) (hSpos := hSpos)
  simpa using this

end

/-- Complement mass identity on a finite support:
if `G ⊆ S` and `0 < |S|`, then `|S \\ G|/|S| = 1 - |G|/|S|` (in `ℝ`). -/
lemma complement_mass_div_eq_one_minus {Ω : Type*} [DecidableEq Ω]
  (S G : Finset Ω) (hGS : G ⊆ S) (hS : 0 < S.card) :
  ((S \ G).card : ℝ) / (S.card : ℝ) = 1 - (G.card : ℝ) / (S.card : ℝ) := by  classical
  have hdisj : Disjoint G (S \ G) := by
    refine Finset.disjoint_left.mpr ?_
    intro ω hωG hωSdiff
    exact (Finset.mem_sdiff.mp hωSdiff).2 hωG
  have hunion : G ∪ (S \ G) = S := Finset.union_sdiff_of_subset hGS
  -- sum of ones across the disjoint union
  have hsum1 :
      S.sum (fun _ => (1 : ℝ))
        = G.sum (fun _ => (1 : ℝ)) + (S \ G).sum (fun _ => (1 : ℝ)) := by
    have : (G ∪ (S \ G)).sum (fun _ => (1 : ℝ))
            = G.sum (fun _ => (1 : ℝ)) + (S \ G).sum (fun _ => (1 : ℝ)) :=
      Finset.sum_union hdisj
    simpa [hunion, add_comm, add_left_comm, add_assoc] using this
  have hcard_add :
      (S.card : ℝ) = (G.card : ℝ) + ((S \ G).card : ℝ) := by
    simpa [Finset.sum_const, nsmul_eq_mul] using hsum1
  have hS_ne : (S.card : ℝ) ≠ 0 := by exact_mod_cast hS.ne'
  have hcomp :
      ((S \ G).card : ℝ) = (S.card : ℝ) - (G.card : ℝ) := by
    exact (eq_sub_iff_add_eq).2 (by simpa [add_comm] using hcard_add.symm)
  calc
    ((S \ G).card : ℝ) / (S.card : ℝ)
        = ((S.card : ℝ) - (G.card : ℝ)) / (S.card : ℝ) := by simp [hcomp]
    _ = 1 - (G.card : ℝ) / (S.card : ℝ) := by
          simpa [div_self hS_ne] using
            (sub_div (S.card : ℝ) (G.card : ℝ) (S.card : ℝ))

/--
**Lemma B (finite-ensemble expectation, per-sample trade).**
If for each `i ∈ S` we have
  * link: `c * (-(Δ2f i)) - κ * ((dPrev i)^2 + (dNext i)^2) ≤ Δ2U i`,
  * negative curvature: `Δ2f i ≤ -(α i)`,
  * step budget: `(dPrev i)^2 + (dNext i)^2 ≤ ε i`,
  * trade: `κ * (ε i) ≤ c * (α i)`,
with `0 ≤ c` and `0 ≤ κ`, then the batch average is nonnegative.
-/
theorem lemmaB_expected_nonneg_finset_var
    {ι : Type*} (S : Finset ι)
    (Δ2U Δ2f dPrev dNext α ε : ι → ℝ)
    {c κ : ℝ}
    (hc : 0 ≤ c) (hκ : 0 ≤ κ)
    (hlink : ∀ i ∈ S, c * (-(Δ2f i)) - κ * ((dPrev i)^2 + (dNext i)^2) ≤ Δ2U i)
    (hΔ2f : ∀ i ∈ S, Δ2f i ≤ -(α i))
    (hsq   : ∀ i ∈ S, (dPrev i)^2 + (dNext i)^2 ≤ ε i)
    (htrade : ∀ i ∈ S, κ * (ε i) ≤ c * (α i))
    (hSpos : 0 < S.card) :
    (1 / (S.card : ℝ)) * S.sum (fun i => Δ2U i) ≥ 0 := by
  classical
  -- Pointwise: 0 ≤ Δ2U i
  have hpoint : ∀ i ∈ S, 0 ≤ Δ2U i := by
    intro i hi
    -- as in lemmaB_bridge_nonneg but with α i, ε i
    have hneg : α i ≤ -Δ2f i := by simpa using (neg_le_neg (hΔ2f i hi))
    have h1   : c * α i ≤ c * (-Δ2f i) := mul_le_mul_of_nonneg_left hneg hc
    have h2   : κ * ((dPrev i)^2 + (dNext i)^2) ≤ κ * ε i :=
      mul_le_mul_of_nonneg_left (hsq i hi) hκ
    have h2'  : -(κ * ε i) ≤ -(κ * ((dPrev i)^2 + (dNext i)^2)) := by
      simpa using (neg_le_neg h2)
    have hsum : c * α i - κ * ε i
                ≤ c * (-Δ2f i) - κ * ((dPrev i)^2 + (dNext i)^2) := by
      simpa [sub_eq_add_neg] using add_le_add h1 h2'
    have hlow : c * α i - κ * ε i ≤ Δ2U i := le_trans hsum (hlink i hi)
    have hz   : 0 ≤ c * α i - κ * ε i := sub_nonneg.mpr (htrade i hi)
    exact le_trans hz hlow
  -- Sum and scale
  have hsum_nonneg : 0 ≤ S.sum (fun i => Δ2U i) :=
    Finset.sum_nonneg (by intro i hi; exact hpoint i hi)
  have hcardpos : 0 < (S.card : ℝ) := by exact_mod_cast hSpos
  have hone_div_nonneg : 0 ≤ (1 / (S.card : ℝ)) :=
    one_div_nonneg.mpr (le_of_lt hcardpos)
  exact mul_nonneg hone_div_nonneg hsum_nonneg

end NOC
