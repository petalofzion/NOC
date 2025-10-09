import Mathlib

/-!
Module: NOC.E.Interfaces.DI_Averaging
Status: small helper lemmas (no sorrys).

Purpose: lift fiberwise (conditional) per-step bounds to averaged bounds with
nonnegative weights. This matches the “uniform SDPI across conditioning” story:
- if `post_f ≤ η_f * pre_f` for each fiber `f` and `η_f ≤ ηsup`,
  then `∑ w_f · post_f ≤ ηsup · ∑ w_f · pre_f` provided `w_f ≥ 0` and `pre_f ≥ 0`.

These lemmas avoid measure-theoretic machinery by working on finite index sets
and nonnegative real weights. They are building blocks to derive the per-step
`sdpi_step` inequality from fiberwise witnesses.
-/

namespace NOC
open Classical
-- We use explicit `Finset.sum` to avoid relying on binder notation.

/-- If `a i ≤ b i` pointwise on a finite set and weights are nonnegative, then
`∑ w i * a i ≤ ∑ w i * b i`. -/
lemma sum_mul_mono
  {ι : Type} (s : Finset ι)
  (w a b : ι → ℝ)
  (hw : ∀ i ∈ s, 0 ≤ w i)
  (hpoint : ∀ i ∈ s, a i ≤ b i) :
  (s.sum (fun i => w i * a i)) ≤ (s.sum (fun i => w i * b i)) := by
  classical
  refine Finset.sum_le_sum ?_;
  intro i hi; exact mul_le_mul_of_nonneg_left (hpoint i hi) (hw i hi)

/-- Uniform SDPI averaging: if `post i ≤ η i * pre i` and `η i ≤ ηsup`, with
nonnegative weights and nonnegative `pre`, then `∑ w i · post i ≤ ηsup · ∑ w i · pre i`.
-/
lemma sum_uniform_sdpi
  {ι : Type} (s : Finset ι)
  (w pre post η : ι → ℝ) (ηsup : ℝ)
  (hw : ∀ i ∈ s, 0 ≤ w i)
  (hpre : ∀ i ∈ s, 0 ≤ pre i)
  (hηle : ∀ i ∈ s, η i ≤ ηsup)
  (hηsup_nonneg : 0 ≤ ηsup)
  (hstep : ∀ i ∈ s, post i ≤ η i * pre i) :
  (s.sum (fun i => w i * post i)) ≤ ηsup * (s.sum (fun i => w i * pre i)) := by
  classical
  -- First: sum w·post ≤ sum w·(η i * pre)
  have h1 : (s.sum (fun i => w i * post i)) ≤ (s.sum (fun i => w i * (η i * pre i))) :=
    sum_mul_mono s w post (fun i => η i * pre i) hw (by
      intro i hi; exact hstep i hi)
  -- Bound each `η i` by `ηsup` and pull it out of the sum by monotonicity
  have h2_point : ∀ i ∈ s, (w i * (η i * pre i)) ≤ (w i * (ηsup * pre i)) := by
    intro i hi
    have hηle' := hηle i hi
    have hpre_nonneg : 0 ≤ pre i := hpre i hi
    have hηpre : η i * pre i ≤ ηsup * pre i :=
      mul_le_mul_of_nonneg_right hηle' hpre_nonneg
    have hw_nonneg : 0 ≤ w i := hw i hi
    exact mul_le_mul_of_nonneg_left hηpre hw_nonneg
  have h2 : (s.sum (fun i => w i * (η i * pre i))) ≤ (s.sum (fun i => w i * (ηsup * pre i))) :=
    Finset.sum_le_sum (by intro i hi; exact h2_point i hi)
  -- Combine and factor ηsup
  have hsum : (s.sum (fun i => w i * (ηsup * pre i))) = ηsup * (s.sum (fun i => w i * pre i)) := by
    -- Distribute ηsup across the sum
    calc
      (s.sum (fun i => w i * (ηsup * pre i)))
          = (s.sum (fun i => (ηsup * (w i * pre i)))) := by
              apply Finset.sum_congr rfl; intro i hi; ring
      _   = ηsup * (s.sum (fun i => (w i * pre i))) := by
              simpa [Finset.mul_sum]
  exact h1.trans (h2.trans (by simpa [hsum]))

end NOC
