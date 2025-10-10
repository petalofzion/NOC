import Mathlib
import NOC.E.Interfaces.DI
import NOC.E.Interfaces.DI_Averaging

-- Silence common linter warnings for this file
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unusedSectionVars false

/-!
Module: NOC.E.Interfaces.DI_Fiberwise
Status: reusable DI–DPI composition from fiberwise (conditional) step bounds (no sorrys).

Scope and boundary
- Applies only under NCC couplings (post‑processing on the upstream leg): for each step `t`,
  `U_t → S_bef_t → S_aft_t | F_{t−1}`. Outside NCC (e.g., interference/MAC), ablation can
  increase DI; do not use these lemmas there (see Gaussian boundary files).

Purpose
- Given per‑fiber inequalities `post_f ≤ η · pre_f` and nonnegative weights, build the aggregated
  per‑step inequality and conclude global DI contraction (and strict variant).

Uniformity and strictness
- The global monotone bound uses a uniform (over fibers) per‑step SDPI constant `η_t ∈ [0,1]`.
- Strictness does not require `sup_f η_t(f) < 1` on all fibers: it suffices that at some step there
  exists a positive‑probability fiber set with `η_t(f) < 1` and positive `pre_t(f)`; the strict lemma
  models this by requiring a single fiber with positive weight and `pre>0`.

Weights and degenerate case
- Weights are probability masses `w_t(f) = P(F_{t−1}=f)` (nonnegative). When presenting weighted
  global bounds vs `AggBefore`, guard the degenerate case `AggBefore = 0`, in which the inequality
  is trivial (`AggAfter = 0`).
-/

namespace NOC
open Classical
open scoped BigOperators

variable {X Y ι : Type}

/-- Aggregated per-step quantities from fiberwise pieces on a finite index set `s`. -/
def aggPre (s : Finset ι) (w : ι → ℝ)
  (pre_f : Time → (Time → X) → (Time → Y) → ι → ℝ)
  (t : Time) (x : Time → X) (y : Time → Y) : ℝ :=
  s.sum (fun i => w i * pre_f t x y i)

def aggPost (s : Finset ι) (w : ι → ℝ)
  (post_f : Time → (Time → X) → (Time → Y) → ι → ℝ)
  (t : Time) (x : Time → X) (y : Time → Y) : ℝ :=
  s.sum (fun i => w i * post_f t x y i)

/-- DI–DPI from fiberwise bounds (monotone). -/
theorem di_dpi_from_fibers
  [DirectedInfo X Y] [SDPI X Y]
  (s : Finset ι)
  (w : ι → ℝ)
  (pre_f post_f : Time → (Time → X) → (Time → Y) → ι → ℝ)
  (n : Nat) (x : Time → X) (y : Time → Y)
  -- Witnesses and bounds
  (h_per_le_post : ∀ t, DirectedInfo.perStep t x y ≤ aggPost s w post_f t x y)
  (hw_nonneg : ∀ i ∈ s, 0 ≤ w i)
  (hpre_nonneg : ∀ t i, i ∈ s → 0 ≤ pre_f t x y i)
  (h_uniform_sdpi : ∀ t i, i ∈ s → post_f t x y i ≤ SDPI.η (X:=X) (Y:=Y) t * pre_f t x y i) :
  DirectedInfo.DI n x y ≤
    (Finset.range (n+1)).sum (fun t => SDPI.η (X:=X) (Y:=Y) t * aggPre s w pre_f t x y) := by
  classical
  -- Build per-step aggregated SDPI via weighted averaging
  have h_sdpi_step : ∀ t,
      aggPost s w post_f t x y ≤ SDPI.η (X:=X) (Y:=Y) t * aggPre s w pre_f t x y := by
    intro t
    -- Map to the averaging lemma types
    let w' : ι → ℝ := w
    let pre' : ι → ℝ := fun i => pre_f t x y i
    let post' : ι → ℝ := fun i => post_f t x y i
    have hw' : ∀ i ∈ s, 0 ≤ w' i := by intro i hi; exact hw_nonneg i hi
    have hpre' : ∀ i ∈ s, 0 ≤ pre' i := by intro i hi; simpa using (hpre_nonneg t i hi)
    have hstep' : ∀ i ∈ s, post' i ≤ SDPI.η (X:=X) (Y:=Y) t * pre' i := by
      intro i hi; simpa using (h_uniform_sdpi t i hi)
    -- Apply the uniform SDPI sum lemma with ηsup := η t
    simpa [aggPost, aggPre]
      using (sum_uniform_sdpi (s := s) (w := w') (pre := pre') (post := post') (η := fun _ => SDPI.η (X:=X) (Y:=Y) t)
              (ηsup := SDPI.η (X:=X) (Y:=Y) t) hw' hpre'
              (by intro i hi; exact le_rfl)
              (by exact (SDPI.η_range (X:=X) (Y:=Y) t).1)
              (by intro i hi; exact hstep' i hi))
  -- Use the explicit aggregator
  exact DI.di_monotone_under_garbling_explicit (X:=X) (Y:=Y)
    (pre := aggPre s w pre_f) (post := aggPost s w post_f) n x y h_per_le_post h_sdpi_step

/-- Strict DI–DPI from fiberwise bounds: if `pre_f t0` is positive for some fiber with
positive weight and `η t0 < 1`, then strict global decrease holds. -/
theorem di_dpi_from_fibers_strict
  [DirectedInfo X Y] [SDPI X Y]
  (s : Finset ι)
  (w : ι → ℝ)
  (pre_f post_f : Time → (Time → X) → (Time → Y) → ι → ℝ)
  (n : Nat) (x : Time → X) (y : Time → Y)
  (h_per_le_post : ∀ t, DirectedInfo.perStep t x y ≤ aggPost s w post_f t x y)
  (hw_nonneg : ∀ i ∈ s, 0 ≤ w i)
  (hpre_nonneg : ∀ t i, i ∈ s → 0 ≤ pre_f t x y i)
  (h_uniform_sdpi : ∀ t i, i ∈ s → post_f t x y i ≤ SDPI.η (X:=X) (Y:=Y) t * pre_f t x y i)
  -- strict step witness
  (t0 : Nat) (ht0 : t0 ∈ Finset.range (n+1))
  (hη_lt : SDPI.η (X:=X) (Y:=Y) t0 < 1)
  (i0 : ι) (hi0 : i0 ∈ s) (hw_pos : 0 < w i0) (hpre_pos : 0 < pre_f t0 x y i0) :
  DirectedInfo.DI n x y <
    (Finset.range (n+1)).sum (fun t => aggPre s w pre_f t x y) := by
  classical
  -- Build the monotone ingredients as above
  have hpre_nonneg_sum : ∀ t ∈ Finset.range (n+1), 0 ≤ aggPre s w pre_f t x y := by
    intro t ht
    -- sum of nonnegatives with nonnegative weights
    have : ∀ i ∈ s, 0 ≤ w i * pre_f t x y i := by
      intro i hi
      exact mul_nonneg (hw_nonneg i hi) (hpre_nonneg t i hi)
    simpa [aggPre] using Finset.sum_nonneg this
  have h_sdpi_step : ∀ t,
      aggPost s w post_f t x y ≤ SDPI.η (X:=X) (Y:=Y) t * aggPre s w pre_f t x y := by
    -- identical to the monotone proof
    intro t
    let w' : ι → ℝ := w
    let pre' : ι → ℝ := fun i => pre_f t x y i
    let post' : ι → ℝ := fun i => post_f t x y i
    have hw' : ∀ i ∈ s, 0 ≤ w' i := by intro i hi; exact hw_nonneg i hi
    have hpre' : ∀ i ∈ s, 0 ≤ pre' i := by intro i hi; simpa using (hpre_nonneg t i hi)
    have hstep' : ∀ i ∈ s, post' i ≤ SDPI.η (X:=X) (Y:=Y) t * pre' i := by
      intro i hi; simpa using (h_uniform_sdpi t i hi)
    simpa [aggPost, aggPre]
      using (sum_uniform_sdpi (s := s) (w := w') (pre := pre') (post := post') (η := fun _ => SDPI.η (X:=X) (Y:=Y) t)
              (ηsup := SDPI.η (X:=X) (Y:=Y) t) hw' hpre'
              (by intro i hi; exact le_rfl)
              (by exact (SDPI.η_range (X:=X) (Y:=Y) t).1)
              (by intro i hi; exact hstep' i hi))
  -- Show pre t0 > 0 from a positive-weight fiber with positive pre_f
  have hpre_t0_pos : 0 < aggPre s w pre_f t0 x y := by
    -- pre t0 ≥ w i0 * pre_f t0 i0 > 0
    have hterm_pos : 0 < w i0 * pre_f t0 x y i0 :=
      mul_pos hw_pos hpre_pos
    -- sum over s is ≥ that term
    have hle : w i0 * pre_f t0 x y i0 ≤ aggPre s w pre_f t0 x y := by
      classical
      have hnonneg_all : ∀ i ∈ s, 0 ≤ w i * pre_f t0 x y i := by
        intro i hi; exact mul_nonneg (hw_nonneg i hi) (hpre_nonneg t0 i hi)
      simpa [aggPre]
        using (Finset.single_le_sum hnonneg_all hi0)
    exact lt_of_lt_of_le hterm_pos hle
  -- Apply strict explicit lemma
  exact DI.di_strict_under_garbling_explicit (X:=X) (Y:=Y)
    (pre := aggPre s w pre_f) (post := aggPost s w post_f) n x y
    h_per_le_post h_sdpi_step hpre_nonneg_sum t0 ht0 hη_lt hpre_t0_pos

end NOC
-- Silence common linter warnings for this file
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unusedSectionVars false
