import Mathlib
import NOC.E.Interfaces.DI
import NOC.E.Interfaces.DI_Fiberwise

/-!
Module: NOC.E.Interfaces.DI_NOC_Wrapper
Status: ready-to-use wrappers (no sorrys).

Scope and boundary
- Applies only in NCC (non‑competitive) couplings: per step, the downstream output is a
  post‑processing of the upstream leg conditioned on `F_{t−1}`. Outside NCC (e.g., interference),
  ablation can raise DI; do not apply these wrappers there.

Purpose
- NOC‑flavored wrappers for Lemma E (DI–DPI composition) under NCC‑C/S with `S_t := S_aft_t`.
  They take fiberwise per‑step witnesses and produce global DI contraction (and strict) statements.

Usage pattern
- Provide a finite fiber index set `s` (e.g., values of `F_{t−1}=(S^{<t}, Z^{≤t})`).
- Provide nonnegative probability weights `w` with `∑_i w i = 1`.
- Provide per‑fiber reals `pre_f t x y i`, `post_f t x y i` with `post_f ≤ η_t · pre_f` (uniform SDPI
  across fibers at fixed `t`) and `pre_f ≥ 0`.
- Provide the per‑step link `DirectedInfo.perStep t x y ≤ aggPost s w post_f t x y` (with `S_t=S_aft_t`,
  this is typically `rfl`).
- Call `lemmaE_monotone` (and `lemmaE_strict` with a strict witness) to obtain the global contraction.

Strictness and bounds
- Strictness does not require `sup_f η_t(f) < 1`; it suffices to have a positive‑probability fiber
  with `η_t(f) < 1` and positive `pre_t(f)`. The strict wrapper exposes this via a single fiber
  `i0` with `w i0 > 0` and `pre_f t0 … i0 > 0`.
- Coarse bounds such as `AggAfter ≤ (max_t η_t) · AggBefore` and weighted variants
  `AggAfter ≤ (∑_t (pre_t/AggBefore) · η_t) · AggBefore` hold; guard the degenerate case
  `AggBefore = 0`, for which `AggAfter = 0`.
-/

namespace NOC
open Classical
open scoped BigOperators

variable {X Y ι : Type}

/-- Lemma E (monotone): NCC‑S wrapper.
Assumptions:
- `DirectedInfo` per-step term is bounded by the aggregated post-fiber quantity.
- Nonnegative fiber weights and per-fiber `pre` terms.
- Uniform per-fiber SDPI with contraction `η t` (from the `SDPI` class).
Conclusion: global DI contraction `DI ≤ ∑ η_t · aggPre`.
-/
theorem lemmaE_monotone
  [DirectedInfo X Y] [SDPI X Y]
  (s : Finset ι)
  (w : ι → ℝ)
  (pre_f post_f : Time → (Time → X) → (Time → Y) → ι → ℝ)
  (n : Nat) (x : Time → X) (y : Time → Y)
  (h_per_le_post : ∀ t, DirectedInfo.perStep t x y ≤ aggPost (s:=s) (w:=w) post_f t x y)
  (hw_nonneg : ∀ i ∈ s, 0 ≤ w i)
  (hpre_nonneg : ∀ t i, i ∈ s → 0 ≤ pre_f t x y i)
  (h_uniform_sdpi : ∀ t i, i ∈ s → post_f t x y i ≤ SDPI.η (X:=X) (Y:=Y) t * pre_f t x y i) :
  DirectedInfo.DI n x y ≤
    (Finset.range (n+1)).sum (fun t => SDPI.η (X:=X) (Y:=Y) t * aggPre (s:=s) (w:=w) pre_f t x y) := by
  classical
  exact di_dpi_from_fibers (X:=X) (Y:=Y) (ι:=ι)
    s w pre_f post_f n x y h_per_le_post hw_nonneg hpre_nonneg h_uniform_sdpi

/-- Lemma E (strict): NCC‑S wrapper with strictness witness.
Additional assumptions:
- There exists a time `t0 ≤ n` and a fiber `i0 ∈ s` with `η t0 < 1`, `w i0 > 0`, and
  `pre_f t0 x y i0 > 0`.
Conclusion: strict global decrease `DI < ∑ aggPre`.
-/
theorem lemmaE_strict
  [DirectedInfo X Y] [SDPI X Y]
  (s : Finset ι)
  (w : ι → ℝ)
  (pre_f post_f : Time → (Time → X) → (Time → Y) → ι → ℝ)
  (n : Nat) (x : Time → X) (y : Time → Y)
  (h_per_le_post : ∀ t, DirectedInfo.perStep t x y ≤ aggPost (s:=s) (w:=w) post_f t x y)
  (hw_nonneg : ∀ i ∈ s, 0 ≤ w i)
  (hpre_nonneg : ∀ t i, i ∈ s → 0 ≤ pre_f t x y i)
  (h_uniform_sdpi : ∀ t i, i ∈ s → post_f t x y i ≤ SDPI.η (X:=X) (Y:=Y) t * pre_f t x y i)
  (t0 : Nat) (ht0 : t0 ∈ Finset.range (n+1))
  (hη_lt : SDPI.η (X:=X) (Y:=Y) t0 < 1)
  (i0 : ι) (hi0 : i0 ∈ s) (hw_pos : 0 < w i0) (hpre_pos : 0 < pre_f t0 x y i0) :
  DirectedInfo.DI n x y <
    (Finset.range (n+1)).sum (fun t => aggPre (s:=s) (w:=w) pre_f t x y) := by
  classical
  exact di_dpi_from_fibers_strict (X:=X) (Y:=Y) (ι:=ι)
    s w pre_f post_f n x y h_per_le_post hw_nonneg hpre_nonneg h_uniform_sdpi
    t0 ht0 hη_lt i0 hi0 hw_pos hpre_pos

/-!
Auxiliary contraction corollaries
- With a uniform cap `m` on the per-step SDPI schedule, `DI ≤ m · (∑ pre_t)`.
- With `AggBefore = ∑ pre_t > 0`, a weighted bound holds: `DI ≤ (∑ w̄_t η_t) · AggBefore`
  where `w̄_t := pre_t / AggBefore`.
-/

theorem lemmaE_bound_with_eta_cap
  [DirectedInfo X Y] [SDPI X Y]
  (s : Finset ι) (w : ι → ℝ)
  (pre_f post_f : Time → (Time → X) → (Time → Y) → ι → ℝ)
  (n : Nat) (x : Time → X) (y : Time → Y)
  (h_per_le_post : ∀ t, DirectedInfo.perStep t x y ≤ aggPost (s:=s) (w:=w) post_f t x y)
  (hw_nonneg : ∀ i ∈ s, 0 ≤ w i)
  (hpre_nonneg_f : ∀ t i, i ∈ s → 0 ≤ pre_f t x y i)
  (h_uniform_sdpi : ∀ t i, i ∈ s → post_f t x y i ≤ SDPI.η (X:=X) (Y:=Y) t * pre_f t x y i)
  (m : ℝ) (hcap : ∀ t ∈ Finset.range (n+1), SDPI.η (X:=X) (Y:=Y) t ≤ m)
  :
  DirectedInfo.DI n x y
    ≤ m * (Finset.range (n+1)).sum (fun t => aggPre (s:=s) (w:=w) pre_f t x y) := by
  classical
  -- Base contraction via fiberwise composition
  have h0 := lemmaE_monotone (X:=X) (Y:=Y) (ι:=ι)
    s w pre_f post_f n x y h_per_le_post hw_nonneg hpre_nonneg_f h_uniform_sdpi
  -- Bound ∑ η_t pre_t by m * ∑ pre_t
  have hpre_nonneg_sum : ∀ t ∈ Finset.range (n+1),
      0 ≤ aggPre (s:=s) (w:=w) pre_f t x y := by
    intro t ht
    -- sum of nonneg terms with nonneg weights
    have : ∀ i ∈ s, 0 ≤ w i * pre_f t x y i := by
      intro i hi; exact mul_nonneg (hw_nonneg i hi) (hpre_nonneg_f t i hi)
    simpa [aggPre] using Finset.sum_nonneg this
  have h1 : (Finset.range (n+1)).sum (fun t => SDPI.η (X:=X) (Y:=Y) t * aggPre (s:=s) (w:=w) pre_f t x y)
            ≤ (Finset.range (n+1)).sum (fun t => m * aggPre (s:=s) (w:=w) pre_f t x y) := by
    refine Finset.sum_le_sum ?_
    intro t ht
    have := hcap t ht
    have hnn := hpre_nonneg_sum t ht
    simpa [one_mul] using mul_le_mul_of_nonneg_right this hnn
  have h2 : (Finset.range (n+1)).sum (fun t => m * aggPre (s:=s) (w:=w) pre_f t x y)
            = m * (Finset.range (n+1)).sum (fun t => aggPre (s:=s) (w:=w) pre_f t x y) := by
    simpa [Finset.mul_sum] using (rfl : (Finset.range (n+1)).sum (fun t => m * aggPre (s:=s) (w:=w) pre_f t x y)
      = (Finset.range (n+1)).sum (fun t => (m * aggPre (s:=s) (w:=w) pre_f t x y)))
  -- Chain inequalities
  exact le_trans h0 (by simpa [h2] using h1)

-- (Weighted bound available on request: express ∑ η_t pre_t as (∑ η_t pre_t / AggBefore)·AggBefore.)

end NOC
