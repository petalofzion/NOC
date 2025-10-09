import Mathlib
import NOC.E.Interfaces.DI_NOC_Wrapper
import NOC.E.Interfaces.Examples.DI_NOC_BSC

/-!
Module: NOC.E.Interfaces.Examples.DI_Weighted_Bound
Status: small weighted-bound example (no sorrys).

Purpose
- Demonstrate `lemmaE_bound_weighted`: with a single fiber and the strict `etaStrict`
  schedule from the BSC example, the weighted global bound matches the average
  contraction factor times `AggBefore`.

Setup
- Use the `Unit` model and instances from `DI_NOC_BSC`:
  perStep t = post t = etaStrict t, pre t = 1, η t = etaStrict t.
  For fiberization, take a single fiber with weight 1.
/-

namespace NOC
namespace DI

open scoped BigOperators

/- Single-fiber index and weight. -/
def Fiber := Unit

@[simp] def sFiber : Finset Fiber := {()}
@[simp] def wFiber (_ : Fiber) : ℝ := 1

/- Per‑fiber pre/post specialized to the BSC schedule. -/
@[simp] def pre_f
  (t : Time) (_x : Time → Unit) (_y : Time → Unit) (_i : Fiber) : ℝ := 1

@[simp] def post_f
  (t : Time) (_x : Time → Unit) (_y : Time → Unit) (_i : Fiber) : ℝ := etaStrict t

/- Weighted bound instance: for any horizon n, the weighted global bound holds. -/
lemma bsc_weighted_bound (n : Nat) :
  let x : Time → Unit := fun _ => ()
  let y : Time → Unit := fun _ => ()
  let AggBefore : ℝ := (Finset.range (n+1)).sum (fun t => aggPre (s:=sFiber) (w:=wFiber) pre_f t x y)
  DirectedInfo.DI (X:=Unit) (Y:=Unit) n x y ≤
    ((Finset.range (n+1)).sum (fun t =>
       (aggPre (s:=sFiber) (w:=wFiber) pre_f t x y) / AggBefore * SDPI.η (X:=Unit) (Y:=Unit) t))
       * AggBefore := by
  classical
  intro x y AggBefore
  -- Per-step inequality: perStep = post (by construction), so ≤ aggPost trivially
  have h_per_le_post : ∀ t, DirectedInfo.perStep (X:=Unit) (Y:=Unit) t x y
                        ≤ aggPost (s:=sFiber) (w:=wFiber) post_f t x y := by
    intro t; simp [aggPost]
  -- Nonnegativity of weights and pre_f
  have hw_nonneg : ∀ i ∈ sFiber, 0 ≤ wFiber i := by intro i hi; simp [wFiber] at hi ⊢; norm_num
  have hpre_nonneg : ∀ t i, i ∈ sFiber → 0 ≤ pre_f t x y i := by
    intro t i hi; simp [pre_f] at hi ⊢; norm_num
  -- Uniform SDPI: post_f = η t * pre_f
  have h_uniform_sdpi : ∀ t i, i ∈ sFiber →
      post_f t x y i ≤ SDPI.η (X:=Unit) (Y:=Unit) t * pre_f t x y i := by
    intro t i hi; simp [post_f, pre_f]
  -- AggBefore > 0 (sum of ones over a nonempty range)
  have hAggPos : 0 < AggBefore := by
    unfold AggBefore
    have : 0 < ((Finset.range (n+1)).card : ℝ) := by
      simpa using (Nat.cast_add_one_pos_iff.mpr (Nat.zero_le n))
    simpa [aggPre, pre_f, Finset.sum_const, Finset.card_range, nsmul_eq_mul] using this
  -- Apply weighted bound lemma
  simpa [AggBefore] using
    (lemmaE_bound_weighted (X:=Unit) (Y:=Unit) (ι:=Fiber)
      (s:=sFiber) (w:=wFiber) (pre_f:=pre_f) (post_f:=post_f)
      n x y h_per_le_post hw_nonneg hpre_nonneg h_uniform_sdpi hAggPos)

end DI
end NOC

