import Mathlib
import NOC.E.Interfaces.DI

/-!
Module: NOC.E.Interfaces.DI_Toy
Status: ready-to-instantiate scaffolding (no sorrys).

Purpose: package minimal data for the toy DI–DPI model so that, once the user
supplies per-step decompositions and SDPI witnesses, the global lemmas from
`NOC.E.Interfaces.DI` become available immediately.
-/

namespace NOC
universe u

namespace DI
open scoped BigOperators

/-- Data specifying the per-step directed-information contribution. -/
class PerStepData (X Y : Type u) where
  perStep : Time → (Time → X) → (Time → Y) → ℝ

instance (X Y : Type u) [d : PerStepData X Y] : DirectedInfo X Y where
  perStep  := d.perStep
  DI       := fun n x y => (Finset.range (n+1)).sum (fun t => d.perStep t x y)
  chainRule := by
    intro n x y
    simp

/-- Contraction data for the Strong Data-Processing Inequality. -/
class SDPIData (X Y : Type u) where
  η : Time → ℝ
  η_range : ∀ t, 0 ≤ η t ∧ η t ≤ 1

instance (X Y : Type u) [s : SDPIData X Y] : SDPI X Y where
  η       := s.η
  η_range := s.η_range

/-- Witness functions providing the per-step SDPI inequality. -/
class SDPIStepData (X Y : Type u) [DirectedInfo X Y] [SDPI X Y] where
  pre  : Time → (Time → X) → (Time → Y) → ℝ
  post : Time → (Time → X) → (Time → Y) → ℝ
  sdpi_step  : ∀ t x y, post t x y ≤ SDPI.η (X:=X) (Y:=Y) t * pre t x y
  per_le_post : ∀ t x y, DirectedInfo.perStep t x y ≤ post t x y

instance (X Y : Type u)
    [DirectedInfo X Y] [SDPI X Y] [w : SDPIStepData X Y] :
    SDPIStepWitness X Y where
  pre        := w.pre
  post       := w.post
  sdpi_step  := w.sdpi_step
  per_le_post:= w.per_le_post

end DI
end NOC
