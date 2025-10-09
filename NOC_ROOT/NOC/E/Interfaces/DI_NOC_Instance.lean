import Mathlib
import NOC.E.Interfaces.DI
import NOC.E.Interfaces.DI_Toy

/-!
Module: NOC.E.Interfaces.DI_NOC_Instance
Status: instance scaffolding (no sorrys).

Purpose
- Provide a small, reusable scaffold to register a NOC per‑step model with the
  existing typeclass route for Lemma E.

How to use
- Fill `NOCStepModel` with your per‑step reals (`perStep := post`, `pre`, `post`),
  a uniform SDPI schedule `eta : Time → ℝ` with `0 ≤ η t < 1`, and the per‑step
  inequalities `per_le_post` and `sdpi_step`.
- Then create typeclass instances via `mkPerStepData`, `mkSDPIData`, and
  (after those are in scope) `mkSDPIStepData`. This enables the global lemmas
  `DI.di_monotone_under_garbling` and `DI.di_strict_under_garbling`.

Notes
- This scaffold mirrors `NOC.E.Interfaces.DI_Toy`, but packages the obligations
  in one record to reduce boilerplate at call sites.
-/

namespace NOC
namespace DI

universe u

/- Per‑step model and SDPI witnesses packed in one record. -/
structure NOCStepModel (X Y : Type u) where
  perStep : Time → (Time → X) → (Time → Y) → ℝ
  pre     : Time → (Time → X) → (Time → Y) → ℝ
  post    : Time → (Time → X) → (Time → Y) → ℝ
  eta     : Time → ℝ
  eta_range : ∀ t, 0 ≤ eta t ∧ eta t < 1
  per_le_post : ∀ t x y, perStep t x y ≤ post t x y
  sdpi_step   : ∀ t x y, post t x y ≤ eta t * pre t x y

/- Construct PerStepData from the model. -/
def mkPerStepData (X Y : Type u) (m : NOCStepModel X Y) : PerStepData X Y :=
  { perStep := m.perStep }

/- Construct SDPIData from the model. -/
def mkSDPIData (X Y : Type u) (m : NOCStepModel X Y) : SDPIData X Y :=
  { η := m.eta, η_range := m.eta_range }

/- After registering `PerStepData` and `SDPIData` as instances, use this to
   provide `SDPIStepData` for the global aggregators. -/
def mkSDPIStepData (X Y : Type u) (m : NOCStepModel X Y)
  [DirectedInfo X Y] [SDPI X Y]
  (hη : ∀ t, SDPI.η (X:=X) (Y:=Y) t = m.eta t)
  (hper : ∀ t x y, DirectedInfo.perStep t x y = m.perStep t x y)
  : SDPIStepData X Y :=
  { pre := m.pre, post := m.post,
    sdpi_step := by
      intro t x y
      have := m.sdpi_step t x y
      simpa [hη t] using this,
    per_le_post := by
      intro t x y
      have := m.per_le_post t x y
      simpa [hper t x y] using this }

end DI
end NOC
