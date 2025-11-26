import Mathlib
import NOC.E.Interfaces.DI
import NOC.E.Interfaces.DI_Toy
import NOC.E.Interfaces.DI_NOC_Instance

/-!
Module: NOC.E.Interfaces.Examples.DI_NOC_BSC
Status: small strict example (no sorrys).

Purpose
- Demonstrate the typeclass route with a concrete per-step model where
  `pre_t = 1`, `post_t = η_t`, `perStep_t = post_t`, and a strict SDPI step.
  This yields a strict global inequality via `DI.di_strict_under_garbling`.

Note
- This is an algebraic harness (no MI constructors); it mirrors a BSC/q‑SC
  schedule by choosing a strict `η t0 < 1` and `η t < 1` elsewhere.
-/

namespace NOC
namespace DI

open scoped BigOperators

/- Strict schedule: `η t = if t = 1 then 0.64 else 0.95` (both < 1). -/
@[simp] def etaStrict (t : Time) : ℝ := if t = 1 then (0.64 : ℝ) else (0.95 : ℝ)

lemma etaStrict_range : ∀ t, 0 ≤ etaStrict t ∧ etaStrict t < 1 := by
  intro t; by_cases h : t = 1
  · subst h; norm_num
  · have : etaStrict t = 0.95 := by simp [etaStrict, h]
    simp [this]

/- Model: perStep = post; pre = 1; post = η_t. -/
def bscModel : NOCStepModel Unit Unit :=
  { perStep := fun t _ _ => etaStrict t,
    pre     := fun _ _ _ => (1 : ℝ),
    post    := fun t _ _ => etaStrict t,
    eta     := etaStrict,
    eta_range := etaStrict_range,
    per_le_post := by intro t x y; simp,
    sdpi_step := by intro t x y; simp [etaStrict] }

/- Register instances via the scaffold. -/
instance : PerStepData Unit Unit := mkPerStepData _ _ bscModel
instance : SDPIData Unit Unit := mkSDPIData _ _ bscModel
instance : DirectedInfo Unit Unit := by infer_instance
instance : SDPI Unit Unit := by infer_instance
instance : SDPIStepData Unit Unit :=
  mkSDPIStepData _ _ bscModel (hη := by intro t; rfl) (hper := by intro t x y; rfl)

/- Monotone inequality: DI ≤ ∑ η_t * pre_t. -/
lemma bsc_monotone (n : Nat) :
  DirectedInfo.DI (X:=Unit) (Y:=Unit) n (fun _ => ()) (fun _ => ())
    ≤ (Finset.range (n+1)).sum (fun t => SDPI.η (X:=Unit) (Y:=Unit) t * (1 : ℝ)) := by
  simpa using
    (NOC.DI.di_monotone_under_garbling (X:=Unit) (Y:=Unit) n (fun _ => ()) (fun _ => ()))

/- Strict inequality: DI < ∑ pre_t. We pick t0=1 as the strict step. -/
lemma bsc_strict :
  DirectedInfo.DI (X:=Unit) (Y:=Unit) 2 (fun _ => ()) (fun _ => ())
    < (Finset.range (2+1)).sum (fun _t => (1 : ℝ)) := by
  -- Nonnegativity of pre
  have hpre_nonneg : ∀ t ∈ Finset.range (3), 0 ≤ (1 : ℝ) := by
    intro t ht; norm_num
  -- t0 = 1 is in range(3)
  have ht0 : 1 ∈ Finset.range (3) := by decide
  -- η 1 < 1 and pre 1 > 0
  have hη_lt : SDPI.η (X:=Unit) (Y:=Unit) 1 < 1 := by simp [etaStrict]
  have hpre_pos : 0 < (1 : ℝ) := by norm_num
  simpa using
    (NOC.DI.di_strict_under_garbling (X:=Unit) (Y:=Unit)
      2 (fun _ => ()) (fun _ => ()) hpre_nonneg 1 ht0 hη_lt hpre_pos)

end DI
end NOC

