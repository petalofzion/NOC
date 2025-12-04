import Mathlib
import NOC.E.Interfaces.DI
import NOC.E.Interfaces.DI_NOC_Instance

/-!
Module: NOC.E.Examples.StrictBSC
Status: strict T=3 example with mixed schedule.

Purpose
- Implement a T=3 Directed Information example with a 'Mixed' schedule.
- Schedule: η(2) = 0.64 (BSC noise), η(t) = 1 (Identity) for all other t.
- Prove that global DI is STRICTLY LESS than the sum of inputs (AggBefore).
-/

namespace NOC.E.Examples

open scoped BigOperators

/- Mixed schedule: `η t = if t = 2 then 0.64 else 1`. -/
@[simp] def etaMixed (t : Nat) : ℝ := if t = 2 then (0.64 : ℝ) else (1 : ℝ)

lemma etaMixed_range : ∀ t, 0 ≤ etaMixed t ∧ etaMixed t ≤ 1 := by
  intro t
  simp [etaMixed]
  split_ifs <;> norm_num

/- Model: perStep = post; pre = 1; post = η_t. -/
def mixedModel : NOC.DI.NOCStepModel Unit Unit :=
  { perStep := fun t _ _ => etaMixed t,
    pre     := fun _ _ _ => (1 : ℝ),
    post    := fun t _ _ => etaMixed t,
    eta     := etaMixed,
    eta_range := etaMixed_range,
    per_le_post := by intro t x y; simp [etaMixed],
    sdpi_step := by intro t x y; simp [etaMixed] }

/- Register instances via the scaffold. -/
instance : NOC.DI.PerStepData Unit Unit := NOC.DI.mkPerStepData _ _ mixedModel
instance : NOC.DI.SDPIData Unit Unit := NOC.DI.mkSDPIData _ _ mixedModel
instance : NOC.DirectedInfo Unit Unit := by infer_instance
instance : NOC.SDPI Unit Unit := by infer_instance
instance : NOC.DI.SDPIStepData Unit Unit :=
  NOC.DI.mkSDPIStepData _ _ mixedModel (hη := by intro t; rfl) (hper := by intro t x y; rfl)

/- Strict inequality: DI < ∑ pre_t (AggBefore) because of the single noisy step at t=2. -/
theorem mixed_strict_ineq :
  NOC.DirectedInfo.DI (X:=Unit) (Y:=Unit) 3 (fun _ => ()) (fun _ => ())
    < (Finset.range (3+1)).sum (fun _t => (1 : ℝ)) := by
  -- Nonnegativity of pre
  have hpre_nonneg : ∀ t ∈ Finset.range (4), 0 ≤ NOC.SDPIStepWitness.pre (X:=Unit) (Y:=Unit) t (fun _ => ()) (fun _ => ()) := by
    intro t ht
    -- The instance definition guarantees this is 1, but we might need to unfold it.
    -- NOC.SDPIStepWitness.pre reduces to mixedModel.pre via the instance.
    change 0 ≤ (1 : ℝ)
    norm_num

  -- t0 = 2 is in range(4)
  have ht0 : 2 ∈ Finset.range (4) := by decide

  -- η 2 < 1 and pre 2 > 0
  have hη_lt : NOC.SDPI.η (X:=Unit) (Y:=Unit) 2 < 1 := by
    change etaMixed 2 < 1
    norm_num

  have hpre_pos : 0 < NOC.SDPIStepWitness.pre (X:=Unit) (Y:=Unit) 2 (fun _ => ()) (fun _ => ()) := by
    change 0 < (1 : ℝ)
    norm_num

  -- Apply the theorem
  have strict := NOC.DI.di_strict_under_garbling (X:=Unit) (Y:=Unit)
      3 (fun _ => ()) (fun _ => ()) hpre_nonneg 2 ht0 hη_lt hpre_pos
  
  -- The theorem gives DI < ∑ pre. We need DI < 4.
  -- Prove ∑ pre = 4.
  have h_rhs : (Finset.range 4).sum (fun t => NOC.SDPIStepWitness.pre (X:=Unit) (Y:=Unit) t (fun _ => ()) (fun _ => ())) = (Finset.range 4).sum (fun _ => (1 : ℝ)) := by
     apply Finset.sum_congr rfl
     intro t ht
     change (1 : ℝ) = 1
     rfl
  
  rw [h_rhs] at strict
  exact strict

end NOC.E.Examples