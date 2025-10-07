import Mathlib

/-!
Module: NOC.E.Interfaces.DI
Summary: Standard typeclass interfaces for Directed Information and SDPI, plus
         reusable lemma targets (Massey chain, per-step SDPI shim, global DI bound).

These abstractions let a proof agent instantiate DI and SDPI once (for a concrete
model), and then reuse the standard inequalities across the codebase.
-/

namespace NOC
universe u v

/-- Discrete time index. -/
abbrev Time := Nat

/-- Directed information over finite horizons: provide a total `DI n` and a per-step
contribution `perStep t`, with the Massey chain rule `DI n = ∑ perStep t` as a class law. -/
class DirectedInfo (X Y : Type u) where
  DI        : (n : Nat) → (x : Time → X) → (y : Time → Y) → ℝ
  perStep   : (t : Time) → (x : Time → X) → (y : Time → Y) → ℝ
  chainRule : ∀ (n : Nat) (x : Time → X) (y : Time → Y),
    DI n x y = (Finset.range (n+1)).sum (fun t => perStep t x y)

/-- Strong Data-Processing Inequality (per-step) with a contraction `η t ∈ [0,1)`. -/
class SDPI (X Y : Type u) where
  η        : Time → ℝ
  η_range  : ∀ t, 0 ≤ η t ∧ η t < 1

/-- Witness functions to connect a concrete per-step pre/post information quantity to SDPI. -/
class SDPIStepWitness (X Y : Type u) [DirectedInfo X Y] [SDPI X Y] where
  pre  : Time → (Time → X) → (Time → Y) → ℝ
  post : Time → (Time → X) → (Time → Y) → ℝ
  /-- Per-step SDPI inequality: `post_t ≤ η_t * pre_t`. -/
  sdpi_step : ∀ (t : Time) (x : Time → X) (y : Time → Y),
    post t x y ≤ SDPI.η (X:=X) (Y:=Y) t * pre t x y
  /-- Bridge from the DI per-step term to the SDPI `post` witness. -/
  per_le_post : ∀ (t : Time) (x : Time → X) (y : Time → Y),
    DirectedInfo.perStep t x y ≤ post t x y

namespace DI
open scoped BigOperators

/-- Restated chain rule (directly from the class law) for convenience. -/
@[simp] theorem massey_chain_rule
  {X Y : Type u} [DirectedInfo X Y]
  (n : Nat) (x : Time → X) (y : Time → Y) :
  DirectedInfo.DI n x y
    = (Finset.range (n+1)).sum (fun t => DirectedInfo.perStep t x y) := by
  simpa using (DirectedInfo.chainRule (X:=X) (Y:=Y) n x y)

/-- Per-step SDPI shim (target for the agent): relate a concrete `post_t` to `η_t * pre_t`.
Provide this from your concrete stochastic channel/garbling properties. -/
theorem sdpi_step_inequality
  {X Y : Type u} [DirectedInfo X Y] [SDPI X Y] [SDPIStepWitness X Y]
  (t : Time) (x : Time → X) (y : Time → Y) :
  SDPIStepWitness.post t x y ≤ SDPI.η (X:=X) (Y:=Y) t * SDPIStepWitness.pre t x y :=
  SDPIStepWitness.sdpi_step t x y

/-- Global DI contraction under per-step SDPI: DI ≤ ∑ η_t pre_t. -/
theorem di_monotone_under_garbling
  {X Y : Type u} [DirectedInfo X Y] [SDPI X Y] [SDPIStepWitness X Y]
  (n : Nat) (x : Time → X) (y : Time → Y) :
  DirectedInfo.DI n x y ≤
    (Finset.range (n+1)).sum (fun t => SDPI.η (X:=X) (Y:=Y) t * SDPIStepWitness.pre t x y) := by
  classical
  -- Expand DI via chain rule, then apply the per-step SDPI inequality termwise
  have h0 := massey_chain_rule (X:=X) (Y:=Y) n x y
  -- Sum per-step ≤ post
  have hsum_per_le_post :
    (Finset.range (n+1)).sum (fun t => DirectedInfo.perStep t x y)
      ≤ (Finset.range (n+1)).sum (fun t => SDPIStepWitness.post t x y) := by
    apply Finset.sum_le_sum
    intro t ht; exact SDPIStepWitness.per_le_post t x y
  -- Sum post ≤ sum η*pre
  have hsum_post_le_eta_pre :
    (Finset.range (n+1)).sum (fun t => SDPIStepWitness.post t x y)
      ≤ (Finset.range (n+1)).sum (fun t => SDPI.η (X:=X) (Y:=Y) t * SDPIStepWitness.pre t x y) := by
    apply Finset.sum_le_sum
    intro t ht
    exact sdpi_step_inequality (X:=X) (Y:=Y) t x y
  -- Chain the two
  have hsum :
    (Finset.range (n+1)).sum (fun t => DirectedInfo.perStep t x y)
      ≤ (Finset.range (n+1)).sum (fun t => SDPI.η (X:=X) (Y:=Y) t * SDPIStepWitness.pre t x y) :=
    le_trans hsum_per_le_post hsum_post_le_eta_pre
  -- Finish: rewrite DI via chain rule and apply the sum inequality
  simpa [h0]
    using hsum

end DI
end NOC
