import Mathlib
import NOC.E.Interfaces.DI
import NOC.E.Interfaces.DI_Toy

/-!
Module: NOC.E.Interfaces.DI_ToyExample
Status: minimal, non-vacuous toy instantiation (no sorrys).

Purpose: provide a concrete, finite toy model that instantiates the DI/SDPI
interfaces and demonstrates the global DI contraction via the aggregator.

Design:
- Types `X = Unit`, `Y = Unit` (singletons) to avoid probability infrastructure.
- Per-step DI contribution is `η_t` (nontrivial but bounded), SDPI contraction uses
  the same `η_t` with `pre_t = 1` and `post_t = η_t`. This makes the inequality tight
  (equality), serving as a sanity check for the composition lemma.
- This example is deliberately simple but non-vacuous (η_t ∈ (0,1)).
-/

namespace NOC
namespace DI

open scoped BigOperators

/- Toy contraction schedule: constant η_t = 1/2. -/
@[simp] def toyEta (t : Time) : ℝ := (1 / 2 : ℝ)

/- Per-step DI data: the per-step directed information equals η_t. -/
instance : PerStepData Unit Unit where
  perStep := fun t _x _y => toyEta t

/- SDPI contraction data with the same η_t. -/
instance : SDPIData Unit Unit where
  η := toyEta
  η_range := by
    intro t; constructor <;> norm_num

/- SDPI witnesses: post_t = η_t and pre_t = 1, so post_t ≤ η_t·pre_t holds by rfl. -/
instance : SDPIStepData Unit Unit where
  pre        := fun _t _x _y => (1 : ℝ)
  post       := fun t _x _y => toyEta t
  sdpi_step  := by intro t x y; simp [toyEta]
  per_le_post:= by intro t x y; simp [toyEta]

/- A concrete DI contraction instance: the aggregator inequality specializes to an equality here. -/
lemma toy_di_contraction (n : Nat) :
  DirectedInfo.DI (X:=Unit) (Y:=Unit) n (fun _ => ()) (fun _ => ())
    ≤ (Finset.range (n+1)).sum (fun t => SDPI.η (X:=Unit) (Y:=Unit) t * (1 : ℝ)) := by
  -- Directly reuse the generic aggregator; all instances are in scope.
  simpa using
    (NOC.DI.di_monotone_under_garbling (X:=Unit) (Y:=Unit) n (fun _ => ()) (fun _ => ()))

/- Strict contraction variant: since `η_t = 1/2` and `pre_t = 1`, we have a strict
   global drop `DI n < ∑ pre_t`. This exercises the strict typeclass lemma. -/
lemma toy_di_strict_contraction (n : Nat) :
  DirectedInfo.DI (X:=Unit) (Y:=Unit) n (fun _ => ()) (fun _ => ())
    < (Finset.range (n+1)).sum (fun _t => (1 : ℝ)) := by
  -- Use the strict lemma with pre≥0, a strict step at t0=0, and pre_0 > 0.
  have hpre_nonneg : ∀ t ∈ Finset.range (n+1), 0 ≤ (1 : ℝ) := by
    intro t ht; norm_num
  have ht0 : 0 ∈ Finset.range (n+1) := by
    simpa using Nat.succ_pos n
  have hη_lt : SDPI.η (X:=Unit) (Y:=Unit) 0 < 1 := by
    -- η 0 = 1/2
    norm_num [toyEta]
  have hpre_pos : 0 < (1 : ℝ) := by norm_num
  -- Apply strict lemma; all instances are in scope, and `pre` reduces to `1` by def.
  simpa using
    (NOC.DI.di_strict_under_garbling (X:=Unit) (Y:=Unit)
      n (fun _ => ()) (fun _ => ()) (by
        -- rewrite `pre` to `1` and apply `hpre_nonneg`
        intro t ht; simpa using hpre_nonneg t ht)
      0 ht0 hη_lt (by simpa using hpre_pos))

end DI
end NOC
