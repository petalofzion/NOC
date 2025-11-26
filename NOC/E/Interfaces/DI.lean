import Mathlib

/-!
Module: NOC.E.Interfaces.DI
Summary: Standard typeclass interfaces for Directed Information and SDPI, plus
         reusable lemma targets (Massey chain, per-step SDPI shim, global DI bound).

These abstractions let a proof agent instantiate DI and SDPI once (for a concrete
model), and then reuse the standard inequalities across the codebase.

NOC instantiation checklist (what the real model must provide)
- A1 Filtration alignment: fix the conditioning used in per‑step terms (e.g.,
  F_{t−1} ⊆ σ(Y^{<t}) or an explicit sigma‑algebra you will condition on), and
  prove a short Filtration‑Inclusion Lemma so Massey’s chain rule matches that
  conditioning.
- Per‑step DI decomposition: define `DirectedInfo.perStep t x y` to be your
  causally‑conditioned information term (Massey) for step t.
- SDPI data: choose contraction coefficients `η t` with `0 ≤ η t < 1` together
  with the Markov/garbling structure (e.g., U_t → X_t → Y_t given F_{t−1}) that
  justifies a per‑step SDPI bound.
- Witness bridge: give `SDPIStepWitness.pre/post` so that
  `perStep ≤ post ≤ η·pre` holds at each step. This connects your per‑step DI
  term to the SDPI inequality actually applied.
- Strictness (optional): identify at least one step with `η t < 1` and nonzero
  `pre` to derive a strict global inequality.

Note: NOC_v5 describes the DI–DPI plan and the NCC/SDPI premises conceptually,
but the concrete filtration F_{t−1}, the exact per‑step terms, and a per‑edge
SDPI proof must be supplied here to instantiate the real model.
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

/-- Strict DI contraction under per-step SDPI when some step is strictly contracted
and `pre` is nonnegative everywhere. The inequality compares the total DI against
the uncontracted sum of `pre` terms, yielding a strict drop whenever there exists
`t0 ≤ n` with `η t0 < 1` and `0 < pre t0`.

This lemma intentionally adds the `pre≥0` hypothesis rather than building it into
the `SDPIStepWitness` interface; many models naturally provide nonnegativity of
per-step information, but keeping it as an explicit premise avoids over-constraining
the interface.
-/
theorem di_strict_under_garbling
  {X Y : Type u} [DirectedInfo X Y] [SDPI X Y] [SDPIStepWitness X Y]
  (n : Nat) (x : Time → X) (y : Time → Y)
  (hpre_nonneg : ∀ t ∈ Finset.range (n+1), 0 ≤ SDPIStepWitness.pre t x y)
  (t0 : Nat) (ht0 : t0 ∈ Finset.range (n+1))
  (hη_lt : SDPI.η (X:=X) (Y:=Y) t0 < 1)
  (hpre_pos : 0 < SDPIStepWitness.pre t0 x y) :
  DirectedInfo.DI n x y <
    (Finset.range (n+1)).sum (fun t => SDPIStepWitness.pre t x y) := by
  classical
  -- Step 1: DI ≤ ∑ η_t * pre_t (global SDPI contraction)
  have h_contr := di_monotone_under_garbling (X:=X) (Y:=Y) n x y
  -- Step 2: Show strict inequality ∑ η_t pre_t < ∑ pre_t using η_t ≤ 1 and η_{t0} < 1 with pre_{t0} > 0
  have h_all_le :
      ∀ t ∈ Finset.range (n+1),
        SDPI.η (X:=X) (Y:=Y) t * SDPIStepWitness.pre t x y
          ≤ SDPIStepWitness.pre t x y := by
    intro t ht
    have hη_le_one : SDPI.η (X:=X) (Y:=Y) t ≤ 1 := (SDPI.η_range (X:=X) (Y:=Y) t).2.le
    have hpre_nn : 0 ≤ SDPIStepWitness.pre t x y := hpre_nonneg t ht
    simpa [one_mul] using
      (mul_le_mul_of_nonneg_right hη_le_one hpre_nn)
  have h_one_strict :
      SDPI.η (X:=X) (Y:=Y) t0 * SDPIStepWitness.pre t0 x y
        < SDPIStepWitness.pre t0 x y := by
    have hη_le : SDPI.η (X:=X) (Y:=Y) t0 < 1 := hη_lt
    simpa [one_mul] using
      (mul_lt_mul_of_pos_right hη_le hpre_pos)
  have h_strict_exists :
      ∃ t ∈ Finset.range (n+1),
        SDPI.η (X:=X) (Y:=Y) t * SDPIStepWitness.pre t x y
          < SDPIStepWitness.pre t x y := ⟨t0, ht0, h_one_strict⟩
  have h_sum_strict :
      (Finset.range (n+1)).sum (fun t => SDPI.η (X:=X) (Y:=Y) t * SDPIStepWitness.pre t x y)
        < (Finset.range (n+1)).sum (fun t => SDPIStepWitness.pre t x y) :=
    Finset.sum_lt_sum h_all_le h_strict_exists
  -- Chain inequalities: DI ≤ ∑ η·pre < ∑ pre
  exact lt_of_le_of_lt h_contr h_sum_strict

/- Explicit (non‑typeclass) variant of the global DI contraction.
Provide concrete `pre`/`post` per‑step functions together with the two per‑step
inequalities and conclude `DI ≤ ∑ η_t · pre_t`. This avoids installing a global
`SDPIStepWitness` instance when you want local control. -/
theorem di_monotone_under_garbling_explicit
  {X Y : Type u} [DirectedInfo X Y] [SDPI X Y]
  (pre post : Time → (Time → X) → (Time → Y) → ℝ)
  (n : Nat) (x : Time → X) (y : Time → Y)
  (h_per_le_post : ∀ t, DirectedInfo.perStep t x y ≤ post t x y)
  (h_sdpi_step  : ∀ t, post t x y ≤ SDPI.η (X:=X) (Y:=Y) t * pre t x y) :
  DirectedInfo.DI n x y ≤
    (Finset.range (n+1)).sum (fun t => SDPI.η (X:=X) (Y:=Y) t * pre t x y) := by
  classical
  have h0 := massey_chain_rule (X:=X) (Y:=Y) n x y
  have hsum_per_le_post :
    (Finset.range (n+1)).sum (fun t => DirectedInfo.perStep t x y)
      ≤ (Finset.range (n+1)).sum (fun t => post t x y) := by
    refine Finset.sum_le_sum ?_
    intro t ht; exact h_per_le_post t
  have hsum_post_le_eta_pre :
    (Finset.range (n+1)).sum (fun t => post t x y)
      ≤ (Finset.range (n+1)).sum (fun t => SDPI.η (X:=X) (Y:=Y) t * pre t x y) := by
    refine Finset.sum_le_sum ?_
    intro t ht; exact h_sdpi_step t
  have hsum := le_trans hsum_per_le_post hsum_post_le_eta_pre
  simpa [h0] using hsum

/- Strict explicit variant: if `pre_t ≥ 0` for all `t ≤ n` and some `t0 ≤ n` has
`η_t0 < 1` and `pre_t0 > 0`, then `DI < ∑ pre_t`. -/
theorem di_strict_under_garbling_explicit
  {X Y : Type u} [DirectedInfo X Y] [SDPI X Y]
  (pre post : Time → (Time → X) → (Time → Y) → ℝ)
  (n : Nat) (x : Time → X) (y : Time → Y)
  (h_per_le_post : ∀ t, DirectedInfo.perStep t x y ≤ post t x y)
  (h_sdpi_step  : ∀ t, post t x y ≤ SDPI.η (X:=X) (Y:=Y) t * pre t x y)
  (hpre_nonneg : ∀ t ∈ Finset.range (n+1), 0 ≤ pre t x y)
  (t0 : Nat) (ht0 : t0 ∈ Finset.range (n+1))
  (hη_lt : SDPI.η (X:=X) (Y:=Y) t0 < 1)
  (hpre_pos : 0 < pre t0 x y) :
  DirectedInfo.DI n x y <
    (Finset.range (n+1)).sum (fun t => pre t x y) := by
  classical
  have h_contr := di_monotone_under_garbling_explicit (X:=X) (Y:=Y)
      pre post n x y h_per_le_post h_sdpi_step
  have h_all_le : ∀ t ∈ Finset.range (n+1),
      SDPI.η (X:=X) (Y:=Y) t * pre t x y ≤ pre t x y := by
    intro t ht
    have hη_le_one : SDPI.η (X:=X) (Y:=Y) t ≤ 1 := (SDPI.η_range (X:=X) (Y:=Y) t).2.le
    have hpre_nn : 0 ≤ pre t x y := hpre_nonneg t ht
    simpa [one_mul] using mul_le_mul_of_nonneg_right hη_le_one hpre_nn
  have h_one_strict : SDPI.η (X:=X) (Y:=Y) t0 * pre t0 x y < pre t0 x y := by
    simpa [one_mul] using (mul_lt_mul_of_pos_right hη_lt hpre_pos)
  have h_strict_exists : ∃ t ∈ Finset.range (n+1),
      SDPI.η (X:=X) (Y:=Y) t * pre t x y < pre t x y := ⟨t0, ht0, h_one_strict⟩
  have h_sum_strict :
      (Finset.range (n+1)).sum (fun t => SDPI.η (X:=X) (Y:=Y) t * pre t x y)
        < (Finset.range (n+1)).sum (fun t => pre t x y) :=
    Finset.sum_lt_sum h_all_le h_strict_exists
  exact lt_of_le_of_lt h_contr h_sum_strict

end DI
end NOC
