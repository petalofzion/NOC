import Mathlib
import NOC.D.BetaStabilityTTSA
import NOC.Prob.MDS
import NOC.Prob.Alignment
import NOC.Prob.RobbinsSiegmund

/-!
Module: NOC.D.TTSA_Convergence
Status: scaffolding (no axioms). Organizes the Option 1 (1‑D projected SA)
and Option 2 (full TTSA A/B) theorem targets with precise, named bundles
and conclusions. These statements are ready for the proof agent to fill.

Design: conclusions are packaged as `Prop` fields in hypothesis bundles
so we avoid committing to a specific measure API in this file. Once the
probability layer lands (NOC.Prob.*), these fields can be realized.

Mathlib toolkit referenced by this scaffold:
- D3 (clamp nonexpansive): `LipschitzWith.id.const_min`,
  `LipschitzWith.const_max` (Topology/MetricSpace/Holder.lean)
- D1 (MDS sums, used by Option 1): see `NOC.Prob.MDS` notes — conditional
  expectation API, martingale construction, Chebyshev/BC and/or a.e.
  martingale convergence.
- D2 (Robbins–Siegmund, used by Option 1 + D6): see `NOC.Prob.RobbinsSiegmund`.
- Deterministic stepping lemmas (window/hitting) already live in
  `NOC.D.BetaStabilityTTSA` and are imported above.
-/

namespace NOC.TTSA
noncomputable section
open Classical

/-! ## Shared utilities -/

/-- Non-expansiveness of the canonical clamp projection on the interval
`[0, βmax]`.  We package it as a `LipschitzWith` statement to make it easy
to reuse inside projected stochastic-approximation proofs. -/
lemma clamp_nonexpansive (βmax : ℝ) :
    LipschitzWith 1 (fun x : ℝ => max 0 (min βmax x)) := by
  -- `min βmax` is 1-Lipschitz (composition with the identity), and composing
  -- with `max 0` preserves the constant.
  have hmin : LipschitzWith 1 (fun x : ℝ => min βmax x) :=
    (LipschitzWith.id.const_min βmax)
  simpa using (LipschitzWith.const_max hmin 0)

/-! ## Option 1 — 1‑D projected SA meta‑theorem -/

/-- Hypotheses for the 1‑D projected SA convergence theorem. -/
structure OneDProjectedSAHypotheses where
  βmax         : ℝ
  steps        : Prop   -- Robbins–Monro: ∑ b_n = ∞, ∑ b_n^2 < ∞
  noise        : Prop   -- MDS + bounded conditional second moment
  bias         : Prop   -- ∑ b_n E|δ_{n+1}| < ∞ (or a.s. summable)
  drift        : Prop   -- ḡ continuous, locally Lipschitz, sign window near 0
  root_unique  : Prop   -- unique interior root β⋆ and local stability
  alignment    : Prop   -- β_{n+1} = clamp(β_n + b_n (ḡ + ξ + δ)) (adapted)
  /-- Desired conclusion: a.s. interior hit and convergence to β⋆. -/
  conclusion   : Prop

/-- Projected SA convergence in 1‑D (Option 1).
Under the hypotheses above, the clamped recursion converges a.s. to the
unique, locally stable interior root of the averaged drift. -/
def projected_SA_converges_1D (H : OneDProjectedSAHypotheses) : Prop :=
  -- Target conclusion placeholder; the proof agent will provide a term of this Prop.
  H.conclusion

/-- D4 (alias): Projected SA convergence in 1‑D.
This name matches the meta‑theorem referenced by downstream modules. -/
def projected_SA_converges (H : OneDProjectedSAHypotheses) : Prop :=
  projected_SA_converges_1D H

/-! ## D6 — Interior positivity (bridge lemma)

This is the 1‑D “interior hit” statement used to pass from a positive
drift window near 0 to eventual positivity of the clamped recursion. We
keep it as a Prop‑level target here; downstream files can instantiate it
with Robbins–Siegmund once the probability layer is finalized. -/

/-- Hypotheses for the 1‑D interior hit under stochasticity. -/
structure OneDInteriorHitHypotheses where
  βmax        : ℝ
  steps       : Prop   -- ∑ b_n^2 < ∞ and b_n → 0 (Robbins–Monro)
  noise       : Prop   -- MDS noise with bounded conditional variance
  bias        : Prop   -- ∑ b_n E|δ_{n+1}| < ∞ (or a.s.)
  pos_window  : Prop   -- ḡ(β) ≥ ε on [0, K]
  alignment   : Prop   -- β_{n+1} = clamp(β_n + b_n (ḡ(β_n)+ξ_{n+1}+δ_{n+1}))
  conclusion  : Prop   -- ∃ K>0, τ_K < ∞ a.s. and β_n ≥ K for n ≥ τ_K

/-- D6: interior positivity (stochastic window → a.s. hit). -/
def projected_SA_interior_hit (H : OneDInteriorHitHypotheses) : Prop :=
  H.conclusion

/-! ## Option 2A — Full TTSA with unique fast equilibrium (vector) -/

/-- Hypothesis bundle for TTSA with a unique globally stable fast equilibrium.
Spaces and projections are abstracted; Lipschitz, separation, and noise
conditions are summarized as `Prop` fields to be instantiated later. -/
structure TTSAUniqueEqHypotheses where
  spaces        : Prop   -- Y,B compact convex sets (abstracted)
  projections   : Prop   -- non-expansive projections (Euclidean)
  schedules     : Prop   -- ∑ a_n = ∞, ∑ a_n^2 < ∞; ∑ b_n = ∞, ∑ b_n^2 < ∞; b_n/a_n → 0
  drifts        : Prop   -- H,G Lipschitz
  fast_unique   : Prop   -- ∀β, unique globally stable y*(β), continuous in β
  slow_avg      : Prop   -- define Ḡ(β) = G(y*(β), β), continuous
  slow_proj_ode : Prop   -- projected ODE well-posed (tangent-cone form)
  noise         : Prop   -- two MDS with bounded conditional second moments
  stable_root   : Prop   -- unique locally stable equilibrium β⋆ in int(B)
  conclusion    : Prop   -- tracking + APT + convergence

/-- TTSA meta-theorem (Option 2A, projected): unique fast equilibrium. -/
def TTSA_projected_unique_equilibrium (H : TTSAUniqueEqHypotheses) : Prop :=
  -- Conclusion placeholder: tracking + APT + convergence (to be proved).
  H.conclusion

/-! ## Option 2B — Full TTSA with ergodic fast dynamics (vector) -/

/-- Hypothesis bundle for TTSA with ergodic fast dynamics and averaging. -/
structure TTSAErgodicHypotheses where
  spaces        : Prop   -- Y,B compact convex sets (abstracted)
  projections   : Prop   -- non-expansive projections (Euclidean)
  schedules     : Prop   -- ∑ a_n = ∞, ∑ a_n^2 < ∞; ∑ b_n = ∞, ∑ b_n^2 < ∞; b_n/a_n → 0
  drifts        : Prop   -- H,G Lipschitz; fast Markov dynamics well-defined
  ergodic_fast  : Prop   -- ∀β, invariant μ_β; mixing adequate for averaging
  slow_avg      : Prop   -- Ḡ(β) = ∫ G(y,β) dμ_β(y), continuous
  slow_proj_ode : Prop   -- projected ODE well-posed (tangent-cone form)
  noise         : Prop   -- two MDS with bounded conditional second moments
  stable_root   : Prop   -- unique locally stable equilibrium β⋆ in int(B)
  conclusion    : Prop   -- averaging + APT + convergence

/-- TTSA meta-theorem (Option 2B, projected): ergodic fast dynamics. -/
def TTSA_projected_ergodic (H : TTSAErgodicHypotheses) : Prop :=
  -- Conclusion placeholder: averaging + APT + convergence (to be proved).
  H.conclusion

end
end NOC.TTSA
