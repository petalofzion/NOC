import Mathlib

/-!
Module: NOC.E.ConditionalDIDPI
Status: scaffolding (with proof plan and tactic outline).

Goal: formal shell for a conditional Directed-Information DPI statement used in Lemma E.
We target a finite-horizon, finite-alphabet setting and bundle the assumptions
as records:

- finite process interface (types, horizons);
- a post-processing/garbling clause (Markov structure or contraction witness);
- a per-step Massey decomposition placeholder;
- the main “garbling cannot increase DI” inequality (strict with SDPI).

High‑level proof plan (Massey decomposition + SDPI):
1) Use Massey’s chain rule: I(A^{1:T} → S^{1:T}) = Σ_{t=1..T} I(A^{1:t}; S_t | S^{1:t−1}).
2) Under a post‑processing/garbling relation for the partner’s channel at step t,
   apply a per-step SDPI: I(U; Y) ≤ η·I(U; X) when Y is a contraction of X.
   Encode the step‑t hypothesis as `garble.witness` and `garble.η` with η<1.
3) Combine with conditioning on S^{1:t−1} (monotonicity w.r.t. side‑information) to
   bound each term after ablation by the corresponding pre‑ablation term.
4) Sum over t to get DI_after ≤ DI_before. If η<1 on any relevant step with nonzero
   term, the inequality is strict.

Tactic outline:
- Provide small per-step lemmas (later):
  • `perStepSDPI`: turn the garbling witness into an SDPI bound for the step‑t mutual info;
  • `cond_monotone`: conditioning on S^{1:t−1} is admissible and preserves the SDPI shape;
  • `massey_chain`: expand DI via the chain rule and rewrite sums.
- Conclude by replacing each term after ablation with its bound in terms of the
  corresponding pre‑ablation term and summing inequalities.
Currently, we keep the final theorem as a placeholder to unblock downstream usage.
-/

namespace NOC
noncomputable section
open Classical

/-- Minimal finite-horizon process scaffold (finite alphabets). -/
structure FiniteProcess where
  T : ℕ
  State : Type
  Action : Type
  Observation : Type
  [stateFin : Fintype State]
  [actFin   : Fintype Action]
  [obsFin   : Fintype Observation]

/-- Garbling/post-processing predicate on a per-step channel. -/
structure Garbling where
  η : ℝ           -- contraction (SDPI) coefficient, intended 0 ≤ η < 1
  η_lt_one : η < 1
  witness : Prop  -- formalizes the Markov/garbling structure

/-- Placeholder for a directed-information functional on finite processes. -/
structure DirectedInformation (P : FiniteProcess) where
  value : ℝ

/-- Context bundling original vs. garbled partner along a fixed process horizon. -/
structure DIDPIContext where
  P : FiniteProcess
  garble : Garbling
  DI_before : DirectedInformation P
  DI_after  : DirectedInformation P

/-- Generic DI–DPI aggregator: if the per‑step contributions of the “after” process are bounded
above by those of the “before” process and DI expands as a sum over steps, then the total DI obeys
`DI_after ≤ DI_before`. This is the algebraic shell; instantiate `perBefore/perAfter` later using
Massey’s chain rule and per‑step SDPI bounds. -/
theorem di_dpi_from_perstep (ctx : DIDPIContext)
  (perBefore perAfter : ℕ → ℝ)
  (hBefore : ctx.DI_before.value = (Finset.range ctx.P.T).sum perBefore)
  (hAfter  : ctx.DI_after.value  = (Finset.range ctx.P.T).sum perAfter)
  (hStep   : ∀ t ∈ Finset.range ctx.P.T, perAfter t ≤ perBefore t) :
  ctx.DI_after.value ≤ ctx.DI_before.value := by
  classical
  -- Rewrite both sides via the given expansions, then compare sums termwise.
  have hsum : (Finset.range ctx.P.T).sum perAfter
              ≤ (Finset.range ctx.P.T).sum perBefore :=
    Finset.sum_le_sum (by
      intro t ht
      exact hStep t ht)
  simpa [hBefore, hAfter]
    using hsum
/-- Strict DI–DPI: if each per‑step term after ablation is ≤ the original term and at least one
step is strictly smaller, then the total DI decreases strictly. -/
theorem di_dpi_from_perstep_strict (ctx : DIDPIContext)
  (perBefore perAfter : ℕ → ℝ)
  (hBefore : ctx.DI_before.value = (Finset.range ctx.P.T).sum perBefore)
  (hAfter  : ctx.DI_after.value  = (Finset.range ctx.P.T).sum perAfter)
  (hStep   : ∀ t ∈ Finset.range ctx.P.T, perAfter t ≤ perBefore t)
  (hStrict : ∃ t ∈ Finset.range ctx.P.T, perAfter t < perBefore t) :
  ctx.DI_after.value < ctx.DI_before.value := by
  classical
  have hsum : (Finset.range ctx.P.T).sum perAfter
              < (Finset.range ctx.P.T).sum perBefore :=
    Finset.sum_lt_sum hStep hStrict
  simpa [hBefore, hAfter] using hsum

/-- Massey chain rule (skeleton): per‑step contributions that expand `DI_before` and `DI_after`.
The agent should instantiate these with the actual per‑step directed information terms induced by
the model, then prove the equalities. -/
structure MasseyChainDecomp (ctx : DIDPIContext) where
  perBefore : ℕ → ℝ
  perAfter  : ℕ → ℝ
  chain_before : ctx.DI_before.value = (Finset.range ctx.P.T).sum perBefore
  chain_after  : ctx.DI_after.value  = (Finset.range ctx.P.T).sum perAfter

/-- Per‑step SDPI bound (skeleton): under the post‑processing/garbling predicate at step `t`,
the after‑term is bounded by the before‑term. The agent should formulate this from the model’s
Markov/wiring structure and a standard SDPI coefficient. -/
def perStepSDPI (ctx : DIDPIContext) (D : MasseyChainDecomp ctx) : Prop :=
  ∀ t ∈ Finset.range ctx.P.T, D.perAfter t ≤ D.perBefore t

/-- Strictness for SDPI: at least one step is strictly contracted (η < 1 with nonzero before term).
This enables the global strict inequality. -/
def perStepSDPI_strict (ctx : DIDPIContext) (D : MasseyChainDecomp ctx) : Prop :=
  ∃ t ∈ Finset.range ctx.P.T, D.perAfter t < D.perBefore t

/-- Conditional DI–DPI via Massey + SDPI: global non‑increase. -/
theorem conditional_DI_DPI_massey
  (ctx : DIDPIContext) (D : MasseyChainDecomp ctx)
  (hStep : perStepSDPI ctx D) :
  ctx.DI_after.value ≤ ctx.DI_before.value := by
  classical
  -- Apply the ready-made aggregator with the per‑step decomposition and bounds
  refine di_dpi_from_perstep (ctx := ctx) (perBefore := D.perBefore) (perAfter := D.perAfter)
    (hBefore := D.chain_before) (hAfter := D.chain_after) (hStep := ?_)
  intro t ht; exact hStep t ht

/-- Strict version via Massey + SDPI. -/
theorem conditional_DI_DPI_massey_strict
  (ctx : DIDPIContext) (D : MasseyChainDecomp ctx)
  (hStep : perStepSDPI ctx D) (hStrict : perStepSDPI_strict ctx D) :
  ctx.DI_after.value < ctx.DI_before.value := by
  classical
  refine di_dpi_from_perstep_strict (ctx := ctx)
    (perBefore := D.perBefore) (perAfter := D.perAfter)
    (hBefore := D.chain_before) (hAfter := D.chain_after)
    (hStep := ?_) (hStrict := ?_)
  · intro t ht; exact hStep t ht
  · rcases hStrict with ⟨t, ht, hlt⟩; exact ⟨t, ht, hlt⟩
-- (Aggregator lemmas are defined above.)

 /-- Conditional DI–DPI: if the DI of the “before” and “after” processes expand over the same
 index set and each per-step term after ablation is bounded above by the original term, then the
 total DI cannot increase. This is the Lean version of the Massey + per-step SDPI argument. -/
theorem conditional_DI_DPI (ctx : DIDPIContext)
  (perBefore perAfter : ℕ → ℝ)
  (hBefore : ctx.DI_before.value = (Finset.range ctx.P.T).sum perBefore)
  (hAfter  : ctx.DI_after.value  = (Finset.range ctx.P.T).sum perAfter)
  (hStep   : ∀ t ∈ Finset.range ctx.P.T, perAfter t ≤ perBefore t) :
  ctx.DI_after.value ≤ ctx.DI_before.value :=
  di_dpi_from_perstep (ctx := ctx) (perBefore := perBefore) (perAfter := perAfter)
    (hBefore := hBefore) (hAfter := hAfter) (hStep := hStep)

end
end NOC
