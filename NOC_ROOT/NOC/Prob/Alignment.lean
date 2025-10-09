import Mathlib

/-!
Module: NOC.Prob.Alignment
Status: scaffolding. Defines a minimal record encoding that a slow
increment aligns with an averaged drift `ḡ`, up to an MDS noise and a
summable bias. This is consumed by the projected SA meta-theorem.

This file is intentionally light on measure-theory bindings: the fields
are `Prop`s so concrete applications can instantiate them with mathlib
statements as they become available.

Notes (mathlib, for downstream instantiations):
- Filtration/process: `Filtration`, `Adapted` (Probability/Process/*).
- Conditional expectation MDS condition: `μ[ξ (n+1) | ℱ n] = 0` via
  `MeasureTheory.ConditionalExpectation` (Real-valued API in
  MeasureTheory/Function/ConditionalExpectation/Real.lean).
- Variance bounds and integrability are typically expressed with `MemLp`
  or `Integrable` from `MeasureTheory`.
-/

namespace NOC
namespace Prob
noncomputable section
open Classical

/-- D5: Alignment with an averaged drift `ḡ` for a slow 1‑D recursion.

Intended reading: there exists a filtration `𝓕` such that the increment
for the slow variable satisfies

  β_{n+1} = clamp(β_n + b_n (ḡ(β_n) + ξ_{n+1} + δ_{n+1})),

where `ξ` is an MDS with bounded conditional second moment and the
weighted bias is summable, typically `∑ b_n E |δ_{n+1}| < ∞`.

All fields are `Prop` placeholders to avoid committing to the exact
probability API in this scaffold. -/
structure AlignsWithGbar where
  filtration    : Prop            -- underlying filtration
  adapted       : Prop            -- β_n adapted, b_n predictable
  recursion     : Prop            -- β_{n+1} = clamp(β_n + b_n (ḡ(β_n)+ξ+δ))
  mds_zero_mean : Prop            -- E[ξ_{n+1} | 𝓕_n] = 0
  var_bound     : Prop            -- E[ξ_{n+1}^2 | 𝓕_n] ≤ σ^2
  bias_summable : Prop            -- ∑ b_n E |δ_{n+1}| < ∞ (or a.s.)

end
end Prob
end NOC
