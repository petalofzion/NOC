# NOC Developer Guide & Module Map

## Layout & Imports

- **Root Re-export:** `NOC.lean` (at repo root) re-exports `NOC.All`.
- **Aggregator:** `NOC/All.lean` imports the public-facing modules.

## Module Map

| Module Path | Description |
|---|---|
| `NOC/A/BasicNoHelp.lean` | **Lemma A** (capacity-compatible drift): product/ratio forms. |
| `NOC/A/Helpers.lean` | Helper lemmas for Lemma A algebra. |
| `NOC/B/Core.lean` | **Lemma B** core: supports→link, bridge, local form, δ-wrapper. |
| `NOC/B/Expectation.lean` | Expectation layer for Lemma B (finite ensemble). |
| `NOC/HB/Quadratic.lean` | **Heavy Ball**: HBParams, hbStep, f_at, delta2, and pure quadratic algebra. |
| `NOC/HB/CloseLoop.lean` | **Heavy Ball**: One-variable reduction + small-relative-step ⇒ Δ²f≤0. |
| `NOC/E/Information/Discrete.lean` | **Discrete Info Theory**: Shannon Entropy/MI for Fintype (Foundation for Lemma E). |
| `NOC/Dev/Checks.lean` | Quick `#check`s you can run in VSCode to verify types. |

## Implementation Notes

- All core HB/A/B/C′/C modules use `import Mathlib`.
- **Deep Formalization Goal:** This repo targets "Option C" — full formal proof from first principles. We minimize axioms.
- `HB/CloseLoop.lean` includes a conservative explicit bound (`hb_rhoStar`) with a complete proof that the polynomial bracket is nonpositive for `ρ ≤ ρ⋆(τ,γ)` when `0<τ<2`.

### Standard Stub Patterns

When marking incomplete proofs, use these comment conventions to guide agents and contributors:

- `sorry -- TODO: [Task Description]`: **Actionable**. This is a missing proof that should be filled in.
- `sorry -- EMPIRICAL`: **Deprecated/Transitional**. Only use this for *raw data inputs* (e.g., specific values from a dataset). If a premise represents a mathematical property (e.g., "MI satisfies DPI"), do not mark it empirical; **prove it**.
- `sorry -- BLOCKED`: **Blocked**. Waiting for an upstream dependency or refactor.

**Note on Refactoring:**
Lean module names are path‑based. If you move files, you must update imports.