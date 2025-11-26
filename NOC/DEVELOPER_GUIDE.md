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
| `NOC/Dev/Checks.lean` | Quick `#check`s you can run in VSCode to verify types. |

## Implementation Notes

- All core HB/A/B/C′/C modules use `import Mathlib`.
- Proof scaffolds for D/E may contain intentional `sorry`s (TTSA, DI–DPI, ROI, boundary) where empirical interfaces are used.
- `HB/CloseLoop.lean` includes a conservative explicit bound (`hb_rhoStar`) with a complete proof that the polynomial bracket is nonpositive for `ρ ≤ ρ⋆(τ,γ)` when `0<τ<2`.

**Note on Refactoring:**
Lean module names are path‑based. If you move files, you must update imports.
