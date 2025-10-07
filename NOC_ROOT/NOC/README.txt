
NOC — Lean 4 library (A, B, HB) with tidy module layout

How to use (drop-in):
1) Ensure your project has a Lean 4 toolchain and Lake.
2) Place the `NOC/` folder and the root `NOC.lean` file in your project (same level as `lakefile.lean`).
3) Import `NOC.All` (aggregates everything) or specific modules (e.g. `import NOC.B.Core`).

Layout (modules are imported as shown by their paths):
  NOC.lean                  -- Root module that re-exports `NOC.All`
  NOC/All.lean              -- Aggregator: imports the public-facing modules
  NOC/A.lean                -- Lemma A (capacity-compatible drift): product/ratio forms
  NOC/B/Core.lean           -- Lemma B core: supports→link, bridge, local form, δ-wrapper
  NOC/B/Expectation.lean    -- Expectation layer for Lemma B (finite ensemble)
  NOC/HB/Quadratic.lean     -- HBParams, hbStep, f_at, delta2, and HB algebra (pure quadratic)
  NOC/HB/CloseLoop.lean     -- One-variable reduction + small-relative-step ⇒ Δ²f≤0 + affine capacity close
  NOC/Dev/Checks.lean       -- Quick `#check`s you can run in VSCode

Minimal usage example:

-- In some file in your project (e.g., Main.lean)
import NOC.All

open NOC

-- Now all lemmas are in namespace `NOC`.

Notes:
- All core HB/A/B/C′/C modules use `import Mathlib`. Proof scaffolds for D/E contain
  intentional `sorry`s (TTSA, DI–DPI, ROI, boundary). `HB/CloseLoop.lean` includes
  a conservative explicit bound (`hb_rhoStar`) with a complete proof that the polynomial
  bracket is nonpositive for `ρ ≤ ρ⋆(τ,γ)` when `0<τ<2`. This closes the Δ²f≤0 step under convex λ≥0.
- If you ever change file locations, remember Lean module names are path‑based. Update `import …`
  lines (or provide shims) to reflect any new paths.

Toolchain:
- This repo pins a recent mathlib via `lake-manifest.json` and uses Lean 4.23 RC toolchain.
  The code relies on standard algebra/tactics (`ring`, `nlinarith`, `abs_*`).
