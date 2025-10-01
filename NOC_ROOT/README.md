# NOC Proofs (Lean 4)

NOC is a Lean 4 library with results organized into three themes:

- `A`: Free‑energy drift (Lemma A).
- `B`: Core link/bridge/local forms and expectation wrappers (Lemma B).
- `HB`: Heavy‑ball quadratic algebra and the closed‑loop reduction used by B.

See `NOC/README.txt` for a quick map of modules and how to import them.

## Table of Contents

- [Build](#build)
- [Usage](#usage)
- [Module Map](NOC/README.txt)

## Build

Prerequisites:
- Lean toolchain: `leanprover/lean4:v4.23.0-rc2` (pinned by `lean-toolchain`).
- Lake package manager (bundled with Lean toolchain).

Steps:
- Fetch deps and build: `lake build`
- If building fresh: `lake update` (optional; resolves/pins deps), then `lake build`.
- Run basic smoke checks: open `NOC/Dev/Checks.lean` in VS Code (Lean extension) and hover `#check`s.

Notes:
- The repo pins mathlib and related packages via `lake-manifest.json` for reproducibility.
- Main entry point: `NOC.lean` (re‑exports `NOC.All`). Import `NOC.All` or specific modules like
  `import NOC.B.Core`.

## Usage

Lean file example:

```
import NOC.All

open NOC

-- Now you can use the lemmas, e.g.:
#check NOC.lemmaA_freeEnergy_nonneg_product
```
