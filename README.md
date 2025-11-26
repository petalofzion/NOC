# NOC: Naturalized Orthogonality Collapse (Lean 4)

NOC is a Lean 4 library formalizing the algebraic backbone of the "Naturalized Orthogonality Collapse" (NOC) research. It provides the proofs for Lemmas A, B, and C' (the Σ-laws), while scaffolding the interfaces for empirical components (Lemma E).

For a detailed mapping of how this code corresponds to the paper's claims, notation, and experiments, see **[PAPER_MAPPING.md](PAPER_MAPPING.md)**.

## Big Picture (One Minute)

- The paper defines **objects** (capacity $U$, acceleration $\Delta^2 U$, optionality $\Sigma$, deletion penalty $\Xi_{\mathrm{loss}}$) and **lemmas** (A, B, C′/C, D; E is empirical).
- The Lean library proves the **algebraic / conservative tier**: A, B (expected form), the Σ-bridge (`NOC/Bridge/SigmaBridge.lean`), and C′/C (Σ‑laws) — with *no* `sorry`.
- **What Lean intentionally does *not* define:** $\Sigma$ as MI, empowerment, or any estimator internals; those live in the **experiments**. The Lean side takes them as symbols/inputs and proves the inequalities they must satisfy *if* measured as in the paper.

## Concept → File Map

| Paper concept / claim | What the repo provides | Where |
|---|---|---|
| **Lemma A (β‑choice)** | Arithmetic lemmas capturing the β‑choice trick. | `NOC/A.lean` |
| **Lemma B (Expectation)** | Pointwise bridge + **expected** lifts. | `NOC/B/Expectation.lean` |
| **Lemma C′ (Σ‑law)** | Core boxed inequality $\Delta\Sigma \ge c_1\Delta U - \lambda_\Xi\Xi_{\mathrm{loss}}$. | `NOC/C/CPrime.lean` |
| **Bridge** | Upper link + SDPI-style inequality. | `NOC/Bridge/SigmaBridge.lean` |
| **Lemma E** | **Empirical**. Scaffolding predicates only. | `NOC/E/Core.lean` |

## Build & Usage

**Prerequisites:**
- Lean toolchain: `leanprover/lean4:v4.23.0-rc2` (pinned by `lean-toolchain`).
- Lake package manager.

**Steps:**
1. Fetch deps and build:
   ```bash
   lake build
   ```
2. (Optional) Update dependencies:
   ```bash
   lake update && lake build
   ```

**Usage:**
Import the library in your Lean files:
```lean
import NOC.All

open NOC

#check NOC.lemmaA_freeEnergy_nonneg_product
```

## Directory Structure

- `NOC/`: Main library source.
  - `A.lean`, `B/`, `C/`: Core lemmas.
  - `Bridge/`: Connecting logic.
  - `E/`: Interfaces for empirical assumptions.
- `experiments/`: Python/Agent scripts (unverified code).
- `PAPER_MAPPING.md`: Detailed scientific context.
