# Lean File Analysis: NOC Project

## Project Overview

This project is a formalization of mathematical concepts in Lean, primarily focused on stochastic approximation, information theory, and control theory. The codebase is well-structured and uses advanced features of Lean, including typeclasses and a modular design. The overall goal appears to be the formal proof of a set of lemmas, designated as Lemma A, B, C, D, and E, which are related to the stability and performance of learning systems.

## Dependency Graph

```mermaid
graph TD
    subgraph Core [Core Lemmas]
        A[Lemma A (Drift)] --> A_Basic[NOC.A.BasicNoHelp]
        A_Basic --> A_Help[NOC.A.Helpers]
        
        B[Lemma B (Geometry)] --> B_Core[NOC.B.Core]
        B_Core --> B_Exp[NOC.B.Expectation]
        
        C[Lemma C/C' (Sigma Laws)] --> C_Prime[NOC.C.CPrime]
        C[Lemma C/C' (Sigma Laws)] --> C_Accel[NOC.C.C]
        
        Bridge[Sigma Bridge] --> S_Bridge[NOC.Bridge.SigmaBridge]
        S_Bridge --> A_Help
    end

    subgraph HB [Heavy Ball]
        HB_Quad[NOC.HB.Quadratic]
        HB_Loop[NOC.HB.CloseLoop]
        HB_Loop --> HB_Quad
        HB_Link[NOC.HB.Link] --> HB_Loop
        HB_Int[NOC.HB.Integration] --> HB_Loop & B_Exp
        HB_Adpt[NOC.HB.AdaptiveIntegration] --> HB_Loop & B_Exp
    end

    subgraph Prob [Probability & TTSA]
        MDS[NOC.Prob.MDS]
        RS[NOC.Prob.RobbinsSiegmund]
        TTSA[NOC.D.TTSA_Convergence] --> RS
        TTSA --> MDS
        TTSA --> Beta[NOC.D.BetaStabilityTTSA]
    end

    subgraph E [Lemma E & Interfaces]
        E_Core[NOC.E.Core]
        DI[NOC.E.Interfaces.DI]
        ROI[NOC.E.ConversionVsAblation]
        Info_Disc[NOC.E.Information.Discrete]
    end

    All[NOC.All] --> A_Basic
    All --> B_Core
    All --> C_Prime
    All --> S_Bridge
    All --> TTSA
    All --> HB_Loop
    All --> E_Core
```

## Module Map (Developer Guide)

| Module Path | Description |
|---|---|
| [`NOC/A/BasicNoHelp.lean`](NOC/A/BasicNoHelp.lean) | **Lemma A** (capacity-compatible drift): product/ratio forms. |
| [`NOC/A/Helpers.lean`](NOC/A/Helpers.lean) | Helper lemmas for Lemma A algebra. |
| [`NOC/B/Core.lean`](NOC/B/Core.lean) | **Lemma B** core: supports→link, bridge, local form, δ-wrapper. |
| [`NOC/B/Expectation.lean`](NOC/B/Expectation.lean) | Expectation layer for Lemma B (finite ensemble). |
| [`NOC/HB/Quadratic.lean`](NOC/HB/Quadratic.lean) | **Heavy Ball**: HBParams, hbStep, f_at, delta2, and pure quadratic algebra. |
| [`NOC/HB/CloseLoop.lean`](NOC/HB/CloseLoop.lean) | **Heavy Ball**: One-variable reduction + small-relative-step ⇒ Δ²f≤0. |
| [`NOC/HB/Link.lean`](NOC/HB/Link.lean) | **Heavy Ball**: API bundle for packaging links to be fed into C'. |
| [`NOC/HB/Integration.lean`](NOC/HB/Integration.lean) | **Heavy Ball**: Concrete integration test proving acceleration for $\lambda \in [6, 14]$. |
| [`NOC/HB/AdaptiveIntegration.lean`](NOC/HB/AdaptiveIntegration.lean) | **Heavy Ball**: General theorem proving acceleration for *any* valid curvature with adaptive steps. |
| [`NOC/E/Information/Discrete.lean`](NOC/E/Information/Discrete.lean) | **Discrete Info Theory**: Shannon Entropy/MI for Fintype (Foundation for Lemma E). |
| [`NOC/Dev/Checks.lean`](NOC/Dev/Checks.lean) | Quick `#check`s you can run in VSCode to verify types. |

## File Analysis

The following is a detailed list of all the Lean files in the source directory, along with a brief description of their purpose.

### Root Directory

*   [`All.lean`](NOC/All.lean): An aggregator file that imports all other modules in the library.
*   [`A.lean`](NOC/A/BasicNoHelp.lean): Defines "Lemma A (capacity-compatible drift)" in two forms: product and ratio.
*   [`AHelpers.lean`](NOC/A/Helpers.lean): Provides a set of small, reusable algebra and inequality lemmas that are used in the proof of Lemma A.
*   [`AwithHelpers.lean`](NOC/A/BasicHelp.lean): A version of `A.lean` that uses the lemmas defined in `AHelpers.lean` to simplify the proofs.
*   [`zzzketchpad uwu.lean`](Scratch/zzzketchpad_uwu.lean): A scratchpad file for temporary experiments.

### B Directory

*   [`B/Core.lean`](NOC/B/Core.lean): Defines "Lemma B", which appears to be a statement about the second-order difference of a function `U`.
*   [`B/Expectation.lean`](NOC/B/Expectation.lean): Lifts the pointwise bounds from `B/Core.lean` to statements about averages over finite sets.

### C Directory

*   [`C/C.lean`](NOC/C/C.lean): Defines the "Σ-law (acceleration)", which is a pointwise inequality `ΔΣ ≥ c₁·Δ²U − λΞ·Ξ_loss`.
*   [`C/CPrime.lean`](NOC/C/CPrime.lean): Defines the "Σ-law (improvement)", which is another pointwise inequality of the form `dSigma ≥ P.c1 * dU − P.lambdaXi * xiLoss`.
*   [`C/CPrimeToy.lean`](NOC/C/CPrimeToy.lean): Provides a "toy" 2x2 instance to demonstrate the application of the C' lemma.
*   [`C/CPrimeToyExamples.lean`](NOC/C/CPrimeToyExamples.lean): Contains examples for the C' toy.

### D Directory

*   [`D/Interfaces.lean`](NOC/D/Interfaces.lean): Provides a high-level interface for using the "D-bridge", which seems to be a mechanism for deriving the C' inequality from a pair of "link" conditions.
*   [`D/BetaStability.lean`](NOC/D/BetaStability.lean): Sets up the formalization plan for "Lemma D (β-stability)".
*   [`D/BetaStabilityTTSA.lean`](NOC/D/BetaStabilityTTSA.lean): Refines the scaffolding for Lemma D by introducing a Two-Time-Scale Stochastic Approximation (TTSA) framework.
*   [`D/TTSA_Convergence.lean`](NOC/D/TTSA_Convergence.lean): Contains the main convergence theorems for the TTSA framework.

### E Directory

*   [`E/Core.lean`](NOC/E/Core.lean): Provides the scaffolding for "Lemma E (synergistic empowerment)".
*   [`E/ConversionVsAblation.lean`](NOC/E/ConversionVsAblation.lean): Provides a formalization of the "Return on Investment" (ROI) inequality, which compares the utility of "conversion" versus "ablation".
*   [`E/Boundary/LoewnerHelpers.lean`](NOC/E/Boundary/LoewnerHelpers.lean): Provides a collection of helper lemmas related to the Loewner order on matrices.
*   [`E/Boundary/GaussianMAC.lean`](NOC/E/Boundary/GaussianMAC.lean): Provides a counterexample to the idea that ablating a partner in a communication system always reduces the mutual information for the remaining users.
*   [`E/Boundary/GaussianVector.lean`](NOC/E/Boundary/GaussianVector.lean): Extends the counterexample from `GaussianMAC.lean` to the vector case.
*   [`E/Interfaces/DI.lean`](NOC/E/Interfaces/DI.lean): Defines the core interfaces for Directed Information (DI) and the Strong Data-Processing Inequality (SDPI).
*   [`E/Interfaces/DI_Toy.lean`](NOC/E/Interfaces/DI_Toy.lean): Provides a simplified, "toy" interface for Directed Information and SDPI.
*   [`E/Interfaces/DI_Averaging.lean`](NOC/E/Interfaces/DI_Averaging.lean): Provides helper lemmas for lifting pointwise inequalities to averaged inequalities.
*   [`E/Interfaces/DI_Fiberwise.lean`](NOC/E/Interfaces/DI_Fiberwise.lean): Builds upon the averaging helpers in `DI_Averaging.lean` to provide a way to compose DI-DPI results from "fiberwise" (conditional) bounds.
*   [`E/Interfaces/DI_NOC_Instance.lean`](NOC/E/Interfaces/DI_NOC_Instance.lean): Provides a scaffolding for instantiating the DI-DPI framework for a specific "NOC" model.
*   [`E/Interfaces/DI_NOC_Wrapper.lean`](NOC/E/Interfaces/DI_NOC_Wrapper.lean): Provides a high-level wrapper for the DI-DPI framework, tailored for a "NOC" model.
*   [`E/Interfaces/Examples/DI_Fiberwise_NCC.lean`](NOC/E/Interfaces/Examples/DI_Fiberwise_NCC.lean): Provides a concrete example of how to use the fiberwise DI-DPI framework.
*   [`E/Interfaces/Examples/DI_Weighted_Bound.lean`](NOC/E/Interfaces/Examples/DI_Weighted_Bound.lean): Provides an example of how to use the `lemmaE_bound_weighted` theorem.
*   [`E/Interfaces/Examples/DI_NOC_BSC.lean`](NOC/E/Interfaces/Examples/DI_NOC_BSC.lean): Provides a concrete example of how to use the DI-DPI typeclass interface.
*   [`E/Information/Discrete.lean`](NOC/E/Information/Discrete.lean): Foundation for Discrete Information Theory (Entropy, MI for Fintype).

### Prob Directory

*   [`Prob/Alignment.lean`](NOC/Prob/Alignment.lean): Defines a structure `AlignsWithGbar` which is used to encode the alignment of a stochastic recursion with an averaged drift `ḡ`.
*   [`Prob/MDS.lean`](NOC/Prob/MDS.lean): Defines a framework for working with Martingale Difference Sequences (MDS).
*   [`Prob/RobbinsSiegmund.lean`](NOC/Prob/RobbinsSiegmund.lean): Contains a formalization of the Robbins-Siegmund theorem, a key result in the theory of stochastic approximation.

## Build Report

The project was built using the `lake build` command. The build completed successfully with warnings, but no errors. The warnings indicate that some proofs are incomplete (`sorry`).

## In-depth Analysis of Incomplete Files

This section provides a more detailed look at the files with incomplete proofs and their connection to the project's `TODO.md`.

### `NOC/D/BetaStabilityTTSA.lean`

*   **What is currently implemented:** This file sets up the formalization for "Lemma D (β-stability)" using a Two-Time-Scale Stochastic Approximation (TTSA) framework. It defines the necessary data structures (`TTSASchedules`, `TTSANoise`, `MetaReg`, `AccelWindow`, `BetaTTSAContext`) and includes several proven helper lemmas for deterministic and stochastic recursions, such as `beta_hits_target` and `clamped_hitting_time_under_window`.

*   **What is missing:** The main theorem, `lemmaD_beta_stability_TTSA_ode`, is stated but its proof is `sorry`.

*   **Connection to `TODO.md`:** The `TODO.md` file directly addresses this in the "Lemma D / β-meta stability (TTSA)" section, noting that the proof for `lemmaD_beta_stability_TTSA_ode` is pending. The "Blocked Items" section further explains that this is due to the lack of a full two-time-scale SA/ODE meta-theorem in the `mathlib` library.

*   **Completed TODOs:** The `TODO.md` sub-item "Property-layer stepping lemmas are proved: `TTSA.beta_drift_lower_bound_props`, `TTSA.beta_hits_target_props`, and `DriftHitThresholdPropsContext.hits_threshold_props` (clamp wrappers delegate). No `sorry`s in the arithmetic layer" is confirmed to be complete within this file.

### `NOC/D/TTSA_Convergence.lean`

*   **What is currently implemented:** This file contains the main convergence theorems for the TTSA framework. It includes a detailed proof of `d6_scalar_RS_summable` (a key step for the D6 interior-hit proof) and `ae_summable_of_summable_integral_nonneg` (a helper lemma). It also contains the statement for `pathwise_interior_hit`, a deterministic SA lemma, and placeholders for the full TTSA theorems (`TTSA_projected_unique_equilibrium` and `TTSA_projected_ergodic`).

*   **What is missing:** The proof of `pathwise_interior_hit` is incomplete, with comments indicating that the "Summation logic" and "Staying logic" are omitted. The proofs for `TTSA_projected_unique_equilibrium` and `TTSA_projected_ergodic` are also placeholders.

*   **Connection to `TODO.md`:** The `TODO.md`'s "Option 1: 1-D Projected SA Meta-Theorem" section directly relates to the incomplete `pathwise_interior_hit` proof, which is a crucial part of the `projected_SA_converges_1D` theorem. The "Option 2A" and "Option 2B" sections correspond to the placeholder theorems in this file.

*   **Completed TODOs:** Many items under "Probability layer to implement (new work)" are completed in the `Prob/` directory, including the `MDSData` definition, the development of weighted partial sums, and the proof of analytic control in `MDS.lean`, as well as the "RS summability helpers" in `RobbinsSiegmund.lean`. The `d6_scalar_RS_summable` sub-item under "D6 expectation-level RS step (integrability route)" is also complete.

## Final Review: Mathematical Accuracy and Consistency

This review provides a high-level assessment of the mathematical accuracy and consistency of the Lean formalization with respect to the `NOC_v5.md` document. This is not a formal audit or proof verification, but a conceptual check for any gross misrepresentations.

Overall, the Lean codebase appears to be a faithful and accurate representation of the mathematical claims and structures outlined in `NOC_v5.md`. The modular organization of the project into different lemmas (A, B, C, D, E) and the clear separation of concerns (e.g., core lemmas, interfaces, examples, probability theory) directly mirror the structure of the research blueprint.