# Novel Formalization Targets (NOVEL.md)

**Status:** Research Blueprint
**Objective:** Identify and outline the "PhD-level" formalization targets within the NOC repository. These are foundational mathematical results that are (1) missing from Lean 4's `mathlib`, (2) critical for the rigorous verification of NOC, and (3) represent **major, novel contributions** to the formalized mathematics community.

**Directive:** Do not avoid complexity. Target the most general, least assumption-heavy formulations (e.g., ODE method over Lyapunov).

---

## 0. Critical Validation: Verified Novelty Claims
*Rigorous verification (arXiv/mathlib search, Nov 2025) confirms the following are genuine, unformalized contributions.*

| Direction | Verified Novelty Status | Key Evidence & Critical Notes | Adjusted Breakthrough Hook |
|-----------|--------------------------|------------------------------|----------------------------|
| **1. Unified NOC Meta-Theorem: "Info-Accelerated Stability" (D + Bridge + C)** | **Confirmed novel (high confidence).** No Lean/Coq formalization of Borkar-Meyn/Kushner-Clark ODE method exists; extensions to info-penalties (e.g., Ξ_loss ≥ η ΔΣ) are absent even informally. Mathlib has martingales but no SA ODE wiring. A 2024 arXiv extends Borkar-Meyn to Markov noise informally, but no formal ODE interpolation/Ascoli-Arzelà for TTSA. | Coq's Dvoretzky SA (2022) is related but scalar/1D, not multi-scale or info-constrained. Gap: Your repo's TTSA sorry (TTSA_Convergence.lean) aligns perfectly—no priors for Σ-bridge in drifts. 2025 meta-learning papers ignore info costs. | Unchanged: Proving ODE stability under SDPI-perturbed h(β) = c1 ΔU - λΞ would be first "causal meta-RL convergence" theorem—major for verifiable alignment under empowerment drops. |
| **2. General Discrete SDPI Meta-Theorem for NCC Channels (E + ConditionalDIDPI)** | **Confirmed novel (very high confidence).** Zero formalizations in Lean/Agda/Coq; mathlib has entropy/MI basics but no contraction coeffs or chain-rule SDPI. A 2025 math arXiv discusses SDPI constants informally, and your repo's toys (e.g., BSC) are the closest. | Irrelevant hits (e.g., medical SDPI) dominate; no proof-assistant work. Gap: Massey chain + fiberwise η-bounds unformalized, matching your TODO checklist. Evans-Schulman bounds (for η) are paper-only. | Slightly strengthened: Meta-thm with Dobrushin δ(K)<1 → η ≤ (1-δ)^2 would be first formal spectral-link for causal SDPI—breakthrough for PID/causal ML, enabling auto-verified NCC regimes. |
| **3. Symplectic Heavy Ball Meta-Analysis for Σ-Acceleration (C + HB + Bridge)** | **Confirmed novel (high confidence).** Informal symplectic papers (2019–2025) exist, but no Lean/Coq formalizations of phase-space LMI or Δ²U bridges. Mathlib has optimization basics, not momentum geometry. | 2023 practical symplectic opt paper is algorithmic, not verified. Gap: Your HB/CloseLoop.lean algebra is advanced; no priors for SDP solver in Lean for parameterized systems. | Unchanged: Formal LMI for HB + SDPI-derived cU/κU would yield first "verified momentum-info bridge"—novel for formal opt, quantifying ablation in accelerated gradients. |
| **4. PID Synergy Meta-Decomposition for Lemma E (E + DI_Fiberwise)** | **Confirmed novel (very high confidence).** No formal PID (Williams-Beer lattice, synergy measures) in any assistant; 2025 arXiv uses PID informally for dataset bias. Coq/Lean hits are unrelated (e.g., PID rings). | Gap: Your ESynergyWitness is the only scaffold; no causal extensions (DI/Syn >0 → η<1). Broader PID formalization (lattice ops) absent, per ITP/DROPS. | Unchanged: Proving synergy → strict DI drop via fiberwise PID would be first formal causal PID—major for multi-agent RL verification, linking to DO-calculus sans axioms. |
| **5. Martingale-Driven "Good-Set" Meta-Convergence (B + Prob + D)** | **Partially novel (medium-high confidence).** Mathlib formalizes Doob/RS martingale convergence (2022–2023), and Coq has SA via martingales. But no "good-set" (mass-δ invariant G) ergodic lifts for Σ-laws or stochastic control. | 2025 arXiv on SA convergence via martingales/Lyapunov is informal. Gap: Your TODO D6/D4 wiring + finitary splits (CPrime.lean) extend to uncharted ergodic avg for infinite horizons. | Adjusted: Ergodic MDS thm for E_μ[ΔΣ] ≥ c1 E_μ[ΔU] on G would be first "stationary NOC law" under RS—novel synthesis for ergodic control, beyond basic Doob. |

---

## 1. The "Borkar-Meyn" ODE Approximation (Three-Tier Strategy)
**Domain:** Stochastic Approximation / Dynamical Systems
**Significance:** High. Resolves the tension between "Noise Bias" and "Interpolation Regime."

### The Philosophical Choice: TTSA vs. Lyapunov
We explicitly adopt **TTSA/ODE** over strict Lyapunov analysis.
*   **Lyapunov (Su et al. 2014):** Provides physical intuition ("Energy always decreases") but fails in the **"Edge of Stability"** regime (Cohen et al. 2021) where loss is non-monotonic.
*   **TTSA (Borkar 1997; Konda & Tsitsiklis 2000):** Proves that the *average* trajectory is stable even if individual steps are chaotic. This is robust to the noise inherent in Deep Learning.

### Path A: The "Safe" Pivot ($\epsilon$-Stability)
Prove that the discrete sequence tracks the ODE *approximately*, bounded by the noise variance.
*   **Formalism:** Prove convergence to the **Internally Chain Transitive (ICT) Set** of the Differential Inclusion $\dot{\beta} \in \pi(h(\beta)) + \mathcal{B}(\epsilon)$.
*   **Machinery:** Formalize the **Borkar-Meyn Theorem** (Interpolation, Equicontinuity via Ascoli-Arzelà) for bounded martingale noise.
*   **Outcome:** Rigorous proof that $\beta_n$ stays near $\beta^\star$.

### Path B: The "Profound" Corollary (Conditional Exactness)
Prove that if the system is in the **Interpolation Regime** (Loss $\to$ 0), it converges *exactly*.
*   **Formalism:** Introduce `class InterpolationRegime` asserting $\mathbb{E}[\|\xi\|^2] \le C \|\nabla L(\theta)\|^2$.
*   **Proof:** Show that under this assumption, the bias $\mathcal{B}(\epsilon) \to 0$ as $\theta \to \theta^\star$, collapsing the ICT set to {$\beta^\star$}.
*   **Novelty:** Formalizes the "Vanishing Noise" phenomenon in modern Deep Learning verification.

### Path C: The "Deepest" Formalization (Neural Tangent Kernel)
Prove that the **Interpolation Regime** actually exists for Neural Networks.
*   **Formalism:** Formalize the **Neural Tangent Kernel (NTK)** limit ($width \to \infty$).
*   **Proof:** Prove **Global Convergence of Gradient Descent** for overparameterized networks (Linearized Dynamics).
*   **Link:** Show Global Convergence $\implies$ Loss $\to$ 0 $\implies$ Noise $\to$ 0. This closes the loop, proving Path B's assumption from first principles.

---

## 2. Discrete Strong Data Processing Inequality (SDPI)
**Domain:** Information Geometry / Spectral Graph Theory
**Significance:** High. First formal spectral-link for causal SDPI.

### The Problem
Instantiate `DirectedInfo` and `SDPI` for concrete channels (BSC, Z-Channel).

### The Missing Machinery
1.  **Discrete Information Theory:** Define `Entropy` and `MutualInformation` for `Fintype` (independent of heavy measure-theory if possible). Prove **Massey Chain Rule** explicitly: $I(A^n \to B^n) = \sum I(A^i; B_i | B^{i-1})$.
2.  **Contraction Coefficient:** Prove **Dobrushin Coefficient** bound or **Evans-Schulman** bound for specific $W$.
    *   *Specific Target:* Prove $\eta_{\text{BSC}(\epsilon)} = (1-2\epsilon)^2$. This involves analyzing the convexity of the KL divergence on the probability simplex.

---

## 3. Heavy Ball "Upper Link" Geometry
**Domain:** Optimization Theory / Symplectic Geometry
**Significance:** Medium-High. First "verified momentum-info bridge."

### The Problem
Prove $\Delta^2 U \le c_U \Delta(\text{Energy}) - \kappa_U \Delta(\text{Loss})$ for HB on Quadratics.

### The Missing Machinery
1.  **Lyapunov Construction:** Quadratic $V(z)$ on augmented state $z_k = (x_k, x_{k-1})$.
2.  **LMI Solver:** Automate the check that $V(z_{k+1}) - V(z_k) \le -\rho \|\nabla f \|^2$ holds for all parameters (Automated LMI Tactic). Requires solving the 2x2 block LMI symbolically in Lean.

---

## 4. Two-Time-Scale Stochastic Approximation (TTSA)
**Domain:** Stochastic Approximation (Multi-Agent)
**Significance:** High. Extends Target #1 to coupled Fast/Slow systems.

### The Problem
Coupled update $\theta_{n+1} = \dots$, $\phi_{n+1} = \dots$ with $\gamma_n / \beta_n \to 0$.

### The Missing Machinery
*   **Quasi-Static Approximation:** Prove fast process tracks equilibrium $\lambda(\theta)$ instantly.
*   **Coupling Error:** Formalizing the bounds to prove that the difference between the coupled system and the averaged system vanishes a.s.

---

## 5. The "Synergy" Inequality (Lemma E & E')
**Domain:** Information Decomposition (PID) / Geometric Control Theory
**Significance:** Medium. First formal causal PID and Geometric Control link to Empowerment.

### The Problem
Prove $I(X; Y, Z) - I(X; Y) = \text{Unique}(Z) + \text{Synergy}$. Connect this to Manifold Collapse.

### The Missing Machinery
1.  **PID Definitions:** Formalize Partial Information Decomposition (lattice of information measures). 
    *   *Context:* There are multiple competing definitions (e.g., **Bertschinger et al. (BROJA)** using convex optimization, **Williams-Beer** using lattice structure, **Griffith**).
    *   *Breakthrough:* Formalizing *any* of these is novel. The "Lattice of Information" (Williams-Beer) is the most algebraic and likely the easiest to formalize first.
2.  **The PID-to-Contraction Link (Lemma E):** The "missing bridge" between PID and SDPI.
    *   *The Gap:* Current Lemma E *assumes* ablation is a garbling ($\eta < 1$). We need to derive this from the physics.
    *   *The Theorem (Geometric Control):* **"Rank-Deficient Control Authority."** Prove that if the interaction is "Non-Holonomic" (requires Lie Brackets $[f_1, f_2]$ to move), then ablating $f_2$ reduces the Rank of the Reachability Gramian.
    *   *Physics:* "Synthetic Lethality" (Genetics) and "Percolation Threshold" (Physics). If the system is at a critical point (Synergistic Core), ablation collapses the manifold dimensionality.
3.  **Lemma E' (The General Metric):** "Interaction Sign Determines Empowerment Change."
    *   *Formalism:* Define **O-Information ($\Omega$)** or Spectral Gap.
    *   *Theorem:* If $\Omega < 0$ (Synergy), Empowerment Collapses (Original Lemma E). If $\Omega > 0$ (Interference), Empowerment Increases.
    *   *Significance:* This generalized lemma explains the *switch* in behavior. NOC drives the agent from E' (Redundant) to E (Synergistic).

---

## 6. Martingale Difference Sequence (MDS) Strong Laws
**Domain:** Probability Theory
**Significance:** High. SLLN for Martingales is missing from mathlib.

### The Gem
`NOC/Prob/MDS.lean` already proves `weighted_sum_ae_converges`.

### The Opportunity
*   **Generalized SLLN:** Prove $\frac{1}{n} \sum M_i \to 0$ a.s. for general MDS with bounded variance.
*   **Borel-Cantelli for Martingales:** Generalize existing convergence theorems to "Conditional Borel-Cantelli" lemmas (Lévy's extension).

---

## 7. Inverse Antitonicity & Operator Monotonicity
**Domain:** Functional Analysis / Matrix Analysis
**Significance:** Medium-High.

### The Gem
`NOC/E/Boundary/LoewnerHelpers.lean` proves $\log \det$ monotonicity.

### The Opportunity
*   **Löwner-Heinz Theorem:** Formalize Operator Monotone functions and their connection to analytic functions (Pick functions). This connects Matrix Analysis to Complex Analysis.

---

## 8. Generalized Robbins-Siegmund Theorem
**Domain:** Functional Analysis / Stochastic Processes
**Significance:** High.

### The Gem
`NOC/Prob/RobbinsSiegmund.lean` implements the 1D version.

### The Opportunity
*   **Hilbert Space Extension:** Generalize 1D RS theorem to Hilbert/Banach spaces.
*   **Applications:** Use this to prove convergence of SGD on Reproducing Kernel Hilbert Spaces (RKHS) (hot topic in theoretical ML).

---

## 9. Automated LMI Verification Tactic
**Domain:** Control Theory / Meta-Programming
**Significance:** Medium.

### The Gem
`NOC/HB/Quadratic.lean`.

### The Opportunity
*   **`tactic.lmi`:** Write a Lean 4 tactic that takes a dynamical system update and a Lyapunov candidate, extracts the matrices, checks the Linear Matrix Inequality (LMI) conditions (using sum-of-squares or determinant checks), and automatically generates the stability proof.

---

## 10. Neural Tangent Kernel (NTK) & The "Grokking" Transition
**Domain:** Deep Learning Theory / Statistical Physics
**Significance:** High. Resolves the tension between "Lazy Learning" (Redundancy) and "Rich Learning" (Synergy).

### The Problem
Standard NTK theory proves that infinitely wide networks stay in the "Lazy Regime" (linear dynamics, high redundancy, no feature learning). This contradicts the "Synergy" claim of Lemma E.
However, empirical Deep Learning shows a **Phase Transition** ("Grokking") where networks leave the Lazy regime and learn structured features.

### The "Kinetic" Mechanism (Formalization Roadmap)
*   **Hypothesis:** NOC acts as an **"Edge of Stability" (EoS)** controller. Maximizing $\Delta^2 U$ (acceleration) pushes the system to the limit of stable curvature.
*   **The Catapult Phase:** Prove that large steps/momentum (NOC dynamics) destabilize the sharp minima of the Lazy/NTK regime, forcing the system to "catapult" into a flatter basin.
*   **The Rich Regime:** Prove that this new basin corresponds to the "Rich" regime (feature learning), where weights deviate from initialization and redundancy is shed.
*   **Outcome:** NOC *activates* Lemma E by forcing the transition from **Lazy (Interference)** to **Rich (Synergy)**.

---

## 11. Geometric Control Theory of Synergy (Lemma E Proof)
**Domain:** Differential Geometry / Non-Linear Control
**Significance:** High. Provides the rigorous mechanism for "Synergy = Fragility."

### The Problem
Why does high synergy imply that removing a partner causes a catastrophic drop in control?

### The Missing Machinery
1.  **Formalize Lie Brackets:** Define the Lie Bracket $[f, g]$ for vector fields on a manifold.
2.  **The "Rank Deficient" Theorem:**
    *   Define a system as "Synergistic" (Non-Holonomic) if the rank of the control distribution $\Delta = \text{span}\{f_1, \dots, f_k\}$ is less than the rank of the Lie Algebra $\text{Lie}(\Delta)$.
    *   Prove that ablating a vector field $f_i$ reduces the rank of the reachable set (Manifold Collapse).
    *   *Link:* If the system needs Lie Brackets to move (Parallel Parking), losing one actuator kills the emergent dimension.
3.  **Connection to O-Information:** Link the geometric "Rank Deficiency" to the statistical "Negative O-Information."

---

## 12. Neural Collapse (ETF Simplex) Geometry
**Domain:** High-Dimensional Geometry / Optimization
**Significance:** Medium-High. The geometric endpoint of NOC.

### The Problem
What is the specific geometry that NOC converges to?

### The Missing Machinery
1.  **Equiangular Tight Frame (ETF):** Define the ETF Simplex in Lean.
2.  **The "Simplex" Theorem:** Prove that minimizing the "Cross-Entropy + Weight Decay" (NOC proxy) objective forces feature vectors to converge to an ETF Simplex.
3.  **The "Fragility" Corollary:** Prove that an ETF Simplex has **Zero Redundancy**. Removing any vertex destroys the frame properties.
    *   *Conclusion:* Optimizing for the Simplex (NOC) *mathematically necessitates* Lemma E (Fragility).