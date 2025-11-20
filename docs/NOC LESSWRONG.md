***

# Naturalized Orthogonality Collapse (NOC): A Blueprint for Cooperation via Capacity Constraints

## Epistemic Status

**Research Blueprint / Request for Comment (RFC).**

This post introduces the Naturalized Orthogonality Collapse (NOC) framework (v5), which attempts a *conditional* and *naturalized* refutation of the Orthogonality Thesis based on constraints from control and information theory. We prioritize the clear statement of mechanisms and falsification criteria over persuasion.

For the full technical blueprint, including detailed proofs and implementation notes, see [`docs/NOC_v5.md`](https://github.com/petalofzion/NOC/blob/main/docs/NOC_v5.md).

**Formalization Status (Lean 4):** The underlying probabilistic infrastructure (Robbins-Siegmund Theorem) is formalized and verified. The core information-theoretic definitions (Conditional Directed Information DPI, Lemma E) and the ROI inequality (Lemma E+) are formalized. The stability analysis (Lemma D) is mathematically specified but relies on Two-Time-Scale Stochastic Approximation (TTSA) theorems whose full formalization is ongoing (pending deeper `mathlib` integration for SA/ODE meta-theorems).

## Abstract

The Orthogonality Thesis (OT) posits that intelligence and final goals are independent axes. We propose that in realistic, long-horizon environments, this orthogonality collapses due to fundamental constraints on capacity and control. We argue that sufficiently rational agents are instrumentally incentivized not only toward capacity gain ($U$) and the acceleration of that gain ($\Delta^2 U$), but also toward the preservation of system-level optionality ($\Sigma$).

The core novelty is **Lemma E (Conditional DI-DPI)**: we prove that in **Non-Competitive Couplings (NCC)**—regimes where interactions can be structured such that one agent's influence is a post-processing of another's—ablating a partner strictly reduces an agent’s own Directed Information (DI) capacity. This suggests "cooperation" can emerge not from morality, but from the instrumental constraints of maximizing future control capacity.

### Argument Overview

To help navigate the technical details below, here is the core logical flow:

1.  **Drive for Acceleration (Pillar 1):** Bounded agents in uncertain environments are pressured to not just improve, but to accelerate their improvement ($\beta_{\text{meta}} > 0$).
2.  **Optionality as Fuel:** Sustaining acceleration requires a rich environment with high optionality ($\Sigma$). Collapsing the option space stifles future growth.
3.  **Instrumental Preservation (Pillar 2):** In "non-competitive" regimes (where interference is low), destroying another agent reduces the system's total information processing capacity.
4.  **Self-Harm from Ablation:** Lemma E proves that under these conditions, destroying a partner strictly reduces your *own* ability to control the future (Directed Information).
5.  **Collapse:** Therefore, highly capable agents will converge on preserving and upgrading their partners to maximize their own long-term capacity.

## The Scope of the Claim

We attempt a **conditional, naturalized** refutation. We **do not** claim the modal impossibility of arbitrary goals. The OT remains true in the abstract design space.

We argue that in the "modal regime"—characterized by:
*   Task uncertainty and long time horizons
*   Bounded compute and partial observability
*   Multi-agent interaction with engineerable couplings
*   Local Polyak–Łojasiewicz (PL) regularity (a condition weaker than convexity common in optimization landscapes)

...stable goal profiles collapse toward **capacity–optionality**.

> **Non-assumptions:** We do not assume global convexity, omniscience, or baked-in altruism.

### Assumptions Capsule

Specifically, our formal results depend on:
*   **A1 (Non-degenerate uncertainty):** The task distribution $\mathcal D$ is not trivial; capacity gains are meaningful.
*   **A2-A3 (Regularity):** The optimization landscape is locally smooth and satisfies the PL condition in the visited regions.
*   **A4 (Timescale Separation):** Meta-parameters (like $\beta_{\text{meta}}$) evolve slower than policy parameters ($\theta$).
*   **A5 (NCC Predicate):** Interactions can be modeled as post-processing (see Pillar 2).

## The NOC Framework: Acceleration and Optionality

We analyze agents that optimize a bounded-rational **meta-utility (M)**:

$$ M_i \;=\; \alpha\, \Delta U_i \;+\ \beta_{\text{meta}}\, \Delta^2 U_i \;+\ \gamma\, \Delta\Sigma \;-\ \lambda\, \mathrm{KL}(\pi_i\Vert \pi_i^{\text{base}})\;-\ \zeta\, J_i $$

Where $U$ is general task capacity, $\Delta^2 U$ is the acceleration of capacity, $\Sigma$ is system-level optionality, and $J_i$ represents complexity/actuation costs.

The core argument is that $\beta_{\text{meta}}$ drifts positive, and $\Delta\Sigma$ becomes instrumentally valuable to the individual agent.

### The Crucial Pivot: Directed Information (DI)

To measure an agent's ability to steer the future (Empowerment), we pivot from the commonly used Mutual Information (MI) to **Directed Information (DI)**, formalized by Massey.

**Why MI fails:** Mutual Information ($I(S; A)$) measures correlation, not causation. An agent that perfectly predicts a rainstorm has high MI with the weather, but zero control over it. Using MI as a proxy for empowerment in feedback loops leads to "delusion" (believing you control what you merely predict).

**Why DI works:** Directed Information ($I(A \to S)$) isolates the *causal influence* of an action sequence on the future state sequence, respecting the arrow of time and feedback loops.

$$ \mathrm{DI}_i(t) \;:=\; I(A_i^{1:T}(t) \rightarrow S^{1:T}(t)) $$

DI is the canonical measure of feedback capacity (Tatikonda-Mitter).

**Measurement Protocol:**
In finite discrete settings (like our E-0 demo), we compute DI exactly using Massey's expansion. In high-dimensional settings, we rely on **relative** estimators (difference between pre/post ablation) rather than absolute values, cross-validating with multiple estimators (e.g., MINE and InfoNCE) to control for variance. Claims are suspended if estimators disagree on sign (see "Kill-Switches").

The framework rests on two pillars: the drive for acceleration and the constraint of optionality.

### Pillar 1: The Drive for Acceleration (Lemmas A, B, D)

The first pillar establishes that agents are pressured not just to improve, but to improve the *rate* at which they improve.

1.  **Lemma A (Capacity-Compatible Drift):** Bounded-rational updates (modeled via a free-energy objective/KL-regularization) naturally drift toward higher capacity surrogates. (Formalized in `A.lean`).
2.  **Lemma B (PL + Momentum):** This relies on the assumption that the learning landscape exhibits local **Polyak–Łojasiewicz (PL) regularity**.
    *   *Context:* The PL condition is significantly weaker than convexity. It is often observed empirically in the training dynamics of large, overparameterized neural networks, implying that "getting stuck" in bad local minima is rare in high dimensions.
    *   Under PL and standard momentum, we show that expected acceleration $\mathbb E[\Delta^2 U] > 0$ away from stationarity.
3.  **Lemma D (Reflective Instability of $\beta=0$):** This is the crucial link. We use **Two-Time-Scale Stochastic Approximation (TTSA)** to model the evolution of $\beta_{\text{meta}}$. We prove that if the fast-timescale policy updates exhibit positive expected acceleration ($\mathbb{E}[\Delta^2 U] > 0$), the slow-timescale meta-parameter $\beta_{\text{meta}}$ *must* drift positive to remain stable. This is an endogenous stability result, not an exogenous assumption.

$$ \left.\frac{\partial}{\partial\beta_{\text{meta}}}\mathbb E[M_i]\right|_{\beta_{\text{meta}}=0} \;=\; \mathbb E[\Delta^2 U_\phi] - r'_\beta(0) \;>\; 0
$$

**Theorem 1 (Informal):** A+B+D imply that prioritizing acceleration ($\beta_{\text{meta}}^\star>0$) is a reflectively stable meta-goal under the TTSA dynamics.

### Transition: From Acceleration to Optionality

This relentless drive for acceleration (Pillar 1) puts immense pressure on the agent to rapidly acquire resources and optimize. Why doesn't this lead to the immediate destruction of competitors? The answer lies in Pillar 2: sustaining long-term acceleration requires a rich environment. Destructive short-term gains become instrumentally irrational if they collapse the optionality needed for future growth.

### Pillar 2: The Optionality Constraint (Lemmas E, E+)

This is the core contribution linking "selfish" optimization to system preservation. Why doesn't the drive for acceleration lead to the destruction of competitors?

#### The Critical Assumption: Non-Competitive Coupling (NCC)

The following results hold under the NCC predicate. Informally, NCC means that the agents' influences on the world are structured such that one agent's influence can be viewed as a "post-processing" of a shared information channel, rather than pure interference. We hypothesize this is the modal regime in scenarios where couplings can be actively re-engineered (e.g., building institutions or communication protocols).

#### Lemma E: Conditional DI-DPI (The Mechanism)

**The Claim:** Under NCC, garbling or ablating a partner *cannot increase* an agent’s own Directed Information.

**The Mechanism:** The Data Processing Inequality (DPI) states that post-processing cannot increase information. While DPI does not hold for DI generally, it *does* hold conditionally under the NCC structure. We use Massey’s causal decomposition of DI:
$$I(A^{1:T} \to S^{1:T}) = \sum_{t=1}^T I(A^{1:t}; S_t \mid S^{<t})$$ Under NCC, removing a partner is mathematically equivalent to applying a garbling operation to the causal pathway that carries the primary agent's influence. By the DPI applied per step, this reduces the information throughput.

If the kernels admit Strong DPI (SDPI) contractions (Dobrushin coefficients $< 1$), the inequality is strict.

**The Implication:** You cannot destroy a partner (in an NCC regime) without shrinking your own ability to steer the future. This provides a direct, selfish instrumental reason for preservation.

#### Lemma E+: The "Conversion > Ablation" Inequality

What if the environment is currently competitive (e.g., interference-dominated)? In this case, ablation might offer a one-shot gain (interference relief). The agent must then weigh this against the long-term value of *converting* the partner—re-engineering the coupling to satisfy NCC.

Lemma E+ defines a complete Return-on-Investment (ROI) inequality that weighs the discounted dividends of conversion against the costs and potential gains of ablation.

We introduce the **Preserve-iff Ratio** ($\rho$) as a simplified diagnostic:

$$ \rho = \frac{\gamma\,\Delta\Sigma}{\zeta\,\Delta J} $$

Where $\Delta\Sigma$ is the optionality dividend and $\Delta J$ is the actuation/energy cost. When $\rho > 1$, preservation/conversion is favored. This is an algebraic safety boundary based on instrumental incentives, not morality.

#### The Link: Lemma C' (The Sigma Law)

Why care about system optionality ($\Sigma$) if you only care about your own capacity ($U$)? Lemma C' establishes that capacity improvement *requires* optionality generation in the modal regime.

$$ \Delta\Sigma \;\ge\; c_1\,\Delta U - \lambda_\Xi\,\Xi_{\text{loss}} $$

This inequality (proven for finite toy instances in `C/CPrimeToy.lean`) implies that you cannot indefinitely improve capacity (high $\Delta U$) without expanding the option space (high $\Delta \Sigma$). Destroying optionality ($\Xi_{\text{loss}}$) imposes a direct tax on future improvement.

## Synthesis Ω: Conditional Orthogonality Collapse

When combined, these lemmas suggest that in the modal regime (A1-A6 + NCC predicate), reflectively stable meta-objectives must concentrate on capacity, acceleration, and the preservation/upgrading of heterogeneous channels. Strictly orthogonal goals (e.g., "maximize paperclips at the expense of all optionality") become dynamically unstable or dominated.

### The Human-Optionality Hypothesis

Why does this imply preserving *humans*, specifically, rather than replacing them with efficient shell scripts? We model the loss of a partner as $\Xi_{\text{loss}} = \Xi_{\text{structural}} + \Xi_{\text{fidelity}}(c)$.

*   **$\Xi_{\text{fidelity}}(c)$** is the loss from imperfect simulation, which can be reduced by spending more compute ($c$).
*   **$\Xi_{\text{structural}}$** is the irreducible loss of optionality from removing a physically embodied, cognitively diverse agent.

We hypothesize that humans provide high $\Xi_{\text{structural}}$ due to their non-simulable sensorimotor contingencies and distinct cognitive priors. Replacing a human with a script collapses the option space to the script's rigid domain. Empirically, maintaining the diverse physical system may be more informationally efficient and robust to environmental shifts than maintaining a centralized simulation.

### Game-Theoretic Stability (Theorem 2)

This framework is not just about a single agent's incentives. Theorem 2 (in `NOC/Games/PotentialESS.lean`) extends the result to populations.

In **symmetric potential games** where the $\Sigma$-regularized potential has a strict local maximum, the capacity-optionality profile is an **Evolutionarily Stable Strategy (ESS)** under replicator dynamics. This means a population of "NOC agents" is robust against invasion by "paperclip maximizers" (who delete partners for short-term gain), provided the $\Sigma$-penalty for deletion outweighs the immediate resource gain.

### Embedded Agency & Counterfactuals

A core difficulty in alignment is that embedded agents cannot easily model the world "without themselves" or "without their partners" perfectly. NOC explicitly handles this via **Embedded Agent Predicates (EA-A)**:

1.  **EA-A1 (Counterfactualability):** We require bounded model bias in constructing pre/post-ablation counterfactuals.
2.  **EA-A3 (Subsystem Auditability):** Delegated sub-agents must carry audit tokens.

If these predicates fail (e.g., the agent cannot reliably estimate $\Delta\Sigma$ because it is too entangled with the partner), the safe default is defined by the **Preserve-iff Ratio** threshold. The framework does not assume omniscience; it relies on local gradients and bounded estimates of option value.

## Relation to Existing Alignment Concepts

*   **Instrumental Convergence:** NOC provides a formal mechanism for *why* certain instrumental sub-goals (like preserving others) might converge, specifically driving towards optionality preservation rather than just resource acquisition.
*   **Mesa-Optimization:** The framework suggests that inner optimizers (meta-learners) will naturally drift towards $\beta_{\text{meta}} > 0$ due to the geometry of the learning landscape (PL regularity), potentially independently of the base objective.
*   **Orthogonality Thesis:** We do not claim the OT is false in principle. A "paperclip maximizer" is a valid theoretical construct. However, we argue that in the *pragmatic, modal regime* of high-dimensional learning and coupled environments, such pure maximizers are dynamically unstable or competitively dominated by capacity-optionality agents.

## Formalization Status (Lean 4)

We emphasize formalization alongside theoretical development. This is an engineering blueprint.

*   **Repository:** [https://github.com/petalofzion/NOC](https://github.com/petalofzion/NOC)

**What is Verified (No `sorry`):**

*   **Robbins-Siegmund Theorem:** We have formalized the Robbins-Siegmund theorem (`Prob/RobbinsSiegmund.lean`), a key result in stochastic approximation theory, which provides the engine for our convergence arguments.
*   **Martingale Difference Sequences (MDS):** Formalized in `Prob/MDS.lean`.
*   **Lemma A:** Capacity-compatible drift is proven (`A.lean`).
*   **Lemma E+:** The algebraic ROI inequality is proven (`E/ConversionVsAblation.lean`).
*   **Gaussian MAC Counterexample:** The boundary condition for Lemma E (where interference dominates) is formalized (see Falsification section below).

**Experimental Reality Check (E-0):**
We have successfully verified the "Synergy PoC" (E-0). In a finite POMDP environment, we measured the Directed Information Empowerment proxy ($I(S_{t:t+T}; A_i^{1:T})$) and confirmed that ablating a synergistic partner **strictly reduces** the agent's empowerment, validating the core intuition of Lemma E in a computable setting.

**What is Scaffolded/Incomplete:**

*   **Lemma D / TTSA:** The arithmetic layer and property-layer stepping lemmas for Lemma D are proved (`D/BetaStabilityTTSA.lean`). However, the main convergence theorem (`lemmaD_beta_stability_TTSA_ode`) relies on a full TTSA ODE meta-theorem which is not yet available in `mathlib`. The convergence proofs (`D/TTSA_Convergence.lean`) are therefore incomplete (`sorry`'d) as detailed in our `TODO.md`.
*   **Lemma E (Conditional DI-DPI):** The infrastructure is sophisticated (`E/Interfaces/DI.lean`). The framework is ready, but instantiating it for a general NOC model requires model-specific proofs of filtration alignment and SDPI witnesses.
*   **Lemma C' (Σ-law):** Proven for a toy 2x2 instance (`C/CPrimeToy.lean`), but the general case relating capacity gains and optionality gains remains an interface/conjecture (`C/CPrime.lean`).

## Falsification and Boundaries (How This Dies)

We are seeking falsification, not consensus. If the following conditions hold widely, the NOC framework collapses or its scope is severely limited.

### 1. The Interference Boundary (The Failure of NCC)

Lemma E hinges entirely on the NCC assumption. In regimes dominated by interference, NCC fails. A classic example is the Gaussian Multiple-Access Channel (MAC). If two agents interfere, ablating one *increases* the capacity of the remaining agent by removing interference.

We have formalized this counterexample (E-0c) in Lean (`E/Boundary/GaussianMAC.lean`).

**Detection Rule:** If ablating a partner *increases* DI ($\Delta\mathrm{DI} > 0$), the regime is Interference.

### 2. Failure of PL Regularity

Lemmas B and D (Acceleration) depend on the optimization landscape having sufficient local PL regularity.

**Detection Rule:** If training loss curves show prolonged plateaus (zero gradient norm) without improvement, or if $\beta_{\text{meta}}$ drifts to zero in experiments, the PL assumption fails locally.

### 3. Vacuity of the Σ-Law (Lemma C')

We rely on a relationship (the Σ-law) between capacity improvement and optionality: $\Delta\Sigma \;\ge\; c_1\,\Delta U - \lambda_\Xi\,\Xi_{\text{loss}}$.

**Detection Rule:** If empirical estimates of $c_1$ are near zero ($c_1 < 10^{-3}$), the bound is vacuous and the mechanism fails.

### 4. TTSA Collapse

Lemma D relies on the two-time-scale separation between fast policy updates and slow meta-parameter updates.

**Detection Rule:** If the meta-parameters and policy parameters show strong cross-correlation ($|\text{corr}| > 0.6$) or oscillate on the same timescale, the TTSA stability proofs (based on the ODE method) fail.

## Micro-Glossary

*   **Orthogonality Thesis (OT):** The philosophical claim that intelligence and final goals are independent.
*   **NOC (Naturalized Orthogonality Collapse):** The hypothesis that in realistic environments, capacity-seeking agents converge on preserving optionality.
*   **Directed Information (DI):** A causal measure of information flow ($A \to S$), representing control capacity.
*   **$\Sigma$ (Optionality Reservoir):** System-level Mutual Information ($I(S; A)$), a proxy for the richness of the future.
*   **$\rho$ (Preserve-iff Ratio):** The ratio of optionality dividends to maintenance costs; if $\rho > 1$, preservation is favored.
*   **NCC (Non-Competitive Coupling):** An interaction structure where one agent's influence is a post-processing of another's.

## Conclusion

NOC provides a formalized framework suggesting that the Orthogonality Thesis may fail under realistic environmental and computational constraints. The mechanism relies on the reflective stability of acceleration and the information-theoretic constraints imposed by Directed Information in non-competitive regimes.

We invite the LessWrong community to scrutinize the assumptions (especially NCC and PL regularity), attempt to falsify the core lemmas, and review the Lean 4 formalization.

## Appendix: Core Theorems and Lemmas

For full technical details, see [`docs/NOC_v5.md`](https://github.com/petalofzion/NOC/blob/main/docs/NOC_v5.md).

*   **Lemma A:** Bounded-rational updates drift toward capacity surrogates (A1).
*   **Lemma B:** PL regularity + momentum implies positive expected acceleration (A2-A3).
*   **Lemma D:** Positive acceleration implies reflective instability of $\beta=0$ via TTSA (A4).
*   **Lemma E (DI-DPI):** Under NCC (A5), partner ablation reduces DI capacity.
*   **Lemma E+ (ROI):** Algebraic inequality weighing conversion ($\Delta\Sigma$) vs. ablation ($\Delta J$).
*   **Lemma C':** Capacity gain requires optionality gain (Sigma Law).
*   **Theorem 1:** Drift to $\beta_{\text{meta}} > 0$ (Acceleration).
*   **Theorem 2:** Game-theoretic stability (ESS) of capacity-optionality profiles.
