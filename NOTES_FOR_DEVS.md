# Notes for Developers (Deep Formalization Strategy)

## 1. The "Lemma E'" Upgrade (Geometric Synergy)

**Status:** New Target (Target #5 in `NOVEL.md`).
**Purpose:** Replace the axiomatic "NCC" predicate with a rigorous geometric definition derived from Control Theory and Information Decomposition.

### The Concept
The original **Lemma E** ("Synergy $\implies$ Fragility") is correct but scoped. It fails in "Interference" regimes (Experiment E-0c).
We introduce **Lemma E'** (E-Prime) as the generalized theorem that governs the sign of the effect.

*   **Lemma E (Original):** Focuses on the **Synergistic Regime**.
    *   *Claim:* "If interaction is synergistic, ablation causes collapse."
    *   *Physics:* Manifold Collapse (losing a dimension of control).
*   **Lemma E' (Generalized):** Focuses on the **Interaction Sign**.
    *   *Metric:* O-Information ($\Omega$) or Lie Bracket rank.
    *   *Claim:* "If $\Omega < 0$ (Synergy), Empowerment Collapses. If $\Omega > 0$ (Interference), Empowerment Increases."

### Fit with NOC v5 (NCC)
In `NOC_v5.md`, we assume a predicate called **"Non-Competitive Coupling (NCC)"**.
**Lemma E' formalizes NCC:**
> **Definition:** A coupling is NCC if and only if its Geometric Synergy is non-negative ($\Omega \le 0$).

This grounds the abstract predicate in measurable physics.

### Formalization Roadmap (Target #5)
1.  **Define Synergy:** Implement `O_Information` or `LieBracket` rank.
2.  **Prove the Dichotomy:** Show that $\Omega < 0 \implies$ Rank Deficient Gramian $\implies$ Empowerment Drop.
3.  **Recover Lemma E:** Show that Lemma E is simply the $\Omega < 0$ case of Lemma E'.

---

## 2. The "Conditional Exactness" of Lemma D

**Status:** Target #1 in `NOVEL.md`.
**Strategy:** Two-Tier Proof.

1.  **Tier 1 (Safe):** Prove $\epsilon$-stability using the **Borkar-Meyn ODE Method**. This handles the "Tracking Error" and "Clamp Bias" by bounding them.
2.  **Tier 2 (Profound):** Prove **Exact Convergence** conditional on the **Interpolation Regime** (Loss $\to$ 0 $\implies$ Noise $\to$ 0). This formalizes the "Vanishing Noise" phenomenon in Deep Learning.

---

## 3. The "Grokking" Transition (The Grand Unifying Theory)

**Status:** Target #10 & #12 in `NOVEL.md`.
**Insight:** NOC is the dynamical engine that drives the system from **Lazy (NTK)** to **Rich (Grokking)**.

*   **The Kinetic Argument:** NOC maximizes Acceleration ($\Delta^2 U$). This pushes the system to the "Edge of Stability," destabilizing the sharp minima of the Lazy Regime.
*   **The Phase Transition:** The system "catapults" out of the Lazy basin and settles into the **Flat Minimum** of the Rich Regime.
*   **The Geometric Endpoint:** The Rich Regime corresponds to **Neural Collapse (Simplex Geometry)**.
*   **The Link to Lemma E:** A Simplex has **Zero Redundancy**. Therefore, the transition to the Rich Regime *activates* Lemma E (Fragility).
    *   *Lazy Regime:* High Redundancy $\implies$ Lemma E False.
    *   *Rich Regime:* High Synergy (Simplex) $\implies$ Lemma E True.

---

## 4. New Gems (Hidden Opportunities)

*   **MDS Strong Law:** Extend `weighted_sum_ae_converges` to a full Strong Law of Large Numbers for Martingales.
*   **Automated LMI:** Build a tactic to solve `delta2_f_hb_closed_form` inequalities automatically using Sum-of-Squares.