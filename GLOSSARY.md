# NOC Glossary

This glossary defines the key mathematical symbols and variable names used throughout the NOC (Naturalized Orthogonality Collapse) Lean library.

## Core Variables

| Symbol (Lean) | Symbol (Paper) | Definition |
|---|---|---|
| `β` | $\beta$ | **Inverse Temperature / Precision**. A control parameter governing the sharpness of the policy or distribution. Often evolves over time in TTSA. |
| `U` | $U$ | **Capacity / Utility**. The objective function being maximized (or the potential function whose drift is analyzed). |
| `ΔU` | $\Delta U$ | **Capacity Drift**. The first difference $U_{t+1} - U_t$. |
| `Δ²U` | $\Delta^2 U$ | **Capacity Acceleration**. The second difference $U_{t+1} - 2U_t + U_{t-1}$. |
| `Σ` | $\Sigma$ | **Optionality / Entropy**. A measure of the agent's freedom or available choices (e.g., Mutual Information, Empowerment). |
| `Ξ_loss` | $\Xi_{\mathrm{loss}}$ | **Deletion Penalty / Synergy Loss**. The loss in $\Sigma$ incurred by ablating/removing a component of the system. |
| `g` | $g(\beta)$ | **Mean Drift Function**. The expected change in the system state for a given $\beta$. |
| `ḡ` | $\bar{g}(\beta)$ | **Averaged Mean Drift**. The drift function averaged over fast-scale noise. |
| `ξ` | $\xi$ | **Noise**. Martingale difference noise term in stochastic recursions. |
| `δ` | $\delta$ | **Bias**. Small perturbation or bias term in stochastic recursions. |
| `m` | $m$ | **Drift Slope**. Lower bound constant for the drift, often appearing in Lemma A premises ($m\Delta U \le \Delta ER$). |
| `L` | $L$ | **Lipschitz / Smoothness Constant**. Upper bound constant, often appearing in Lemma A premises ($\Delta KL \le L \Delta U$). |

## Heavy Ball (HB) Specifics

| Symbol | Definition |
|---|---|
| `f` | The objective function in the quadratic model (analogue to $-U$). |
| `x` | Position / Parameter vector. |
| `xstar` | $x^\star$, the optimum position. |
| `λ` / `lam` | Momentum or convex combination parameter. |
| `ρ` / `rho` | Convergence rate or relative step size. |
| `τ` / `tau` | Time-scale separation parameter. |

## Abbreviations

*   **TTSA**: Two-Time-Scale Stochastic Approximation.
*   **MDS**: Martingale Difference Sequence.
*   **RS**: Robbins-Siegmund (a theorem for stochastic convergence).
*   **DI**: Directed Information.
*   **SDPI**: Strong Data-Processing Inequality.
*   **ER**: Expected Reward (or Energy).
*   **KL**: Kullback-Leibler Divergence (control cost).
