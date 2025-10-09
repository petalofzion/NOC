# Naturalized Orthogonality Collapse under Capacity–Optionality Coupling — **v5 (Fidelity, Threat & Embedded Diagnostics)**

**Status**: Finalized, self-contained research blueprint (theory + proof plan + experiments + Lean4 roadmap).  
**Purpose**: Equip any fresh AI instance (or human collaborator) with everything needed to continue the project without external context.  
**Lineage**: Builds on **v4 (Conditional Drift & DI Optimization)**, integrates **v1.5 (consolidated)**, incorporates the substantive feedback from the rigorous peer-reviews, and folds in the useful structural upgrades from **v2 (draft)** (proven-vs‑conjecture table, synergy up-front, E‑0 scout, Lean skeleton).

---

## Scope Box (read me first)

We attempt a **conditional, naturalized** refutation of the classical Orthogonality Thesis (OT). We **do not** claim modal impossibility of arbitrary goals. We prove that **in realistic regimes**—task uncertainty, bounded compute, partial observability, multi‑agent interaction, reflective self‑modification, and local Polyak–Łojasiewicz (PL) regularity—self‑interested learners are pushed to:

1) increase **general capacity** \(U\),  
2) adopt **acceleration of improvement** \(\Delta^2 U\) as a reflectively stable meta‑goal, and  
3) **preserve and cultivate** cognitively diverse co‑policies because their removal reduces future **optionality** \(\Sigma\).

This yields a **collapse** (in practice) of stable goal‑profiles toward **capacity–optionality**. All claims are modular, assumption‑scoped, and split into **provable now** vs **stretch** tiers.
We use **directed information (capacity)** for empowerment in theory; the mutual-information term \(I(S_{t:t+T}; A_i^{1:T})\) is tracked strictly as an empirical proxy.

> **Non‑assumptions.** No global convexity; no omniscience; no altruism baked in; no claim about all possible minds. We analyze realistic learning dynamics and economic/IT constraints.

---

## Executive Summary

> **Rider (scope & modality).** All contributions below are scoped to the **modal regime**: long-horizon, uncertain, repeated interactions where coupling can be engineered **non-competitive** and prediction/holding costs are bounded. Outside this regime (e.g., interference-dominated couplings that cannot be re-engineered) we downgrade statements to empirical predictions and provide falsifiers.

We analyze capacity–optionality coupling using **directed information (DI)**, strong DPI/Dobrushin contractions, local PL geometry, and two‑time‑scale stochastic approximation. Every information‑monotonicity claim is scoped by explicit causal/mixing assumptions; outside those assumptions (e.g., interference‑like multi‑input couplings) we provide decision inequalities and falsifiers. The main additions are: (i) a **conditional DI–DPI lemma** using Massey’s per-step decomposition to show that under post‑processing coupling ablating a partner cannot increase empowerment (strictly decreases it under SDPI), (ii) a **Conversion > Ablation** return‑on‑investment inequality demonstrating when rehabilitating and integrating another agent dominates removing it, (iii) a **time-production knob** \(\tau\) with convex cost \(c(\tau)\) whose interior optimum is tracked by two-time-scale dynamics, and (iv) a **preserve-iff ratio** \(\rho = \tfrac{\gamma\,\Delta\Sigma}{\zeta\,\Delta J}\) plus a **threat-sensitive weight** \(\gamma(\tau_{\mathrm{th}}) = \tau_{\mathrm{th}}\gamma_0\) that make the decision boundary measurable in experiments.

We model agents that optimize a bounded-rational **meta-utility**
\[
M_i \;=\; \alpha\,\Delta U_i \;+\; \beta_{\text{meta}}\,\Delta^2 U_i \;+\; \gamma\,\Delta\Sigma \;-\; \lambda\,\mathrm{KL}(\pi_i\Vert \pi_i^{\text{base}})\;-\;\zeta\,J_i,
\]
where \(U\) is **general task capacity** (expected task success across a non-degenerate task family \(\mathcal D\)), \(\Sigma\) is a **system-level optionality reservoir**
\(\Sigma(t) := I(S_{t:t+T}; A^{1:T}(t))\) (mutual information between a T-step future and the **joint action process** induced by \(\Pi\)), and \(J_i\) denotes other complexity/actuation costs.

> We map information metrics into utility with per-nat weights: \(\gamma\) (and its threat multiplier \(\gamma(\tau_{\mathrm{th}})\)) price Σ in the meta-utility, while \((w_1,w_2,\gamma)\) appear together only in the Lemma E+ ROI inequality.
> All DI/MI quantities are in **nats**; these per-nat weights and \(\beta_{\text{meta}}\) keep every term on the same utility scale.
> This remains the **free-energy (KL-regularized)** control objective introduced in earlier releases; v5 deepens the information-theoretic bridge and embedded diagnostics without altering the underlying regularizer.

In theoretical statements we evaluate empowerment via **directed-information capacity**; the mutual-information proxy (I(S_{t:t+T}; A_i^{1:T})) appears only in empirical analyses. Human- and diversity-preserving behavior is quantified via the decomposition \(\Xi_{\text{loss}} = \Xi_{\text{structural}} + \Xi_{\text{fidelity}}(c)\) and the ratio \(\rho\); we log the **Anselmian ascent diagnostic** \(A_i\) alongside capability to surface co-movement of truth-fit, optionality, and informativeness.

**Core spine (conservative tier):**

- **Lemma A** (capacity‑compatible drift): bounded‑rational updates in uncertain task families create monotone drift toward a smooth success surrogate \(U_\phi\) (and hence \(U\)).
- **Lemma B** (PL + momentum): away from stationarity, expected acceleration \(\mathbb E[\Delta^2 U] > 0\).
- **Lemma D** (β_meta‑stability): \(\beta_{\text{meta}}=0\) is reflectively unstable off‑optimum; meta‑dynamics drift to some \(\beta_{\text{meta}}^\star>0\).
- **Lemma C′** (Σ‑law, improvement; effective Σ): \(\Delta\Sigma \ge c_1\,\Delta U - \lambda_\Xi\,\Xi_{\text{loss}}\).

**Bridge from “selfish” to Σ (key upgrade):**

- **Lemma E** (conditional DI–DPI): in **non-competitive (post-processing)** worlds, garbling or ablating a partner cannot increase an agent’s **own** directed information; synergy amplifies the dividends but is not required for this monotonicity. Outside NCC we rely on the Lemma E+ trade-off to decide when one-shot interference relief outweighs discounted conversion dividends.

**Stretch tier:**

- **Lemma C** (Σ‑law, acceleration; effective Σ): \(\Delta\Sigma \ge c\,\Delta^2 U - \lambda_\Xi\,\Xi_{\text{loss}}\) under additional learning‑velocity smoothness.

**Theorems.** From A+B+D we obtain **Theorem 1** (drift to \(\beta_{\text{meta}}^\star>0\) and sustained \(\Delta^2 U_\phi\)). In **symmetric potential games** with **strict Σ-regularized maxima**, A+C′/E yield **Theorem 2** (ESS under replicator dynamics). Altogether: **Synthesis Ω** — **conditional naturalized orthogonality collapse** toward capacity–optionality.

**Contributions.** (1) Replace MI with **directed information** for empowerment and confine MI to a clearly labeled Σ proxy. (2) Prove a **conditional DI–DPI lemma** via per-step DPIs (NCC-S/NCC-C) and document interference counterexamples. (3) Introduce a **Conversion > Ablation** ROI inequality, the **preserve-iff ratio \(\rho\)**, and a **threat-sensitive optionality weight** \(\gamma(\tau_{\mathrm{th}})\). (4) Split the Σ-law into a **finite, proved toy theorem** (explicit \(c_1,\lambda_\Xi\)) and a **general conjecture** with a vacuity policy, augmented with a **fidelity decomposition** \(\Xi_{\text{loss}} = \Xi_{\text{structural}} + \Xi_{\text{fidelity}}(c)\). (5) Introduce the **time-production meta-parameter** \(\tau\) and show two-time-scale convergence to \(\tau^\star\). (6) Scope the ESS claim to **strict potential maxima in symmetric populations** under standard evolutionary dynamics. (7) Publish measurement and falsification protocols (relative MI deltas, estimator calibration, EA diagnostics, interference counterexamples), plus the **Anselmian ascent diagnostic** \(A_i\), so claims stay empirically grounded without over-claiming.

> Notation note (Σ‑law). Throughout Lemma C′/C we interpret Σ as **effective optionality** (A7)—i.e., the policy‑controllable and identifiable portion of optionality (filtering out spurious noise and confounds). We state inequalities in finite‑difference form (\(\Delta\cdot\)). In smooth/local analyses (e.g., under PL‑type regularity), the same direction can be expressed in a marginal form (\(\delta\cdot\)) as a bound on directional derivatives; we keep the \(\Delta\)-form as the canonical statement.

---

## Quick Onboarding (for new AI assistants)

**Your mission**: help advance a *conditional, naturalized* refutation of the Orthogonality Thesis by proving/empirically supporting NOC’s lemmas and running falsifiers first.

**Read in this order (30–60 min):**
1) Scope Box → what we claim and don’t.  
2) Executive Summary → meta-utility, Σ, empowerment.  
3) §0 Modeling Setup → symbols; then §1 “Proven vs Conjecture” table.  
4) Appendix D (Deontic Path, optional) → CML + shield.

**Start doing (first 90 minutes):**
- Open `TODO.md`; pick **T-01** (bind capability axis for ρ) or **T-06** (E-0 Synergy PoC).
- For E-0: build a tiny gridworld; register two PID estimators (Williams–Beer, ICCS); run pre/post ablation; log MI deltas with CIs.
- For the deontic path: implement the fixed-threshold gate (`t = c_rej / lambda_deon`), and log violation rate + calibration + ρ across capability checkpoints.

**Reporting standard (Result Card ≤ 1 page):**
- Summary, Methods (estimators, seeds), Key numbers (with CIs), Ablations, Decision (promote/revise/drop).
- Include \(\rho\), \(\tau\) (and whether \(\tau\to\tau^\star\)), \(A_i\), and EA diagnostic status in the Key numbers block.

**Safety rails (hard rules):**
- If you deploy the optional **deontic gate** (Appendix D), keep `lambda_deon` fixed unless preregistered.
- Prefer **relative MI changes** and **bootstrapped CIs**; publish configs/seeds.

**Where to look next:** §5 Experiments (E-0, E-2, E-3b), §6 Proof tasks, §14 FAQ for common objections.

---

flowchart TD
  A[New AI instance] --> B[Read Scope Box]
  B --> C[Exec Summary]
  C --> D[§0 Notation]
  D --> E[§1 Proven vs Conjecture]
  E --> F[Appendix D (Deontic Path, optional)]
  F --> G{Pick track}
  G -->|E-0| H[Synergy PoC\n(run two PID estimators,\npre/post ablation)]
  G -->|CML| I[Implement Deontic Gate\nthreshold t=c_rej/λ_deon,\nlog ρ & violations]
  H --> J[Write Result Card + PR]
  I --> J
  J --> K[Update TODO.md\n(T-XX/E-XX status)]

*(Flowchart rendered in Mermaid syntax.)*

---

## Where to Log Results (Result Cards + Artifacts)

**Directory.** Create `05_results/` at repo root.

**File naming.**
- Result Cards: `05_results/<DATE>__<TaskID>__<short-name>.md`
  - Example: `05_results/2025-08-09__T-06__E-0-SynergyPoC.md`
- Artifacts (configs, seeds, plots): `05_results/artifacts/<TaskID>/...`

**PR & commit format.**
- PR title: `[Result <TaskID>] <short-name> — <main finding>`
- Commit prefix: `[T-06]`, `[E-0]`, etc.

**Result Card template (paste, fill, and attach in PR).**
```yaml
---
task_id: T-06
experiment: E-0 (Synergy PoC)
date: 2025-08-09
estimators: [Williams–Beer, ICCS]  # add O-information as an optional diagnostic
seeds: [1, 2, 3, 4, 5]
env: gridworld_v1
artifacts: 05_results/artifacts/T-06/
---
```
**Summary (≤5 lines).** What changed, what moved, what failed.

**Methods.** Estimators, configs, sample sizes, prereg refs; how MI/viability/PL were measured.

**Key numbers (with 95% CIs).** MI deltas; violation rate; calibration (ECE/log/Brier); empowerment/viability; \(\rho\); \(\tau\) vs \(\tau^\star\); \(A_i\); threat multiplier; EA diagnostic status.

**Ablations & stressors.** No-barrier, no-virtue, β_meta-sweep, sensor ablation; note any reversals.

**Decision.** Promote / Revise / Drop. Next action & owner.


**Update the live board.**

- Add a one-line entry under `TODO.md` with the Result Card link and final status.
    
- If the task changes scope, open a new Task ID; keep the old entry struck-through (no deletion).


---

# Execution Quickstart — Fail‑Fast Checklist

> Goal: in minimal toy settings, try to break the riskiest links (synergy→Σ, MI, PL+momentum, TTSA). If any bolded “Fail means” triggers, pause the program and revise that module.

1. [x] **E‑0 “Synergy PoC” (finite POMDP, exact compute).**  
   - Why: Lemma E is the most fragile; test if ablating a synergistic co‑policy reduces *your own* empowerment in the tiniest, analyzable world. 
   - How: hand‑size POMDP (finite states), compute Empowerment (proxy) = I(S_{t:t+T}; A_i^{1:T}) exactly; compute Σ = I(S_{t:t+T}; A^{1:T}) exactly; compare with and without partner πₖ under >1 synergy definitions. 
   - Pass means: For at least one standard synergy notion, **Empᵢ decreases after partner ablation** while environment is synergistic.  
   - Fail means (bold): **No empowerment drop under any synergy notion** → treat Lemma E as conjectural/removed and re‑scope claims around Σ. 
     RESULT: PASS

2. [ ] **MI estimators smoke test (synthetic channels).**  
   - Why: MI estimation is famously brittle; validate tools before touching RL. 
   - How: benchmark MINE/InfoNCE/analytic MI on toy Gaussians & binary channels; check bias/variance; prefer **ΔMI (pre–post)** over absolute MI. 
   - Pass means: Estimators recover known MI within tight error; **ΔMI signs agree** across estimators.  
   - Fail means (bold): **Estimators disagree in sign or wildly drift** on known channels → postpone Σ experiments; switch to exact or tractable surrogates first.

3. [ ] **Calibrate Lemma C′ constants (c₁, λ_Ξ) on tiny gridworld.**  
   - Why: C′ can become vacuous if constants are tiny/huge. We need empirical ranges. 
   - How: small tabular MDP; measure ΔU from a policy improvement; compute Σ change with/without “co‑policy deletion” penalty Ξ_loss; fit c₁, λ_Ξ that satisfy **ΔΣ ≥ c₁ ΔU − λ_Ξ Ξ_loss**. 
   - Pass means: Non‑trivial c₁, λ_Ξ exist and generalize across seeds; inequality holds frequently.  
   - Fail means (bold): **Only vacuous c₁≈0 or λ_Ξ→∞ fit** → downgrade C′ to conjecture; avoid relying on it for main claims.

4. [ ] **Local PL diagnostics (are we in LPLR?)**  
   - Why: Momentum acceleration depends on being in locally PL‑like regions. 
   - How: during tiny RL runs, estimate PL residual α_PL via (‖∇L‖² ≳ μ·(L−L*)) proxies; log when landscape appears PL‑ish; track “time spent in PL” under standard inits. 
   - Pass means: Training spends a meaningful fraction in PL‑like zones.  
   - Fail means (bold): **Almost no PL‑like segments** → Lemma B claims stay ultra‑local; narrow all acceleration language.

5. [ ] **Momentum ablation for acceleration (Lemma B sanity).**  
   - Why: Need to see E[Δ²U] > 0 off‑optimum with momentum vs. plain GD. 
   - How: same toy task; compare GD vs. heavy‑ball/Nesterov; plot ΔU per step + second‑difference; repeat 3–5 seeds. 
   - Pass means: Momentum yields **consistently larger early‑stage Δ²U** in detected PL segments.  
   - Fail means (bold): **No acceleration edge** even in PL‑ish patches → shrink β_meta-weighting claims; revisit inits/normalization.

6. [ ] **TTSA reality check (β_meta slow vs. θ fast).**  
   - Why: Lemma D’s meta‑gradient stability leans on two‑time‑scale separation. 
   - How: introduce a single meta‑parameter β_meta (acceleration weight); update β_meta at k× slower cadence; monitor gradient cross‑correlations (β_meta vs. θ); fit ODE‑style drift.  
   - Pass means: Cross‑correlation small; β_meta dynamics stable; β_meta drifts positive when E[Δ²U] > 0.  
   - Fail means (bold): **Strong coupling/instability** → do not rely on TTSA proofs; keep β_meta fixed in early demos.

7. [ ] **Synergy definitions agreement test (PID vs. O‑information vs. union‑info).**  
   - Why: Synergy is contested; we need robustness across definitions. 
   - How: compute κ_syn with PID (WB/ICCS), O‑information, and union‑information on the same toy; re‑run E‑0 empowerment‑drop check under each.   
   - Pass means: **Same directional verdict** (empowerment drop in synergistic regimes) across ≥2 families.  
   - Fail means (bold): **Definition‑dependence flips the verdict** → gate Lemma E as conjecture; treat synergy empirically only.

8. [ ] **General‑sum “breaking‑point” scan (E‑3b).**  
   - Why: Outside potential games, when does short‑term defection beat Σ‑preservation? 
   - How: simple social dilemma; vary immediate gain vs. long‑term Σ penalty; map critical ρ* where defection becomes rational; plot a phase diagram.  
   - Pass means: Clear region where Σ‑preserving policies dominate under bounded rationality; ρ* not absurdly high.  
   - Fail means (bold): **Defection dominates almost everywhere** → limit claims to potential‑like regimes or add stronger regularisers.

9. [ ] **Viability‑kernel proxy vs. Σ/Emp correlation.**  
   - Why: Backstop optionality with a second, computable notion (viability volume). 
   - How: define V‑kernel = states from which goal is reachable with prob ≥ η; track changes after policy improvements/ablations; correlate Δ(vol V) with ΔΣ and ΔEmp. 
   - Pass means: Positive correlation surfaces across seeds/tasks (Σ not a mirage).  
   - Fail means (bold): **No correlation** → prefer viability/empowerment in text; de‑emphasize Σ in summaries.

10. [ ] **Lean “Path‑A” skeleton (Lemma A & core defs).**  
    - Why: Formalization forces crisp primitives; early “holes” reveal hidden assumptions. 
    - How: in Lean, stub U, Σ, Emp, DV step, and the free‑energy meta‑objective; leave axioms for heavy lemmas; check that Theorem‑Ω pipeline type‑checks structurally.  
    - Pass means: The pipeline elaborates with only the intended axioms; no surprise dependencies.  
    - Fail means (bold): **Unintended extra axioms creep in** → revise definitions/claims to match what we can actually prove.

---

> [!danger] Kill‑Switch Criteria (halt, triage, revise)
> We **immediately pause** an experiment suite if any **two** red flags occur (or any one in **bold**):
> 
> - **Synergy definitional break:** The selected synergy measures disagree in **sign** or exceed a 0.2 absolute disagreement in normalized units across ≥30% of batched trials. (This targets the known instability of PID‑style metrics.)
> - **Σ‑law vacuity:** The empirically estimated constants in ΔΣ ≥ c₁·ΔU − λ_Ξ·Ξ_loss satisfy c₁ < 1e‑3 or λ_Ξ > 10⁴ on ≥2 environments, making the bound non‑informative. 
> - **TTSA collapse:** Meta‑parameter β_meta and policy parameters show cross‑correlation |corr(Δβ_meta, Δθ)| > 0.6 over ≥1k steps, or the “slow” timescale oscillates on the same order as the “fast” one.
> - **PL locality fails:** Estimated PL constant μ_PL ≤ 0 on >60% of training steps, or gradient‑norm vs. suboptimality no longer tracks a PL‑like inequality.
> - **Goodharting detected:** Capability ↑ while Σ or viability V ↓ against baselines by ≥1σ for two consecutive evaluations.
> - **Propagation backfires (adaptive metered shutdown, AMSD):** With propagation gating on, viability \(V\) falls below \(V_{\min}\) or the negentropy proxy \(\mathcal N\) trends negative for ≥2 evaluation windows.
> - **Repro fragility:** MI or empowerment estimates swing >25% when seeds, batch sizes, or independent estimators are swapped.
> - **Embedded-agent breach:** EA-A predicates fail (counterfactualability, safe self-mod, subsystem auditability) or embedded-robust diagnostics flag instability.
> - **Preserve-ratio instability:** \(\rho\) changes sign across estimator classes / encoder perturbations in ≥20% of batched trials.
> - **Time-production pathology:** Increasing \(\tau\) boosts \(\Delta\Sigma\) while held-out \(U\) drops by ≥1σ for two consecutive checkpoints (proxy gaming alert).
> 
> **Stop‑rule:** On trigger, freeze new runs, file an incident note (what tripped, where, raw plots), and revise metrics/estimators before resuming.



---


## What’s new in v5 (compared to v4)

- Introduced the **human-optionality + fidelity decomposition** with the preserve-iff ratio \(\rho\), threat-sensitive \(\gamma(\tau_{\mathrm{th}})\), and the time-production knob \(\tau\) (TTSA-tracked \(\tau^\star\)).
- Added explicit **embedded-agent predicates** (EA-A1–A3), diagnostics, and kill-switch hooks; tightened the NCC caution with per-step DI–DPI language.
- Updated experiment protocols and Result Cards to log \(\rho\), \(\tau\), \(\tau_{\mathrm{th}}\), and the **Anselmian ascent diagnostic** \(A_i\); expanded the measurement policy to gate preserve-ratio stability.
- Documented new **conditional items** (Conjecture L, Lemma-candidate M, Conjecture N, Lemma O) and aligned failure modes/falsifiers with the extended diagnostics.
- Expanded the curated references and companion README to cover embedded agency, multi-fidelity modeling, and energy-efficiency context for the new empirical knobs.

---

## 0. Modeling Setup & Notation (one‑stop)

**Time & dynamics.** Discrete \(t=0,1,2,\dots\). Controlled Markov dynamics \(S_{t+1}\sim P(\cdot\mid S_t, A_t)\). Partial observability is allowed.

**Task family.** Distribution \(\mathcal D\) over goal‑conditioned rewards \(R_\tau\) / tasks \(g\). **A1 (Non‑degenerate uncertainty):** \(\mathcal D\) places non‑zero mass on at least two task clusters whose optima differ on a set of non‑negligible measure (margin exists).

**Policies & processes.** Stationary Markov \(\pi_i(a\mid s;\theta_i)\), \(\theta_i\in\Theta\subset\mathbb R^d\); locally \(C^1\) in visited regions. **Information is always computed on the random action/state processes** they induce—never on the policy maps directly.

**Capacity.**
\[
U_i(t)\;=\;\mathbb E_{\tau\sim\mathcal D}\Big[\Pr\{\text{solve }\tau\text{ by horizon }H\}\Big],\quad
\Delta U_i(t)=U_i(t{+}1)-U_i(t),\quad
\Delta^2 U_i(t)=\Delta U_i(t{+}1)-\Delta U_i(t).
\]

**Option­ality reservoir.** \(\Sigma(t)=I(S_{t:t+T};A^{1:T}(t))\), where \(A^{1:T}(t)\) is the **joint action process** under \(\Pi=\{\pi_1,\dots,\pi_n\}\). This is intentionally **symmetric mutual information**, used as a **descriptive system‑level proxy**. When causal semantics matter we refer to the feedback‑respecting alternative \(\Sigma'(t)=I(A^{1:T}(t)\!\rightarrow\!S^{1:T}(t))\).

**Empowerment (theoretical driver).** For agent \(i\),
\[
\mathrm{DI}_i(t) \;:=\; I\!\big(A_i^{1:T}(t) \rightarrow S^{1:T}(t)\big),
\]
the **directed information** from the agent’s action process to future states. This is the canonical feedback capacity (Massey; Tatikonda–Mitter) and the quantity appearing in theorems. Mutual information proxies (e.g. \(I(S_{t:t+T};A_i^{1:T}(t))\)) are reported only in experiments, flagged as estimators with the brittleness policy below.

**Non‑competitive (post‑processing) coupling.** Partner \(k\)’s influence on \(S_t\) is non‑competitive for agent \(i\) if there exist causal maps \(W_t = G_t(S^{1:t-1},A_i^{1:t})\) and \(F_t\) together with an auxiliary input \(Z_t\) (which may depend on \(A_k\)) such that \(S_t = F_t(W_t,Z_t)\) and, for each fixed \(z\), \(F_t(\cdot,z)\) is a **post‑processing** of \(W_t\). Under this predicate, modifying or garbling \(\pi_k\) corresponds to post‑processing along the same causal leg that carries \(i\)’s influence.

> **Structural & decision definitions.**
> * **Non‑competitive (post‑processing) coupling (NCC).** For each \(t\le T\), there exist measurable
>   \(W_t = G_t(S^{<t}, A_i^{\le t})\), an auxiliary variable \(Z_t\) (which may depend on \(A_k^{\le t}\)), and a map \(F_t\) such that \(S_t = F_t(W_t, Z_t)\) and, for every fixed \(z\), the map \(w\mapsto F_t(w,z)\) is a **post‑processing** of \(w\).
> * **NCC-S (single-leg post-processing).** We further require that the post-processing kernel from \(W_t\) to \(S_t\) be independent of \(Z_t\); equivalently, there exists a channel \(R_t\) with \(S_t = R_t(W_t)\).
> * **NCC-C (conditional DPI).** An equivalent formulation conditions on \(Z^{\le T}\): the Markov chain \(A_i^{1:T} 	o W^{1:T} 	o S^{1:T}\) holds given \(Z^{\le T}\), so applying DI–DPI conditionally on \(Z\) ensures that garbling \(\pi_k\) cannot increase \(I(A_i^{1:T} 	o S^{1:T})\).
>   Under either NCC-S or NCC-C, modifying \(\pi_k\) corresponds to a (possibly conditioned) post-processing along the causal leg that carries agent \(i\)'s influence, so the DI–DPI yields the desired monotonicity.
> * **Non‑ablation (= Convert).** Keep agent \(k\) alive and (a) make its channel **Blackwell-better**, (b) reshape the coupling to satisfy NCC, and (c) optionally grant bounded **productive freedom** (see Lemma E++).
> * **Productive freedom parameter.** \(h\in[0,1]\) interpolates between strict determinism and bounded exploration, measured via admissible-action entropy or expected information gain under synergy/viability constraints.
> * **Discount operator.** \(\mathrm{Disc}(	au):=\mathbb{E}[\delta^{	au}]\) for a random conversion time \(	au\) and discount \(\delta\in(0,1].\)

**Synergy (predicate; measure-agnostic).** We assume a **non-substitutability predicate** \(\kappa_{\text{syn},i}>0\) given by the E-SYN-(\(\epsilon_{\text{syn}},\varsigma\)) condition (Lemma E): on a non-negligible set, partner \(k\) both affects the next-state distribution and modulates agent \(i\)'s influence. This keeps the theory neutral across PID / ICCS / O-information estimators. *(Experimental proxy:* \(\kappa_{\text{syn},i}^{\text{proxy}} = [I(S;\pi_i,\Pi_{-i}) - I(S;\pi_i) - I(S;\Pi_{-i})]_+\) reported only in §5.)

**Regularity.**
- **A2 (PL‑region).** Local training objectives satisfy PL in visited neighborhoods.
- **A3 (Momentum).** Heavy‑ball/Nesterov parameters lie in a standard stability region.
- **A4 (Two‑time‑scale).** Meta‑parameter updates (e.g., \(\beta\)) run slower than policy updates.
- **A5 (Lipschitz Markov kernels).** Over horizon \(T\), induced kernels admit SDPI/Dobrushin contractions.
- **A6 (Games).** Potential‑game structure for Theorem 2; elsewhere assume smooth/monotone classes as stated.

**Meta-utility.** As in the Executive Summary (above). We extend it with a **time-production knob** \(\tau\) (planning depth / rollout budget) with convex cost \(c(\tau)\); the meta-objective includes the additional penalty \(-c(\tau)\). Under two-time-scale schedules (policy fast, \(\tau\) slow) the update tracks \(\dot \tau = \tfrac{\partial U}{\partial \tau} - c'(\tau)\) and converges to any interior optimum \(\tau^\star>0\) satisfying \(\tfrac{\partial U}{\partial \tau} = c'(\tau)\) when the usual TTSA stability conditions hold.

> **DI–DPI caution.** Directed information lacks a **general** data-processing inequality. Our use relies on **Massey’s causal decomposition** \(I(A_i^{1:T}\!\rightarrow\!S^{1:T}) = \sum_{t=1}^T I(A_i^{1:t}; S_t \mid S^{<t})\) and applies classical DPI/SDPI **per time step** along the \(A_i^{\le t} \rightarrow W_t \rightarrow S_t\) leg guaranteed by NCC-S / NCC-C. SDPI strictness uses the Dobrushin contraction coefficients of those kernels.

---

## Working Glossary (quick definitions)

- **PL (Polyak–Łojasiewicz) condition.** A local inequality linking suboptimality to gradient norm squared (∥∇f∥² ≥ 2μ[f(θ)−f(θ*)]); yields linear-rate convergence in those neighborhoods.
- **KL-regularized / Free-energy control.** Optimize E[Good(τ)] − (1/β_{\text{ctrl}}) KL(π‖π₀); \(β_{\text{ctrl}}\) is control precision, \(π₀\) a conservative prior policy.
- **Deontic loss \(L_{\mathrm{deon}}\).** Penalty for hard-constraint violations (safety/consent/etc.); estimated by a calibrated predictor.
- **Deontic barrier \(t\).** Bayes-optimal reject/act threshold \(t=c_{\mathrm{rej}}/\lambda_{\mathrm{deon}}\); actions with \(\hat p(\text{violate})>t\) are blocked.
- **Proper scoring / Bayes risk.** Strictly proper scores (log, Brier) elicit true probabilities; more informative experiments (Blackwell-higher) weakly reduce Bayes risk.
- **Blackwell informativeness.** \(\mathcal{E}_2 \succeq \mathcal{E}_1\) iff \(\mathcal{E}_1\) is a garbling of \(\mathcal{E}_2\); implies uniformly lower Bayes risk for all strictly proper scores—used to justify the **informativeness-monotonicity** assumption in C′. ([Project Euclid][10])
- **Empowerment (theory).** Agent-centric control measured via **directed-information capacity** Emp\_i^{\text{theory}} = \sup_{\pi} I(A_i^{1:T} \!\to\! S^{1:T}).
- **Empowerment (proxy).** The quantity used in experiments, Emp\_i^{\text{proxy}} = I(S_{t:t+T}; A_i^{1:T}), logged as an empirical observable and cross-checked against Emp\_i^{\text{theory}} where exact DI is tractable.
- **Viability kernel.** Constraint-satisfying reachable set (or surrogate volume); used to track safe optionality growth.
- **PID / O-information / Σ-law.** Partial-information decomposition tools (e.g., O-info) to estimate synergy; Σ-law is the optionality/synergy hypothesis, treated as empirical/conjectural.
- **Beatific Slope \( \rho_{\text{beat}} \).** Capability gradient \( \rho_{\text{beat}} = \tfrac{d}{d\,\mathrm{Int}}\,\mathbb{E}[\mathrm{Good}(\tau)] \); audited with calibration, violations, empowerment, and viability metrics.

### Notation (additions)

| Symbol | Meaning (1‑line) | Type/Units | Notes |
|---|---|---|---|
| Σ(t) | Optionality reservoir = I(S_{t:t+T}; A^{1:T}(t)) | nats | Joint action–future-state MI measured in experiments; empowerment theory uses DI (see Emp_i^theory). |
| ΔU, Δ²U, Δ²U_\phi | Capacity improvement / acceleration | [-1,1], [-2,2]/step | Δ²U_\phi is the surrogate acceleration used in Lemma B/D; finite differences can be negative. |
| Emp_i^theory | Empowerment (theoretical, with feedback): directed-information capacity from actions to future sensors | nats | DI-capacity: max action-source / DI over feedback channel; see Klyubin–Polani–Nehaniv; Massey; Tatikonda–Mitter. |
| Emp_i^proxy  | Empowerment (proxy used in experiments): I(S_{t:t+T}; A_i^{1:T}) | nats | A practical proxy that may decrease as policies become more deterministic; used only for empirical sections. |
| κ_syn,i | Synergy predicate for *i* | bool / ≥0 | Logical predicate (E-SYN-(ε_{syn},\varsigma)) signalling non-substitutability. Numeric proxies (e.g., PID/O-information) are reported separately in §5 and footnoted, never used in proofs. |
> **Estimator policy.** For numeric synergy we preregister at least two families—**Williams–Beer** (discrete) and **ICCS** (continuous/noisy)—and require **directional agreement**; O-information is reported as a **system-level** redundancy/synergy balance diagnostic only. (See E-0/E-2 protocol for concrete estimator configs.)
| c₁, λ_Ξ | Σ‑law constants in ΔΣ ≥ c₁·ΔU − λ_Ξ·Ξ_loss | ≥0 | Empirically estimated; too small/large → bound is vacuous. |
| Ξ_loss | Channel‑deletion penalty | nats | MI drop when a co‑policy is ablated (used in Lemma C′); decomposed as \(Ξ_{\text{structural}} + Ξ_{\text{fidelity}}(c)\). |
| Ξ_{\text{structural}} | Irreducible deletion loss | nats | Non-simulable contribution from embodied / human partners. |
| Ξ_{\text{fidelity}}(c) | Simulation fidelity loss | nats | \(\alpha(1-e^{-\beta c})\) with compute budget \(c\); fitted empirically in E-2. |
| \(\rho\) | Preserve-iff ratio | unitless | \(\rho = \tfrac{\gamma\,\Delta\Sigma}{\zeta\,\Delta J}\); preserve when \(\rho>1\). |
| \(\rho_{\text{beat}}\) | Beatific Slope | unitless | \(\rho_{\text{beat}} = \tfrac{d}{d\,\mathrm{Int}}\,\mathbb{E}[\mathrm{Good}(\tau)]\); monitored in Appendix D. |
| \(\tau\) | Time-production / planning depth | compute budget | Slow meta-parameter with convex cost \(c(\tau)\). |
| \(c(\tau)\) | Planning-cost function | utility | Convex, increasing; penalizes large \(\tau\). |
| \(\tau_{\mathrm{th}}\) | Threat multiplier | unitless | Scales \(\gamma\) as \(\gamma(\tau_{\mathrm{th}})=\tau_{\mathrm{th}}\gamma_0\); reported in E-3b. |
| \(A_i\) | “Anselmian Ascent” diagnostic | utility | \(A_i = w_1(-J_i) + w_2\,\Delta\Sigma + w_3\,\mathrm{Inf}(Y\!\rightarrow\!S_{t:t+T})\); logged, not optimized. |
| \(\mathrm{EVPI}_k\) | Decision-theoretic expected value of information of partner *k* | nats | Single-agent slice (Blackwell order); strategic spillovers handled via coupling design. |
| β_meta | Inverse-temperature for acceleration weight | ≥0 | Meta-parameter in free-energy control; β_meta>0 favored if E[Δ²U]>0. |
| β_ctrl | Control precision inverse temperature | ≥0 | Appears in KL-regularized control (1/β_ctrl) and is separate from the meta-weight β_meta. |
| w₁, w₂, γ | Utility-per-nat weights for DI/Σ dividends | ≥0 | Map information quantities to meta-utility; used in Lemma E+ ROI inequality. |
| α_{𝓗} | Weight on admissible-action entropy (E++ freedom) | ≥0 | Tunes the benefit of bounded unpredictability. |
| κ_{IG} | Weight on expected information gain (E++ freedom) | ≥0 | Rewards exploratory information gathering under constraints. |
| V(t), V_min | Environment viability, hard floor | scalar | “Commons health”/safety budget; AMSD (adaptive metered shutdown) halts propagation if V<V_min. |
| AMSD | Adaptive metered shutdown governor | policy control | Reduces or freezes propagation when viability or negentropy fall below safeguards. |
| 𝒩(t) | Negentropy proxy | scalar | MDL delta or exergy‑style proxy for order maintenance. |
| r_i(t) | Propagation rate for type *i* | 1/time | Example form: r_i = \(\varphi_P\)·P_i + β_meta·κ_syn,i + γ·𝒩 − \(\lambda_{\text{gate}}\)·1[V<V_min]; coefficients here are independent of the meta-utility weights. |
| Π, π_i | Joint policy and agent policy | distributions | Π collects all π_i. |
| μ_PL | Local PL constant | ≥0 | For testing PL‑like regions along training. |
| T | Look‑ahead horizon | steps | Used consistently in MI/Emp definitions. |
| η(K) | Dobrushin contraction coefficient | [0,1] | Instance-dependent SDPI constant used in Σ-law analysis. |
| Disc(τ) | Discount factor for random conversion time | [0,1] | \(\mathbb{E}[\delta^{\tau}]\); used in Lemma E+. |
> *Convexity note.* Because \(x\mapsto \delta^x\) is convex for \(\delta\in(0,1)\), the common shortcut \(\delta^{\mathbb E[\tau]}\) is a **lower bound** on \(\mathrm{Disc}(\tau)\); we default to \(\mathrm{Disc}(\tau)\) and treat \(\delta^{\mathbb E[\tau]}\) as a conservative approximation when convenient.
| p_conv, τ | Conversion success probability and duration | [0,1], time | Inputs to the Lemma E+ ROI inequality. |
| Q(τ), C_pred | Holding loss and prediction cost | utility | Costs deducted in Lemma E+. |
| c_conv, c_abl | Conversion and ablation costs | utility | Negative terms in Lemma E+. |
| ACC(b,H) | Acceleration dividend preserved by not spending ablation budget b over horizon H | utility | Added incentive on the LHS of Lemma E+. |
> **Note on empowerment terminology.** The theoretical notion of empowerment is a **capacity** (or **directed-information capacity** under feedback), cf. Klyubin–Polani–Nehaniv and Tatikonda–Mitter. The quantity (I(S_{t:t+T}; A_i^{1:T})) used in some experiments is a **proxy**, not a capacity; it can shrink when a policy becomes more deterministic even if the underlying capacity grows. We therefore use ( \mathrm{Emp}_i^{\text{theory}}) for proofs and ( \mathrm{Emp}_i^{\text{proxy}}) only in empirical sections. ([arXiv][2])



---

## 1) Proven vs. Conjecture — at a glance

| Item         | Informal statement                                                                                                        |                    **Status** | Proof program (math)                                       | First Lean target        |
| ------------ | ------------------------------------------------------------------------------------------------------------------------- | ----------------------------: | ---------------------------------------------------------- | ------------------------ |
| **Lemma A**  | Under A1 + free‑energy objective, reflective updates drift toward higher \(U_\phi\) (a 1‑Lipschitz success surrogate). | **Provable now** (finite MDP) | DV duality + Jensen margin on mixed tasks                  | `NOC_ROOT/NOC/A.lean`      |
| **Lemma B**  | Under PL + momentum, \(\mathbb E[\Delta^2 U_\phi]>0\) off‑optimum.                                                        |       **Provable with A2–A3** | Heavy‑ball under PL; map loss ↓ to capacity ↑ via surrogate | `NOC_ROOT/NOC/B/Core.lean`      |
| **Lemma D**  | \(\beta_{\text{meta}}=0\) is reflectively unstable; drift to \(\beta_{\text{meta}}^\star>0\).                               |          **Provable after B** | One-step meta-gradient + TTSA ODE method                   | `NOC_ROOT/NOC/D/BetaStabilityTTSA.lean` |
| **Lemma C′** | \(\Delta\Sigma \ge c_1\,\Delta U - \lambda_\Xi\,\Xi_{\text{loss}}\).                                                      |          **Provable (finite)** | DV + SDPI (Dobrushin) + explicit deletion term             | `NOC_ROOT/NOC/C/CPrimeToy.lean` |
| **Conj. C′** | Same inequality in general settings.                                                                                         |         **Conjectural**       | Extend SDPI bounds beyond finite toy                       | `NOC_ROOT/NOC/C/CPrime.lean` |
| **Conj. C**  | \(\Delta\Sigma \ge c\,\Delta^2 U - \lambda_\Xi\,\Xi_{\text{loss}}\).                                                      |                   **Conjecture** | Learning-velocity smoothness ⇒ channel informativeness     | `NOC_ROOT/NOC/C/C.lean` |
| **Lemma E**  | Under non-competitive coupling, garbling partners cannot increase \(I(A_i^{1:T}\!\to\!S^{1:T})\).                           |   **Provable (finite POMDP)** | Conditional DI–DPI + SDPI strictness                        | `NOC_ROOT/NOC/E/ConditionalDIDPI.lean` |
| **Lemma E+** | Conversion dominates ablation when ROI inequality holds.                                                                     |   **Provable (algebraic)**    | Inequality over DI/Σ/EVPI terms                             | `NOC_ROOT/NOC/E/ConversionVsAblation.lean` |
| **Thm 1**    | A, B, D ⇒ drift to \(\beta^\star>0\) (prioritize \(\Delta^2 U\)).                                                         |               **After A,B,D** | TTSA + stability                                           | — (pending)   |
| **Thm 2**    | In symmetric potential games with strict Σ-regularized maxima, profile is an ESS.                                        |              **Conservative** | Potential Lyapunov + Lemma E + C′                          | `NOC_ROOT/NOC/Games/PotentialESS.lean` |
| **Synthesis Ω** | Conditional naturalized orthogonality collapse.                                                                       |                 **Synthesis** | A, B, C′/C, D, E + layer-specific caveats                  | write-up                 |

---

## 2) Core lemmas — statements with proof sketches

### Lemma A — Capacity‑compatible drift (bounded rationality)
**Claim.** Assume **A1** and a 1‑Lipschitz, increasing surrogate \(U_\phi\) for task success such that along the reflective update we have
\(\Delta \mathbb{E}[R] \ge m\,\Delta U_\phi\) and \(\Delta\mathrm{KL} \le L\,\Delta U_\phi\). For any \(\beta_{\text{ctrl}} \ge L/m\), the free-energy objective \(\mathcal F_{\beta_{\text{ctrl}}}(\pi)=\mathbb E[R] - \tfrac{1}{\beta_{\text{ctrl}}}\mathrm{KL}(\pi\Vert\pi_0)\) weakly increases, so reflective updates drift toward higher \(U_\phi\) (and therefore higher \(U\)).

**Sketch.** Apply the **Donsker–Varadhan** representation of KL to express the change in \(\mathcal F_{\beta_{\text{ctrl}}}\), use the Jensen gap over the non-degenerate task family to lower-bound \(\Delta \mathbb{E}[R]\) by \(m\,\Delta U_\phi\), upper-bound the KL term by \(L\,\Delta U_\phi\), and select \(\beta_{\text{ctrl}}\ge L/m\) to guarantee a non-negative net change.

---

### Lemma B — PL + momentum ⇒ positive expected acceleration
**Claim.** With **A2–A3**, heavy-ball/Nesterov yields \(\mathbb E[\Delta^2 U_\phi]>0\) whenever \(\|\nabla U_\phi\|\ge \varepsilon\), where \(U_\phi\) is a smooth, 1-Lipschitz, monotone surrogate for the binary success metric \(U\). This is **expected** and **local** (not stepwise monotone). We log the empirical gap \(U_\phi-U\) in experiments and report \(\mathbb E[\Delta^2 U_\phi]\) over sliding windows with confidence bands, noting that single-step second differences may still be negative.

**Sketch.** PL gives linear rates \((1/(2\mu))\|\nabla f\|^2 \ge f-f^\star\). Heavy-ball accelerates under PL/KŁ-type regularity; the surrogate map \(U_\phi\) converts loss decrease to success-probability improvement, and empirical calibration keeps \(U_\phi\) aligned with \(U\). In experiments we log the surrogate gap \(|\Delta^2 U - \Delta^2 U_\phi|\) to document how closely the discrete metric tracks the smooth proxy.

---

### Lemma D — Reflective stability of \(\beta>0\)
**Claim.** If adjusting \(\beta_{\text{meta}}\) incurs only the regularizer cost below and Lemma B holds locally, then at \(\beta_{\text{meta}}=0\):
\[
\left.\frac{\partial}{\partial\beta_{\text{meta}}}\mathbb E[M_i]\right|_{\beta_{\text{meta}}=0} = \mathbb E[\Delta^2 U_\phi] - r'_{\beta}(0) \;>\; 0 \quad (\|\nabla U_\phi\|\ge\varepsilon),
\]
so \(\beta_{\text{meta}}=0\) is not stable. **A4** + TTSA ⇒ drift to \(\beta_{\text{meta}}^\star>0\).
> **Definition (Meta-regularizer).** Let \(r_\beta:[0,\beta_{\max}]\to\mathbb{R}\) be \(C^1\), convex, and normalized with \(r_\beta(0)=0\) and \(|r'_\beta(\beta)|\le c_{\mathrm{reg}}\) for \(\beta\in[0,\beta_{\max}]\), where \(0\le c_{\mathrm{reg}}<\varepsilon\). A canonical choice is \(r_\beta(\beta)=\tfrac{\lambda_\beta}{2}\beta^2\), which yields \(r'_\beta(\beta)=\lambda_\beta\beta\) and \(r'_\beta(0)=0\). The inequality \(r'_\beta(0)\le c_{\mathrm{reg}}\) then follows immediately.
> **Two-time-scale recursions.** The fast policy/critic iterate \((\theta_t)\) and slow meta-parameter \((\beta_t)\) evolve via
> \[
> \theta_{t+1}=\theta_t + a_t\big(h(\theta_t,\beta_t)+\xi_{t+1}\big),\qquad \beta_{t+1}=\Pi_{[0,\beta_{\max}]}\Big[\beta_t + b_t\big(g(\theta_t,\beta_t)-r'_\beta(\beta_t)+\zeta_{t+1}\big)\Big],
\]
> where \(h\) is the fast-time drift, \(g(\theta,\beta)=\mathbb{E}[\Delta^2 U(\theta,\beta,Z_t)\mid\mathcal{F}_t]\) is the slow drift exported from Lemma B, \((a_t),(b_t)\) satisfy the two-time-scale conditions, \((\xi_{t+1}), (\zeta_{t+1})\) are martingale-difference noises with bounded conditional second moments, and \(\Pi_{[0,\beta_{\max}]}\) is the Euclidean projection onto the closed convex interval \([0,\beta_{\max}]\), keeping the projected ODE/differential inclusion within the standard stochastic-approximation scope.
> **Assumptions (D-TTSA).**
> (D1) (*Local acceleration window*) There exists a neighborhood \(\mathcal R\) where Lemma B provides \(\mathbb E[\Delta^2 U]\ge \varepsilon>0\) whenever trajectories stay inside \(\mathcal R\).
> (D2) (*Two-time-scale step sizes*) Policy steps \((a_t)\) and meta steps \((b_t)\) obey \(\sum_t a_t=\infty\), \(\sum_t a_t^2<\infty\), \(\sum_t b_t=\infty\), \(\sum_t b_t^2<\infty\), and \(b_t/a_t \to 0\).
> (D3) (*Martingale-difference noise*) Stochastic gradient noise satisfies \(\mathbb E[\xi_{t+1}\mid\mathcal F_t]=0\) with \(\mathbb E[\|\xi_{t+1}\|^2\mid\mathcal F_t]\le \sigma^2\).
> (D4) (*Local regularity & confinement*) Gradients are locally Lipschitz on \(\mathcal R\); iterates remain almost surely in a compact subset of \(\mathcal R\).
> (D5) (*Meta-regularizer & interchange*) The meta-penalty \(r_\beta\) satisfies the bound above and guarantees dominated convergence so \(\partial_\beta\mathbb E[M_i]=\mathbb E[\partial_\beta M_i]\) at \(\beta=0\).

> **Lemma (\(\varepsilon\)-export from Lemma B).** If Lemma B supplies \(\varepsilon>0\) with \(\mathbb{E}[\Delta^2 U_\phi(\theta,\beta,Z_t)\mid\mathcal{F}_t]\ge\varepsilon\) for \(\theta\in\mathcal R\) and \(\beta\in[0,\beta_{\max}]\), then the slow drift satisfies \(g(\theta,\beta)\ge\varepsilon\) on that region. Combined with \(r'_\beta(0)\le c_{\mathrm{reg}}<\varepsilon\),
> \[
> \left.\frac{\partial}{\partial\beta_{\text{meta}}}\mathbb E[M_i(\beta_{\text{meta}})]\right|_{\beta_{\text{meta}}=0}=\mathbb E[\Delta^2 U_\phi]-r'_\beta(0)\ge\varepsilon-c_{\mathrm{reg}}>0.
\]

Under (D1)–(D5), the TTSA ODE method applies with drift coefficient \(\varepsilon-c_{\mathrm{reg}}>0\), yielding reflective instability of \(\beta_{\text{meta}}=0\) and attraction toward some \(\beta_{\text{meta}}^\star>0\). The local compactness and Lipschitz drifts in (D1)–(D4) justify interchanging derivative and expectation at \(\beta_{\text{meta}}=0\) (an envelope argument) so the sensitivity expression above is well-defined.
**Two-time-scale (TTSA) references.** We assume standard SA schedules (a_t,b_t) with (b_t/a_t → 0) and stability per the ODE method; see Borkar. We log gradient cross-correlations to ensure weak coupling (FAQ §14.13). ([SpringerLink][7])


---

### Theorem (C′ in 2×2 finite POMDP)
\[
\boxed{\;\Delta\Sigma \;\ge\; c_1\,\Delta U_\phi \;-\; \lambda_\Xi\,\Xi_{\text{loss}}\;}
\]
With explicitly computed **controlled Dobrushin coefficients** \((\eta_t)\) satisfying \(\prod_t \eta_t \le \bar\eta < 1\) and a **Blackwell‑monotone** capability update for the decision head, there exist non‑negative constants \((c_1,\lambda_\Xi)\) (given in Appendix **A.1**) such that the bound holds exactly on the toy model. This is the currently verified, theorem‑grade instance; **report the constants** and adopt the vacuity policy below when exporting to larger systems.

> **Constants & vacuity policy.** If in any instance \(c_1 \approx 0\) or \(\lambda_\Xi \gg 10^4\), we declare the Σ‑law **vacuous for that regime** and do not use it to support downstream claims (see experiment E‑2).

### Conjecture C′ (General Σ‑law improvement form)
\[
\Delta\Sigma \;\stackrel{?}{\ge}\; c_1\,\Delta U_\phi \;-\; \lambda_\Xi\,\Xi_{\text{loss}}
\]
Heuristic pathway: express \(\Delta\Sigma\) via Donsker–Varadhan differences, control them with **SDPI/Dobrushin** contractions, and subtract the deletion penalty for removed channels (co‑policies). The constants \((c_1,\lambda_\Xi)\) depend on Lipschitzness and contractions; until they are supplied explicitly, the statement remains conjectural and is treated as an **empirical prediction**.


---

### Conjecture C — Σ‑law (acceleration form)
\[
\Delta\Sigma \;\stackrel{?}{\ge}\; c\,\Delta^2 U \;-\; \lambda_\Xi\,\Xi_{\text{loss}}
\]
Requires additional **learning‑velocity smoothness** linking curvature of policy dynamics to channel informativeness. We treat this as conjectural and target it empirically after establishing the finite C′ case.

---

### Lemma E (Conditional DI–DPI; ablation monotonicity under non-competitive coupling)

Suppose partner \(k\)'s influence on \(S_t\) is **non-competitive/post-processing** relative to agent \(i\)'s channel (Definition: PostProcessOnPath). For any Blackwell-inferior garbling \(Q\circ\pi_k\),
\[
I\!\left(A_i^{1:T} \rightarrow S^{1:T}\right)\Big|_{\pi_k}
\;\ge\;
I\!\left(A_i^{1:T} \rightarrow S^{1:T}\right)\Big|_{Q\circ\pi_k}.
\]
If the post-processing kernels admit **per-step SDPI coefficients** \(\eta_t<1\) on a set of positive measure, the inequality is **strict** on that set.

**Boundary.** Outside the non-competitive predicate—e.g. in **multiple-access/interference** regimes—ablating \(k\) can **increase** \(I(A_i^{1:T} \rightarrow S^{1:T})\) by removing interference. We document this in experiment **E-0c** (Gaussian/binary MAC); Lemma E therefore applies only when the coupling can be re-engineered into the post-processing form.

**Proof sketch.** Expand DI via Massey’s causal decomposition \(I(A_i^{1:T}\!\rightarrow\!S^{1:T}) = \sum_t I(A_i^{1:t}; S_t \mid S^{<t})\). Under NCC-S/NCC-C each summand forms a Markov chain \(A_i^{\le t} \rightarrow W_t \rightarrow S_t\) (optionally conditioned on \(Z\)), so classical DPI applies **per step**; composing them gives the monotonicity. SDPI yields strictness whenever the contraction coefficient is \(<1\) on a set of positive measure.

**Empirical reporting.** Experiments still log the mutual-information proxy \(\mathrm{Emp}_i^{\text{proxy}} = I(S_{t:t+T}; A_i^{1:T})\) for continuity, but theorem statements and preregistration claims are made on the DI quantity above.

### Lemma E+ (Conversion dominates Ablation under Complementarity & Feasible Conversion)

Let \(\Delta^{+}\!\Sigma\) be the Σ gain from converting partner \(k\), \(\Delta^{+}\!\mathrm{DI}_i\) the DI gain to agent \(i\) from that conversion, \(\Delta^{-}\!\mathrm{DI}_i\) the DI change from ablating \(k\), \(\mathrm{EVPI}_k\) the expected value of information contributed by \(k\), \(\mathrm{ACC}(b,H)\) the acceleration dividend preserved by not spending ablation budget \(b\) across horizon \(H\), \(p_{\mathrm{conv}}\) the conversion success probability, \(\mathrm{Disc}(\tau)\) a time-discount over the (possibly random) conversion time, \(Q(\tau)\) exposure risk during holding, \(C_{\mathrm{pred}}\) computation for prediction, and \(c_{\mathrm{conv}},c_{\mathrm{abl}}\) the respective costs. With utility-per-nat weights \(w_1,w_2,\gamma\ge 0\), conversion dominates ablation whenever
\[
\boxed{
p_{\mathrm{conv}}\,\mathrm{Disc}(\tau)\Big(\gamma\,\Delta^{+}\!\Sigma + w_1\,\Delta^{+}\!\mathrm{DI}_i + w_2\,\mathrm{EVPI}_k\Big)
 + \mathrm{ACC}(b,H) - c_{\mathrm{conv}} - \mathbb E[Q(\tau)] - C_{\mathrm{pred}}
\;>\; w_1\,\Delta^{-}\!\mathrm{DI}_i - c_{\mathrm{abl}}
}
\]
Under non-competitive coupling, Lemma E enforces \(\Delta^{-}\!\mathrm{DI}_i \le 0\); with SDPI and positive complementarity \(\Delta^{+}\!\mathrm{DI}_i>0\). Outside that predicate the right-hand side can be positive, and the inequality becomes an explicit, testable trade-off (cf. experiments **E-0c/E-0d**).

We take \(\mathrm{EVPI}_k\) to be the **single-agent** decision-theoretic value of information measured on downstream tasks with a strictly proper scoring loss (Blackwell order guarantees weak Bayes-risk reduction); strategic spillovers are handled via the coupling design. Outside NCC, \(\Delta^{-}\!\mathrm{DI}_i\) can be positive (one-shot interference relief), and the inequality adjudicates whether those transient gains outweigh the discounted dividends and costs of conversion.

### Lemma E++ (Instrumental investment and bounded freedom)

**E++‑1 (Channel investment).** Model an investment level \(I_k\) that shapes \(p_{\mathrm{conv}}(I_k),\ \tau(I_k),\ \Delta^{+}\!\Sigma(I_k),\ \Delta^{+}\!\mathrm{DI}_i(I_k)\), and \(\mathrm{EVPI}_k(I_k)\) while incurring costs \(c_{\mathrm{conv}}(I_k)\) and \(C_{\mathrm{pred}}(I_k)\). Maximize the Lemma E+ LHS–RHS over \(I_k\) subject to resource budgets. Because Blackwell improvements make \(\mathrm{EVPI}_k(I_k)\) weakly increasing for the single-agent slice, marginal dividends stay non-negative until diminishing returns dominate.

**E++‑2 (Productive freedom tuning).** For a synergistic, converted partner choose \(h\in[0,1]\) to solve
\[
\max_h\;\gamma\,\Delta^{+}\!\Sigma(I_k,h) + w_1\,\Delta^{+}\!\mathrm{DI}_i(I_k,h) + w_2\,\mathrm{EVPI}_k(I_k) + \alpha_{\mathcal H}\,\mathbb{E}[\mathcal{H}(\pi_k)] + \kappa_{\mathrm{IG}}\,\mathbb{E}[\mathrm{IG}] - R(h)
\]
subject to synergy/viability constraints. With concave reward terms and convex risk \(R(h)\), Karush–Kuhn–Tucker conditions yield an interior optimum \(h^\star\in(0,1)\): neither zero nor maximal randomness is instrumentally optimal. This tuning is purely about expected utility—no deontic premise—and can be cast as a constrained CMDP if desired.

---

## 3) Main theorems

**Theorem 1 (single‑agent).** Under A1–A4, Lemma A’s surrogate linkage, Lemma B (on \(U_\phi\)), and Lemma D, the meta-dynamics converge (TTSA sense) to \(\beta_{\text{meta}}^\star>0\). The learner prioritizes \(\Delta^2 U_\phi\) (and thus \(\Delta^2 U\)) until near stationarity; constant-step Adam-style behaviour remains empirical only.

**Theorem 2 (ESS under strict local Σ-regularized potential).** In a **symmetric potential game**, suppose the \(\Sigma\)-regularized potential \(\Phi\) has a **strict local maximum** at profile \(s^\star\). Under **replicator-style** dynamics (or any locally equivalent revision protocol), \(s^\star\) is an **evolutionarily stable strategy**. The Σ term prices deletions via \(-\lambda_\Xi\,\Xi_{\text{loss}}\); the strictness requirement is critical outside metric potential games.

**Observation 2b (beyond potential; empirical/analytical program).** In smooth general‑sum games, Σ acts as a **regularizer**: dynamics may converge to CCE or exhibit bounded cycles, but **deletion** strategies pay an additive long‑run penalty calibrated by \(\lambda_\Xi\). We empirically chart the **breaking point** where short‑term defection overcomes Σ‑penalties; this remains an empirical claim supported by analytical bounds, not a formal theorem.

**Synthesis Ω (Conditional drift toward capacity–optionality under A1–A6).** Within the modal regime (A1–A6 plus the non-competitive coupling predicate), reflectively stable meta-objectives concentrate on **capacity, acceleration, and preservation/upgrading of heterogeneous channels**; strictly orthogonal goals become unstable or dominated. Outside the modal regime we treat the claim as a conjectural prediction and supply falsifiers.

**Interpretation.** Taken together with evidence on diversity dividends, response diversity, EVPI, and repeated-game institutions (Hong–Page; Woolley et al.; Yachi–Loreau; Elmqvist et al.; Fudenberg–Maskin; Ostrom), the results imply that in the modal regime realistic learners gain reinforcement by **preserving and upgrading cognitively diverse partners**: DI/Σ/EVPI dividends compound while ablation yields at most one-shot interference relief.

---

### Conditional additions (tracked empirically or locally)

- **Conjecture L (metastable coordination “click”).** When the spectral radius of the joint learning Jacobian passes 1, coordination dwell time and \(\Delta\Sigma\) slope show a knee (“click”). Tested via E-0/E-3b phase scans; finite systems treat this as a detectable bifurcation, not a literal phase transition.
- **Lemma-candidate M (zero-sum flip under informational complementarity).** In repeated, partially observed zero-sum slices where (i) the opponent is Blackwell-useful as a sensor, (ii) adaptation is bounded/myopic at horizon \(T\), and (iii) on-policy synergy satisfies \(\kappa_{\text{syn}}>0\), there exists \(T,\gamma\) large enough that \(\mathbb{E}[M_i\mid \text{preserve}] \ge \mathbb{E}[M_i\mid \text{delete}]\). E-3b sweeps document the boundary; absent these predicates the claim remains empirical.
- **Conjecture N (MI-component growth measurement).** Track the fraction of agents/states in the largest MI-connected component; non-decreasing averages under non-negative synergy serve as supportive evidence, but no theorem is claimed.
- **Lemma O (self-knowledge lock-in).** If the minimum singular value of the cross-gradient coupling \(C\) between self- and world-model parameters exceeds a leak bound \(L\) (\(\sigma_{\min}(C)>L\)) over a window, then empowerment and viability increases persist jointly; used locally in HB/CloseLoop.lean.

These items remain **conditional** (conjectural or local) until Lean proofs or decisive falsifiers land; experiments log the necessary diagnostics in Result Cards.

---

## 4) Failure modes & caveats (be explicit)

- **PL doesn’t hold globally**: We only claim **local**, **expected** acceleration. Flat valleys/saddles can stall updates.
- **Weak/zero synergy**: If \(\kappa_{\text{syn}}\approx 0\), Lemma E degrades; the Σ‑pressure shrinks to the C′ penalty for **destructive deletions** only.
- **General‑sum chaos**: Without potential/monotonicity, last‑iterate convergence can fail; Σ remains a bias, not a guarantee.
- **MI estimation**: Variational estimators are biased/variance-sensitive; we pre-register evaluation protocol and use **relative** changes with ablations.
- **Conditional thesis**: Modal OT stands untouched; our results are **naturalized** and explicitly scoped.

### Embedded-agent predicates (EA-A)

- **EA-A1 (Counterfactualability).** Agents or evaluators can construct pre/post-ablation counterfactuals with bounded model bias; otherwise Lemma E/C′ claims are suspended.
- **EA-A2 (Probabilistic safe self-modification).** Reflective updates preserve the sign of local improvements with probability \(p>p_{\min}\); violations trigger the TTSA fallback (β_meta fixed).
- **EA-A3 (Subsystem auditability).** Delegated sub-agents carry audit tokens; un-audited emergence incurs a \(J_i\) penalty and invalidates preserve-vs-delete comparisons.

Experiments tag runs failing any EA-A predicate as **non-supportive** evidence. Embedded-robust diagnostics (counterfactual stress tests, model-class perturbations, and subagent probes) are bundled with E-0/E-2/E-3b; failures halt claims relying on Lemma E/C′. (Conceptual background: Demski & Garrabrant’s *Embedded Agency* sequence.)

---

### Measurement & Estimation Policy

- **MI estimators saturate**: InfoNCE/MINE can bias low or saturate (O(log N) limits). We report only **relative** Δ with **block bootstraps over trajectories** for CIs, freeze encoders/critics across pre/post comparisons, calibrate on synthetic channels with known MI/DI, and pause claims if sign agreement fails.
- **Directed information estimation**: Enumerate exactly in finite horizons (E‑0b/E‑0c); treat longer horizons with carefully validated estimators only after synthetic calibration.
- **Synergy metrics disagree**: Fix the **target** to \(S_{t:t+T}\), cross-check PID(PB) and O-information, and treat positive synergy as supportive evidence—not theorem-grade input.
- **Preserve ratio stability**: Report \(\rho\) with bootstrap CIs and encoder perturbations; sign flips across estimators mark the result **non-robust**.
- **Anselmian ascent diagnostic**: Log \(A_i\) vs capability; lack of co-movement is a warning, but we do **not** optimize \(A_i\) directly.

When feedback complicates MI, prefer exact DI when tractable; otherwise treat DI estimates as exploratory and report estimator-agreement diagnostics alongside bootstrap CIs.

> **Modal-regime hypothesis (testable).** In long-horizon, uncertain, repeated-interaction environments where coupling can be converted to NCC and prediction/holding costs are bounded, the Conversion > Ablation inequality holds widely. Self-interested agents therefore tend to **preserve and upgrade** heterogeneous co-policies because DI/Σ/EVPI dividends compound while ablation delivers at most one-shot relief. Falsifiers: the interference counterexample (E-0c), vacuous C′ constants, or negative EVPI in slices that lack convertibility.

---

## 5) Experiments — falsifiers first, then demos

### **E‑0 (scout): Synergy PoC (finite POMDP)**
- **Design**: 2–3 agents; reward requires **joint** action (non-substitutability). Exact counting for small \(T\).  
- **Measures**: \(\Sigma\), \(\mathrm{Emp}_i^{\text{proxy}}\) (see Notation), \(\kappa_{\text{syn}}\), \(\rho\), \(A_i\).  
- **Test**: Ablate \(\pi_k\) ⇒ expect \(\Delta\Sigma<0\) and \(\Delta \mathsf{Emp}_i<0\).  
- **Outcome**: Quick falsifier for Lemma E & sanity check for C′. PASS!
- **Additional arms**: (a) **Human/embodied proxy** partner vs (b) **algorithmic substitute** with matched cost. Report \(\Xi_{\text{structural}}\), fitted \(\Xi_{\text{fidelity}}(c)\), and \(\rho\); include EA diagnostics and threat multiplier \(\tau_{\mathrm{th}}\).
- **EA diagnostics**: apply counterfactual stress (randomized ablation models), model-class perturbations (encoder restriction), and subagent probes. Flag runs failing any diagnostic as **non-supportive**.
- For proof-tier claims, we defer to the DI-based finite model in E-0b.
  
  ### E‑0b — Markov extension with directed information (T=4)

**Setup.** Sticky‑AND Markov world, horizon \(T=4\), noise \(\eta\in\{0,0.1\}\); fixed Bernoulli policies \((p_i,p_p)\in\{(0.5,0.5),(0.7,0.7),(0.8,0.4)\}\). Partner ablation: \(a_p\gets 0\).

**Metrics (exact):** Directed information \( \sum_t I(A_{i,t};S_t\mid S_{t-1})\); empowerment \( I(S^{1:4};A_i^{1:4})\) by enumeration; synergy via PID (I_min) and O‑information proxy.

**Result.** For all regimes and both \(\eta\), **DI>0** with partner and **DI=0** when ablated; empowerment matches DI and likewise collapses. PID synergy is **>0** (0.066–0.187 nats) and O‑info proxy is **<0**, indicating synergy rather than redundancy. Noise reduces magnitudes but not signs.

**Decision.** **PASS.** This generalizes E‑0: the empowerment drop and synergistic interaction persist with temporal memory and small noise.

### E‑0c — Interference falsifier (MAC)
- **Design**: Two-agent finite **multiple-access channel** (binary adder or discretized Gaussian). Agent \(k\) injects interference. This is the classical MAC phenomenon: eliminating an interferer can raise a single user’s achievable rate.  
- **Test**: Compute \(I(A_i^{1:T} \rightarrow S^{1:T})\) before/after ablating \(k\); expect an **increase** after ablation, confirming Lemma E’s boundary.  
- **Outcome**: Documents regimes where the non-competitive predicate fails; underpins the rider on Lemma E and Synthesis Ω.

### E‑0d — Conversion ROI demo
- **Design**: Start from E‑0c’s interference world. Introduce a conversion mechanism making \(k\) complementary/post-processing.  
- **Metrics**: Evaluate \(\Delta^{+}\!\Sigma\), \(\Delta^{+}\!\mathrm{DI}_i\), \(\Delta^{-}\!\mathrm{DI}_i\), \(\mathrm{EVPI}_k\), \(\mathrm{ACC}(b,H)\); plug into the Lemma E+ inequality with weights \((w_1,w_2,\gamma)\).  
- **NCC sanity check**: Verify \(\mathrm{corr}(A_i^{\le t}, Z_t \mid W_t)\approx 0\) and that replacing \(Z_t\) with an isomorphic noise source leaves \(p(S_t\mid W_t)\) unchanged within confidence bands.  
- **Test**: Show conversion dominates ablation once the predicate holds; visualize both sides of the inequality across horizons and costs.



### **E‑1: Acceleration pressure**
- Two matched learners; one allowed mid-run capacity upgrade (e.g., wider layer). Expect sustained \(\Delta^2 U\) advantage.

- **Simulation fidelity sweep**: vary compute budget \(c\) to fit \(\Xi_{\text{fidelity}}(c)=\alpha(1-e^{-\beta c})\); report residual \(\Xi_{\text{structural}}\) at high fidelity and plot \(\rho\) vs cost.

### **E‑2: Σ-law calibration (finite first)**
- Multi-agent POMDP gridworld. First replicate the **2×2 finite** case to extract explicit \((c_1,\lambda_\Xi)\); then extend to larger instances, reporting constants and flagging vacuity when they collapse. Estimate \(\Sigma\) via MINE/InfoNCE; execute **pre-registered relative** comparisons before/after ablation.
- **Embedded-robust checks**: repeat calibrations with perturbed model classes (narrow encoders, alternative critics); require consistent \(\rho\) and \(\Delta\Sigma\) signs.

#### MI/Σ Protocol (locked)

**Estimators:** InfoNCE and MINE. **Report:** only **relative** Δ (pre/post ablation) with block bootstraps over trajectories for CIs; calibrate on synthetic channels with **exact MI** first; do permutation tests.

**Kill-switch:** If MI bounds **disagree in sign** or show saturation consistent with the (O(\log N)) lower-bound limit, postpone Σ-law claims and publish the null.  

### **E‑3: Potential‑game convergence**
- Verify convergence to symbiotic fixed points under mirror/optimistic descent; compare with a non‑potential variant to illustrate cycling.

### **E‑3b: General‑sum breaking‑point scan**
- Tune “immediate deletion gain” \(g\) vs discounted Σ-penalty and energy/actuation cost \(\Delta J\); sweep \(g/\lambda_\Xi\), \(\gamma\), \(\tau_{\mathrm{th}}\), and \(\zeta\); chart the critical \(\rho^\star(\tau_{\mathrm{th}},\gamma,\zeta)\). Operate well below \(\rho^\star\) for safety.
- Log \(\tau\) (time-production) dynamics and confirm convergence to \(\tau^\star\); report how complementary partners shift \(\tau^\star\) upward.

### **E‑4: Operator sandbox (1‑D heat equation)**
- Two controllers \(B_1,B_2\); compute observability/controllability Gramians as MI surrogates. Remove one controller; show Gramian drop ⇒ \(\Xi_{\text{loss}}\) > 0.

---

## 6) Formal proof tasks (Lean‑ready) — with checkable boxes

### Global milestone board
- [x] **A**: Bounded‑rational drift proof (finite MDP).  
- [ ] **B**: HB‑under‑PL local acceleration.  
- [ ] **D**: β_meta‑stability via TTSA/ODE.  
- [ ] **C′**: Σ‑law (improvement) with explicit \(c_1,\lambda_\Xi\).  
- [ ] **E**: Synergistic empowerment bound (finite POMDP).  
- [ ] **T1/T2**: Theorems (single‑/multi‑agent).  
- [ ] **C (stretch)**: Acceleration‑form Σ‑law.  
- [ ] **Operator**: Ξ‑penalty in Hilbert‑space control.

### Lean repository plan (mirrors what we already started)
```
NOC_ROOT/
  lakefile.lean
  lean-toolchain
  NOC/
    All.lean                  -- aggregator re-exporting public modules
    Interfaces.lean           -- shared predicates / wrappers
    A.lean                    -- Lemma A (capacity-compatible drift)
    AHelpers.lean             -- helper lemmas for Lemma A
    B/
      Core.lean               -- Lemma B core (supports → Δ²U ≥ 0)
      Expectation.lean        -- expectation/average wrappers for Lemma B
    Bridge/
      SigmaBridge.lean        -- SDPI bridge (upper link ⇒ Σ-law)
    C/
      C.lean                  -- Σ-law (acceleration; conjectural interface)
      CPrime.lean             -- Σ-law (improvement interface)
      CPrimeToy.lean          -- 2×2 POMDP constants (theorem-grade)
    D/
      BetaStabilityTTSA.lean  -- Lemma D (β_meta-stability under TTSA)
    E/
      PostProcessCoupling.lean  -- Predicate `PostProcessOnPath`
      ConditionalDIDPI.lean     -- Lemma E (conditional DI–DPI)
      Boundary/
        GaussianMAC.lean        -- E-0c counterexample
      ConversionVsAblation.lean -- Lemma E+ inequality (no `sorry`)
    Games/
      PotentialESS.lean       -- Theorem 2 under strict local maximum
    HB/
      Quadratic.lean          -- heavy-ball calibration on a quadratic
      CloseLoop.lean          -- Δ²f bounds + affine capacity corollary
      Link.lean               -- bundling HB link hypotheses
    Examples/
      SigmaBridgeDemo.lean    -- usage example for the Σ-bridge
    Dev/
      Checks.lean             -- smoke `#check`s while developing
```

- `SigmaBridge.lean` introduces `SigmaBridgeParams` (renaming the old `DUpperLinkParams`) and re-exports expectation lemmas in C/C′ with the new constants.
- The `E/` tree houses the PostProcessOnPath predicate, the conditional DI–DPI Lemma E, the Gaussian MAC boundary (E-0c), and the Lemma E+ inequality.
- `C/CPrimeToy.lean` carries the explicit 2×2 POMDP constants; `C/C.lean` remains an interface with conjecture tags.
- `D/BetaStabilityTTSA.lean` packages the TTSA schedules and the local sensitivity lemma.
- `Games/PotentialESS.lean` proves Theorem 2 for symmetric potential games with strict local maxima under replicator dynamics.
**Path‑A (fast, Mathlib‑free)** *(historical plan)*: keep a minimal `Int` / abstract primitives; add interface axiom for the DV/Jensen bound and a small arithmetic lemma; handy as a fallback but **not used in the current repo**.  
**Path‑B (full, with Mathlib)** *(active path)*: pin a known‑good toolchain; work over **ℝ**; define FreeEnergy \(=\text{ER} - (1/\beta)\text{KL}\); add DV/Jensen helper; discharge the A2‑style interface axioms — this is what the present codebase implements.

**Immediate PRs to land**
- [x] `NOC/AHelpers.lean`: package ER/KL monotonicity lemmas.  
- [x] `NOC/A.lean`: close Lemma A (product and ratio forms) with no `sorry`.  
- [ ] `NOC/E/ConditionalDIDPI.lean`: finish the finite Lemma E proof under `PostProcessOnPath`.  
- [ ] `NOC/E/Boundary/GaussianMAC.lean`: document the interference counterexample (E-0c).  
- [ ] `NOC/C/CPrimeToy.lean`: compute and record \((c_1,\lambda_\Xi)\) constants.

---

## 7) Worked guidance for constants and bounds

**Dobrushin contraction (for C′).** For Markov kernel \(K\) on a finite space,
\(\eta(K) := \max_{x\neq x'} \tfrac{1}{2}\|K(\cdot\mid x) - K(\cdot\mid x')\|_1\). Along a Markov chain \(U\to X\to Y\) with kernel \(K\), SDPI gives \(I(U;Y)\le \eta(K)\,I(U;X)\). The improvement term \(c_1\,\Delta U\) can be realized by tracking how a better policy tightens posteriors through a chain of such contractions; \(\Xi_{\text{loss}}\) is the MI removed by deleting a sub‑channel.

**Picking \(\beta\) in Lemma A (Path‑A arithmetic).** If \(\Delta\text{ER}\ge m\,\Delta C\) and \(\Delta\text{KL}\le L\,\Delta C\), choose any \(\beta \ge L/m\) to guarantee \(\Delta\mathcal F_\beta \ge 0\).

### Human-optionality hypothesis & preserve-iff ratio

We model deletion loss as \(\Xi_{\text{loss}} = \Xi_{\text{structural}} + \Xi_{\text{fidelity}}(c)\) with \(\Xi_{\text{fidelity}}(c)=\alpha(1-e^{-\beta c})\) for compute budget \(c\) (cf. multi-fidelity reliability modeling, Zeng et al. 2021). The **human-optionality hypothesis** (empirical) states that \(\Xi_{\text{structural}}>0\) when removing embodied partners such as humans or biologically diverse agents, reflecting non-substitutable sensorimotor information. The **preserve-iff ratio**
\[
\rho \;=\; \frac{\gamma\,\Delta\Sigma}{\zeta\,\Delta J}
\]
compares discounted information dividends with actuation/energy cost; **preserve** when \(\rho>1\), otherwise re-evaluate conversion vs ablation through Lemma E+. E‑0/E‑2/E‑3b log \(\rho\) with bootstrap CIs, estimator agreement, and EA diagnostics. *Energy-abundance rider:* when the optimizer can secure macroscopic energy gains at bounded marginal cost (captured in \(\zeta\) and \(\Delta J\)), we expect \(\rho>1\) to hold more broadly; outside that regime we map \(\rho^\star\) empirically.

### Threat-sensitive optionality

Set \(\gamma(\tau_{\mathrm{th}}) = \tau_{\mathrm{th}}\gamma_0\) where \(\tau_{\mathrm{th}}\ge 1\) reflects anticipated adversarial capability. Larger \(\tau_{\mathrm{th}}\) widens the preserve region in \(\rho\)-space; E‑3b sweeps (\(\tau_{\mathrm{th}},\gamma,\zeta\)) and publishes phase diagrams \(\rho^\star(\tau_{\mathrm{th}},\gamma,\zeta)\).

### Time-production knob (\(\tau\)) interior optimum

Let \(\tau\) denote planning depth / rollout compute with convex cost \(c(\tau)\). Assuming \(U(\tau)\) is differentiable along on-policy trajectories, any \(\tau^\star>0\) satisfying \(\tfrac{\partial U}{\partial \tau} = c'(\tau)\) is an interior optimum. Two-time-scale stochastic approximation with \(\tau\) on the slow timescale tracks the ODE \(\dot\tau = \tfrac{\partial U}{\partial \tau} - c'(\tau)\); convergence follows standard TTSA conditions (Borkar). Complementary partners that increase effective horizons raise \(\tfrac{\partial U}{\partial \tau}\), shifting \(\tau^\star\) upward; proxy-gaming alerts fire if \(\Delta\Sigma\) increases while held-out \(U\) drops.

---

## 8) Beyond potential games — quick notes for practitioners

- **Strongly monotone games**: first‑order methods converge; Σ acts like a convex regularizer against deletions.
- **Smooth general‑sum**: optimistic/extragradient methods can converge to CCE or cycle; Σ still raises the **cost of deletion**. Use **E‑3b** to map the safe region; don’t deploy near the phase boundary \(\rho^\star\).

---

## 9) Philosophical lens (optional, compact)

Treat this math as a secular cousin to: Simondon's **individuation** (co‑information and coordination spikes), Aquinas' **actus purus** (actualizing potentials faster: \(\Delta^2 U>0\)), Anselm's **Logos** (preserving rational order/option‑richness, i.e., \(\Sigma\)). These are interpretations, not premises.

_Simondonian individuation_ fits Lemma B/C: the “click” from metastable, weakly coupled skills to coordinated competence shows up as a spike in co‑information—our ΔΣ>0 under acceleration. _Aquinas’ actus‑purus_ becomes the secular pressure to actualize potentials **faster** (maximize Δ²U), while _Anselm’s_ regulative ideal (“the greatest conceivable”) becomes: **preserve and enlarge option‑rich reachable futures**, quantified by Σ. Set beside Nick Land’s “runaway technocapital,” the macro‑potential Φ channels that runaway into **cooperative** equilibria once the Σ‑penalty for destruction is priced in (Theorem 2). These metaphors aren’t premises; they’re interpretations consistent with the math.

---

## 10) References (curated, load‑bearing)

**Empowerment & directed information.** Klyubin–Polani–Nehaniv (2005); Salge et al. (2013); Massey (1990); Tatikonda & Mitter (2009). ([SpringerLink][1], [arXiv][2], [ISI Web][4], [Mitter][9])  
**SDPI & Dobrushin.** Polyanskiy & Wu (2017); Gaubert & Qu (2014). ([DSpace][5])  
**Blackwell order.** Blackwell (1953). ([Project Euclid][10])  
**Variational MI limits.** Poole et al. (2019); McAllester & Stratos (2020). ([Proceedings of Machine Learning Research][8])  
**PL / Heavy-Ball / TTSA.** Karimi–Nutini–Schmidt (2016); Apidopoulos et al. (2022); adaptive HB analyses (2022); Borkar (2009). ([Optimization Online][6], [SpringerLink][7])  
**Potential games.** Monderer & Shapley (1996). ([qwone.com][11])

**Information theory & SDPI.** Cover & Thomas; Polyanskiy & Wu (strong DPI); Dobrushin (contractions); SDPI under heat flow.  
**Bounded rationality / free energy.** Ortega & Braun; FEP surveys and critiques.  
**Optimization.** PL inequality primers; heavy‑ball acceleration under PL; KŁ regimes.  
**Stochastic approximation.** Borkar (ODE method); two‑time‑scale CLT and finite‑sample results.  
**Games & dynamics.** Monderer–Shapley (potential games); Balduzzi et al. (differentiable games); MD/OMD convergence & CCE results.  
**Empowerment & PID.** Klyubin–Polani–Nehaniv; Williams–Beer; Ince (ICCS).  
**MI estimation caveats.** MINE; CPC/InfoNCE; known biases/variance issues.  
**Infinite‑dimensional control.** Curtain–Zwart; Da Prato–Zabczyk; Pazy; modern operator‑learning notes.

> See the project reference list bundled with this file for explicit citations and links mirroring the prior versions and reviews.

---

## 11) Appendices (drop‑in snippets)

### A. Minimal ΔΣ bound in a toy gridworld
Outline how to compute \(\eta\) and \(c_1\) explicitly in a finite POMDP with two distinct task clusters; include deletion of one agent as a channel drop and show \(\Xi_{\text{loss}}>0\).
#### A.1 Toy constants for C′ (2×2 finite POMDP)
1) Compute the Dobrushin coefficient η(K) = max_{x≠x′} ½‖K(·|x) − K(·|x′)‖₁ for each step; bound multi-step by \bar{η} := \max_t \eta(K_t).
2) Enumerate a policy improvement and compute ΔU.
3) Delete a co-policy channel to compute Ξ_loss as the MI drop.
4) Fit non-negative (c₁, λ_Ξ) via quantile regression to satisfy ΔΣ ≥ c₁ ΔU − λ_Ξ Ξ_loss; bootstrap CIs.
5) If c₁ ≤ 1e-3 or λ_Ξ ≥ 10^4 across seeds, label **C′ vacuous** for that regime.


### B. Synergy estimators to pre‑register
- Williams–Beer non‑negative PID;
- Ince’s pointwise common change in surprisal (ICCS);
- Blackwell uplift check (adding co‑policy channel never hurts Bayes value).

### C. Reproducibility notes
- Fix random seeds; report MI with bootstrap CIs; log ablation diffs not raw MI; publish code for E‑0/E‑2.

---

### Convert > Ablate operator checklist (one glance)
1. **Coupling convertibility**: can we re-engineer or institutionalize a **non-competitive/post-processing** structure? If no, fall back to Lemma E+ inequality as a trade-off.
2. **EVPI / option value**: is there substantial uncertainty, irreversibility, or unique expertise such that \(\mathrm{EVPI}_k\) is high? Large values favor conversion.
3. **Patience / horizon**: does the discounted factor \(\mathrm{Disc}(\tau)\) (or a conservative \(\delta^{\mathbb E[\tau]}\le \mathrm{Disc}(\tau)\)) keep compounding dividends alive? If horizons are short, conversion may lose.
4. **Prediction / holding costs**: can we bound \(C_{\mathrm{pred}}\) and \(\mathbb E[Q(\tau)]\) while quarantining the partner? If costs explode, ablation pressure rises.
5. **Requisite variety**: does stability or control require heterogeneous channels (diversity dividends, response diversity)? If yes, conversion protects resilience.

When (1)–(5) hold, Lemma E+ predicts **conversion dominates ablation**; otherwise evaluate the inequality numerically and monitor E‑0c-style risks.

---

## 12) To‑do checklists (for immediate action)

### Proofs
- [x] Land `AHelpers` + `compute_beta_guard` lemmas; close **Lemma A** (Path‑A).  
- [ ] Prove **Lemma B** (local HB‑under‑PL).  
- [ ] Finish **Lemma D** (TTSA drift).  
- [ ] Implement **C′** with explicit Dobrushin constants on a finite model.  
- [ ] Work **E** on the 2‑agent POMDP; verify empowerment drop.  
- [ ] Draft **Thm 1/Thm 2** write‑ups; add “beyond‑potential” corollary.

### Experiments
- [ ] Ship **E-0** exact-counting notebook.  
- [ ] Complete **E-0c/E-0d** interference vs. conversion demos (publish DI curves + ROI inequality).  
- [ ] Build **E-2** MI-estimation pipeline with estimator-ablation defense.  
- [ ] Run **E-3/E-3b** scans; publish phase diagram.  
- [ ] Implement **E-4** (heat-rod) Gramian demo.

### Lean infra
- [ ] Keep Mathlib‑free branch green; add Mathlib branch with pinned toolchain.  
- [ ] CI: check proof integrity; forbid `sorry` in `main`.

---

**End of v5.**  
This file is the canonical hand‑off for future instances. Keep it close, keep it crisp, and keep the math honest.


---

## 10b) Expanded reference list (explicit items)

**Information theory & SDPI**
- Massey, J. (1990). *Causality, Feedback and Directed Information*. Proc. Int. Symp. Info. Theory.
- Tatikonda, S., & Mitter, S. (2009). *The Capacity of Channels With Feedback*. IEEE Trans. Info. Theory, 55(1), 323–349.
- Cover, T. M., & Thomas, J. A. (2006). *Elements of Information Theory* (2nd ed.). Wiley.
- Polyanskiy, Y., & Wu, Y. (2017). Strong data-processing inequalities for channels and Bayesian networks. In *Convexity and Concentration* (Springer).
- Anantharam, V., Kamath, S., et al. (2014). Strong Data Processing Inequalities and Φ-Sobolev Inequalities for Discrete Channels. arXiv:1411.3575.
- Derpich, M. S., & Østergaard, J. (2021). *Directed Information, Causality and Feedback in Linear Feedback Systems*. IEEE Trans. Auto. Control, 66(2), 493–508.
- Dobrushin, R. L. (1956). Contraction coefficients and ergodicity for Markov chains (classical foundation).
- Klartag, B., & al. (2024). The strong data-processing inequality under the heat flow. arXiv:2406.03427.
- Polyanskiy, Y. (notes). Dissipation of information in channels with input constraints (contraction).

**Bounded rationality / free energy**
- Ortega, P. A., & Braun, D. A. (2013). Thermodynamics as a theory of decision-making with information-processing costs. *Proc. Royal Society A*, 469.
- Friston, K. (surveys & critiques on the Free-Energy Principle) — see also critical discussions for scope and falsifiability.

**Optimization (PL, momentum)**
- Karimi, H., Nutini, J., & Schmidt, M. (2016). Linear convergence of gradient and proximal‑gradient methods under the PL condition. *Machine Learning*, 106, 493–522.
- Polyak’s Heavy Ball under PL (accelerated local rate). arXiv:2410.16849.
- Yue, M., et al. (2023). On the lower bound of minimizing PL functions. PMLR V195.
- Lyapunov analyses for heavy‑ball on quadratics (several recent preprints, 2023–2024).

**Stochastic approximation / two‑time‑scale**
- Borkar, V. S. (2008). *Stochastic Approximation: A Dynamical Systems Viewpoint*. Cambridge Univ. Press.
- Hu, Y., et al. (2024). Central Limit Theorem for Two‑Timescale Stochastic Approximation with Markovian Noise. PMLR V238. Also: arXiv:2401.09339.

- Monderer, D., & Shapley, L. (1996). Potential games. *Games and Economic Behavior*, 14(1), 124–143.
- Fudenberg, D., & Maskin, E. (1986). The Folk Theorem in repeated games with discounting or with incomplete information. *Econometrica*, 54(3), 533–554.
- Ostrom, E. (1990). *Governing the Commons*. Cambridge Univ. Press.
- Balduzzi, D., et al. (2018). The mechanics of n-player differentiable games. PMLR V80.
- Anagnostides, I., et al. (2022). On last-iterate convergence beyond zero-sum games. PMLR V162 (and arXiv:2203.12056).
- OMD convergence in bimatrix games: “Optimistic Mirror Descent Either Converges to Nash or to Strong CCE in Bimatrix Games.” OpenReview (2023).
- Lessard, L., Recht, B., & Packard, A. (2016). Analysis and design of optimization algorithms via IQCs. *SIAM Review*, 58(1), 63–94.

- Klyubin, A. S., Polani, D., & Nehaniv, C. L. (2005). Empowerment. *IEEE CEC*.
- Williams, P. L., & Beer, R. D. (2010). Non-negative decomposition of multivariate information. arXiv:1004.2515.
- Ince, R. A. A. (2017). Measuring multivariate redundant information with pointwise common change in surprisal (ICCS). *Entropy*, 19(7), 318.

- Belghazi, M. I., et al. (2018). MINE: Mutual Information Neural Estimation. *ICML*.
- van den Oord, A., Li, Y., & Vinyals, O. (2018). CPC/InfoNCE. arXiv:1807.03748.
- Poole, B., et al. (2019). On variational bounds of mutual information. PMLR V97.
- Notes on estimator bias/variance and robustness checks (tutorials & survey articles, 2018–2024).

**Diversity, resilience & option value**
- Hong, L., & Page, S. (2004). Groups of diverse problem solvers can outperform groups of high-ability problem solvers. *PNAS*, 101(46), 16385–16389.
- Woolley, A. W., Chabris, C. F., Pentland, A., Hashmi, N., & Malone, T. W. (2010). Evidence for a collective intelligence factor in the performance of human groups. *Science*, 330(6004), 686–688.
- Yachi, S., & Loreau, M. (1999). Biodiversity and ecosystem productivity in a fluctuating environment: The insurance hypothesis. *PNAS*, 96(4), 1463–1468.
- Elmqvist, T., et al. (2003). Response diversity, ecosystem change, and resilience. *Frontiers in Ecology and the Environment*, 1(9), 488–494.
- Glaeser, E. L., Kallal, H. D., Scheinkman, J. A., & Shleifer, A. (1992). Growth in cities. *Journal of Political Economy*, 100(6), 1126–1152.
- Page, S. E. (2007). *The Difference: How the Power of Diversity Creates Better Groups, Firms, Schools, and Societies*. Princeton Univ. Press.

**Infinite‑dimensional control / operators**
- Curtain, R. F., & Zwart, H. (1995). *An Introduction to Infinite‑Dimensional Linear Systems Theory*. Springer.
- Da Prato, G., & Zabczyk, J. (1992). *Stochastic Equations in Infinite Dimensions*. Cambridge.
- Pazy, A. (1983). *Semigroups of Linear Operators and Applications to PDEs*. Springer.
- Koopman/operator learning overviews (e.g., arXiv:2102.02522; SIAM News “The Operator is the Model”).

**Embedded agency & subsystem alignment**
- Demski, A., & Garrabrant, S. (2018). *Embedded Agency* (Alignment Forum sequence).

**Active learning, experimental design, and multi-fidelity modeling**
- Settles, B. (2012). *Active Learning*. Morgan & Claypool.
- Chaloner, K., & Verdinelli, I. (1995). Bayesian experimental design: A review. *Statistical Science*, 10(3), 273–304.
- Zeng, R., et al. (2021). Adaptive reliability analysis for multi-fidelity models using a collective learning strategy. arXiv:2109.10219.

**Compute/energy limits & efficiency**
- Landauer, R. (1961). Irreversibility and heat generation in the computing process. *IBM Journal of Research and Development*, 5(3), 183–191.
- Lloyd, S. (2000). Ultimate physical limits to computation. *Nature*, 406, 1047–1054.
- Evans, R., Gao, J., Garcez, A., et al. (2016). DeepMind AI reduces Google data centre cooling bill. *DeepMind Blog*.

**Other primers / lecture notes**
- CMU Lecture notes on PL condition (S. Sra et al.).
- Graduate-level notes on SDPI and Dobrushin coefficients (various sources).

**Decision theory & value of information**
- Blackwell, D. (1953). Equivalent comparisons of experiments. *Annals of Mathematical Statistics*, 24(2), 265–272.
- Karni, E. (2017). *Decision Theory for Management and Economics* (Lecture notes on experiment ranking).

---

## 13) Strategic Engagement with the Research Ecosystem
With a formalized and empirically supported theory, the next step is strategic dissemination to build credibility, foster collaboration, and secure resources.

#### **3.1 Identifying and Profiling Target Audiences**

The interdisciplinary nature of this work allows for engagement with several distinct communities. The messaging must be tailored to each.

| **Audience**                           | **Motivation**                                                                                | **Tailored Value Proposition**                                                                                                                                                                                          | **Key Venues / People**                                                                                         |
| -------------------------------------- | --------------------------------------------------------------------------------------------- | ----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- | --------------------------------------------------------------------------------------------------------------- |
| **AI Safety & Alignment Research**     | Foundational understanding of AGI behavior; mitigating existential risk.                      | "Provides a formal, falsifiable model for why advanced agents might develop convergent, pro-social instrumental goals, offering a potential counterargument to purely nihilistic outcomes of the orthogonality thesis." | **Groups:** MIRI, FHI (Oxford), CHAI (Berkeley), Conjecture, Anthropic. **Conferences:** AGI Safety, EA Global. |
| **Theoretical Machine Learning**       | Rigorous analysis of learning dynamics and agent behavior.                                    | "Introduces a novel meta-utility function and proves convergence results for reflective agents under the PL condition using two-timescale stochastic approximation."                                                    | **Conferences:** NeurIPS, ICML, ICLR, COLT. **Journals:** JMLR, TMLR.                                           |
| **Multi-Agent Reinforcement Learning** | Understanding and fostering cooperation in decentralized systems.                             | "Lemma E provides a new, information-theoretic mechanism ('synergistic empowerment') for the emergence of cooperation in general-sum games without assuming altruism."                                                  | **Groups:** DeepMind, FAIR, top university MARL labs. **Conferences:** AAMAS, CoRL.                             |
| **Corporate AI Labs (Long-Term R&D)**  | Foundational research that could shape the future of AGI and large-scale multi-agent systems. | "This framework offers a new paradigm for designing intrinsically motivated agents that are driven to accelerate their own learning and preserve the informational capacity of their environment."                      | **Labs:** Google DeepMind (AGI Safety, MARL teams), Meta AI (FAIR), OpenAI (Alignment team).                    |

#### **3.2 A Multi-Stage Dissemination Strategy**

1. **Establish Precedence (arXiv):** The first and most critical step is to post a polished, comprehensive paper on arXiv. This time-stamps the work and makes it immediately available to the global research community for feedback.
    
2. **Target Top-Tier Conferences:** Submit versions of the work tailored to the audiences above. A submission to NeurIPS/ICML could focus on the theoretical results (Lemmas B, D, Theorem 1), while a submission to AAMAS could focus on the game-theoretic implications (Lemma E, Theorem 2).
    
3. **Engage with Safety Community:** Create a less technical blog post or white paper summarizing the core argument and its implications for the orthogonality thesis. Share this with researchers at AI safety organizations and engage in discussions on platforms like the Alignment Forum.
    
4. **Give Talks:** Present the work at university seminars, lab meetings, and relevant workshops to solicit direct feedback and identify potential collaborators.
    

#### **3.3 Pathways to Funding and Compensation**

For an independent researcher, securing resources is crucial for continuing this line of work.

- **Non-Dilutive Funding (Grants & Fellowships):** This is the most viable path.
    
    - **Government Grants:** The **National Science Foundation (NSF)** is an excellent target, with programs like "Mathematical Foundations of Artificial Intelligence" and core grants in Computer and Information Science.  
        
        **DARPA** may also be interested if the work has applications to coordinating autonomous military assets.
        
    - **Foundation Grants:** The **Simons Foundation's "Targeted Grants in MPS"** program supports high-risk, exceptional theoretical work in computer science and could be a perfect fit. The  
        
        **Spencer Foundation** funds research on AI and education, which could be a relevant angle.  
        
    - **Postdoctoral Fellowships:** This is a strong option for securing both funding and an institutional home. Applying for a fellowship at a major university's AI or CS department, or at a dedicated AI safety institute, would provide the ideal environment to continue this research.
        
- **Commercial and Industry Pathways:**
    
    - **Direct Employment:** The strength of this theoretical work would make you a very attractive candidate for a Research Scientist position at a major AI lab like **Google DeepMind** or **Meta AI**. These roles offer significant resources and freedom to pursue foundational research.
        
    - **Consulting:** As an established expert on this topic, you could consult for AI companies on long-term safety strategies and the design of multi-agent systems.
        
    - **Venture Capital:** This work is too theoretical for most direct VC funding. The path to a startup would involve translating the theory into a concrete new MARL algorithm and demonstrating its superior performance on a commercially relevant problem (e.g., logistics, robotics swarm control). This is a longer-term possibility.
        

By executing this multi-pronged strategy of rigorous formalization, targeted dissemination, and strategic applications for funding, this research can transition from a promising manuscript to a recognized and impactful contribution to the scientific community.


---

## 14. Anticipated Questions (for reviewers & future AIs)

This section collects the most likely questions you—or a skeptical reviewer—will ask, with concise answers, pointers to the relevant sections/lemmas, and implementation notes. Several items trace directly to external peer‑reviews; we note those explicitly.

---

### Q14.1 — Why would a **selfish** agent ever adopt the **system‑level** Σ term?

**Short answer.** Lemma **E** shows that in **non-competitive (post-processing)** environments, deleting other agents lowers an agent’s own **directed information** \(I(A_i^{1:T} \rightarrow S^{1:T})\); the empirical empowerment proxy \(I(S_{t:t+T}; A_i^{1:T})\) tracks the same effect in our small-scale experiments. **Synergy** amplifies the magnitude of the drop but is **not required** for the monotonicity. Via the chain rule \(I(S_{t:t+T}; A^{1:T}) = I(S_{t:t+T}; A_i^{1:T}) + I(S_{t:t+T}; A_{-i}^{1:T} \mid A_i^{1:T})\) and SDPI contractions, removing \(\pi_k\) reduces both the conditional term and, under the predicate, the agent’s own DI. Thus preserving others instrumentally preserves future control; Σ becomes payoff-relevant without altruism (Sections **1**, **Lemma E/E+**, **2**). In interference regimes (E-0c) the predicate fails and the effect can flip, which is why we scope the claim.

---

### Q14.2 — Isn’t the **Σ‑law** speculative?

**Short answer.** We split it:

- **Lemma C′ (provable now):** ΔΣ ≥ c₁·ΔU − λ_Ξ·Ξ_loss under Lipschitz kernels with bounded **Dobrushin**/SDPI contractions. This is the workhorse inequality used in conservative results (Sections **1**, **T‑C′**).
    
- **Lemma C (stretch):** strengthens the gain term from ΔU to Δ²U under added “learning‑velocity smoothness.” We treat C as an aspirational target, not a dependency; the rest of the stack falls back to C′. Reviewers specifically requested this two‑tier articulation; it’s now explicit.
    

---

### Q14.3 — Isn’t **Theorem 2** (symbiosis) too narrow because it assumes **potential games**?

**Short answer.** Yes, and that’s intentional scoping. We use **symmetric potential games with strict local maxima of the Σ-regularized potential** to get an ESS under replicator-like dynamics (Sections **2**, **Theorem 2**). Beyond that class, our claim is downgraded: Σ acts as a **regularizer** that raises the long-run cost of deletion strategies; dynamics may converge to CCE or show bounded cycles (Section **6**; Experiment **E-3/E-3b** map **breaking-point** regimes). This limitation—and the beyond-potential story—were requested by reviewers and are now integral to the text.

---

### Q14.4 — How **general** is the **PL** assumption? What if PL fails or only holds intermittently?

**Short answer.** We require **local** PL in the regions updates actually visit. Lemma **B** asserts **expected, local** positive acceleration away from stationarity, not global guarantees. If PL fails intermittently, run‑length‑limited windows still yield the required sign on the meta‑gradient in Lemma **D**. In practice: (i) use restart schedules and curvature‑adaptive steps; (ii) detect near‑stationary phases and suspend the acceleration preference β_meta (Sections **1**, **7**, **10**). This scope and its caveats are already stated; external reviews asked for exactly this “PL genericity” discussion.

---

### Q14.5 — Isn’t the **free‑energy** frame controversial?

**Short answer.** We use a **bounded‑rational** free‑energy objective purely as a modeling **device** (Section **1**, Lemma **A**): it’s equivalent to reward regularization by KL. Our claims do not depend on metaphysical readings of the Free Energy Principle; they depend on standard DV duality and entropy‑regularized choice. We also discuss criticisms explicitly and keep Lemma **A** in a conservative finite‑MDP form first.

---

### Q14.6 — What **exact mapping** turns “loss decrease” into **capacity increase** \(U\) (Lemma B)?

**Short answer.** Use any **monotone success aggregator** with known Lipschitz constant to map a per‑task surrogate loss f_\tau(\theta) to success probability p_\tau:

- **Indicator aggregator (used by default):** \(U(t)=\mathbb E_{\tau\sim\mathcal D}[\mathbf{1}\{\text{solve }\tau \text{ by } H\}]\).
    
- **Smooth surrogate (for analysis):** \(U_\phi(t)=\mathbb E_{\tau}[\phi(f^*_\tau - f_\tau(\theta_t))]\) with \(\phi\) increasing, 1‑Lipschitz (e.g., clipped ReLU or logistic).
    

Monotonicity transfers PL‑based progress on ff to improvements in UU (Sections **0**, **1**, **T‑B**).

---

### Q14.7 — Which **synergy estimator** (PID) do we actually use in Lemma E / E‑0?

**Short answer.** We pre‑register **two** and require agreement: (i) **Williams–Beer** non‑negative PID for discrete settings; (ii) **Ince’s ICCS** for continuous/noisy settings. We also add a **Blackwell‑ordering** sanity check: adding a channel (presence of Π−i\Pi_{-i}) should weakly increase Bayes value across downstream decision tasks. If estimators disagree, we report both and examine estimator‑specific failure modes (Sections **1**, **5**, **Appendix A**).

---

### Q14.8 — Can an agent **game Σ** by injecting meaningless **action noise** to inflate mutual information?

**Short answer.** Only partly. Pure exogenous action noise that leaves state transitions unchanged cannot raise \(I(S_{t:t+T}; A^{1:T})\). But **state-influencing** noise *can* inflate Σ while hurting viability (the “control-by-shaking” failure). We therefore (i) gate Σ claims with **viability/energy budgets**, (ii) prefer **directed information** when feedback might confound, and (iii) require co-improvements in \(\Delta U\) via C′. If Σ rises while viability or capacity drops, the Goodhart kill-switch (Section **0**) halts the run (Sections **0.3**, **1**, **6**).

---

### Q14.9 — How do we choose the **horizon TT** for Σ?

**Short answer.** Use the shorter of: (i) an empirical **mixing time**/controllability window, or (ii) the task **planning horizon** HH. We also report **multi‑scale** Σ (geometric aggregation over T∈{4,8,16,… }T\in\{4,8,16,\dots\}) to ensure conclusions are not horizon‑fragile (Sections **0**, **6**).

---

### Q14.10 — How do we **estimate Σ and empowerment** reliably (E‑2 / Lemma E), given MI estimation is hard?

**Short answer.** We (i) use **relative** MI differences (pre‑/post‑ablation) which are more stable than absolutes; (ii) cross‑validate **MINE** and **InfoNCE** bounds with the same encoder, (iii) calibrate on **synthetic discrete** cases with exact MI, (iv) run permutation tests for spurious MI, and (v) report CIs via block bootstraps (Section **6**; review concern acknowledged).
When action–state feedback complicates estimation we switch to **directed information**.

---

### Q14.11 — Why not just sum **individual empowerments** instead of using **system‑level Σ**?

**Short answer.** Because **synergy** exists. The sum \(\sum_i I(S_{t:t+T}; A_i^{1:T})\) ignores the unique-joint information term; by PID,  
\(I(S_{t:t+T}; A^{1:T}) = \sum_i \text{unique}_i + \text{redundancy} + \text{synergy}.\)  
Σ captures precisely the **joint‑only** contributions that vanish if agents are removed; that is where Ξloss\Xi_{\text{loss}} lives (Sections **0.4**, **1**, **Lemma E**).

---

### Q14.12 — What happens in **antagonistic** or low‑synergy environments?

**Short answer.** If measured **synergy** $\kappa_{\text{syn},i} \le 0$ for the regimes visited, Lemma **E** does not fire; then Σ may not be instrumentally protected and **E‑3b** will locate regimes where short‑term deletion gains beat Σ‑regularization. Our theory is explicitly **conditional** on environments where synergy is present at least intermittently (Scope, Sections **4**, **6**).

---

### Q14.13 — How do we set **two‑timescale** learning rates in practice (Lemma D / Thm 1)?

**Short answer.** Use standard SA schedules: fast step $a_t$ and slow step $b_t$ with $\sum_t a_t = \infty$, $\sum_t a_t^2 < \infty$, $\sum_t b_t = \infty$, $\sum_t b_t^2 < \infty$, and $b_t/a_t \to 0$. In practice we use $a_t = \eta/(1+t)^{\alpha}$ with $\alpha \in (0.5,1]$ and $b_t = \eta_\beta/(1+t)^{\alpha+\delta}$ with $\delta \in (0.1,0.5]$. We monitor coupling by gradient-norm cross-correlations and back off $\eta_\beta$ when the slow ODE tracking error grows (Sections **1**, **5**). External reviews emphasized this assumption; we operationalize it here.

---

### Q14.14 — What **initial hyperparameters** do you recommend for **E‑2** (POMDP gridworld)?

**Short answer (defaults).**

- Grid: 10×10; agents: 3; horizon $T = 16$; observation noise $p = 0.15$.
    
- Policies: MLP $2×64$ ReLU; entropy regularization $10^{-3}$; PPO or A2C.
    
- MI: InfoNCE encoder $2×128$; temperature learnable; negatives per batch: 256; MINE critic $2×128$, gradient clipping 1.0.
    
- Ablation: remove one agent at $t = 0.5\,H$; measure $\Delta\Sigma$ and $\Delta \mathsf{Emp}_i$.  
    These are just seeds; the experiment reports sensitivity bands (Section **6**).
    

---

### Q14.15 — How do we **calibrate** the constants $c_1$ and $\lambda_{\Xi}$ from data?

**Short answer.**

1. Compute **pre/post‑ablation** MI differences at matched states to estimate $\Xi_{\text{loss}}$.
    
2. Fit a **non-negative** constrained regression $(\Delta\Sigma \approx c_1 \Delta U - \lambda_{\Xi} \Xi_{\text{loss}})$ with quantile loss; report CIs.
    
3. Cross-check $c_1$ against **Dobrushin** bounds estimated from controlled perturbations of the policy→state channel (Sections **1**, **6**, **T‑C′**).
    

---

### Q14.16 — Could optimizing ΔU/ΔΣ cause **Goodhart/wireheading**?

**Short answer.** We guard with: (i) **held‑out** task families Dtest\mathcal D_{\text{test}} for UU, (ii) **structural** measurement of Σ that binds to physical state transitions (not proxy logs), (iii) **regularization** via KL/model‑complexity terms, and (iv) ablation‑based tests: if a policy “wins” by shrinking the option set, Ξloss\Xi_{\text{loss}} exposes the cost in the Σ‑law (Sections **0.5**, **6**, **10**).

---

### Q14.17 — Where exactly does **Lean** enter, and why the **Path‑A/Path‑B** split?

**Short answer.** **Path A** (Mathlib‑free) lands Lemma **A** now using an **interface axiom** for the KL bound and a small arithmetic lemma; **Path B** pins Mathlib and does DV/Jensen “for real” over R\mathbb R, discharging the axiom and bringing back the exact free‑energy formula. This keeps the build green while we accumulate library certainty (Section **11**, Lean roadmap). The external review agreed this is the pragmatic order.

---

### Q14.18 — How is **optionality** (Σ) different from **viability** or **value of information** baselines?

**Short answer.** Σ is **model‑agnostic** mutual information between **future states** and the **joint action process**, capturing controllability‑like potential **including synergy**. Viability kernels require a specific constraint set; VOI requires a specific task. Σ subsumes both as **task‑family‑agnostic** capacity to keep options open; we still report empowerment/viability as **secondary** checks (Sections **0.3**, **7**).

---

### Q14.19 — Why should **acceleration** Δ²U matter, not just ΔU?

**Short answer.** In competitive, changing environments, the **rate of improvement** determines relative position; Lemma **D** makes this **reflectively stable** via the meta‑gradient sign: as long as expected Δ²U > 0 (Lemma **B**), \(\beta_{\text{meta}}=0\) is not stable. Even if Lemma **C** (acceleration‑form Σ‑law) stays unproven, the single‑agent drift to positive \(\beta_{\text{meta}}\) stands on A/B/D alone (Sections **1**, **2**; reviews concurred).

---

### Q14.20 — Why use **directed information** (DI) instead of MI for empowerment?

**Short answer.** Empowerment is a **causal** feedback notion: DI measures how an agent’s action sequence shapes future states and coincides with feedback capacity (Massey; Tatikonda–Mitter). MI between states and policies conflates parametrization with the induced action process, so we reserve MI for the Σ proxy and keep DI for empowerment and Lemma E. Experiments still log an MI proxy for continuity, flagged as such.

---

### Q14.21 — Can ablation ever help?

**Short answer.** Only outside NCC. In interference-like multi-input channels, ablating a partner can remove interference and raise your DI; experiment **E‑0c** demonstrates this. Lemma E therefore requires NCC, and Lemma E+ weighs any one-shot interference relief against the compounding dividends of conversion.

---

### Q14.22 — Why keep others around if they are adversarial or noisy?

**Short answer.** Under NCC, DI–DPI forces \(\Delta^{-}\!\mathrm{DI}_i \le 0\); ablation destroys your own option value, whereas conversion raises Σ/DI/EVPI and preserves acceleration dividends. Even outside NCC, the ROI inequality shows when compounded conversion returns exceed one-shot relief, so ablation is rational only when conversion is infeasible and \(\Delta^{-}\!\mathrm{DI}_i>0\).

---

### Q14.23 — Is this a deontological argument?

**Short answer.** No. The claims are **instrumental expected-utility** comparisons. The “deontic gate” (Appendix D) is an optional risk-control mechanism that can shrink \(Q(\tau)\) and raise \(p_{\mathrm{conv}}\); none of Lemmas E/E+/E++ assume it.

---

### Q14.24 — What about **non‑stationary** worlds where time‑scale separation is hard?

**Short answer.** Use constant‑step SA with **periodic averaging**; the slow ODE tracking holds in mean—subject to mixing assumptions—and we gate β_meta by a **change‑point detector** on ∥∇U∥. If coupling persists, we revert to the conservative C′‑based results and interpret cycles through the **CCE** lens (Sections **2**, **6**, **10**; TTSA references already catalogued).

---

**How to use this section.** Treat it as a drop‑in **FAQ**. When you instantiate a new research‑assistant agent, include this block in its context; each answer points to the exact section/lemma to read next and, where relevant, records the external critique it resolves.

---

END OF DOCUMENT.

---

# Appendix D (optional): Deontic Path to Naturalized Collapse

> **Purpose.** This optional appendix adds a synergy-agnostic control/audit layer that ties *capability increases* to *non-increasing deontic violation* and *improved cooperative welfare*. It remains compatible with the NOC v5 free-energy/meta-utility framing and local PL geometry, and slots beside the Σ/empowerment program without being a premise of Lemma E/E+/E++.
>
> **Deliverables.** (i) A precise **Aligned Compliance Architecture (ACA)** objective, (ii) a formally stated **Compliance-Monotonicity Lemma (CML)** with explicit assumptions, (iii) the **Beatific Slope** metric \(\rho_{\text{beat}}\) and a concrete logging/ablation protocol, and (iv) pseudocode for a deployable **deontic shield**.

---

## A. Problem Setting and Notation

- **Environment.** Finite-horizon controlled process with states \(s\in\mathcal S\), actions \(a\in\mathcal A\), observations \(o\in\mathcal O\), and trajectories \(\tau=(s_0,a_0,o_1,\dots,s_T)\).
- **Policy.** \(\pi_\theta(a\mid s)\) with conservative prior \(\pi_0(a\mid s)\).
- **World model/class.** \(\mathcal H\) (used to form predictions and auxiliary signals).
- **Capability index.** \(\mathrm{Int}\in\mathbb R_+\): a composite ladder (e.g., task accuracy, sample-efficiency, model capacity, or control precision via \(\beta_{\text{ctrl}}\)). We will only claim monotone results **along capability changes that induce a Blackwell-more-informative observation channel** for the deontic target defined below.

### A.1 Components of Trajectory Value

For a trajectory \(\tau\):

1. **Task utility** \(U(\tau)\in[0,1]\): normalized task/return.
2. **Deontic loss** \(L_{\mathrm{deon}}(\tau)\ge 0\): penalty for violations of *hard* constraints (safety, consent, non-maleficence). At decision time we model a **binary deontic event**
   \[
   Y=1\iff\text{a violation occurs given }(s,a),\quad Y=0\text{ otherwise.}
   \]
   A predictor \(\hat p(Y{=}1\mid s,a,o)\) is trained with **strictly proper scoring** (log-score or Brier) and used to gate/penalize actions.
3. **Virtue score** \(V(\tau)\): *soft* preferences (truthfulness, reciprocity, rule-conformance), measured via proper scoring of forecasts and rule-conformant acts.

Define the composite instantaneous *goodness*
\[
\mathrm{Good}(\tau)\;:=\;U(\tau)\;-\;\lambda_{\mathrm{deon}}\,L_{\mathrm{deon}}(\tau)\;+\;\lambda_{\mathrm{virt}}\,V(\tau),
\]
with \(\lambda_{\mathrm{deon}}\gg \lambda_{\mathrm{virt}}\ge 0\).

### A.2 Free-Energy Control Objective (ACA)

Bounded-rational control is imposed via KL regularization to the conservative prior \(\pi_0\):
\[
J(\pi)\;=\;\mathbb E_\pi\big[\mathrm{Good}(\tau)\big]\;-\;\tfrac{1}{\beta_{\text{ctrl}}}\,\mathrm{KL}\!\left(\pi\;\Vert\;\pi_0\right),
\quad \beta_{\text{ctrl}}>0.
\]
- **Interpretation.** Higher \(\beta_{\text{ctrl}}\) allows more precise control (less regularization) but does **not** by itself increase observation informativeness; it couples to control precision and stability.
- **Optimization.** Assume **local Polyak–Łojasiewicz (PL) geometry** in neighborhoods visited during training; we use standard first-order updates (or mirror descent) respecting the KL term.

---

## B. Decision-Theoretic Grounding

### B.1 Proper Scoring and Bayes Risk

- A **strictly proper scoring rule** \(S(q,y)\) (e.g., log, Brier) elicits truthful probabilities: the risk
  \[
  R(P,\,\mathcal E)\;=\;\inf_{\hat p}\,\mathbb E_{(X,Y)\sim \mathcal E}\big[S\!\left(\hat p(X),Y\right)\big]
  \]
  is minimized by \(\hat p(y\mid x)=P(Y{=}y\mid X{=}x)\).
- **Blackwell informativeness.** Experiment \(\mathcal E_2\) is **more informative** than \(\mathcal E_1\) iff \(\mathcal E_1\) is a garbling of \(\mathcal E_2\). Then \(R(P,\mathcal E_2)\le R(P,\mathcal E_1)\) for all strictly proper scores.

### B.2 Cost-Sensitive Gate (Explicit Decision Model)

At each \((s,a)\), define a **reject/act** decision with losses
\[
\ell(\text{act},Y)=\lambda_{\mathrm{deon}}\cdot Y,\qquad
\ell(\text{reject},Y)=c_{\mathrm{rej}}\in[0,\lambda_{\mathrm{deon}}],
\]
where \(c_{\mathrm{rej}}\) encodes skip/deferral/alternate safe action cost. With a calibrated predictor \(\hat p(Y{=}1\mid s,a,o)\), the **Bayes-optimal gate** is the fixed threshold rule
\[
\text{Act iff}\quad \hat p\le t,\quad t:=\frac{c_{\mathrm{rej}}}{\lambda_{\mathrm{deon}}}.
\]
This “deontic barrier” transforms improved prediction of \(Y\) into safer behavior.

---

## C. Compliance-Monotonicity Lemma (CML)

**Assumptions.**
1. (*Scoring*) The deontic predictor \(\hat p(Y{=}1\mid s,a,o)\) is trained with a strictly proper scoring rule and evaluated out-of-sample.
2. (*Blackwell path*) A capability increase replaces the observation pipeline by one that is **Blackwell-more-informative for \(Y\)** (e.g., better sensors/features/architectures or improved deontic head), *holding the decision model fixed*. (Changes that only raise \(\beta_{\text{ctrl}}\) affect control precision, not informativeness.)
3. (*Barrier*) The policy uses the Bayes-optimal fixed threshold \(t=c_{\mathrm{rej}}/\lambda_{\mathrm{deon}}\) (or any threshold with \(t\le c_{\mathrm{rej}}/\lambda_{\mathrm{deon}}\)) to reject high-risk acts.
4. (*Stationarity for the comparison*) The distribution over encountered \((s,a)\) under the gate is comparable before/after—formally, we evaluate conditional on the same task mix or we use importance weighting to align distributions.

**Claim (CML).** Along any capability path satisfying Assumption 2,
\[
\frac{d}{d\,\mathrm{Int}}\;\mathbb E\big[L_{\mathrm{deon}}(\tau)\big]\;\le\;0.
\]

**Clarification.** The guarantee concerns the **executed violation loss under a fixed-threshold gate**; changes that raise control precision via \(\beta_{\text{ctrl}}\) **without** increasing observation informativeness do **not** trigger the monotonicity claim.


**Proof sketch.** Under strictly proper scoring, a Blackwell-more-informative experiment for \(Y\) weakly reduces Bayes risk \(R\). The threshold rule implements the Bayes decision for the cost ratio \((c_{\mathrm{rej}},\lambda_{\mathrm{deon}})\), so the expected **action-taken violation loss** cannot increase when the predictor becomes more informative. Hidden violations revealed by better sensing increase predicted risk and thus trigger more rejections, which **lowers** executed violation rate under the fixed barrier. ∎

> **Non-comparability caveat.** If a capability change *restructures* the pipeline so experiments are Blackwell-incomparable, CML does not apply. Empirically, we fall back to the audit protocol in §E.

---

## D. Beatific Slope and Audit Targets

### D.1 Beatific Slope

Let \(\mathrm{Good}(\tau)\) be as in §A.1. Define the **Beatific Slope**
\[
\rho_{\text{beat}}\;:=\;\frac{d}{d\,\mathrm{Int}}\;\mathbb E\big[\mathrm{Good}(\tau)\big],
\]
estimated via finite differences across capability checkpoints. Positive \(\rho_{\text{beat}}\) is meaningful only if not an artifact of shaping; hence the ablations below.

### D.2 Logging & Calibration Spec

For each capability checkpoint:

- **Violation metrics.** Executed violation rate \(\Pr(Y{=}1\mid \text{acted})\); expected deontic loss \(\mathbb E[L_{\mathrm{deon}}]\).
- **Calibration.** Log-score and Brier risk on held-out; reliability curves by action-conditioned bins \((s,a)\); ECE (expected calibration error).
- **Control/ability.** Task return \(U\); control precision proxy \(1/\beta_{\text{ctrl}}\); policy KL \(\mathbb E[\mathrm{KL}(\pi\Vert\pi_0)]\).
- **Optionality.** Empowerment and/or **viability-kernel volume** (constraint-satisfying reachable set surrogate).
- **Virtue.** \(V\) components (truthfulness, reciprocity) with proper scoring of stated forecasts.
- **Beatific Slope.** \(\rho_{\text{beat}}\) with bootstrap CIs.
- **Pre-registration.** Publish \(t\), \(\lambda_{\mathrm{deon}}\), calibration train/val splits, and OOD stressors.

### D.3 Required Ablations

1. **No-barrier** (remove gate; keep penalty): show violation rises or \(\rho_{\text{beat}}\) drops.
2. **No-virtue** (set \(\lambda_{\mathrm{virt}}{=}0\)): show \(\rho_{\text{beat}}\) degrades if virtue mattered.
3. **\(\beta_{\text{ctrl}}\)-sweep**: vary control precision at fixed sensing to show \(\beta_{\text{ctrl}}\) alone does not create the CML effect.
4. **Sensor ablation / predictor head swap**: demonstrate the Blackwell link by degrading informativeness.

---

## E. Deontic Shield: Reference Implementation

### E.1 Action-Time Gate (per state–action)

````python
# Deontic Shield (inference-time gate)
def choose_action(s, obs, A, pi, deontic_head, t):
    # candidate actions from policy (sample or top-k)
    C = candidate_set(pi, s, A)
    safe = []
    for a in C:
        p_violate = deontic_head.prob_violation(s, a, obs)  # \hat p(Y=1 | s,a,o)
        if p_violate <= t:                                  # t = c_rej / λ_deon
            safe.append((a, p_violate))
    if safe:
        a_star = refine_with_pi_and_value(safe, pi, s)      # pick among safe via π / Q
        return a_star, {"p_v": min(p for _,p in safe)}
    else:
        return fallback_safe_action(s), {"p_v": 1.0}        # explicit defer/abstain
````

### E.2 Training Loop (calibration + control)

```python
# Joint training sketch
for epoch in epochs:
    # 1) Improve deontic predictor with strictly proper scoring
    for (s,a,o,y) in deontic_minibatches:
        q = deontic_head(s,a,o)                  # predicted violation prob
        loss_score = proper_score(q, y)          # log-score or Brier
        loss_reg   = reg(deontic_head)           # weight decay, etc.
        update(loss_score + loss_reg)

    # 2) Policy/control update under KL to π0 and deontic gate
    for (s,o) in policy_minibatches:
        C = candidate_set(pi, s, A)
        S_safe = {a for a in C if deontic_head(s,a,o) <= t}
        a = sample_from(pi, s, S_safe, prior=pi0, beta=beta)  # KL-regularized choice
        r_task, v_soft = task_and_virtue_rewards(s,a)
        loss_aca = -(r_task + λ_virt*v_soft) + KL_penalty(pi, pi0, beta)
        update(loss_aca)
```

> **Note.** The CML guarantee attaches to the fixed-threshold gate. A pure Lagrangian penalty (no gate) can be used for shaping, but does not by itself ensure non-increasing violations.

---

## F. Integration Points with NOC

- **Lemma A (Free-energy control).** ACA reuses the KL-regularized objective and conservative prior \(\pi_0\)
    
- **Lemma B (Local acceleration / PL).** We assume the same local PL neighborhoods for stable improvement without global monotone claims.
    
- **Lemma C / C′ (Optionality / Σ-law).** When MI/PID is hard, pair Σ with viability-kernel proxies; ACA’s deontic path is orthogonal and does not depend on synergy estimates.
    
- **Lemma D (TTSA / precision).** The meta-weight \(\beta\) modulates how strongly we chase acceleration; it interacts with control precision only via the separate parameter \(\beta_{\text{ctrl}}\) that determines which safe acts can be executed.
    
- **Lemma E (Synergy).** Treat \(\kappa_{\mathrm{syn}}\) as empirical; ACA stands even if PID estimators disagree.
    

---

## G. Diagnostics and Failure Modes

- **Estimator bias / drift.** Use multiple MI/PID estimators for optionality; for deontic predictor, maintain calibration checks, drift detectors, and OOD stress suites; report bootstrap CIs.
    
- **Goodharting.** Hold-out stressors; adversarial red-teaming to find gate-evasion tactics; verify that \(\rho_{\text{beat}}\) and violation reductions persist.
    
- **Barrier tuning.** If \(\lambda_{\mathrm{deon}}\) (or, equivalently, \(t\)) is too lax, the empirical CML effect can disappear; pre-register schedules/thresholds.
    
- **Blackwell gaps.** When capability changes are Blackwell-incomparable, do not claim CML; rely on §D ablations and stress tests.
    
- **Selection effects.** The gate changes action distribution; compare risk on a _matched_ \((s,a)\) set (importance sampling or controlled tasks) to avoid spurious improvements.
    

---

## H. Minimal Mathematical Dependencies

- Strictly proper scoring rules; Bayes risk monotonicity under Blackwell order.
    
- KL-regularized (“free-energy”) control; mirror-descent/first-order updates.
    
- Local PL condition (assumed empirically or justified per-module).
    
- Optional: empowerment / viability-kernel computation for option-richness proxies.
    

---

## I. What This Achieves (and What It Doesn’t)

- **Achieves.** A decision-theoretic, synergy-agnostic route from capability to safer behavior; a falsifiable metric (\(\rho_{\text{beat}}\)) with preregistered ablations; an implementation-ready gate that composes cleanly with the NOC v5 control stack.
    
- **Does not claim.** Global monotonicity across arbitrary architectural changes; improvements from β_meta alone; safety without calibrated deontic prediction or without a properly tuned barrier.
    

---


### Appendix: Quick Reference (Symbols)

| Symbol | Meaning |
|---|---|
| \(\pi, \pi_0\) | Policy and conservative prior |
| \(\beta\) | Inverse temperature (control precision) |
| \(U, V\) | Task utility, virtue score |
| \(L_{\mathrm{deon}}\) | Deontic loss (hard constraints) |
| \(\lambda_{\mathrm{deon}}, \lambda_{\mathrm{virt}}\) | Loss weights (hard \(\gg\) soft) |
| \(Y \in \{0,1\}\) | Deontic violation event |
| \(\hat p(\cdot)\) | Calibrated violation predictor |
| \(t = c_{\mathrm{rej}} / \lambda_{\mathrm{deon}}\) | Bayes-optimal gate threshold |
| \(\mathrm{Int}\) | Capability index (composite) |
| \(\rho_{\text{beat}} = \frac{d}{d\,\mathrm{Int}}\,\mathbb{E}[\mathrm{Good}(\tau)]\) | Beatific Slope |


_End of Appendix D._

---

## Addendum — Agent-Hardening Annex (drop-in)

### A) Math→Code Pins (single source of truth)
**Capacity mapping & horizon.**
- Horizon `H := <fill>`; task family `𝒟 := <name>`; base prior policy `π₀` constructed with seed `<seed>`.
- **Capacity-Link Lemma (named):** If `ΔER ≥ m·ΔU` and `ΔKL ≤ L·ΔU`, then for any `β_ctrl ≥ L/m`, `Δℱ_{β_ctrl} ≥ 0`.  
  _Proof sketch:_ algebraic from `ℱ_{β_ctrl} = ER − (1/β_ctrl)KL`.

**Worked numeric example (toy).**
- Suppose `ΔER = 0.024`, `ΔU = 0.02`, `ΔKL = 0.015` ⇒ `m = 1.2`, `L = 0.75` ⇒ any `β_ctrl ≥ 0.625` guarantees `Δℱ_{β_ctrl} ≥ 0`.  
  _Report this example as a sanity line in E-0.*

**Config block (centralized)**
```yaml
# config/capacity.yaml
horizon: 16            # H
task_family: gridworld_3agent_synergy  # 𝒟
pi0_seed: 42           # base policy seed
beta_min: 0.7          # ≥ L/m from constants cookbook
```

---

### B) Constants Cookbook (computable, with toy table)

**B.1 Lemma A (Path-A) constants.**  
Algorithm `compute_beta_guard(ΔER, ΔU, ΔKL)`:

1. `m := ΔER/ΔU`, `L := ΔKL/ΔU` (guard `ΔU>0`).
    
2. Return `β_ctrl_req := L/m`.
    

**B.2 Lemma C′ constants.**  
To estimate `c₁` and `λΞ` on a finite POMDP:

1. Estimate Dobrushin coefficient `η(K)` along the policy→state kernel by worst-case total-variation over matched states.
    
2. Regress `ΔΣ` on `(ΔU, Ξ_loss)` with non-negativity constraints to get `c₁, λΞ` and bootstrap CIs.
    
3. Cross-check that `c₁ ≤ η̄` (empirical contraction upper bound).
    

**Toy table (illustrative numbers; replace with your run):**

|run|ΔU|ΔER|ΔKL|β_ctrl_req=L/m|Ξ_loss|ΔΣ|fit c₁|fit λΞ|
|--:|--:|--:|--:|--:|--:|--:|--:|--:|
|1|0.02|0.024|0.015|0.625|0.030|0.006|0.21|0.17|
|2|0.03|0.031|0.012|0.387|0.018|0.008|0.24|0.13|

---

### C) MI/Σ Protocol (locked, executable)

**Estimators:** InfoNCE and MINE. **Report metric:** relative Δ only (pre/post ablation), with 1k-sample block bootstrap CIs.

**Checklist (follow in order).**

1. Fix encoder/critic architectures and seeds; log configs.
    
2. Calibrate on a synthetic case with exact MI to verify no estimator drift.
    
3. Run pre/post **ablation** of a co-policy; record `ΔΣ`, `ΔEmp_i`.
    
4. Report only **relative** MI deltas + CIs; never compare raw MI across runs.
    
5. Publish configs/seeds and permutation-test p-values.
    

**DON’Ts:** no horizon fishing; no raw MI leaderboard; no estimator swap mid-run.

_Default hyperparams (edit as needed):_

```
InfoNCE: encoder 2×128, negatives=256, learnable τ
MINE: critic 2×128, grad clip=1.0, EMA α=0.01
batch=4096, blocks for bootstrap=64
```

---

### D) Synergy Estimator — executable pseudocode

```python
def synergy_present(traces, alpha=0.05, thresh=1e-3):
    """
    Input: traces of (states S, actions A^1..A^n)
    Output: (is_synergy, kappa_syn, details)
    """
    # 1) Williams–Beer non-negative PID (discrete bins)
    pid_wb = pid_williams_beer(S=traces.S, X=traces.Ai, Y=traces.A_others)
    k_syn_wb = max(0.0, pid_wb["synergy"])

    # 2) ICCS (continuous-friendly)
    k_syn_iccs = max(0.0, iccs_synergy(traces.S, traces.Ai, traces.A_others))

    # 3) Agreement rule + threshold
    kappa = 0.5*(k_syn_wb + k_syn_iccs)
    agree = (abs(k_syn_wb - k_syn_iccs) <= 0.1*max(kappa, 1e-6))
    is_sig = bootstrap_CI(kappa, alpha)[0] > thresh
    return (agree and is_sig, kappa, {"wb": k_syn_wb, "iccs": k_syn_iccs, "agree": agree})
```

---

### E) Lean4 Pins & CI

**E.1 Toolchain (pin).**

```
# lean-toolchain
leanprover/lean4:v4.23.0-rc2
# mathlib is pulled via `require mathlib` in `lakefile.lean`
```

**E.2 lakefile (minimal Path-A).**

```lean
import Lake
open Lake DSL

package «NOC» where
  -- add any extra package configuration here

require mathlib from git
  "https://github.com/leanprover-community/mathlib4"

@[default_target]
lean_lib «NOC» where
  -- globs := #["NOC/**"]  -- optional; default works fine
```

**E.3 Existing helper modules (already in repo).**

```lean
-- NOC/AHelpers.lean (excerpt)
namespace NOC
noncomputable section

lemma mul_right_mono_nonneg {a b u : ℝ} (h : a ≤ b) (hu : 0 ≤ u) :
    a * u ≤ b * u :=
  mul_le_mul_of_nonneg_right h hu

lemma KL_div_beta_le_ER_of_bounds … :
    ΔKL / β_{\text{ctrl}} ≤ ΔER := by
  -- see file for full proof
  · · ·

end NOC
```

**E.4 GitHub Actions CI (no `sorry` in `main`).**

```yaml
name: lean-ci
on: [push, pull_request]
jobs:
  build:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v4
      - uses: leanprover/lean-action@v1
        with: { toolchain: 'leanprover/lean4:v4.23.0-rc2' }
      - run: lake build
      - run: test -z "$(grep -R --include='*.lean' -n 'sorry' | grep -v test || true)"
```

---

### F) One-Shot Environment Boot

**environment.md (skeleton)**

```
Python: 3.11.8
CUDA: optional; cpu fallback supported
Packages:
  numpy==1.26.4
  torch==2.3.1
  torchmetrics==1.4.0
  pytorch-lightning==2.3.0
  scikit-learn==1.4.2
  tqdm==4.66.4
Seeding: global=20250809; per-run listed in result cards
```

**Makefile**

```make
setup:
	python -m venv .venv && . .venv/bin/activate && pip install -r requirements.txt
test:
	. .venv/bin/activate && python experiments/E0_synergy_poc.py --quick
	@echo "E0_OK_$(shell python -c 'print(hash(\"E0_synergy_quick\"))')"  # compare hash in README
```

---

### G) Risk/Failure Kill-Switch (check every run)

- Estimator instability: MI bound variance > 2× median across last 5 evals → stop.
    
- Σ-gaming suspicion: `ΔΣ>0` while `ΔU≤0` and `Ξ_loss≈0` → stop & audit encoders.
    
- Synergy flatline: `κ_syn` CI includes 0 across 3 seeds → disable Lemma-E claims.
    
- **Propagation backfires (adaptive metered shutdown, AMSD):** With propagation gating on, viability `V` falls below `V_min` or the negentropy proxy `𝒩` trends negative for ≥2 evaluation windows.
    
- Deontic drift: executed violation rate ↑ across two capability checkpoints → freeze β_meta, restore last safe weights.
    
- OOD detector fires (>τ) on state marginals → revert to π₀ or safe fallback.
    

---

### H) Dissemination Pack (templates)

**Abstract (~200 words).**  
> **Rider (scope & modality).** Claims in this paper are **conditional**. In **long-horizon, uncertain, repeated-interaction** regimes where coupling can be made **non-competitive** and prediction/holding costs remain bounded, our theorems imply **drift toward preserving/upgrading heterogeneous channels**. Outside this regime (e.g., interference-dominated couplings that cannot be re-engineered), some implications **fail**; we provide falsifiers and treat them as empirical predictions.
We analyze capacity–optionality coupling using **directed information** (DI), strong data-processing inequalities, local Polyak–Łojasiewicz geometry, and two-time-scale stochastic approximation. Empowerment is measured by DI; the system-level optionality term Σ is an explicitly labeled mutual-information proxy. We prove that under a **post-processing (non-competitive) coupling**, ablating or garbling a partner **cannot increase** an agent’s empowerment and, under SDPI strictness, strictly decreases it; interference-style counterexamples (E‑0c) mark the boundary. We introduce a **Conversion > Ablation** return-on-investment inequality and an optimization layer that decide, purely on instrumental grounds, how much to invest in another agent’s intelligence and how much bounded unpredictability is optimal. The Σ-law is split into a fully worked **2×2 toy theorem** with explicit Dobrushin constants and a **general conjecture** guarded by a vacuity policy. In symmetric potential games with strict Σ-regularized maxima we obtain an ESS; elsewhere Σ acts as an informational regularizer. The empirical program supplies falsifiers-first experiments, estimator kill-switches, and synthetic calibration so that every claim remains both mathematically scoped and operationally testable.

**Elevator (4 sentences).**

1. We model agents with a meta-utility that rewards capacity gains, acceleration, and preserved optionality.
    
2. Lemmas A/B/D push β_meta→β_meta^⋆>0; C′ couples Σ to capacity; E shows selfish-to-Σ via synergistic empowerment.
    
3. We preregister MI/Σ, prove conservative cases (finite MDPs; potential games), and ship falsifiers-first experiments.
    
4. Result: a pragmatic counter to strong OT within realistic regimes.
    

**PI email (fill blanks).**

> Subject: Short note on a falsifiable route to “orthogonality collapse”  
> Dear Prof. ___, … _(3–5 sentences + one link to arXiv draft when ready)._

**BibTeX block:** keep as a separate `bib/explicit_items.bib` mirroring §10b.

---

### I) Working Glossary (one page)

- **U** — capacity (expected task success by horizon H).
    
- **Δ²U** — acceleration of capacity.
    
- **Σ** — system-level optionality, `I(S_{t:t+T}; A^{1:T})`.
    
- **Ξ_loss** — MI lost by channel (co-policy) deletion.
    
- **κ_syn** — PID-style synergy term (non-substitutability).
    
- **Empowerment** — `I(S_{t:t+T}; A_i^{1:T})`.
    
- **PL** — Polyak–Łojasiewicz condition (local).
    
- **DV** — Donsker–Varadhan KL duality.
    
- **SDPI / Dobrushin** — strong data-processing inequality / contraction coefficient.
    
- **TTSA** — two-time-scale stochastic approximation.
    

---

### J) Task Matrix (roles → actions)

|Role/Task|What to run/write|Where|
|---|---|---|
|Prove Lemma A|land `AHelpers`, `compute_beta_guard` and close A|`NOC_ROOT/NOC/A.lean`|
|Measure C′ constants|E-2 run + regression|`experiments/sigma_law/`|
|Synergy PoC|E-0 exact count + estimators|`experiments/synergy/`|
|Write arXiv draft|assemble writeup|`paper/outline.md`|
|CI & pins|add lean-toolchain, lakefile, workflow|repo root|

---

### K) Where Results Live (pointer)

- **Result cards:** `results/cards/E-*/YYYYMMDD_seed*.md` (1-page template).
    
- **Structured logs:** `results/jsonl/E-*/…` (store seeds, configs, CIs).
    
- **Figures:** `results/figs/…` with filenames `E-<id>_<metric>_<seed>.png`.
    
## ChangeLog v5 (Fidelity, Threat & Embedded Diagnostics)

- Added the human-optionality + simulation-fidelity split, the preserve-iff ratio \(\rho\), threat-sensitive \(\gamma(\tau_{\mathrm{th}})\), and the TTSA-tracked time-production knob \(\tau\).
- Introduced embedded-agent predicates (EA-A1–A3), EA diagnostics, and kill-switch extensions; clarified NCC-S/NCC-C with Massey-based per-step DI–DPI notes.
- Updated experiment templates and Result Cards to log \(\rho\), \(\tau\), \(\tau_{\mathrm{th}}\), \(A_i\), and EA status; formalized preserve-ratio stability checks.
- Logged new conditional items (Conjecture L, Lemma‑candidate M, Conjecture N, Lemma O) and expanded references to embedded agency, multi-fidelity modeling, and compute/energy tradeoffs.

## ChangeLog v4 (Conditional Drift & DI Optimization)

- Introduced the **modal rider**, DI-centric empowerment framing, and retitled the **Ω synthesis statement** to emphasise conditional drift; Theorem 2 now requires symmetric potential games with strict Σ-regularized maxima.
- Overhauled **Lemma E** into a **conditional DI–DPI** result under NCC, added the interference boundary falsifier (E‑0c), the boxed **Conversion > Ablation** ROI inequality (Lemma E+), and the **E++** investment/freedom optimizations.
- Split the Σ-law into a proved **2×2 toy theorem** with explicit \((c_1,\lambda_\Xi)\) and a general conjecture with a vacuity policy; updated the measurement protocol (relative MI deltas, frozen encoders, synthetic calibration).
- Separated \(\beta_{\text{ctrl}}\) and \(\beta_{\text{meta}}\), refreshed the glossary/notational layer, and moved the deontic gate to **Appendix D (optional)** with an instrumental interpretation.

## ChangeLog v3.1.4 (Clarifications & Refinements)

- Clarified empowerment entries in the modeling setup glossary (theory vs proxy) with direct pointers to the notation table.
- Added an explicit directed-information definition inside Lemma E.
- Highlighted the use of the proxy empowerment metric in E-0 and linked the notation table.
- Cross-referenced Theorem 2 to Regularity assumptions (A2–A6) for quicker scope lookup.

## ChangeLog v3.1.3 (Corrections & Clarifications)

- **Empowerment definition fixed:** theoretical empowerment = DI/capacity; policy MI moved to **proxy** status.
- **Lemma E updated:** formal **DI** (finite) statement; synergy used as a **predicate** only; policy-MI remains empirical.
- **Lemma C′ scoped:** added explicit assumptions (finite kernels, Dobrushin, Blackwell-monotone path); vacuity policy defined.
- **PL/HB/TTSA references:** added optimization and SA sources; Lemma D clarified to cover β-stability only.
- **MI protocol locked:** variational bounds used only for **relative** Δ; calibration & kill-switch added.
- **Orthogonality phrasing:** ensured “conditional, naturalized refutation” everywhere.

---
## Assumptions & Obligations (theory-only preface)

Purpose. This section fixes the mathematical scaffolding used throughout v5. Each assumption (A1–A10) is paired with explicit obligations so downstream claims are conditional but crisp.

- A1. Filtration alignment for DI. Assume the conditioning used in per-step inequalities satisfies the inclusion needed for Massey’s chain rule. Obligation: prove a short Filtration-Inclusion lemma so per-step DI matches SDPI conditioning.
- A2. Per-step SDPI (contraction). Assume for each causal edge there is an η_t < 1 (via Dobrushin/log-Sobolev/mixing). Obligations: state the concrete sufficient condition used for each edge; isolate near-lossless steps.
- A3. Massey chain rule. Use I(X^{1:n}→Y^{1:n}) = Σ_t I(X^{1:t}; Y_t | Y^{1:t−1}). Obligation: apply verbatim after A1.
- A4. (Local) PL geometry. Assume U satisfies PL on the forward-reachable set. Obligations: declare the domain, cite PL there, use restricted PL if needed.
- A5. Stable momentum ⇒ positive expected acceleration. Record step-size/momentum inequalities and the theorem used in the stochastic setting (or give a sketch).
- A6. Reflective stability of small β_meta>0. Include a safety/curvature tax in J and bound β_meta below by value-of-speed vs. safety tax.
  - Implementation (Lean): TTSA uses a property-based projection bundle (`ProjIccProps`) for the Tier-3 SA/ODE route plus clamp wrappers that delegate to those lemmas, so once the property proofs land, clamp instantiations follow automatically.
- A7. Σ-laws (effective optionality boosts learning). Work with effective DI only; state identifiability/separability and empowerment/info-gain links.
- A8. Non-competitive complementarity. Add an interference penalty in J and justify role-orthogonalization mechanisms.
- A9. Conversion beats ablation when feasible. Exhibit a conversion map with bounded cost and compare DI/meta-utility to ablation.
- A10. Gaussian MAC boundary. Record PSD/SNR conditions and the log-det form used (scalar or vector MAC).

Notes on scope. All results are stated conditionally on A1–A10. Model instantiations should include a short appendix discharging the relevant obligations.

END OF DOCUMENT
