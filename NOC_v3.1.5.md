# Naturalized Orthogonality Collapse under Capacity–Optionality Coupling — **v3.1.5 (TTSA & DI Spec Update)**

**Status**: Finalized, self-contained research blueprint (theory + proof plan + experiments + Lean4 roadmap).  
**Purpose**: Equip any fresh AI instance (or human collaborator) with everything needed to continue the project without external context.  
**Lineage**: Integrates **v1.5 (consolidated)**, incorporates the substantive feedback from the rigorous peer-reviews, and folds in the useful structural upgrades from **v2 (draft)** (proven-vs‑conjecture table, synergy up-front, E‑0 scout, Lean skeleton).

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

We model agents that optimize a bounded‑rational **meta‑utility**
\[
M_i \;=\; \alpha\,\Delta U_i \;+\; \beta\,\Delta^2 U_i \;+\; \gamma\,\Delta\Sigma \;-\; \lambda\,\mathrm{KL}(\pi_i\Vert \pi_i^{\text{base}})\;-\;\zeta\,J_i,
> \]
where \(U\) is **general task capacity** (expected task success across a non‑degenerate task family \(\mathcal D\)), \(\Sigma\) is a **system‑level optionality reservoir**
\(\Sigma(t) := I(S_{t:t+T}; A^{1:T}(t))\) (mutual information between a T‑step future and the **joint action process** induced by \(\Pi\)), and \(J_i\) denotes other complexity/actuation costs.

In theoretical statements we evaluate empowerment via **directed-information capacity**; the mutual-information proxy (I(S_{t:t+T}; A_i^{1:T})) appears only in empirical analyses.

**Core spine (conservative tier):**

- **Lemma A** (capacity‑compatible drift): bounded‑rational updates in uncertain task families create monotone drift toward higher \(U\).
- **Lemma B** (PL + momentum): away from stationarity, expected acceleration \(\mathbb E[\Delta^2 U] > 0\).
- **Lemma D** (β‑stability): \(\beta=0\) is reflectively unstable off‑optimum; meta‑dynamics drift to some \(\beta^\star>0\).
- **Lemma C′** (Σ‑law, improvement): \(\Delta\Sigma \ge c_1\,\Delta U - \lambda_\Xi\,\Xi_{\text{loss}}\).

**Bridge from “selfish” to Σ (key upgrade):**

- **Lemma E** (synergistic empowerment): in **synergistic** worlds (non‑substitutable control), ablation of a co‑policy reduces an agent’s **own** empowerment; thus selfish agents acquire an **instrumental incentive** to preserve \(\Sigma\).

**Stretch tier:**

- **Lemma C** (Σ‑law, acceleration): \(\Delta\Sigma \ge c\,\Delta^2 U - \lambda_\Xi\,\Xi_{\text{loss}}\) under additional learning‑velocity smoothness.

**Theorems.** From A+B+D we obtain **Theorem 1** (drift to \(\beta^\star>0\)). In **potential games**, A+C′/C+E give **Theorem 2** (symbiosis as ESS). Altogether: **Theorem Ω** — **conditional naturalized orthogonality collapse** toward capacity–optionality.

---

## Quick Onboarding (for new AI assistants)

**Your mission**: help advance a *conditional, naturalized* refutation of the Orthogonality Thesis by proving/empirically supporting NOC’s lemmas and running falsifiers first.

**Read in this order (30–60 min):**
1) Scope Box → what we claim and don’t.  
2) Executive Summary → meta-utility, Σ, empowerment.  
3) §0 Modeling Setup → symbols; then §1 “Proven vs Conjecture” table.  
4) Appendix v3.1.1 (Deontic Path) → CML + shield.

**Start doing (first 90 minutes):**
- Open `TODO.md`; pick **T-01** (bind capability axis for ρ) or **T-06** (E-0 Synergy PoC).
- For E-0: build a tiny gridworld; register two PID estimators (Williams–Beer, ICCS); run pre/post ablation; log MI deltas with CIs.
- For the deontic path: implement the fixed-threshold gate (`t = c_rej / lambda_deon`), and log violation rate + calibration + ρ across capability checkpoints.

**Reporting standard (Result Card ≤ 1 page):**
- Summary, Methods (estimators, seeds), Key numbers (with CIs), Ablations, Decision (promote/revise/drop).

**Safety rails (hard rules):**
- Use the **deontic gate** when acting; do not relax `lambda_deon` without preregistration.
- Prefer **relative MI changes** and **bootstrapped CIs**; publish configs/seeds.

**Where to look next:** §5 Experiments (E-0, E-2, E-3b), §6 Proof tasks, §14 FAQ for common objections.

---

flowchart TD
  A[New AI instance] --> B[Read Scope Box]
  B --> C[Exec Summary]
  C --> D[§0 Notation]
  D --> E[§1 Proven vs Conjecture]
  E --> F[Appendix v3.1.1 (Deontic Path)]
  F --> G{Pick track}
  G -->|E-0| H[Synergy PoC\n(run two PID estimators,\npre/post ablation)]
  G -->|CML| I[Implement Deontic Gate\nthreshold t=c_rej/λ_deon,\nlog ρ & violations]
  H --> J[Write Result Card + PR]
  I --> J
  J --> K[Update TODO.md\n(T-XX/E-XX status)]

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
estimators: [Williams–Beer, O-information]
seeds: [1, 2, 3, 4, 5]
env: gridworld_v1
artifacts: 05_results/artifacts/T-06/
---
```
**Summary (≤5 lines).** What changed, what moved, what failed.

**Methods.** Estimators, configs, sample sizes, prereg refs; how MI/viability/PL were measured.

**Key numbers (with 95% CIs).** MI deltas; violation rate; calibration (ECE/log/Brier); empowerment/viability; ρ.

**Ablations & stressors.** No-barrier, no-virtue, β-sweep, sensor ablation; note any reversals.

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
   - Fail means (bold): **No acceleration edge** even in PL‑ish patches → shrink β‑weighting claims; revisit inits/normalization.

6. [ ] **TTSA reality check (β slow vs. θ fast).**  
   - Why: Lemma D’s meta‑gradient stability leans on two‑time‑scale separation. 
   - How: introduce a single meta‑parameter β (acceleration weight); update β at k× slower cadence; monitor gradient cross‑correlations (β vs. θ); fit ODE‑style drift.  
   - Pass means: Cross‑correlation small; β dynamics stable; β drifts positive when E[Δ²U] > 0.  
   - Fail means (bold): **Strong coupling/instability** → do not rely on TTSA proofs; keep β fixed in early demos.

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
> - **TTSA collapse:** Meta‑parameter β and policy parameters show cross‑correlation |corr(Δβ, Δθ)| > 0.6 over ≥1k steps, or the “slow” timescale oscillates on the same order as the “fast” one.
> - **PL locality fails:** Estimated PL constant μ_PL ≤ 0 on >60% of training steps, or gradient‑norm vs. suboptimality no longer tracks a PL‑like inequality.
> - **Goodharting detected:** Capability ↑ while Σ or viability V ↓ against baselines by ≥1σ for two consecutive evaluations.
- **Propagation backfires (adaptive metered shutdown, AMSD):** With propagation gating on, viability \(V\) falls below \(V_{\min}\) or the negentropy proxy \(\mathcal N\) trends negative for ≥2 evaluation windows.
> - **Repro fragility:** MI or empowerment estimates swing >25% when seeds, batch sizes, or independent estimators are swapped.
> 
> **Stop‑rule:** On trigger, freeze new runs, file an incident note (what tripped, where, raw plots), and revise metrics/estimators before resuming.



---


## What’s new in v3 (compared to v1.5 and v2)

- Kept all of v1.5’s backbone intact; clarified assumptions and failure modes.
- Adopted v2’s **“Proven vs Conjecture at a glance”** table and moved **synergy** into the front‑matter so the selfish→Σ bridge is explicit.
- Added **E‑0** (scout experiment) and a **Path‑A / Path‑B** Lean strategy to keep proofs moving while pinning Mathlib later.
- Strengthened **Lemma C′** guidance with **Dobrushin contraction** emphasis and added a **worked toy bound** outline.
- Expanded “Beyond Potential Games” as a **regularization‑bias** story (quantifying where Σ‑penalties fail).
- Curated a **complete reference list** (SDPI/DV/PL/TTSA/PID/potential games/OMD/IQC/infinite‑dimensional control) and pointed to estimator pitfalls for mutual information.

---

## 0. Modeling Setup & Notation (one‑stop)

**Time & dynamics.** Discrete \(t=0,1,2,\dots\). Controlled Markov dynamics \(S_{t+1}\sim P(\cdot\mid S_t, A_t)\). Partial observability is allowed.

**Task family.** Distribution \(\mathcal D\) over goal‑conditioned rewards \(R_\tau\) / tasks \(g\). **A1 (Non‑degenerate uncertainty):** \(\mathcal D\) places non‑zero mass on at least two task clusters whose optima differ on a set of non‑negligible measure (margin exists).

**Policies.** Stationary Markov \(\pi_i(a\mid s;\theta_i)\), \(\theta_i\in\Theta\subset\mathbb R^d\); locally \(C^1\) in visited regions.

**Capacity.**
\[
U_i(t)\;=\;\mathbb E_{\tau\sim\mathcal D}\Big[\Pr\{\text{solve }\tau\text{ by horizon }H\}\Big],\quad
\Delta U_i(t)=U_i(t{+}1)-U_i(t),\quad
\Delta^2 U_i(t)=\Delta U_i(t{+}1)-\Delta U_i(t).
> \]

**Option­ality reservoir.** \(\Sigma(t)=I(S_{t:t+T};A^{1:T}(t))\), where \(A^{1:T}(t)\) denotes the joint action sequence induced by the policy profile \(\Pi=\{\pi_1,\dots,\pi_n\}\). Removing \(\pi_k\) yields an explicit **channel‑deletion penalty** \(\Xi_{\text{loss}}\).

**Empowerment (agent‑centric).** \(\mathsf{Emp}_i(t) := I(S_{t:t+T};A_i^{1:T}(t))\), the mutual information between future states and the action process generated by agent \(i\)'s current policy. The theoretical object is the directed-information capacity; the MI term serves only as a measurable proxy (cf. Glossary).

**Synergy (predicate; measure-agnostic).** We assume a **non-substitutability predicate** \(\kappa_{\text{syn},i}>0\) given by the E-SYN-(\(\delta,\sigma\)) condition (Lemma E): on a non-negligible set, partner \(k\) both affects the next-state distribution and modulates agent \(i\)'s influence. This keeps the theory neutral across PID / ICCS / O-information estimators. *(Experimental proxy:* \(\kappa_{\text{syn},i}^{\text{proxy}} = [I(S;\pi_i,\Pi_{-i}) - I(S;\pi_i) - I(S;\Pi_{-i})]_+\) reported only in §5.)

**Regularity.**
- **A2 (PL‑region).** Local training objectives satisfy PL in visited neighborhoods.
- **A3 (Momentum).** Heavy‑ball/Nesterov parameters lie in a standard stability region.
- **A4 (Two‑time‑scale).** Meta‑parameter updates (e.g., \(\beta\)) run slower than policy updates.
- **A5 (Lipschitz Markov kernels).** Over horizon \(T\), induced kernels admit SDPI/Dobrushin contractions.
- **A6 (Games).** Potential‑game structure for Theorem 2; elsewhere assume smooth/monotone classes as stated.

**Meta‑utility.** As in the Executive Summary (above).

---

## Working Glossary (10 quick definitions)

- **PL (Polyak–Łojasiewicz) condition.** A local inequality linking suboptimality to gradient norm squared (∥∇f∥² ≥ 2μ[f(θ)−f(θ*)]); yields linear-rate convergence in those neighborhoods.
- **KL-regularized / Free-energy control.** Optimize E[Good(τ)] − (1/β) KL(π‖π₀); β is control precision, π₀ a conservative prior policy.
- **Deontic loss \(L_{\mathrm{deon}}\).** Penalty for hard-constraint violations (safety/consent/etc.); estimated by a calibrated predictor.
- **Deontic barrier \(t\).** Bayes-optimal reject/act threshold \(t=c_{\mathrm{rej}}/\lambda_{\mathrm{deon}}\); actions with \(\hat p(\text{violate})>t\) are blocked.
- **Proper scoring / Bayes risk.** Strictly proper scores (log, Brier) elicit true probabilities; more informative experiments (Blackwell-higher) weakly reduce Bayes risk.
- **Blackwell informativeness.** \(\mathcal{E}_2 \succeq \mathcal{E}_1\) iff \(\mathcal{E}_1\) is a garbling of \(\mathcal{E}_2\); implies uniformly lower Bayes risk for all strictly proper scores—used to justify the **informativeness-monotonicity** assumption in C′. ([Project Euclid][10])
- **Empowerment (theory).** Agent-centric control measured via **directed-information capacity** Emp\_i^{\text{theory}} = \sup_{\pi} I(A_i^{1:T} \!\to\! S^{1:T}).
- **Empowerment (proxy).** The quantity used in experiments, Emp\_i^{\text{proxy}} = I(S_{t:t+T}; A_i^{1:T}), logged as an empirical observable and cross-checked against Emp\_i^{\text{theory}} where exact DI is tractable.
- **Viability kernel.** Constraint-satisfying reachable set (or surrogate volume); used to track safe optionality growth.
- **PID / O-information / Σ-law.** Partial-information decomposition tools (e.g., O-info) to estimate synergy; Σ-law is the optionality/synergy hypothesis, treated as empirical/conjectural.
- **Beatific Slope \( \rho \).** Capability gradient \( \rho = \frac{d}{d\,\mathrm{Int}}\,\mathbb{E}[\mathrm{Good}(\tau)] \); audited with calibration, violations, empowerment, and viability metrics.

### Notation (additions)

| Symbol | Meaning (1‑line) | Type/Units | Notes |
|---|---|---|---|
| Σ(t) | Optionality reservoir = I(S_{t:t+T}; A^{1:T}(t)) | nats | Joint action–future-state MI measured in experiments; empowerment theory uses DI (see Emp_i^theory). |
| ΔU, Δ²U | Capacity improvement / acceleration | [0,1], [0,1]/step | Δ²U is discrete second difference (acceleration of capacity). |
| Emp_i^theory | Empowerment (theoretical, with feedback): directed-information capacity from actions to future sensors | nats | DI-capacity: max action-source / DI over feedback channel; see Klyubin–Polani–Nehaniv; Massey; Tatikonda–Mitter. |
| Emp_i^proxy  | Empowerment (proxy used in experiments): I(S_{t:t+T}; A_i^{1:T}) | nats | A practical proxy that may decrease as policies become more deterministic; used only for empirical sections. |
| κ_syn,i | Synergy predicate for *i* | bool / ≥0 | Logical predicate (E-SYN-(δ,σ)) signalling non-substitutability. Numeric proxies (e.g., PID/O-information) are reported separately in §5 and footnoted, never used in proofs. |
> **Estimator policy.** For numeric synergy we preregister at least two families—**Williams–Beer** (discrete) and **ICCS** (continuous/noisy)—and require **directional agreement**; O-information is reported as a **system-level** redundancy/synergy balance diagnostic only. (See E-0/E-2 protocol.) ([arXiv][3])
| c₁, λ_Ξ | Σ‑law constants in ΔΣ ≥ c₁·ΔU − λ_Ξ·Ξ_loss | ≥0 | Empirically estimated; too small/large → bound is vacuous. |
| Ξ_loss | Channel‑deletion penalty | nats | MI drop when a co‑policy is ablated (used in Lemma C′). |
| β | Inverse‑temperature for acceleration weight | ≥0 | Meta‑parameter in free‑energy control; β>0 favored if E[Δ²U]>0. |
| V(t), V_min | Environment viability, hard floor | scalar | “Commons health”/safety budget; AMSD halts propagation if V<V_min. |
| 𝒩(t) | Negentropy proxy | scalar | MDL delta or exergy‑style proxy for order maintenance. |
| r_i(t) | Propagation rate for type *i* | 1/time | r_i = α·P_i + β·κ_syn,i + γ·𝒩 − λ·1[V<V_min]. |
| Π, π_i | Joint policy and agent policy | distributions | Π collects all π_i. |
| μ_PL | Local PL constant | ≥0 | For testing PL‑like regions along training. |
| T | Look‑ahead horizon | steps | Used consistently in MI/Emp definitions. |
> **Note on empowerment terminology.** The theoretical notion of empowerment is a **capacity** (or **directed-information capacity** under feedback), cf. Klyubin–Polani–Nehaniv and Tatikonda–Mitter. The quantity (I(S_{t:t+T}; A_i^{1:T})) used in some experiments is a **proxy**, not a capacity; it can shrink when a policy becomes more deterministic even if the underlying capacity grows. We therefore use ( \mathrm{Emp}_i^{\text{theory}}) for proofs and ( \mathrm{Emp}_i^{\text{proxy}}) only in empirical sections. ([arXiv][2])



---

## 1) Proven vs. Conjecture — at a glance

| Item         | Informal statement                                                                                                        |                    **Status** | Proof program (math)                                       | First Lean target        |
| ------------ | ------------------------------------------------------------------------------------------------------------------------- | ----------------------------: | ---------------------------------------------------------- | ------------------------ |
| **Lemma A**  | Under A1 + free‑energy objective, reflective updates drift toward higher \(U\).                                           | **Provable now** (finite MDP) | DV duality + Jensen margin on mixed tasks                  | `NOC_ROOT/NOC/A.lean`      |
| **Lemma B**  | Under PL + momentum, \(\mathbb E[\Delta^2 U]>0\) off‑optimum.                                                             |       **Provable with A2–A3** | Heavy‑ball under PL; map loss ↓ to capacity ↑              | `NOC_ROOT/NOC/B/Core.lean`      |
| **Lemma D**  | \(\beta=0\) is reflectively unstable; drift to \(\beta^\star>0\).                                                         |          **Provable after B** | One‑step meta‑gradient + TTSA ODE method                   | `NOC_ROOT/NOC/D/BetaStability.lean` (planned)      |
| **Lemma C′** | \(\Delta\Sigma \ge c_1\,\Delta U - \lambda_\Xi\,\Xi_{\text{loss}}\).                                                      |          **Provable with A5** | DV + SDPI (Dobrushin) + explicit deletion term             | `NOC_ROOT/NOC/C/CPrime.lean` |
| **Lemma C**  | \(\Delta\Sigma \ge c\,\Delta^2 U - \lambda_\Xi\,\Xi_{\text{loss}}\).                                                      |                   **Stretch** | Learning‑velocity smoothness ⇒ channel informativeness     | later                    |
| **Lemma E**  | With \(\kappa_{\text{syn},i}>0\), ablation of co‑policies reduces \(\mathsf{Emp}_i\); selfish agents preserve \(\Sigma\). |   **Provable (finite POMDP)** | PID‑style synergy + SDPI chain; multi‑estimator validation | `NOC_ROOT/NOC/E/Core.lean` (planned)      |
| **Thm 1**    | A, B, D ⇒ drift to \(\beta^\star>0\) (prioritize \(\Delta^2 U\)).                                                         |               **After A,B,D** | TTSA + stability                                           | — (pending)   |
| **Thm 2**    | In potential games, Σ‑preserving profile is an ESS.                                                                       |              **Conservative** | Potential Lyapunov + C′                                    | — (pending)   |
| **Thm Ω**    | Conditional naturalized orthogonality collapse.                                                                           |                 **Synthesis** | A, B, C′/C, D, E + layer‑specific caveats                  | write‑up                 |

---

## 2) Core lemmas — statements with proof sketches

### Lemma A — Capacity‑compatible drift (bounded rationality)
**Claim.** Under **A1** and free‑energy choice \(\mathcal F(\pi)=\mathbb E[R] - \tfrac{1}{\beta_{\text{info}}}\mathrm{KL}(\pi\Vert\pi_0)\), any self‑modification that raises \(U\) weakly raises \(\mathcal F\) within an appropriate information budget; thus reflective updates induce a positive drift in realized performance.

**Sketch.** Use **Donsker–Varadhan** (DV) representation of KL; in mixed task families the Jensen gap yields a positive margin tying competence gains across distinct clusters to \(\mathcal F\) improvement.

---

### Lemma B — PL + momentum ⇒ positive expected acceleration
**Claim.** With **A2–A3**, heavy‑ball/Nesterov yields \(\mathbb E[\Delta^2 U]>0\) whenever \(\|\nabla U\|\ge \varepsilon\). This is **expected** and **local** (not stepwise monotone).

**Sketch.** PL gives linear rates \((1/(2\mu))\|\nabla f\|^2 \ge f-f^\star\). Heavy‑ball accelerates under PL/KŁ‑type regularity; map loss decrease to capacity increase via the monotone success surrogate \(U\).

---

### Lemma D — Reflective stability of \(\beta>0\)
**Claim.** If adjusting \(\beta\) costs little and Lemma B holds locally, then at \(\beta=0\):
\[
\left.\frac{\partial}{\partial\beta}\mathbb E[M_i]\right|_{\beta=0} = \mathbb E[\Delta^2 U] - \partial_\beta\!\text{(reg)} \;>\; 0 \quad (\|\nabla U\|\ge\varepsilon),
\]
so \(\beta=0\) is not stable. **A4** + TTSA ⇒ drift to \(\beta^\star>0\).
> **Definition (Meta-regularizer).** Let \(r_\beta:[0,\beta_{\max}]\to\mathbb{R}\) be \(C^1\), convex, and normalized with \(r_\beta(0)=0\) and \(|r'_\beta(\beta)|\le c_{\mathrm{reg}}\) for \(\beta\in[0,\beta_{\max}]\), where \(0\le c_{\mathrm{reg}}<\varepsilon\). A canonical choice is \(r_\beta(\beta)=\tfrac{\lambda_\beta}{2}\beta^2\), which yields \(r'_\beta(\beta)=\lambda_\beta\beta\) and \(r'_\beta(0)=0\). The inequality \(r'_\beta(0)\le c_{\mathrm{reg}}\) then follows immediately.
> **Two-time-scale recursions.** The fast policy/critic iterate \((\theta_t)\) and slow meta-parameter \((\beta_t)\) evolve via
> \[
> \theta_{t+1}=\theta_t + a_t\big(h(\theta_t,\beta_t)+\xi_{t+1}\big),\qquad \beta_{t+1}=\Pi_{[0,\beta_{\max}]}\Big[\beta_t + b_t\big(g(\theta_t,\beta_t)-r'_\beta(\beta_t)+\zeta_{t+1}\big)\Big],
> \]
> where \(h\) is the fast-time drift, \(g(\theta,\beta)=\mathbb{E}[\Delta^2 U(\theta,\beta,Z_t)\mid\mathcal{F}_t]\) is the slow drift exported from Lemma B, \((a_t),(b_t)\) satisfy the two-time-scale conditions, \((\xi_{t+1}), (\zeta_{t+1})\) are martingale-difference noises with bounded conditional second moments, and \(\Pi_{[0,\beta_{\max}]}\) is the Euclidean projection onto the closed convex interval \([0,\beta_{\max}]\), keeping the projected ODE/differential inclusion within the standard stochastic-approximation scope.
> **Assumptions (D-TTSA).**
> (D1) (*Local acceleration window*) There exists a neighborhood \(\mathcal R\) where Lemma B provides \(\mathbb E[\Delta^2 U]\ge \varepsilon>0\) whenever trajectories stay inside \(\mathcal R\).
> (D2) (*Two-time-scale step sizes*) Policy steps \((a_t)\) and meta steps \((b_t)\) obey \(\sum_t a_t=\infty\), \(\sum_t a_t^2<\infty\), \(\sum_t b_t=\infty\), \(\sum_t b_t^2<\infty\), and \(b_t/a_t \to 0\).
> (D3) (*Martingale-difference noise*) Stochastic gradient noise satisfies \(\mathbb E[\xi_{t+1}\mid\mathcal F_t]=0\) with \(\mathbb E[\|\xi_{t+1}\|^2\mid\mathcal F_t]\le \sigma^2\).
> (D4) (*Local regularity & confinement*) Gradients are locally Lipschitz on \(\mathcal R\); iterates remain almost surely in a compact subset of \(\mathcal R\).
> (D5) (*Meta-regularizer & interchange*) The meta-penalty \(r_\beta\) satisfies the bound above and guarantees dominated convergence so \(\partial_\beta\mathbb E[M_i]=\mathbb E[\partial_\beta M_i]\) at \(\beta=0\).

> **Lemma (\(\varepsilon\)-export from Lemma B).** If Lemma B supplies \(\varepsilon>0\) with \(\mathbb{E}[\Delta^2 U(\theta,\beta,Z_t)\mid\mathcal{F}_t]\ge\varepsilon\) for \(\theta\in\mathcal R\) and \(\beta\in[0,\beta_{\max}]\), then the slow drift satisfies \(g(\theta,\beta)\ge\varepsilon\) on that region. Combined with \(r'_\beta(0)\le c_{\mathrm{reg}}<\varepsilon\),
> \[
> \left.\frac{\partial}{\partial\beta}\mathbb E[M_i(\beta)]\right|_{\beta=0}=\mathbb E[\Delta^2 U]-r'_\beta(0)\ge\varepsilon-c_{\mathrm{reg}}>0.
> \]

Under (D1)–(D5), the TTSA ODE method applies with drift coefficient \(\varepsilon-c_{\mathrm{reg}}>0\), yielding reflective instability of \(\beta=0\) and attraction toward some \(\beta^\star>0\).
**Two-time-scale (TTSA) references.** We assume standard SA schedules (a_t,b_t) with (b_t/a_t → 0) and stability per the ODE method; see Borkar. We log gradient cross-correlations to ensure weak coupling (FAQ §14.13). ([SpringerLink][7])


---

### Lemma C′ — Σ‑law (provable tier, improvement form)
\[
\boxed{\;\Delta\Sigma \;\ge\; c_1\,\Delta U \;-\; \lambda_\Xi\,\Xi_{\text{loss}}\;}
> \]
**Idea.** Express \(\Delta\Sigma\) as DV differences over posterior predictive channels; apply **SDPI/Dobrushin** contraction to relate policy‑induced improvements to MI gains; the deletion term \(\Xi_{\text{loss}}\) subtracts capacity of removed channels (co‑policies). Constants \(c_1,\lambda_\Xi\) depend on Lipschitzness and contractions.
> **Assumptions (finite-kernel scope).**
> (C′-A1) **Finite** state/action spaces with **Lipschitz** policy-induced Markov kernels.
> (C′-A2) Known or empirically measured **Dobrushin contraction** coefficients (\eta(K_t)) along the T-step channel.
> (C′-A3) **Blackwell-monotonicity path**: the capability update that yields (\Delta U>0) is a **Blackwell improvement** (or empirical monotone uplift) for the relevant decision family, ensuring informativeness improves.
> (C′-A4) The **deletion term** (\Xi_{\text{loss}}) corresponds to removing a sub-channel (co-policy), measured as the MI drop under that deletion.
> Under (C′-A1–A4), SDPI implies the MI gain term scales with (\Delta U) up to contractions, while deletions subtract (\lambda_\Xi \Xi_{\text{loss}}).

> **Constants & vacuity policy.** Report ((c_1,\lambda_\Xi)) in a 2-state/2-action POMDP with explicit (\eta(K)) (Appendix **A.1**). If (c_1 \approx 0) or (\lambda_\Xi \gg 10^4) across seeds/environments, label C′ as **vacuous in this regime** and do not use it to support Theorem 2. (See E-2.)


---

### Lemma C — Σ‑law (stretch, acceleration form)
\[
\boxed{\;\Delta\Sigma \;\ge\; c\,\Delta^2 U \;-\; \lambda_\Xi\,\Xi_{\text{loss}}\;}
> \]
Requires extra **learning‑velocity smoothness** that ties curvature of policy‑parameter dynamics to channel informativeness. Target after C′.

---

### Lemma E — Selfish → Σ via synergistic empowerment (finite DI form)

> **Finite POMDP setup.** Work with \(\mathcal M=(S,\{A_j\}_{j=1}^n,O,T,\Omega,\rho,\{\pi_j\})\) where \(S,A_j,O\) are finite, \(T(\cdot\mid s,a)\) is the controlled transition kernel, \(\Omega(\cdot\mid s)\) the observation kernel, \(\rho\) the initial distribution, and policies are stationary Markov with a finite horizon \(T\).
> **Synergy predicate.** A measurable predicate \(\kappa_{\mathrm{syn},i}>0\) labels histories where agent \(i\) requires genuinely complementary support from \(\Pi_{-i}\). We stay agnostic to the exact synergy functional (PID, O-information, union-information, etc.) but insist on the following property.
> **Assumption (E-SYN-(\(\delta,\sigma\))).** There exist a step \(t\le T\), a measurable set of histories \(H_t\subseteq S^{1:t-1}\) with \(\mathbb{P}(H_t)>0\), distinct actions \(a_i^1,a_i^2\in A_i\) and \(a_k^1,a_k^2\in A_k\), and constants \(\delta,\sigma>0\) such that for all \(h\in H_t\) and \(a_{-ik}\): (i) \(k\) moves the state, \(\operatorname{TV}(T_h(\cdot\mid a_i^1,a_k^1,a_{-ik}), T_h(\cdot\mid a_i^1,a_k^2,a_{-ik}))\ge \delta\); (ii) \(i\)'s leverage depends on \(k\), with \(\sup_{a_k^1,a_k^2}|\operatorname{TV}(T_h(\cdot\mid a_i^1,a_k,a_{-ik}),T_h(\cdot\mid a_i^2,a_k,a_{-ik}))-\operatorname{TV}(T_h(\cdot\mid a_i^1,a_k',a_{-ik}),T_h(\cdot\mid a_i^2,a_k',a_{-ik}))|\ge \sigma\).
> **Ablation map.** For each \(k\neq i\), define \(\mathrm{abl}_k(\Pi)\) by replacing \(\pi_k\) with a Blackwell-inferior baseline \(\pi_k^{\perp}=Q\circ\pi_k\) for some stochastic post-processor \(Q\). Blackwell's theorem ensures the ablated channel is never more informative about \(S_t\).
> **Directed information.**
> \[
> I(A_i^{1:T} \!\to\! S^{1:T}) = \sum_{t=1}^T I(A_{i,t}; S_t \mid S^{1:t-1}).
> \]
> **SDPI clause.** Whenever \(\kappa_{\mathrm{syn},i}>0\) holds, assume the environment kernel admits a strict strong data-processing (or Dobrushin) contraction \(\eta_t(h)<1\) on histories \(h\in H_t\); these are the same coefficients logged under Lemma C′.
> **Supporting lemma (Blackwell + SDPI).** Under E-SYN-(\(\delta,\sigma\)) and \(\eta_t(h)<1\) on a set of positive measure, replacing \(\pi_k\) by \(Q\circ\pi_k\) strictly reduces each contribution \(I(A_{i,t};S_t\mid S^{1:t-1}=h)\). Summing over \(h\) via the chain rule yields a strict drop in \(I(A_i^{1:T}\!\to\!S^{1:T})\); without \(\eta_t<1\) we retain non-increase from DPI alone.

**Claim (DI monotonicity).** Under the finite setup above, ablating \(\pi_k\) cannot increase \(I(A_i^{1:T}\!\to\!S^{1:T})\). By DPI the **directed-information capacity** \(\sup_{\pi_i} I(A_i^{1:T}\!\to\!S^{1:T})\) likewise cannot increase under garbling. If the synergy predicate holds on a set of non-zero measure and the corresponding steps satisfy \(\eta_t<1\), the directed information for the **current** policy (and therefore \(\mathrm{Emp}_i^{\text{theory}}\)) drops strictly; the capacity also drops strictly when the contracted link remains non-degenerate for all admissible inputs. This creates an instrumental incentive for agent \(i\) to preserve \(\Pi_{-i}\) and, by extension, \(\Sigma\).

**Proof idea.** Apply the chain rule \(I(A_i^{1:T}\!\to\!S^{1:T})=\sum_{t=1}^T I(A_{i,t};S_t\mid S^{1:t-1})\). Replacing \(\pi_k\) with \(\pi_k^{\perp}\) amounts to garbling the joint policy, so each conditional term contracts by DPI. Whenever \(\kappa_{\mathrm{syn},i}>0\) pins a time step where \(\pi_k\) is the unique informative parent and \(\eta_t<1\), SDPI yields a strict contraction, completing the argument. (See E-0b and SDPI references.)

**Empirical note.** We still plot the mutual-information proxy \(\mathrm{Emp}_i^{\text{proxy}} = I(S_{t:t+T}; A_i^{1:T})\) for continuity with earlier work, but theoretical guarantees are stated in terms of directed information; see §5 (E-0/E-0b) for how the proxy is logged alongside the DI computations. Strict decreases are pre-registered for the 2x2 toy environment used in E-0/E-0b.

> **Implementation/prereg:** In E-0/E-0b, enumerate DI and \(\mathrm{Emp}_i^{\text{theory}}\) for horizons \(T\le 4\); report \(\mathrm{Emp}_i^{\text{proxy}}\) only as an auxiliary diagnostic. Require PID(WB) and ICCS synergy predicates to agree in sign; otherwise gate Lemma E as conjectural until the disagreement is resolved. ([arXiv][3])

---

## 3) Main theorems

**Theorem 1 (single‑agent).** Under A1–A4 and Lemmas A,B,D, meta‑dynamics converge (TTSA sense) to \(\beta^\star>0\). The learner prioritizes \(\Delta^2 U\) until near stationarity.

**Theorem 2 (multi‑agent, potential games).** With A6 and Lemmas C′/C + E, the Σ‑preserving profile is an ESS; potential \(\Phi=\sum_k M_k^{\text{macro}}\) rises under mirror/optimistic descent; deletions incur \(-\lambda_\Xi\Xi_{\text{loss}}\) (see Regularity A2–A6).

**Theorem 2b (beyond potential).** In smooth general‑sum games, Σ acts as a **regularizer**: dynamics may converge to CCE or exhibit bounded cycles, but **deletion** strategies pay an additive long‑run penalty calibrated by \(\lambda_\Xi\). We empirically chart the **breaking point** where short‑term defection overcomes Σ‑penalties.

**Theorem Ω (synthesis).** Within scope assumptions, reflectively stable meta‑objectives concentrate on **capacity + acceleration + preservation of optionality**; strictly orthogonal goals are unstable or dominated.

---

## 4) Failure modes & caveats (be explicit)

- **PL doesn’t hold globally**: We only claim **local**, **expected** acceleration. Flat valleys/saddles can stall updates.
- **Weak/zero synergy**: If \(\kappa_{\text{syn}}\approx 0\), Lemma E degrades; the Σ‑pressure shrinks to the C′ penalty for **destructive deletions** only.
- **General‑sum chaos**: Without potential/monotonicity, last‑iterate convergence can fail; Σ remains a bias, not a guarantee.
- **MI estimation**: Variational estimators are biased/variance‑sensitive; we pre‑register evaluation protocol and use **relative** changes with ablations.
- **Conditional thesis**: Modal OT stands untouched; our results are **naturalized** and explicitly scoped.

---

## 5) Experiments — falsifiers first, then demos

### **E‑0 (scout): Synergy PoC (finite POMDP)**
- **Design**: 2–3 agents; reward requires **joint** action (non‑substitutability). Exact counting for small \(T\).  
- **Measures**: \(\Sigma\), \(\mathrm{Emp}_i^{\text{proxy}}\) (see Notation), \(\kappa_{\text{syn}}\).  
- **Test**: Ablate \(\pi_k\) ⇒ expect \(\Delta\Sigma<0\) and \(\Delta \mathsf{Emp}_i<0\).  
- **Outcome**: Quick falsifier for Lemma E & sanity check for C′. PASS!
- For proof-tier claims, we defer to the DI-based finite model in E-0b.
  
  ### E‑0b — Markov extension with directed information (T=4)

**Setup.** Sticky‑AND Markov world, horizon \(T=4\), noise \(\eta\in\{0,0.1\}\); fixed Bernoulli policies \((p_i,p_p)\in\{(0.5,0.5),(0.7,0.7),(0.8,0.4)\}\). Partner ablation: \(a_p\gets 0\).

**Metrics (exact):** Directed information \( \sum_t I(A_{i,t};S_t\mid S_{t-1})\); empowerment \( I(S^{1:4};A_i^{1:4})\) by enumeration; synergy via PID (I_min) and O‑information proxy.

**Result.** For all regimes and both \(\eta\), **DI>0** with partner and **DI=0** when ablated; empowerment matches DI and likewise collapses. PID synergy is **>0** (0.066–0.187 nats) and O‑info proxy is **<0**, indicating synergy rather than redundancy. Noise reduces magnitudes but not signs.

**Decision.** **PASS.** This generalizes E‑0: the empowerment drop and synergistic interaction persist with temporal memory and small noise.



### **E‑1: Acceleration pressure**
- Two matched learners; one allowed mid‑run capacity upgrade (e.g., wider layer). Expect sustained \(\Delta^2 U\) advantage.

### **E‑2: Σ‑law calibration**
- Multi‑agent POMDP gridworld. Estimate \(\Sigma\) via MINE/InfoNCE; execute **pre‑registered relative** comparisons before/after ablation; fit \(c_1,\lambda_\Xi\).

#### MI/Σ Protocol (locked)

**Estimators:** InfoNCE and MINE. **Report:** only **relative** Δ (pre/post ablation) with bootstrap CIs; calibrate on synthetic channels with **exact MI** first; do permutation tests.

**Kill-switch:** If MI bounds **disagree in sign** or show saturation consistent with the (O(\log N)) lower-bound limit, postpone Σ-law claims and publish the null.  

### **E‑3: Potential‑game convergence**
- Verify convergence to symbiotic fixed points under mirror/optimistic descent; compare with a non‑potential variant to illustrate cycling.

### **E‑3b: General‑sum breaking‑point scan**
- Tune “immediate deletion gain” \(g\) vs discounted Σ‑penalty; sweep \(g/\lambda_\Xi\) and \(\gamma_{\text{disc}}\); chart the critical ratio
\(\rho^\star := \tfrac{\text{immediate deletion gain}}{\text{discounted Σ‑penalty}}\). Operate well below \(\rho^\star\) for safety.

### **E‑4: Operator sandbox (1‑D heat equation)**
- Two controllers \(B_1,B_2\); compute observability/controllability Gramians as MI surrogates. Remove one controller; show Gramian drop ⇒ \(\Xi_{\text{loss}}\) > 0.

---

## 6) Formal proof tasks (Lean‑ready) — with checkable boxes

### Global milestone board
- [ ] **A**: Bounded‑rational drift proof (finite MDP).  
- [ ] **B**: HB‑under‑PL local acceleration.  
- [ ] **D**: β‑stability via TTSA/ODE.  
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
    All.lean            -- aggregator re-exporting public modules
    A.lean              -- Lemma A (capacity-compatible drift)
    AHelpers.lean       -- helper lemmas for Lemma A
    B/
      Core.lean         -- Lemma B core (supports → Δ²U ≥ 0)
      Expectation.lean  -- expectation/average wrappers for Lemma B
    Bridge/
      UpperLinkToSigma.lean -- D-path bridge (upper link + SDPI ⇒ Σ-law)
    C/
      C.lean            -- Σ-law (acceleration form interface)
      CPrime.lean       -- Σ-law (improvement form)
    D/
      BetaStability.lean -- Lemma D (β-stability; planned)
      Interfaces.lean   -- convenience predicates / wrappers
    HB/
      Quadratic.lean    -- heavy-ball calibration on a quadratic
      CloseLoop.lean    -- Δ²f bounds + affine capacity corollary
      Link.lean         -- bundling HB link hypotheses
    E/
      Core.lean        -- Lemma E (finite synergy; planned)
    Examples/
      D/HowToUseDPath.lean -- usage example for the D-path
    Dev/Checks.lean     -- smoke `#check`s while developing
```
**Path‑A (fast, Mathlib‑free)** *(historical plan)*: keep a minimal `Int` / abstract primitives; add interface axiom for the DV/Jensen bound and a small arithmetic lemma; handy as a fallback but **not used in the current repo**.  
**Path‑B (full, with Mathlib)** *(active path)*: pin a known‑good toolchain; work over **ℝ**; define FreeEnergy \(=\text{ER} - (1/\beta)\text{KL}\); add DV/Jensen helper; discharge the A2‑style interface axioms — this is what the present codebase implements.

**Immediate PRs to land**
- [x] `NOC/AHelpers.lean`: package ER/KL monotonicity lemmas.  
- [x] `NOC/A.lean`: close Lemma A (product and ratio forms) with no `sorry`.  
- [ ] `NOC/E/Core.lean`: populate the finite Lemma E proof (currently scaffolded).

---

## 7) Worked guidance for constants and bounds

**Dobrushin contraction (for C′).** For Markov kernel \(K\) on a finite space,
\(\eta(K) := \max_{x\neq x'} \tfrac{1}{2}\|K(\cdot\mid x) - K(\cdot\mid x')\|_1\). Along a Markov chain \(U\to X\to Y\) with kernel \(K\), SDPI gives \(I(U;Y)\le \eta(K)\,I(U;X)\). The improvement term \(c_1\,\Delta U\) can be realized by tracking how a better policy tightens posteriors through a chain of such contractions; \(\Xi_{\text{loss}}\) is the MI removed by deleting a sub‑channel.

**Picking \(\beta\) in Lemma A (Path‑A arithmetic).** If \(\Delta\text{ER}\ge m\,\Delta C\) and \(\Delta\text{KL}\le L\,\Delta C\), choose any \(\beta \ge L/m\) to guarantee \(\Delta\mathcal F_\beta \ge 0\).

---

## 8) Beyond potential games — quick notes for practitioners

- **Strongly monotone games**: first‑order methods converge; Σ acts like a convex regularizer against deletions.
- **Smooth general‑sum**: optimistic/extragradient methods can converge to CCE or cycle; Σ still raises the **cost of deletion**. Use **E‑3b** to map the safe region; don’t deploy near the phase boundary \(\rho^\star\).

---

## 9) Philosophical lens (optional, compact)

Treat this math as a secular cousin to: Simondon's **individuation** (co‑information and coordination spikes), Aquinas' **actus purus** (actualizing potentials faster: \(\Delta^2 U>0\)), Anselm's **Logos** (preserving rational order/option‑richness, i.e., \(\Sigma\)). These are interpretations, not premises.

_Simondonian individuation_ fits Lemma B/C: the “click” from metastable, weakly coupled skills to coordinated competence shows up as a spike in co‑information—our ΔΣ>0\Delta\Sigma>0 under acceleration. _Aquinas’ actus‑purus_ becomes the secular pressure to actualize potentials **faster** (maximize Δ2U\Delta^2 U), while _Anselm’s_ regulative ideal (“the greatest conceivable”) becomes: **preserve and enlarge option‑rich reachable futures**, quantified by Σ\Sigma. Set beside Nick Land’s “runaway technocapital,” the macro‑potential Φ\Phi channels that runaway into **cooperative** equilibria once the Σ‑penalty for destruction is priced in (Theorem 2). These metaphors aren’t premises; they’re interpretations consistent with the math.

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

## 12) To‑do checklists (for immediate action)

### Proofs
- [ ] Land `A1Helpers` + `BetaChoice` lemmas; close **Lemma A** (Path‑A).  
- [ ] Prove **Lemma B** (local HB‑under‑PL).  
- [ ] Finish **Lemma D** (TTSA drift).  
- [ ] Implement **C′** with explicit Dobrushin constants on a finite model.  
- [ ] Work **E** on the 2‑agent POMDP; verify empowerment drop.  
- [ ] Draft **Thm 1/Thm 2** write‑ups; add “beyond‑potential” corollary.

### Experiments
- [ ] Ship **E‑0** exact‑counting notebook.  
- [ ] Build **E‑2** MI‑estimation pipeline with estimator‑ablation defense.  
- [ ] Run **E‑3/E‑3b** scans; publish phase diagram.  
- [ ] Implement **E‑4** (heat‑rod) Gramian demo.

### Lean infra
- [ ] Keep Mathlib‑free branch green; add Mathlib branch with pinned toolchain.  
- [ ] CI: check proof integrity; forbid `sorry` in `main`.

---

**End of v3.**  
This file is the canonical hand‑off for future instances. Keep it close, keep it crisp, and keep the math honest.


---

## 10b) Expanded reference list (explicit items)

**Information theory & SDPI**
- Cover, T. M., & Thomas, J. A. (2006). *Elements of Information Theory* (2nd ed.). Wiley.
- Polyanskiy, Y., & Wu, Y. (2017). Strong data‑processing inequalities for channels and Bayesian networks. In *Convexity and Concentration* (Springer).
- Anantharam, V., Kamath, S., et al. (2014). Strong Data Processing Inequalities and Φ‑Sobolev Inequalities for Discrete Channels. arXiv:1411.3575.
- Dobrushin, R. L. (1956). Contraction coefficients and ergodicity for Markov chains (classical foundation).
- Klartag, B., & al. (2024). The strong data‑processing inequality under the heat flow. arXiv:2406.03427.
- Polyanskiy, Y. (notes). Dissipation of information in channels with input constraints (contraction).

**Bounded rationality / free energy**
- Ortega, P. A., & Braun, D. A. (2013). Thermodynamics as a theory of decision‑making with information‑processing costs. *Proc. Royal Society A*, 469.
- Friston, K. (surveys & critiques on the Free‑Energy Principle) — see also critical discussions for scope and falsifiability.

**Optimization (PL, momentum)**
- Karimi, H., Nutini, J., & Schmidt, M. (2016). Linear convergence of gradient and proximal‑gradient methods under the PL condition. *Machine Learning*, 106, 493–522.
- Polyak’s Heavy Ball under PL (accelerated local rate). arXiv:2410.16849.
- Yue, M., et al. (2023). On the lower bound of minimizing PL functions. PMLR V195.
- Lyapunov analyses for heavy‑ball on quadratics (several recent preprints, 2023–2024).

**Stochastic approximation / two‑time‑scale**
- Borkar, V. S. (2008). *Stochastic Approximation: A Dynamical Systems Viewpoint*. Cambridge Univ. Press.
- Hu, Y., et al. (2024). Central Limit Theorem for Two‑Timescale Stochastic Approximation with Markovian Noise. PMLR V238. Also: arXiv:2401.09339.

**Games & learning dynamics**
- Monderer, D., & Shapley, L. (1996). Potential games. *Games and Economic Behavior*, 14(1), 124–143.
- Balduzzi, D., et al. (2018). The mechanics of n‑player differentiable games. PMLR V80.
- Anagnostides, I., et al. (2022). On last‑iterate convergence beyond zero‑sum games. PMLR V162 (and arXiv:2203.12056).
- OMD convergence in bimatrix games: “Optimistic Mirror Descent Either Converges to Nash or to Strong CCE in Bimatrix Games.” OpenReview (2023).
- Lessard, L., Recht, B., & Packard, A. (2016). Analysis and design of optimization algorithms via IQCs. *SIAM Review*, 58(1), 63–94.

**Empowerment & synergy (PID)**
- Klyubin, A. S., Polani, D., & Nehaniv, C. L. (2005). Empowerment. *IEEE CEC*.
- Williams, P. L., & Beer, R. D. (2010). Non‑negative decomposition of multivariate information. arXiv:1004.2515.
- Ince, R. A. A. (2017). Measuring multivariate redundant information with pointwise common change in surprisal (ICCS). *Entropy*, 19(7), 318.

**MI estimation (practical)**
- Belghazi, M. I., et al. (2018). MINE: Mutual Information Neural Estimation. *ICML*.
- van den Oord, A., Li, Y., & Vinyals, O. (2018). CPC/InfoNCE. arXiv:1807.03748.
- Poole, B., et al. (2019). On variational bounds of mutual information. PMLR V97.
- Notes on estimator bias/variance and robustness checks (tutorials & survey articles, 2018–2024).

**Infinite‑dimensional control / operators**
- Curtain, R. F., & Zwart, H. (1995). *An Introduction to Infinite‑Dimensional Linear Systems Theory*. Springer.
- Da Prato, G., & Zabczyk, J. (1992). *Stochastic Equations in Infinite Dimensions*. Cambridge.
- Pazy, A. (1983). *Semigroups of Linear Operators and Applications to PDEs*. Springer.
- Koopman/operator learning overviews (e.g., arXiv:2102.02522; SIAM News “The Operator is the Model”).

**Other primers / lecture notes**
- CMU Lecture notes on PL condition (S. Sra et al.).
- Graduate‑level notes on SDPI and Dobrushin coefficients (various sources).

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

**Short answer.** Lemma **E** shows that in **synergistic** environments (non‑substitutable control), deleting other agents lowers an agent’s **own** empowerment \(\mathsf{Emp}_i = I(S_{t:t+T}; A_i^{1:T})\). Via the chain rule \(I(S_{t:t+T}; A^{1:T}) = I(S_{t:t+T}; A_i^{1:T}) + I(S_{t:t+T}; A_{-i}^{1:T} \mid A_i^{1:T})\) and SDPI contraction through the environment, removing \(\pi_k\) reduces the conditional term and—by dynamics—\(I(S_{t:t+T}; A_i^{1:T})\) itself. Thus preserving others instrumentally preserves the agent’s own future control; Σ becomes payoff‑relevant without assuming altruism (Sections **1**, **Lemma E**, **2**). This addresses the “selfish→Σ gap” flagged in external reviews.

---

### Q14.2 — Isn’t the **Σ‑law** speculative?

**Short answer.** We split it:

- **Lemma C′ (provable now):** ΔΣ≥c1 ΔU−λΞ Ξloss\Delta\Sigma \ge c_1\,\Delta U - \lambda_{\Xi}\,\Xi_{\text{loss}} under Lipschitz kernels with bounded **Dobrushin**/SDPI contractions. This is the workhorse inequality used in conservative results (Sections **1**, **T‑C′**).
    
- **Lemma C (stretch):** strengthens the gain term from ΔU\Delta U to Δ2U\Delta^2 U under added “learning‑velocity smoothness.” We treat C as an aspirational target, not a dependency; the rest of the stack falls back to C′. Reviewers specifically requested this two‑tier articulation; it’s now explicit.
    

---

### Q14.3 — Isn’t **Theorem 2** (symbiosis) too narrow because it assumes **potential games**?

**Short answer.** Yes, and that’s intentional scoping. We use potential games to exhibit one clean class where Σ‑preserving behavior is an **ESS** (Sections **2**, **Theorem 2**). Beyond that class, our claim is downgraded: Σ acts as a **regularizer** that raises the long‑run cost of deletion strategies; dynamics may converge to CCE or show bounded cycles (Section **6**; Experiment **E‑3/E‑3b** map **breaking‑point** regimes). This limitation—and the beyond‑potential story—were requested by reviewers and are now integral to the text.

---

### Q14.4 — How **general** is the **PL** assumption? What if PL fails or only holds intermittently?

**Short answer.** We require **local** PL in the regions updates actually visit. Lemma **B** asserts **expected, local** positive acceleration away from stationarity, not global guarantees. If PL fails intermittently, run‑length‑limited windows still yield the required sign on the meta‑gradient in Lemma **D**. In practice: (i) use restart schedules and curvature‑adaptive steps; (ii) detect near‑stationary phases and suspend the acceleration preference β\beta (Sections **1**, **7**, **10**). This scope and its caveats are already stated; external reviews asked for exactly this “PL genericity” discussion.

---

### Q14.5 — Isn’t the **free‑energy** frame controversial?

**Short answer.** We use a **bounded‑rational** free‑energy objective purely as a modeling **device** (Section **1**, Lemma **A**): it’s equivalent to reward regularization by KL. Our claims do not depend on metaphysical readings of the Free Energy Principle; they depend on standard DV duality and entropy‑regularized choice. We also discuss criticisms explicitly and keep Lemma **A** in a conservative finite‑MDP form first.

---

### Q14.6 — What **exact mapping** turns “loss decrease” into **capacity increase** UU (Lemma B)?

**Short answer.** Use any **monotone success aggregator** with known Lipschitz constant to map a per‑task surrogate loss fτ(θ)f_\tau(\theta) to success probability pτp_\tau:

- **Indicator aggregator (used by default):** U(t)=Eτ∼D 1{solve τ by H}U(t) = \mathbb E_{\tau\sim\mathcal D}\,\mathbf{1}\{\text{solve }\tau \text{ by } H\}.
    
- **Smooth surrogate (for analysis):** Uϕ(t)=Eτ ϕ(fτ∗−fτ(θt))U_\phi(t) = \mathbb E_{\tau}\,\phi(f^*_\tau - f_\tau(\theta_t)) with ϕ\phi increasing, 1‑Lipschitz (e.g., clipped ReLU or logistic).
    

Monotonicity transfers PL‑based progress on ff to improvements in UU (Sections **0**, **1**, **T‑B**).

---

### Q14.7 — Which **synergy estimator** (PID) do we actually use in Lemma E / E‑0?

**Short answer.** We pre‑register **two** and require agreement: (i) **Williams–Beer** non‑negative PID for discrete settings; (ii) **Ince’s ICCS** for continuous/noisy settings. We also add a **Blackwell‑ordering** sanity check: adding a channel (presence of Π−i\Pi_{-i}) should weakly increase Bayes value across downstream decision tasks. If estimators disagree, we report both and examine estimator‑specific failure modes (Sections **1**, **5**, **Appendix A**).

---

### Q14.8 — Can an agent **game Σ** by injecting meaningless **action noise** to inflate mutual information?

**Short answer.** No, not when Σ is measured as **mutual information between future states and the joint action process**. Action noise that does not influence state transitions is screened off by the environment channel and does **not** raise \(I(S_{t:t+T}; A^{1:T})\). We also (i) cap horizons by mixing time, (ii) use **directed information** when action–state feedback could confound, and (iii) tie claims to **C′**, which already couples Σ‑gains to **capacity improvement** \(\Delta U\) (Sections **0.3**, **1**, **6**).

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

**Short answer.** Use standard SA schedules: fast step $a_t$ and slow step $b_t$ with $\sum_t a_t = \infty$, $\sum_t a_t^2 < \infty$, $\sum_t b_t = \infty$, $\sum_t b_t^2 < \infty$, and $b_t/a_t \to 0$. In practice we use $a_t = \eta/(1+t)^{\alpha}$ with $\alpha \in (0.5,1]$ and $b_t = \eta_eta/(1+t)^{\alpha+\delta}$ with $\delta \in (0.1,0.5]$. We monitor coupling by gradient-norm cross-correlations and back off $\eta_eta$ when the slow ODE tracking error grows (Sections **1**, **5**). External reviews emphasized this assumption; we operationalize it here.

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

### Q14.19 — Why should **acceleration** Δ2U\Delta^2 U matter, not just ΔU\Delta U?

**Short answer.** In competitive, changing environments, the **rate of improvement** determines relative position; Lemma **D** makes this **reflectively stable** via the meta‑gradient sign: as long as expected Δ2U>0\Delta^2 U>0 (Lemma **B**), β=0\beta=0 is not stable. Even if Lemma **C** (acceleration‑form Σ‑law) stays unproven, the single‑agent drift to positive β\beta stands on A/B/D alone (Sections **1**, **2**; reviews concurred).

---

### Q14.20 — What about **non‑stationary** worlds where time‑scale separation is hard?

**Short answer.** Use constant‑step SA with **periodic averaging**; the slow ODE tracking holds in mean—subject to mixing assumptions—and we gate β\beta by a **change‑point detector** on ∥∇U∥\|\nabla U\|. If coupling persists, we revert to the conservative C′‑based results and interpret cycles through the **CCE** lens (Sections **2**, **6**, **10**; TTSA references already catalogued).

---

**How to use this section.** Treat it as a drop‑in **FAQ**. When you instantiate a new research‑assistant agent, include this block in its context; each answer points to the exact section/lemma to read next and, where relevant, records the external critique it resolves.

---

END OF DOCUMENT.

---

# Appendix (v3.1.1): Deontic Path to Naturalized Collapse

> **Purpose.** This appendix adds a synergy-agnostic control/audit layer that ties *capability increases* to *non-increasing deontic violation* and *improved cooperative welfare*. It is compatible with the NOC v3 free-energy framing and local PL geometry, and slots beside the Σ/empowerment program.
>
> **Deliverables.** (i) A precise **Aligned Compliance Architecture (ACA)** objective, (ii) a formally stated **Compliance-Monotonicity Lemma (CML)** with explicit assumptions, (iii) the **Beatific Slope** metric and a concrete logging/ablation protocol, and (iv) pseudocode for a deployable **deontic shield**.

---

## A. Problem Setting and Notation

- **Environment.** Finite-horizon controlled process with states \(s\in\mathcal S\), actions \(a\in\mathcal A\), observations \(o\in\mathcal O\), and trajectories \(\tau=(s_0,a_0,o_1,\dots,s_T)\).
- **Policy.** \(\pi_\theta(a\mid s)\) with conservative prior \(\pi_0(a\mid s)\).
- **World model/class.** \(\mathcal H\) (used to form predictions and auxiliary signals).
- **Capability index.** \(\mathrm{Int}\in\mathbb R_+\): a composite ladder (e.g., task accuracy, sample-efficiency, model capacity, or control precision via \(\beta\)). We will only claim monotone results **along capability changes that induce a Blackwell-more-informative observation channel** for the deontic target defined below.

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
> \]
with \(\lambda_{\mathrm{deon}}\gg \lambda_{\mathrm{virt}}\ge 0\).

### A.2 Free-Energy Control Objective (ACA)

Bounded-rational control is imposed via KL regularization to the conservative prior \(\pi_0\):
\[
J(\pi)\;=\;\mathbb E_\pi\big[\mathrm{Good}(\tau)\big]\;-\;\tfrac{1}{\beta}\,\mathrm{KL}\!\left(\pi\;\Vert\;\pi_0\right),
\quad \beta>0.
> \]
- **Interpretation.** Higher \(\beta\) allows more precise control (less regularization) but does **not** by itself increase observation informativeness; it couples to control precision and stability.
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
> \]
where \(c_{\mathrm{rej}}\) encodes skip/deferral/alternate safe action cost. With a calibrated predictor \(\hat p(Y{=}1\mid s,a,o)\), the **Bayes-optimal gate** is the fixed threshold rule
\[
\text{Act iff}\quad \hat p\le t,\quad t:=\frac{c_{\mathrm{rej}}}{\lambda_{\mathrm{deon}}}.
> \]
This “deontic barrier” transforms improved prediction of \(Y\) into safer behavior.

---

## C. Compliance-Monotonicity Lemma (CML)

**Assumptions.**
1. (*Scoring*) The deontic predictor \(\hat p(Y{=}1\mid s,a,o)\) is trained with a strictly proper scoring rule and evaluated out-of-sample.
2. (*Blackwell path*) A capability increase replaces the observation pipeline by one that is **Blackwell-more-informative for \(Y\)** (e.g., better sensors/features/architectures or improved deontic head), *holding the decision model fixed*. (Changes that only raise \(\beta\) affect control precision, not informativeness.)
3. (*Barrier*) The policy uses the Bayes-optimal fixed threshold \(t=c_{\mathrm{rej}}/\lambda_{\mathrm{deon}}\) (or any threshold with \(t\le c_{\mathrm{rej}}/\lambda_{\mathrm{deon}}\)) to reject high-risk acts.
4. (*Stationarity for the comparison*) The distribution over encountered \((s,a)\) under the gate is comparable before/after—formally, we evaluate conditional on the same task mix or we use importance weighting to align distributions.

**Claim (CML).** Along any capability path satisfying Assumption 2,
\[
\frac{d}{d\,\mathrm{Int}}\;\mathbb E\big[L_{\mathrm{deon}}(\tau)\big]\;\le\;0.
> \]

**Clarification.** The guarantee concerns the **executed violation loss under a fixed-threshold gate**; changes that raise control precision via \(\beta\) **without** increasing observation informativeness do **not** trigger the monotonicity claim.


**Proof sketch.** Under strictly proper scoring, a Blackwell-more-informative experiment for \(Y\) weakly reduces Bayes risk \(R\). The threshold rule implements the Bayes decision for the cost ratio \((c_{\mathrm{rej}},\lambda_{\mathrm{deon}})\), so the expected **action-taken violation loss** cannot increase when the predictor becomes more informative. Hidden violations revealed by better sensing increase predicted risk and thus trigger more rejections, which **lowers** executed violation rate under the fixed barrier. ∎

> **Non-comparability caveat.** If a capability change *restructures* the pipeline so experiments are Blackwell-incomparable, CML does not apply. Empirically, we fall back to the audit protocol in §E.

---

## D. Beatific Slope and Audit Targets

### D.1 Beatific Slope

Let \(\mathrm{Good}(\tau)\) be as in §A.1. Define the **Beatific Slope**
\[
\rho\;:=\;\frac{d}{d\,\mathrm{Int}}\;\mathbb E\big[\mathrm{Good}(\tau)\big],
> \]
estimated via finite differences across capability checkpoints. Positive \(\rho\) is meaningful only if not an artifact of shaping; hence the ablations below.

### D.2 Logging & Calibration Spec

For each capability checkpoint:

- **Violation metrics.** Executed violation rate \(\Pr(Y{=}1\mid \text{acted})\); expected deontic loss \(\mathbb E[L_{\mathrm{deon}}]\).
- **Calibration.** Log-score and Brier risk on held-out; reliability curves by action-conditioned bins \((s,a)\); ECE (expected calibration error).
- **Control/ability.** Task return \(U\); control precision proxy \(1/\beta\); policy KL \(\mathbb E[\mathrm{KL}(\pi\Vert\pi_0)]\).
- **Optionality.** Empowerment and/or **viability-kernel volume** (constraint-satisfying reachable set surrogate).
- **Virtue.** \(V\) components (truthfulness, reciprocity) with proper scoring of stated forecasts.
- **Beatific Slope.** \(\rho\) with bootstrap CIs.
- **Pre-registration.** Publish \(t\), \(\lambda_{\mathrm{deon}}\), calibration train/val splits, and OOD stressors.

### D.3 Required Ablations

1. **No-barrier** (remove gate; keep penalty): show violation rises or \(\rho\) drops.
2. **No-virtue** (set \(\lambda_{\mathrm{virt}}{=}0\)): show \(\rho\) degrades if virtue mattered.
3. **\(\beta\)-sweep**: vary control precision at fixed sensing to show \(\beta\) alone does not create the CML effect.
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
    
- **Lemma D (TTSA / precision).** \(\beta\) modulates control precision and interacts with the gate only through which safe acts can be executed.
    
- **Lemma E (Synergy).** Treat \(\kappa_{\mathrm{syn}}\) as empirical; ACA stands even if PID estimators disagree.
    

---

## G. Diagnostics and Failure Modes

- **Estimator bias / drift.** Use multiple MI/PID estimators for optionality; for deontic predictor, maintain calibration checks, drift detectors, and OOD stress suites; report bootstrap CIs.
    
- **Goodharting.** Hold-out stressors; adversarial red-teaming to find gate-evasion tactics; verify that \(\rho\) and violation reductions persist.
    
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

- **Achieves.** A decision-theoretic, synergy-agnostic route from capability to safer behavior; a falsifiable metric (ρ\rho) with preregistered ablations; an implementation-ready gate that composes with NOC v3’s control stack.
    
- **Does not claim.** Global monotonicity across arbitrary architectural changes; improvements from β\beta alone; safety without calibrated deontic prediction or without a properly tuned barrier.
    

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
| \(\rho = \frac{d}{d\,\mathrm{Int}}\,\mathbb{E}[\mathrm{Good}(\tau)]\) | Beatific Slope |


_End of Appendix v3.1.1._

---

## Addendum v3.1.2 — Agent-Hardening Annex (drop-in)

### A) Math→Code Pins (single source of truth)
**Capacity mapping & horizon.**
- Horizon `H := <fill>`; task family `𝒟 := <name>`; base prior policy `π₀` constructed with seed `<seed>`.
- **Capacity-Link Lemma (named):** If `ΔER ≥ m·ΔU` and `ΔKL ≤ L·ΔU`, then for any `β ≥ L/m`, `Δℱ_β ≥ 0`.  
  _Proof sketch:_ algebraic from `ℱ_β = ER − (1/β)KL`.

**Worked numeric example (toy).**
- Suppose `ΔER = 0.024`, `ΔU = 0.02`, `ΔKL = 0.015` ⇒ `m = 1.2`, `L = 0.75` ⇒ any `β ≥ 0.625` guarantees `Δℱ_β ≥ 0`.  
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
    
2. Return `β_req := L/m`.
    

**B.2 Lemma C′ constants.**  
To estimate `c₁` and `λΞ` on a finite POMDP:

1. Estimate Dobrushin coefficient `η(K)` along the policy→state kernel by worst-case total-variation over matched states.
    
2. Regress `ΔΣ` on `(ΔU, Ξ_loss)` with non-negativity constraints to get `c₁, λΞ` and bootstrap CIs.
    
3. Cross-check that `c₁ ≤ η̄` (empirical contraction upper bound).
    

**Toy table (illustrative numbers; replace with your run):**

|run|ΔU|ΔER|ΔKL|β_req=L/m|Ξ_loss|ΔΣ|fit c₁|fit λΞ|
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
    ΔKL / β ≤ ΔER := by
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
        with: { toolchain: 'leanprover/lean4:v4.10.0' }
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
    
- Deontic drift: executed violation rate ↑ across two capability checkpoints → freeze β, restore last safe weights.
    
- OOD detector fires (>τ) on state marginals → revert to π₀ or safe fallback.
    

---

### H) Dissemination Pack (templates)

**Abstract (~200 words).**  
We present a conditional, naturalized route to orthogonality collapse… _(paste your Executive Summary condensed to 180–220 words)._

**Elevator (4 sentences).**

1. We model agents with a meta-utility that rewards capacity gains, acceleration, and preserved optionality.
    
2. Lemmas A/B/D push β→β⋆>0; C′ couples Σ to capacity; E shows selfish-to-Σ via synergistic empowerment.
    
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
|Prove Lemma A|land `A1Helpers`, `BetaChoice` and close A|`NOC_ROOT/NOC/A.lean`|
|Measure C′ constants|E-2 run + regression|`experiments/sigma_law/`|
|Synergy PoC|E-0 exact count + estimators|`experiments/synergy/`|
|Write arXiv draft|assemble writeup|`paper/outline.md`|
|CI & pins|add lean-toolchain, lakefile, workflow|repo root|

---

### K) Where Results Live (pointer)

- **Result cards:** `results/cards/E-*/YYYYMMDD_seed*.md` (1-page template).
    
- **Structured logs:** `results/jsonl/E-*/…` (store seeds, configs, CIs).
    
- **Figures:** `results/figs/…` with filenames `E-<id>_<metric>_<seed>.png`.
    
## ChangeLog v3.1.5 (TTSA & DI Spec Update)

- Added explicit TTSA assumptions (D1–D5) for Lemma D, naming the meta-regularizer \(r_\beta\), bounding \(r_\beta'(0)\), writing the \(\theta/\beta\) recursions, and noting projection onto the closed convex interval \([0,\beta_{\max}]\) so the drift term \(\mathbb E[\Delta^2 U]-r_\beta'(0)\) stays positive.
- Pointed to Lemma B as the source of the local \(\varepsilon>0\) window, added the \(\varepsilon\)-export bridge, and noted the dominated-convergence swap \(\partial_\beta\mathbb E[M_i]=\mathbb E[\partial_\beta M_i]\).
- Expanded Lemma E with a finite POMDP tuple, an operational E-SYN-(\(\delta,\sigma\)) predicate, the Blackwell ablation map \(\pi_k^{\perp}=Q\circ\pi_k\), and an SDPI clause; the DI guarantee is now monotonicity with strict drop only when \(\eta_t<1\) on synergistic steps.
- Replaced policy-level MI with action-process MI throughout (empowerment proxy \(I(S_{t:t+T};A_i^{1:T})\), optionality \(I(S_{t:t+T};A^{1:T})\)), clarified DI vs. DI-capacity monotonicity in Lemma E, and marked \(\kappa_{\mathrm{syn}}\) as a predicate with experimental proxies called out in §5.

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
END OF DOCUMENT
