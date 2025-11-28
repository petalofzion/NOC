# NOC Repo Companion: File Map, Scope, and How It Connects to the Paper

**Audience:** new technical readers, reviewers, and potential collaborators.  
**Purpose:** explain how each Lean file in this repo maps to the claims and notation in the **NOC v5** document, what each piece *does*, and what it *does not* (yet) do. This is a quick navigational index + scope clarifier.

**Maintainer note:** Keep this companion synced with the cross-module glue in `NOC/Bridge/SigmaBridge.lean`, the Lemma E scaffold in `NOC/E/Core.lean`, and any updates to the narrative in the top-level `README.md` or research blueprint.

---

## 0) Big picture (one minute)

- The paper defines **objects** (capacity $U$, acceleration $\Delta^2 U$, optionality $\Sigma$, deletion penalty $\Xi_{\mathrm{loss}}$) and **lemmas** (A, B, C′/C, D; E is empirical).
- The Lean library proves the **algebraic / conservative tier**: A, B (expected form), the Σ-bridge (`NOC/Bridge/SigmaBridge.lean`), and C′/C (Σ‑laws) — with *no* `sorry`.
- **Lemma D (β-stability)** is backed by a rigorous **Two-Time-Scale Stochastic Approximation (TTSA)** framework (`NOC/D/*`). The arithmetic and property layers are proved; the final ODE convergence theorem contains explicit `sorry` placeholders pending upstream mathlib dependencies.
- **What Lean intentionally does *not* define:** $\Sigma$ as MI, empowerment, or any estimator internals; those live in the **experiments** (E‑0, E‑2, E‑3b). The Lean side takes them as symbols/inputs and proves the inequalities they must satisfy *if* measured as in the paper.
- **Lemma E** (synergy ⇒ empowerment drop) is **empirical** in this release. In Lean we expose a clean predicate to carry that assumption, plus a **Directed Information (DI)** shell to formalize the "NCC" (Non-Competitive Coupling) regime where the lemma holds algebraically.

Think of the split as: *Lean proves the shape; Experiments attach numbers to the shape.*

---

## 1) Quick start

- Build: `lake update && lake build`
- Root export: `import NOC.All`
- Minimal MI/synergy interface (finite tabular scaffolding): `import NOC.E.Core` (see §4).
- **Smoke Tests:** Check `NOC/Dev/Checks.lean` to verify that key definitions (A, B, C, HB) elaborate correctly in your environment.

---

## 2) Concept → file map (where to look, what to expect)

| Paper concept / claim | What the repo provides | Where |
|---|---|---|
| **State, policies, trajectories** | Finite-horizon POMDP/Policies scaffolding (`FinPOMDP`, `PolicyProfile`). | `NOC/E/Core.lean` |
| **Capacity $U$, $\Delta U$, $\Delta^2 U$** | Abstract symbols or helper defs; used on the RHS of Σ‑laws. | `NOC/B/*` (expectation wrappers), `NOC/C/*` |
| **Option­ality $\Sigma$** | **Abstract** `dSigma` symbol (Lean does not hard‑code MI). | `NOC/C/*`, `NOC/D/*` |
| **Directed Information (DI)** | Formal shell for DI, Massey's Chain Rule, and SDPI interfaces. | `NOC/E/ConditionalDIDPI.lean`, `NOC/E/Interfaces/DI.lean` |
| **Discrete Information** | Shannon Entropy/MI for Fintype (scaffolding). | `NOC/E/Information/Discrete.lean` |
| **Deletion penalty $\Xi_{\mathrm{loss}}$** | Name/slot and algebraic handling; see interfaces + C′/D usage. | `NOC/C/CPrime.lean`, `NOC/Bridge/SigmaBridge.lean`, `NOC/D/Interfaces.lean` |
| **Lemma A (β‑choice ⇒ $\Delta \mathcal{F}_\beta \ge 0$)** | Arithmetic lemmas `lemmaA_freeEnergy_nonneg_*` (product/ratio) capturing the β‑choice trick. | `NOC/A/BasicHelp.lean`, `NOC/A/BasicNoHelp.lean` (helpers in `NOC/A/Helpers.lean`) |
| **Lemma B (local → expected $\Delta^2 U > 0$)** | Pointwise bridge + **expected**/finite‑support lifts (`avg`, expectation lemmas). | `NOC/B/Core.lean`, `NOC/B/Expectation.lean` |
| **Lemma D (β-stability)** | Meta-gradient dynamics via **Two-Time-Scale Stochastic Approximation (TTSA)**. | `NOC/D/BetaStability.lean` (shell), `NOC/D/BetaStabilityTTSA.lean` (stepping), `NOC/D/TTSA_Convergence.lean` (convergence). |
| **Lemma C′ (Σ‑law, improvement)** | `SigmaLawParams` with `c1, λXi ≥ 0`; pointwise + expected + “good‑set” finitary splits. | `NOC/C/CPrime.lean` |
| **Lemma C (Σ‑law, acceleration)** | The **acceleration** form: $\Delta\Sigma \ge c_1\Delta^2 U - \dots$ (distinct from C′). | `NOC/C/C.lean` |
| **Lemma E (synergy ⇒ empowerment drop)** | **Empirical**. In Lean we expose predicates (`ESynergyWitness`) and POMDP scaffolding. | `NOC/E/Core.lean`, `NOC/E/Interfaces/DI_Fiberwise.lean` (NCC regime) |
| **ROI / Trade-offs** | Logic for "Conversion vs Ablation" comparison (cost-benefit analysis). | `NOC/E/ConversionVsAblation.lean` |
| **Heavy Ball (Dynamics)** | 1D Quadratic HB "lab" for testing acceleration/stability claims. | `NOC/HB/Quadratic.lean`, `NOC/HB/CloseLoop.lean` |
| **Probability/Convergence** | Martingale machinery (Robbins-Siegmund, MDS) backing TTSA. | `NOC/Prob/*` |

---

## 3) What each lemma file *does* vs *does not* do

### A — `NOC/A/`
- **Does:** `BasicHelp.lean` and `BasicNoHelp.lean` formalize the free‑energy arithmetic behind Lemma A. If `ΔER ≥ m·ΔU` and `ΔKL ≤ L·ΔU` and `β ≥ L/m`, then `ΔER − ΔKL/β ≥ 0`. `Helpers.lean` provides reusable algebra steps.
- **Does not:** define $ER$, $KL$, or $U$ themselves; those come from your modeling layer. A is purely inequality algebra.

### B — `NOC/B/Core.lean`, `NOC/B/Expectation.lean`
- **Does:** lift local/pointwise improvement assumptions to **expected** statements over a finite support (via `avg` wrappers). This mirrors “positive expected $\Delta^2 U$ off‑optimum.”
- **Does not:** implement any optimizer dynamics; it assumes PL‑like premises or local curvature and produces expectation forms.

### D — `NOC/D/BetaStability.lean` & TTSA
- **Does:** `BetaStability.lean` defines the high-level stability claim. The heavy lifting is in `BetaStabilityTTSA.lean` and `TTSA_Convergence.lean`.
- **Status:** The **arithmetic** and **stepping** layers are proved. The final ODE convergence theorem is currently **incomplete** (marked with `sorry`) pending a formalization of the TTSA meta-theorem.
- **Dependencies:** Relies heavily on `NOC/Prob/RobbinsSiegmund.lean` (supermartingale convergence), `NOC/Prob/MDS.lean` (martingales), and `NOC/Prob/Alignment.lean` (drift alignment interface).
- **Interfaces:** `NOC/D/Interfaces.lean` provides `UpperLink` and `SDPILink` predicates that connect D-premises to the C' Σ-law.

### C′ (improvement Σ‑law) — `NOC/C/CPrime.lean`
- **Does:** present the core boxed inequality  
  \[
  \Delta\Sigma \;\ge\; c_1\,\Delta U \;-\; \lambda_\Xi\,\Xi_{\mathrm{loss}}
  \]
  with (i) pointwise, (ii) expected, and (iii) **good‑set** finitary split variants (exactly matching the paper’s “mass‑θ on G” usage).
- **Does not:** define $\Sigma$, $\Xi_{\mathrm{loss}}$, or how to compute them; it treats them as named inputs.
- **Proof of Concept:** `NOC/C/CPrimeToyExamples.lean` provides a concrete, no-sorry instantiation of the Σ-law on a 2x2 domain to prove the typeclasses are inhabited.

### C (acceleration Σ‑law) — `NOC/C/C.lean`
- **Does:** The **acceleration** counterpart to C′. States $\Delta\Sigma \ge c_1\Delta^2 U - \lambda_\Xi\Xi_{\mathrm{loss}}$.
- **Does not:** Prove the *dynamical* link from HB to this inequality (that's the job of model-specific files like `NOC/HB`), but provides the algebraic container for it.

### Bridge — `NOC/Bridge/SigmaBridge.lean`
- **Does:** package an “upper link” plus a Dobrushin/SDPI-style inequality via `SigmaBridgeParams`, eliminating intermediates to expose the Σ-law constants (pointwise & expectation).
- **Does not:** prove the SDPI bounds; they are assumed or empirically fitted (typically from E-2).

### Lemma E & Information Geometry — `NOC/E/`
- **NCC Regime (The "Happy Path"):** `Interfaces/DI_Fiberwise.lean` and `DI_NOC_Wrapper.lean` formalize the **Non-Competitive Coupling (NCC)** case. Here, the "ablation" is a data-processing operation (garbling), so strict SDPI applies, and Lemma E holds algebraically.
- **Interference Regime (The Boundary):** `Boundary/GaussianMAC.lean` (scaffolding with `sorry`) and `GaussianVector.lean` provide the infrastructure for counterexamples where NCC fails. In these regimes, ablation can actually *increase* capacity.
- **Core Logic:** `ConditionalDIDPI.lean` and `Interfaces/DI_Toy.lean` provide the high-level shell for Directed Information bounds. `Information/Discrete.lean` (new) provides the scaffolding for Fintype-based Shannon Entropy.

---

## 4) Supporting Infrastructure & Examples

### Dynamics Lab — `NOC/HB/`
- **Does:** rigorous analysis of **Heavy-Ball (HB) momentum** on 1D quadratics.
- **Files:** `Quadratic.lean` (update steps, operators), `CloseLoop.lean` (closed-loop algebra). `Link.lean` provides a **bundle API** (`HBLinkBundle`) for packaging global or restricted links to be fed into the C' expectation lemmas. `Integration.lean` and `AdaptiveIntegration.lean` provide end-to-end verified proofs of acceleration.
- **Why:** serves as a concrete "petri dish" to verify how acceleration creates the $\Delta^2 U$ term required for Lemma C and D.

### Probability Engine — `NOC/Prob/`
- **Does:** general-purpose probability and martingale theory.
- **Files:** `RobbinsSiegmund.lean` (supermartingale convergence), `MDS.lean` (martingale difference sequences), `Alignment.lean` (drift alignment interface).
- **Why:** powers the stochastic convergence proofs in Lemma D (TTSA).

### ROI Logic — `NOC/E/ConversionVsAblation.lean`
- **Does:** Formalizes the comparison: "Is the utility gain from conversion ($\gamma \Delta \Sigma$) greater than the cost of ablation ($\zeta \Delta J$)?"
- **Why:** This is the central "naturalization" check—if this holds, the system prefers to convert capacity rather than destroy it.
- **Status:** Scaffolding (no `sorry`, but logic is purely algebraic).

### Interfaces — `NOC/E/Core.lean`
- **Does:** Defines `FinPOMDP`, `PolicyProfile`, `ESynergyWitness`, and `SDPIHypothesis`.
- **Why:** These are the "clean predicates" assumed by the formal layer. The experiments must instantiate these structures.

### Example Usage — `NOC/Examples/D/HowToUseDPath.lean`
- **Does:** Demonstrates how to **call** the D-path lemmas (Upper Link + SDPI ⇒ C') by passing in user-provided proofs for a model.
- **Why:** Serves as a template for reviewers or developers integrating new models.

---

## 5) What’s intentionally **missing** (and how to plug it)

- **No MI/Σ implementation in Lean.**  
  *Why:* avoids measure‑theory and estimator bias in the formal layer.  
  *Plug:* Experiments (E‑0 exact count; E‑2 with InfoNCE/MINE/kNN; E‑3b sweeps) compute $\Sigma$, $\Delta\Sigma$, and $\Xi_{\mathrm{loss}}$. Those numbers are then fed to the Σ‑law inequalities.

- **No formal Lemma E proof (yet).**  
  *Why:* scoped as empirical in v3.1.2.  
  *Plug:* Use `ESynergyWitness` / `PositiveSynergyOn` as a hypothesis in any theorem that depended on E; use E‑0/E‑2 results to justify it.

- **No SDPI/Dobrushin derivation in Lean.**  
  *Why:* can be imported as premises OR calibrated empirically (E‑2).  
  *Plug:* Provide constants `c1, λXi` via `SigmaBridgeParams` or from fitted experiments.

---

## 6) Contributing

- If you’re adding a new dynamic model, implement your premises (PL region, curvature, or links) and call the **expected Σ‑law** on a good set $G$.  
- If you’re on the experiment side, focus on E‑0 (exact toy), E‑2 (fidelity curve, MI estimators), and E‑3b (cost sweeps and the preserve ratio).

---

*This companion doc is meant to sit next to `README.md`. Feel free to edit file paths to match your exact tree names if they differ slightly in your repo.*
