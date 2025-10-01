# NOC Repo Companion: File Map, Scope, and How It Connects to the Paper

**Audience:** new technical readers, reviewers, and potential collaborators.  
**Purpose:** explain how each Lean file in this repo maps to the claims and notation in the **NOC v3.1.4** document, what each piece *does*, and what it *does not* (yet) do. This is a quick navigational index + scope clarifier.

**Maintainer note:** Keep this companion synced with the cross-module glue in `NOC/Bridge/UpperLinkToSigma.lean`, the Lemma E scaffold in `NOC/E/Core.lean`, and any updates to the narrative in the top-level `README.md` or research blueprint.

---

## 0) Big picture (one minute)

- The paper defines **objects** (capacity \(U\), acceleration \(\Delta^2 U\), optionality \(\Sigma\), deletion penalty \(\Xi_{\mathrm{loss}}\)) and **lemmas** (A, B, C′/C, D; E is empirical).
- The Lean library proves the **algebraic / conservative tier**: A, B (expected form), the Σ-bridge (`NOC/Bridge/UpperLinkToSigma.lean`), and C′/C (Σ‑laws) — with *no* `sorry`; Lemma D (β-stability) remains planned.
- **What Lean intentionally does *not* define:** \(\Sigma\) as MI, empowerment, or any estimator internals; those live in the **experiments** (E‑0, E‑2, E‑3b). The Lean side takes them as symbols/inputs and proves the inequalities they must satisfy *if* measured as in the paper.
- **Lemma E** (synergistic empowerment ⇒ selfish→Σ) is **empirical** in this release: E‑0 exact toy result, E‑2 calibration, E‑3b cost sweeps. In Lean we expose a clean predicate to carry that assumption.

Think of the split as: *Lean proves the shape; Experiments attach numbers to the shape.*

---

## 1) Quick start

- Build: `lake update && lake build`
- Root export: `import NOC`
- Minimal MI/synergy interface: `import NOC.Interfaces.Synergy` (see §4).

---

## 2) Concept → file map (where to look, what to expect)

| Paper concept / claim | What the repo provides | Where |
|---|---|---|
| **State, policies, trajectories** | Basic types/aliases for finite processes & policies (used by examples/lemmas). | `NOC/Model.lean` *(or equivalent foundation file in your tree)* |
| **Meta‑utility (informal)** | Not formalized; used only in commentary and to motivate lemmas A/B/D/C′. | — |
| **Capacity \(U\), ΔU, Δ²U** | Abstract symbols or helper defs; used on the RHS of Σ‑laws. | `NOC/B/*` (expectation wrappers), `NOC/C/*` |
| **Option­ality \(\Sigma\)** | **Abstract** `dSigma` symbol (Lean does not hard‑code MI). | `NOC/C/*`, `NOC/D/*` |
| **Deletion penalty \(\Xi_{\mathrm{loss}}\)** | Name/slot and algebraic handling; see interfaces + C′/D usage. | `NOC/C/CPrime.lean`, `NOC/Bridge/UpperLinkToSigma.lean`, `NOC/D/Interfaces.lean` |
| **Lemma A (β‑choice ⇒ Δℱβ≥0)** | Arithmetic lemmas `lemmaA_freeEnergy_nonneg_*` (product/ratio) capturing the β‑choice trick. | `NOC/A.lean`, `NOC/AHelpers.lean` |
| **Lemma B (local → expected Δ²U>0)** | Pointwise bridge + **expected**/finite‑support lifts (`avg`, expectation lemmas). | `NOC/B/Core.lean`, `NOC/B/Expectation.lean` |
| **Lemma D (β-stability, planned)** | Reflective stability of precision (TTSA meta-gradient). | `NOC/D/BetaStability.lean` |
| **Lemma C′ (Σ‑law, improvement)** | `SigmaLawParams` with `c1, λXi ≥ 0`; pointwise + expected + “good‑set” finitary splits. | `NOC/C/CPrime.lean` |
| **Lemma C (Σ‑law, acceleration)** | Like C′ but with Δ²U and velocity/smoothness constants. | `NOC/C/C.lean` *(if present in your tree)* |
| **Lemma E (synergy ⇒ empowerment drop)** | **Empirical**. In Lean we expose predicates you can assume once experiments verify them. | `NOC/Interfaces/Synergy.lean` |
| **Worked example** | How to pass premises on a “good set” \(G\) and call the expectation Σ‑law. | `NOC/Examples/D/HowToUseDPath.lean` |

> If a specific foundation file is named slightly differently in your tree (e.g., `Model.lean`), update this table accordingly when you commit.

---

## 3) What each lemma file *does* vs *does not* do

### A — `NOC/A.lean`, `NOC/AHelpers.lean`
- **Does:** formalize the free‑energy arithmetic behind Lemma A. If `ΔER ≥ m·ΔU` and `ΔKL ≤ L·ΔU` and `β ≥ L/m`, then `ΔER − ΔKL/β ≥ 0`. This is the β‑choice (“capacity‑compatible drift”) move used in the paper.
- **Does not:** define \(ER\), \(KL\), or \(U\) themselves; those come from your modeling layer. A is purely inequality algebra.

### B — `NOC/B/Core.lean`, `NOC/B/Expectation.lean`
- **Does:** lift local/pointwise improvement assumptions to **expected** statements over a finite support (via `avg` wrappers). This mirrors “positive expected Δ²U off‑optimum.”
- **Does not:** implement any optimizer dynamics; it assumes PL‑like premises or local curvature and produces expectation forms.

### D — `NOC/D/BetaStability.lean` (planned)
- **Does (eventually):** deliver the β-stability lemma via two-time-scale/ODE analysis (using Lemma B’s acceleration). Currently a scaffold with the intended statement and hypotheses.
- **Does not:** contain the Σ-bridge algebra; that now lives in `NOC/Bridge/UpperLinkToSigma.lean`.

### Bridge — `NOC/Bridge/UpperLinkToSigma.lean`
- **Does:** package an “upper link” plus a Dobrushin/SDPI-style inequality via `DUpperLinkParams`, eliminating intermediates to expose the Σ-law constants (pointwise & expectation).
- **Does not:** prove the SDPI bounds; they are assumed or empirically fitted (typically from E-2).

### C′ (improvement Σ‑law) — `NOC/C/CPrime.lean`
- **Does:** present the core boxed inequality  
  \[
  \Delta\Sigma \;\ge\; c_1\,\Delta U \;-\; \lambda_\Xi\,\Xi_{\mathrm{loss}}
  \]
  with (i) pointwise, (ii) expected, and (iii) **good‑set** finitary split variants (exactly matching the paper’s “mass‑θ on G” usage).
- **Does not:** define \(\Sigma\), \(\Xi_{\mathrm{loss}}\), or how to compute them; it treats them as named inputs.

### C (acceleration Σ‑law) — `NOC/C/C.lean` *(if present)*
- **Does:** same pattern as C′ but with Δ²U and an extra smoothness/velocity constant.
- **Does not:** same caveat — no numeric MI on the Lean side.

### Examples — `NOC/Examples/D/HowToUseDPath.lean`
- **Does:** show how a client supplies *their* \(A, B, \Delta U, \Delta\Sigma\), chooses a “good set” \(G\), and calls the expectation Σ‑law. Good template for reviewers and tests.
- **Does not:** compute MI — this is a structural usage example.

---

## 4) Interfaces for empirical Lemma‑E‑style premises

**File:** `NOC/Interfaces/Synergy.lean` (small, dependency‑light)

- `abbrev XiLoss (Ω) := Ω → ℝ` — name for the per‑scenario deletion penalty \(\Xi_{\mathrm{loss}}\).
- `def PositiveSynergyPointwise … := 0 < xi ω` — pointwise positivity (what E‑0 often witnesses).
- `def PositiveSynergyOn …` — average positivity on a finite “good set” \(G\):  
  \(G \neq \varnothing \wedge 0 < \frac{1}{|G|}\sum_{\omega\in G}\Xi_{\mathrm{loss}}(\omega)\).
- Small helper lemmas that turn nonnegativity + one positive point into average positivity.
- `@[inline] def xiDiff withScore withoutScore` — convenience alias to define \(\Xi_{\mathrm{loss}}(\omega)=\Sigma_{\text{with}}(\omega)-\Sigma_{\text{without}}(\omega)\) without committing to MI internals in Lean.

**Why:** The paper treats Lemma E as **empirical** (E‑0 exact toy, E‑2 calibration, E‑3b cost sweeps). On the Lean side we **assume** a synergy predicate where needed; the experiments establish it.

---

## 5) What’s intentionally **missing** (and how to plug it)

- **No MI/Σ implementation in Lean.**  
  *Why:* avoids measure‑theory and estimator bias in the formal layer.  
  *Plug:* Experiments (E‑0 exact count; E‑2 with InfoNCE/MINE/kNN; E‑3b sweeps) compute \(\Sigma\), \(\Delta\Sigma\), and \(\Xi_{\mathrm{loss}}\). Those numbers are then fed to the Σ‑law inequalities.

- **No formal Lemma E proof (yet).**  
  *Why:* scoped as empirical in v3.1.2.  
  *Plug:* Use `PositiveSynergyOn` as a hypothesis in any theorem that depended on E; use E‑0/E‑2 results to justify it.

- **No SDPI/Dobrushin derivation in Lean.**  
  *Why:* can be imported as premises OR calibrated empirically (E‑2).  
  *Plug:* Provide constants `c1, λXi` via `DUpperLinkParams` or from fitted experiments.

---

## 6) How to read the Σ‑law proofs (C′) correctly

- Check **signs** and **quantifiers**:  
  `ΔΣ ≥ c1·ΔU − λXi·Ξ_loss`, with `c1, λXi ≥ 0`.  
  If you use the **expected** form, both sides are expectations (optionally conditioned on a good set).
- The Σ‑law is **agnostic** to how you got \(\Delta\Sigma\) and \(\Xi_{\mathrm{loss}}\) — that’s by design. It’s the reusable bound the empirical side must satisfy.

---

## 7) Minimal workflow for a new contributor

1. **Build Lean**: `lake update && lake build`.  
2. **Skim**: `NOC/C/CPrime.lean` (Σ‑law), `NOC/Bridge/UpperLinkToSigma.lean` (bridge), `NOC/B/Expectation.lean` (expected lifts).  
3. **Use**: open `NOC/Examples/D/HowToUseDPath.lean` to see how to pass premises and call the expectation Σ‑law.  
4. **Experiment side (later)**: run E‑0 / E‑2 to produce \(\Delta\Sigma\) and \(\Xi_{\mathrm{loss}}\) values; compare to Σ‑law; compute the preserve ratio \(\rho=\gamma\Delta\Sigma/(\zeta\Delta J)\).

---

## 8) FAQ for reviewers

- **“Where is \(\Sigma\) defined as MI?”** In the experiments, not in Lean. The formal layer proves the inequalities that MI‑based \(\Delta\Sigma\) must satisfy; the empirical layer computes MI (exact on tiny worlds; estimators on larger ones).
- **“Where is Lemma E?”** Empirical. See `NOC/Interfaces/Synergy.lean` for the predicate we assume and the experiments (E‑0/E‑2) that establish it.
- **“What if my domain violates the premises?”** Then the Σ‑law still holds as a formal implication, but your empirical numbers may not meet the bound; the paper explicitly treats those as **outside** the claimed regime.
- **“Can I swap in different estimators?”** Yes — the formal layer is estimator‑agnostic. The experiments recommend multiple estimators + anti‑Goodhart checks.

---

## 9) Contributing

- If you’re adding a new dynamic model, implement your premises (PL region, curvature, or links) and call the **expected Σ‑law** on a good set \(G\).  
- If you’re on the experiment side, focus on E‑0 (exact toy), E‑2 (fidelity curve, MI estimators), and E‑3b (cost sweeps and the preserve ratio).

---

*This companion doc is meant to sit next to `README.md`. Feel free to edit file paths to match your exact tree names if they differ slightly in your repo.*
