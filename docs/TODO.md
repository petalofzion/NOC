# TODO — Next Formalization Steps

- [ ] **Lemma D / β-meta stability (TTSA)** (`NOC_ROOT/NOC/D/BetaStabilityTTSA.lean`)
  - Context/schedules/noise/regularizer records remain in place; top-level theorem is still a `True` placeholder.
  - Property-layer stepping lemmas are now proved: `TTSA.beta_drift_lower_bound_props`, `TTSA.beta_hits_target_props`, and `DriftHitThresholdPropsContext.hits_threshold_props` (clamp wrappers delegate to them). No `sorry`s remain in the arithmetic layer.
  - Next: connect the abstract drift bounds back to the acceleration window (`g_lower`), then apply a two-time-scale SA/ODE theorem to replace the top-level `True` placeholder with the β-drift result (Tier‑3 target).
  - Optional follow-up: package the projection hypotheses into a dedicated structure (e.g., `ProjIccProps` instance/`IsProjIcc`) so future callers can import the monotonicity bundle directly.

- [x] **Conditional DI–DPI instantiation** (`NOC_ROOT/NOC/E/ConditionalDIDPI.lean` + `NOC_ROOT/NOC/E/Interfaces/DI*.lean`)
  - Interfaces and global lemmas are live; examples added:
    - Typeclass: `NOC/E/Interfaces/Examples/DI_NOC_BSC.lean` (strict schedule).
    - Fiberwise: `NOC/E/Interfaces/Examples/DI_Fiberwise_NCC.lean` (strict fiber).
    - Weighted bound: `NOC/E/Interfaces/Examples/DI_Weighted_Bound.lean` (uses `lemmaE_bound_weighted`).
    - Massey DI toy: `NOC/E/ConditionalDIDPI_Examples.lean` (non‑strict and strict aggregators).
  - Global bounds formalized:
    - `lemmaE_bound_with_eta_cap` (max‑η cap): DI ≤ m · ∑ preₜ when ηₜ ≤ m for all t ≤ n.
    - `lemmaE_bound_weighted` (weighted): with `AggBefore := ∑ preₜ > 0`, DI ≤ (∑ (preₜ/AggBefore)·ηₜ) · AggBefore.
  - DI‑arrow glue available:
    - `conditional_DI_DPI_def` and `_def_strict` build DI_before/after as sums and reuse the aggregator lemmas.

## Lemma E — NCC‑C wiring plan (ready to implement)

Scope and rails
- Regime: NCC only (non‑competitive couplings). Outside NCC (interference/MAC), ablation can raise DI; do not apply Lemma E.
- Horizon: finite `T` (uniform in `T`).
- Filtration: default NCC‑C with `F_{t−1} := (S^{<t}, Z^{≤t})` modeled as a tuple (finite alphabets). NCC‑S is the special case with `Z ≡ ∅`.

Per‑step variables (semantics)
- Upstream `U_t := A_i^{≤t}`. World leg `W_t`. Before output `S_bef_t := R_t(W_t)`. After output `S_aft_t := Q_t(S_bef_t)` with `R_t, Q_t` measurable in `F_{t−1}`.
- Conditional Markov (NCC‑C): `U_t → S_bef_t → S_aft_t | F_{t−1}`.
- Step output for DI: set `S_t := S_aft_t` so `perStep_t = post_t`.

Pre/Post and aggregators
- Per‑step reals: `pre_t := I(U_t; S_bef_t | F_{t−1})`, `post_t := I(U_t; S_aft_t | F_{t−1})`, `perStep_t := post_t`.
- Aggregators: `AggBefore := ∑_t pre_t`, `AggAfter := ∑_t post_t`.
- We compare AggAfter vs AggBefore (not Massey DI). A Massey‑DI thread can be added separately.

Fiberization (for wrappers)
- Fibers `𝔽_t := Supp(F_{t−1})`; weights `w_t(f) := P(F_{t−1}=f)` with `∑_f w_t(f)=1`.
- Per‑fiber: `pre_t(f)`, `post_t(f)`; average to get conditioned `pre_t`, `post_t`.

Per‑step inequalities (DPI + SDPI)
- DPI: for all fibers, `post_t(f) ≤ pre_t(f)` (from the conditional Markov leg) ⇒ `post_t ≤ pre_t`.
- Uniform SDPI: there exists `η_t ∈ [0,1]` such that for all `f`, `post_t(f) ≤ η_t · pre_t(f)`. Averaging yields `post_t ≤ η_t · pre_t`.
- Concrete SDPI sources: BSC/q‑SC (strict unless ε is degenerate) or χ²/spectral bounds. Use a uniform upper bound over fibers.

Strictness
- Global strictness if ∃ `t0` with `η_{t0} < 1` and `pre_{t0}(f0) > 0` on a positive‑probability fiber set: then `AggAfter < AggBefore`.
- Note: strictness does not require `sup_f η_t(f) < 1`; it suffices that some positive‑mass fibers contract strictly with nonzero `pre`.

Global bounds
- Primary: `AggAfter ≤ ∑_t η_t · pre_t`.
- Coarse factor: if all steps contract, `AggAfter ≤ (max_t η_t) · AggBefore`.
- Weighted bound: `AggAfter ≤ (∑_t w̄_t η_t) · AggBefore` with `w̄_t := pre_t / AggBefore` (guard `AggBefore > 0`; if `AggBefore = 0`, then `AggAfter = 0`). Formalized in `lemmaE_bound_weighted`.

Implementation checklist
1) Tighten docstrings and lemma notes (NCC boundary, uniformity clause, strictness on positive‑mass fibers, AggBefore=0 guard, inequality formatting).
2) Add a non‑uniform fiberwise strictness helper: strict sum inequality if ∃ fiber with `η(f) < 1` and positive weighted `pre`.
3) Extend wrappers for NCC‑C (monotone/strict) with clarified docstrings.
4) Add global bounds as corollaries (max‑η, weighted) with the AggBefore guard.
5) Provide a typeclass instance scaffold (NOC model): `perStep := post`, witnesses (`per_le_post := rfl`, `sdpi_step` uniform), `η_range`.
6) Add a small strict example: `T=3`, BSC(0.1) at `t=2`, identity elsewhere ⇒ monotone + strict CI harness.

Status
- Averaging helpers + fiberwise composition lemmas + NOC wrappers are in place (`DI_Averaging`, `DI_Fiberwise`, `DI_NOC_Wrapper`).
- Strict and explicit DI–DPI lemmas exist (`DI.di_strict_under_garbling`, explicit variants).
- Next: execute the checklist above.
  - Next (real NOC model):
    - Fix per‑step conditioning (filtration): choose F_{t−1} and prove inclusion so Massey’s chain rule aligns with SDPI conditioning (A1).
    - Define per‑step DI terms: set `DirectedInfo.perStep t x y` to your causally‑conditioned step term and prove the chain rule identities (before/after).
    - Provide SDPI constants and witnesses: for each step, state η_t with 0 ≤ η_t < 1 and a Markov/garbling witness (e.g., U_t → X_t → Y_t | F_{t−1}); implement `pre/post` with `perStep ≤ post ≤ η·pre`.
    - Strictness (optional): exhibit at least one step with η_t < 1 and nonzero `pre` to get a strict global inequality.
    - Register instances `PerStepData` / `SDPIData` / `SDPIStepData` for the concrete channel and apply `conditional_DI_DPI_massey` and/or `DI.di_monotone_under_garbling`.

- [x] **Interference counterexample (E‑0c)** (`NOC_ROOT/NOC/E/Boundary/GaussianMAC.lean`)
  - Scalar: MI/SNR monotonicity lemmas proved; concrete instances (`scalar_instance_ge`, `scalar_instance_strict`).
  - Vector: `GaussianVector.lean` complete; examples in `GaussianVectorExamples.lean` (identity noise and diagonal specializations). Loewner helpers support whitening and log‑det monotonicity.

- [x] **C′ toy theorem constants (example)** (`NOC_ROOT/NOC/C/CPrimeToyExamples.lean`)
  - A concrete 2×2 instance (Ω = Fin 2) demonstrates `lemmaCprime_expectation_finitary` with explicit params (`P2: c1=1, λΞ=0`) and per‑sample values; see `toy_Cprime_concrete_2x2`.
  - Core scaffolding in `CPrimeToy.lean` kept as‑is; constant computation examples live under `CPrimeToyExamples.lean`.

- [x] **Supplementary examples/tests**
  - Added: `NOC/E/Interfaces/Examples/DI_Weighted_Bound.lean`, `NOC/E/ConditionalDIDPI_Examples.lean`, and ensured `GaussianVectorExamples.lean` remains green.
  - Optional: import examples into `NOC/All.lean` if you want continuous CI coverage for examples.

- [ ] **Documentation sync**
  - After the above items merge, update `docs/README-companion.md`, ChangeLog, and experiment checklists to reflect the completed formalization work.

- [x] **API hygiene (Loewner/log‑det)**
  - Added minimal lemma `logdet_mono_from_opmonotone_min` using only `A ⪯ B` and `PosDef (I±)`.
  - Factored out `det_I_add_psd_ge_one` helper encapsulating the diagonal/product step used to show `det(I+M) ≥ 1`.
  - Kept existing domain‑explicit lemma for stability; callers can migrate to the minimal variant later if preferred.

---

## Blocked Items & Missing Infrastructure

The following tasks are currently stalled because the requisite mathematical or modelling infrastructure is not yet formalised:

- **TTSA β-stability theorem (`lemmaD_beta_stability_TTSA`)**
  - Needs a full two-time-scale SA/ODE meta theorem (measurability, martingale-difference noise bounds, fast attractor selection, ODE limit) which is absent from the library. Until that framework exists the lean proof cannot proceed beyond the arithmetic stepping lemmas.

-- (cleared) Loewner helper lemmas and Gaussian vector boundary are complete and in use.

- **DI instantiation (`NOC_ROOT/NOC/E/Interfaces/DI*.lean`)**
  - Requires a concrete causal model with per-step directed information computations, SDPI witnesses, and filtration-alignment proofs. Those model-specific ingredients are not present, so the typeclass instances and final inequality cannot be instantiated yet.
