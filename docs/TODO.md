# TODO — Next Formalization Steps

- [ ] **Lemma D / β-meta stability (TTSA)** (`NOC_ROOT/NOC/D/BetaStabilityTTSA.lean`)
  - Context/schedules/noise/regularizer records remain in place; top-level theorem is still a `True` placeholder.
  - Property-layer stepping lemmas are now proved: `TTSA.beta_drift_lower_bound_props`, `TTSA.beta_hits_target_props`, and `DriftHitThresholdPropsContext.hits_threshold_props` (clamp wrappers delegate to them). No `sorry`s remain in the arithmetic layer.
  - Next: connect the abstract drift bounds back to the acceleration window (`g_lower`), then apply a two-time-scale SA/ODE theorem to replace the top-level `True` placeholder with the β-drift result (Tier‑3 target).
  - Optional follow-up: package the projection hypotheses into a dedicated structure (e.g., `ProjIccProps` instance/`IsProjIcc`) so future callers can import the monotonicity bundle directly.

- [ ] **Conditional DI–DPI instantiation** (`NOC_ROOT/NOC/E/ConditionalDIDPI.lean` + `NOC_ROOT/NOC/E/Interfaces/DI*.lean`)
  - Status: interfaces and global lemmas are available; a minimal toy instantiation is added in `DI_ToyExample.lean` (Unit×Unit, ηₜ = 1/2) demonstrating the aggregator.
  - Next: instantiate for the concrete model (per-step DI decomposition, SDPI witnesses) and apply `conditional_DI_DPI_massey` / `di_monotone_under_garbling`.
  - Provide filtration-alignment and register `PerStepData`/`SDPIData`/`SDPIStepData` instances for the concrete channel (Tier‑2 deliverable).

- [ ] **Interference counterexample (E‑0c)** (`NOC_ROOT/NOC/E/Boundary/GaussianMAC.lean`)
  - Scalar: MI/SNR monotonicity lemmas are proved; concrete instances added (`scalar_instance_ge`, `scalar_instance_strict`).
  - Vector: `GaussianVector.lean` complete; helper examples added in `GaussianVectorExamples.lean` (identity noise/PSD choices).
  - Loewner helpers complete: `psd_congr`, `inv_antitone_spd`, `logdet_mono_from_opmonotone` (whitening + spectral/product) with robust calc chains.

- [ ] **C′ toy theorem constants** (`NOC_ROOT/NOC/C/CPrimeToy.lean`)
  - Fill in the toy 2×2 instance with explicit Dobrushin/SDPI constants and discharge `toy_Cprime_exists`.
  - Use the existing finitary lemma to export the averaged Σ-law with computed constants.

- [ ] **Supplementary examples/tests**
  - Examples added: `GaussianVectorExamples.lean` and `DI_ToyExample.lean` (sanity harnesses).
  - Next: add a 2×2 diagonal reduction example explicitly showing scalar/vector consistency, and a small ROI example if needed.

- [ ] **Documentation sync**
  - After the above items merge, update `docs/README-companion.md`, ChangeLog, and experiment checklists to reflect the completed formalization work.

- [ ] **API hygiene (Loewner/log‑det)**
  - Add a minimal lemma `logdet_mono_from_opmonotone_min` using only `A ⪯ B` and `PosDef (I±)`.
  - Factor out a `det_I_add_sandwich_psd_ge_one` helper encapsulating the diagonal/product step used to show `det(I+M) ≥ 1`.
  - Optionally migrate GaussianVector to the minimal lemma (or keep domain‑explicit lemma for clarity).

---

## Blocked Items & Missing Infrastructure

The following tasks are currently stalled because the requisite mathematical or modelling infrastructure is not yet formalised:

- **TTSA β-stability theorem (`lemmaD_beta_stability_TTSA`)**
  - Needs a full two-time-scale SA/ODE meta theorem (measurability, martingale-difference noise bounds, fast attractor selection, ODE limit) which is absent from the library. Until that framework exists the lean proof cannot proceed beyond the arithmetic stepping lemmas.

-- (cleared) Loewner helper lemmas and Gaussian vector boundary are complete and in use.

- **DI instantiation (`NOC_ROOT/NOC/E/Interfaces/DI*.lean`)**
  - Requires a concrete causal model with per-step directed information computations, SDPI witnesses, and filtration-alignment proofs. Those model-specific ingredients are not present, so the typeclass instances and final inequality cannot be instantiated yet.
