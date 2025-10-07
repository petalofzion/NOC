# TODO — Next Formalization Steps

- [ ] **Lemma D / β-meta stability (TTSA)** (`NOC_ROOT/NOC/D/BetaStabilityTTSA.lean`)
  - Context/schedules/noise/regularizer records remain in place; top-level theorem is still a `True` placeholder.
  - Property-layer stepping lemmas are now proved: `TTSA.beta_drift_lower_bound_props`, `TTSA.beta_hits_target_props`, and `DriftHitThresholdPropsContext.hits_threshold_props` (clamp wrappers delegate to them). No `sorry`s remain in the arithmetic layer.
  - Next: connect the abstract drift bounds back to the acceleration window (`g_lower`), then apply a two-time-scale SA/ODE theorem to replace the top-level `True` placeholder with the β-drift result (Tier‑3 target).
  - Optional follow-up: package the projection hypotheses into a dedicated structure (e.g., `ProjIccProps` instance/`IsProjIcc`) so future callers can import the monotonicity bundle directly.

- [ ] **Conditional DI–DPI instantiation** (`NOC_ROOT/NOC/E/ConditionalDIDPI.lean` + `NOC_ROOT/NOC/E/Interfaces/DI.lean`)
  - Typeclass interfaces (`DirectedInfo`, `SDPI`, `SDPIStepWitness`) and global lemmas are now available.
  - Instantiate these for the concrete model (per-step DI decomposition, SDPI witnesses) and apply `conditional_DI_DPI_massey` / `di_monotone_under_garbling` to obtain the full lemma.
  - `NOC_ROOT/NOC/E/Interfaces/DI_Toy.lean` provides minimal data containers for per-step and SDPI witnesses.
  - Provide the filtration-alignment proof for the concrete model and register concrete `PerStepData`/`SDPIData`/`SDPIStepData` instances so the global lemmas specialize (Tier‑2 deliverable).

- [ ] **Interference counterexample (E-0c)** (`NOC_ROOT/NOC/E/Boundary/GaussianMAC.lean`)
  - SNR/MI monotonicity lemmas are proved; the remaining task is to pick explicit channel parameters and show DI increases after ablation (`interference_counterexample`).
  - Vector/log-det scaffolds are in `NOC_ROOT/NOC/E/Boundary/GaussianVector.lean` with helper lemmas in `.../LoewnerHelpers.lean`.
  - `psd_congr` is now proved; finish `inv_antitone_spd` and `logdet_mono_from_opmonotone`, then close the vector log-det goals (`loewner_logdet_mono`, `mi_after_ablation_logdet`) to complete the Tier‑2 Gaussian upgrade.

- [ ] **C′ toy theorem constants** (`NOC_ROOT/NOC/C/CPrimeToy.lean`)
  - Fill in the toy 2×2 instance with explicit Dobrushin/SDPI constants and discharge `toy_Cprime_exists`.
  - Use the existing finitary lemma to export the averaged Σ-law with computed constants.

- [ ] **Supplementary examples/tests**
  - Add Lean examples/smoke tests exercising the DI interfaces and ROI inequality.
  - Extend scripts to validate the Gaussian counterexample and toy Σ-law once the proofs land.

- [ ] **Documentation sync**
  - After the above items merge, update `docs/README-companion.md`, ChangeLog, and experiment checklists to reflect the completed formalization work.

---

## Blocked Items & Missing Infrastructure

The following tasks are currently stalled because the requisite mathematical or modelling infrastructure is not yet formalised:

- **TTSA β-stability theorem (`lemmaD_beta_stability_TTSA`)**
  - Needs a full two-time-scale SA/ODE meta theorem (measurability, martingale-difference noise bounds, fast attractor selection, ODE limit) which is absent from the library. Until that framework exists the lean proof cannot proceed beyond the arithmetic stepping lemmas.

- **Loewner helper lemmas (`inv_antitone_spd`, `logdet_mono_from_opmonotone`)**
  - Requires operator-inequality results on the SPD cone: inverse as an order-reversing map and operator-monotonicity of `A ↦ log det(I + A)`. Mathlib currently lacks these, blocking both helpers and the downstream Gaussian vector lemmas.

- **Loewner helper lemmas (`inv_antitone_spd`, `logdet_mono_from_opmonotone`)**
  - Action plan (no new library primitives required):
      1. For `inv_antitone_spd`, whiten via the positive-definite square root of `A`, set `C := A^{-1/2} B A^{-1/2}`, show `C - I` is PSD with `psd_congr`, use the same trick with `C`’s square root to deduce `I - C⁻¹` is PSD, then conjugate back to recover `A⁻¹ - B⁻¹` PSD.
      2. For `logdet_mono_from_opmonotone`, define `φ(t) = log det (I + A + t(B - A))` and compute the derivative using `d log det X = tr(X⁻¹ dX)` to get `φ′(t) = tr((I + A + t(B-A))⁻¹ (B-A)) ≥ 0`; monotonicity of `φ` yields the desired inequality at `t = 1`.
  - Completing these proofs unblocks the Gaussian vector lemmas.

- **Gaussian vector boundary (`loewner_logdet_mono`, `mi_after_ablation_logdet` and the scalar interference example)**
  - Depends on the Loewner lemmas above; once they are implemented, finish the vector comparison and finalize the interference example.

- **DI instantiation (`NOC_ROOT/NOC/E/Interfaces/DI*.lean`)**
  - Requires a concrete causal model with per-step directed information computations, SDPI witnesses, and filtration-alignment proofs. Those model-specific ingredients are not present, so the typeclass instances and final inequality cannot be instantiated yet.
