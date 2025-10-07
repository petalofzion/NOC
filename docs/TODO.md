# TODO — Next Formalization Steps

- [ ] **Lemma D / β-meta stability (TTSA)** (`NOC_ROOT/NOC/D/BetaStabilityTTSA.lean`)
  - Context/schedules/noise/regularizer records remain in place; top-level theorem is still a `True` placeholder.
  - Prove the stepping lemmas (`DriftHitThresholdContext.hits_threshold`, `TTSA.beta_drift_lower_bound`, `TTSA.beta_hits_target`) to replace the current `sorry`s.
  - Use the new property-based projection interface `TTSA.ProjIccProps`; when `proj` is clamp, reuse `TTSA.clamp_props` (wrapper provided).
  - Upgrade `TTSA.ProjIccProps` (or introduce `IsProjIcc`) to package monotonicity in the bundle and port the lemmas to consume it; add matching helper lemmas for `DriftHitThresholdPropsContext` so both property routes line up.
  - After the arithmetic lemmas, hook `g` back to the acceleration window and apply a two-time-scale SA/ODE theorem to obtain the positive fixed point β⋆ > 0 (Tier‑3 target).
  - Once the arithmetic lemmas land, turn the scaffolded TTSA theorem into the full β-drift result (ODE/SA argument).

- [ ] **Conditional DI–DPI instantiation** (`NOC_ROOT/NOC/E/ConditionalDIDPI.lean` + `NOC_ROOT/NOC/E/Interfaces/DI.lean`)
  - Typeclass interfaces (`DirectedInfo`, `SDPI`, `SDPIStepWitness`) and global lemmas are now available.
  - Instantiate these for the concrete model (per-step DI decomposition, SDPI witnesses) and apply `conditional_DI_DPI_massey` / `di_monotone_under_garbling` to obtain the full lemma.
  - `NOC_ROOT/NOC/E/Interfaces/DI_Toy.lean` provides minimal data containers for per-step and SDPI witnesses.
  - Provide the filtration-alignment proof for the concrete model and register concrete `PerStepData`/`SDPIData`/`SDPIStepData` instances so the global lemmas specialize (Tier‑2 deliverable).

- [ ] **Interference counterexample (E-0c)** (`NOC_ROOT/NOC/E/Boundary/GaussianMAC.lean`)
  - SNR/MI monotonicity lemmas are proved; the remaining task is to pick explicit channel parameters and show DI increases after ablation (`interference_counterexample`).
  - Vector/log-det scaffolds are in `NOC_ROOT/NOC/E/Boundary/GaussianVector.lean` with helper lemmas in `.../LoewnerHelpers.lean`.
  - Fill the Loewner helper lemmas (`psd_congr`, `inv_antitone_spd`, `logdet_mono_from_opmonotone`) and close the vector log-det targets (`loewner_logdet_mono`, `mi_after_ablation_logdet`) to finish the Tier‑2 Gaussian upgrade.

- [ ] **C′ toy theorem constants** (`NOC_ROOT/NOC/C/CPrimeToy.lean`)
  - Fill in the toy 2×2 instance with explicit Dobrushin/SDPI constants and discharge `toy_Cprime_exists`.
  - Use the existing finitary lemma to export the averaged Σ-law with computed constants.

- [ ] **Supplementary examples/tests**
  - Add Lean examples/smoke tests exercising the DI interfaces and ROI inequality.
  - Extend scripts to validate the Gaussian counterexample and toy Σ-law once the proofs land.

- [ ] **Documentation sync**
  - After the above items merge, update `docs/README-companion.md`, ChangeLog, and experiment checklists to reflect the completed formalization work.
