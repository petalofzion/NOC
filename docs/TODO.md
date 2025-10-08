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
  - Scalar status: SNR/MI monotonicity lemmas are proved (e.g., `mi_of_snr_mono`, `mi_after_ablation_ge_with_interference`). Pick explicit channel parameters and finalize the illustrative counterexample.
  - Vector path: scaffolds live in `NOC_ROOT/NOC/E/Boundary/GaussianVector.lean`; helper lemmas in `.../LoewnerHelpers.lean`.
  - Loewner helpers: `psd_congr` and `inv_antitone_spd` are proved. `logdet_mono_from_opmonotone` is nearly complete: whitening, unitary conjugation, and determinant factorization are implemented with explicit `calc` chains (no heavy `simp`).
  - Remaining mechanical items in `LoewnerHelpers.logdet_mono_from_opmonotone`:
    - Close the S·(1+B)·S = 1 + M step entirely with `calc` (no recursion): use `B = A + (B−A)`, distribute with `Matrix.mul_add`/`Matrix.add_mul`, and rewrite `Sᴴ = S` once.
    - Keep `U`/`D` local; derive `det(Uᴴ (I+M) U) = det(I+D)` via two `Matrix.det_mul` calls and the identity `det(Uᴴ)·det(U) = 1` (proved via transpose on ℝ).
    - Apply the diagonal determinant identity `det(I + diagonal v) = ∏ (1+vᵢ)` and `eigenvalues(M) ≥ 0` to conclude `det(I+M) ≥ 1`.
    - Finish with `Real.log_le_log` using `det(1+A) = det(R)^2` and `det(1+B) = det(R)^2 · det(1+M)`.
  - Once green, close `GaussianVector.lean` by delegating to the helper for:
    - `loewner_logdet_mono` (matrix Loewner monotonicity of log-det), and
    - `mi_after_ablation_logdet` (PSD-ordering of effective SNR matrices ⇒ MI proxy increases).

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
  - Current status: `psd_one_sub_inv_of_ge_one` and `inv_antitone_spd` are proved. For `logdet_mono_from_opmonotone`, whitening/conjugation and determinant factorization are implemented; remaining work is to finalize the unitary equalities and the diagonal det product rewrite.
  - Concrete next steps (targeted, robust):
      1. Derive `Uᴴ*U = I` (from `eigenvectorUnitary` property) and `U*Uᴴ = I` (via conjTranspose); use `calc` blocks instead of large `simp` chains.
      2. Prove `det(Uᴴ (I+M) U) = det(I+D)` using `Matrix.det_mul` twice and `det(Uᴴ)·det(U)=1`.
      3. Conclude `det(I+M) = det(I+D)` and apply `det(I + diagonal v) = ∏ (1+v_i)` with `v_i = eigenvalues(M) ≥ 0` to get `det(I+M) ≥ 1`.
      4. Apply `Real.log_le_log` using `det(I+A) = det(R)^2` and `det(I+B) = det(R)^2·det(I+M)`.
  - Completing this item unblocks the Gaussian vector lemmas.

- **Gaussian vector boundary (`loewner_logdet_mono`, `mi_after_ablation_logdet` and the scalar interference example)**
  - Depends on the Loewner lemmas above; once they are implemented, finish the vector comparison and finalize the interference example.

- **DI instantiation (`NOC_ROOT/NOC/E/Interfaces/DI*.lean`)**
  - Requires a concrete causal model with per-step directed information computations, SDPI witnesses, and filtration-alignment proofs. Those model-specific ingredients are not present, so the typeclass instances and final inequality cannot be instantiated yet.
