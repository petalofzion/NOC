# TODO — Next Formalization Steps

- [ ] **Lemma D / β_meta-stability proof** (`NOC_ROOT/NOC/D/BetaStabilityTTSA.lean`)
  - Formalize the two-time-scale SA hypotheses (step-size schedules, projection, local compactness).
  - Prove the envelope/sensitivity statement `∂_β_meta E[M]|_{0} = E[Δ²U_φ] - r'_β(0)` and export the drift inequality.
  - Add any supporting lemmas (e.g., gradient cross-correlation diagnostics) needed for the TTSA argument.

- [ ] **Lemma E (Conditional DI–DPI)** (`NOC_ROOT/NOC/E/ConditionalDIDPI.lean`)
  - Define the NCC/PostProcessOnPath predicate, finite POMDP scaffolding, and DI helpers.
  - Prove that garbling a partner under NCC cannot increase `I(A_i^{1:T} → S^{1:T})`; include the SDPI strictness corollary.

- [ ] **Interference counterexample (E-0c)** (`NOC_ROOT/NOC/E/Boundary/GaussianMAC.lean`)
  - Build a small multiple-access/interference channel and show DI **increases** after ablation, matching the text’s boundary rider.

- [ ] **Conversion ROI inequality (Lemma E+)** (`NOC_ROOT/NOC/E/ConversionVsAblation.lean`)
  - Formalize the boxed inequality, with non-negativity/unit checks on the parameters, and expose reusable helper lemmas.

- [ ] **C′ toy theorem constants** (`NOC_ROOT/NOC/C/CPrimeToy.lean`)
  - Instantiate the 2×2 POMDP, compute Dobrushin coefficients, and prove `ΔΣ ≥ c₁ ΔU_φ − λΞ Ξ_loss` with explicit constants + vacuity checks.

- [ ] **Supplementary examples/tests**
  - Add Lean examples for the DI computation (optional) and smoke-checks for the ROI inequality.
  - Extend test scripts to exercise the interference counterexample and toy Σ-law instance once proofs land.

- [ ] **Documentation sync**
  - After the above proofs merge, update `docs/README-companion.md`, the ChangeLog, and experiment checklists to reflect the completed formalizations.
