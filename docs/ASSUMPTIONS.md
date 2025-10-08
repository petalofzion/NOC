NOC v5 — Assumptions Tracker

Purpose
- Central, growing list of assumptions/hypotheses per lemma and file.
- Explains why each assumption is used, how it fits NOC, whether it is questionable, and potential critiques/alternatives.
- Helps reviewers and proof-agents know exactly what must be verified/instantiated.

How to add entries
- Categorize by lemma label (A, B, C, …) from NOC v5, then list the concrete Lean files that implement or support it.
- For each entry, fill the fields below concisely.

Entry format
- Lemma: <Label> — <Short name>
- File(s): <workspace-relative path(s)>
- Statement (1–2 lines): what the lemma claims.
- Hypotheses: precise assumptions (math and Lean-level) used in the proof.
- Why needed: what each hypothesis enables technically.
- Fit to NOC: how this matches the intended NOC modeling (and when it may not).
- Questionable?: anything that could be too strong/overfitted; when it might fail.
- Critiques/Alternatives: standard critiques and how to relax/replace.
- Verification obligations: what a modeler must show to use this lemma.
- Notes for Lean: proof-engineering details (e.g., PSD sandwiches, spectral steps).

-------------------------------------------------------------------------------
Lemma: E (Boundary) — Log‑det monotonicity (support)
File(s): NOC_ROOT/NOC/E/Boundary/LoewnerHelpers.lean
Theorems: inv_antitone_spd, logdet_mono_from_opmonotone

Statement (summary)
- If A ⪯ B and I + A, I + B are SPD, then log det(I + A) ≤ log det(I + B).
  Used as a core tool for Gaussian/vector boundary MI proxies.

Hypotheses
- A,B ∈ ℝ^{n×n} are Hermitian (Lean: `Matrix.IsHermitian A`, `Matrix.IsHermitian B`).
- A,B are PSD (Lean: `Matrix.PosSemidef A`, `Matrix.PosSemidef B`).
- Loewner order: A ⪯ B (Lean alias: `Matrix.PosSemidef (B - A)`).
- I + A and I + B are SPD (Lean: `Matrix.PosDef ((1 : _) + A)` and same for B).
  Note: derivable from A,B ⪰ 0, but tracked explicitly for sqrt/inverse/det_pos.
- Finite dimension over ℝ; standard matrix analysis context (Lean indices `Fin n`).
- No extra axioms; uses classical choice via `noncomputable section` only.

Why needed
- Hermitian/PSD: enables Loewner order, spectral theorem, and PSD-preserving “sandwich” congruence.
- A ⪯ B: encodes “B adds PSD mass” — the monotonicity direction.
- I + A, I + B ≻ 0: makes log(det ·) well-defined and allows whitening by (I + A)^{-1/2}.

Fit to NOC
- Matches linear‑Gaussian boundary proxies: SNR/covariance matrices are symmetric PSD; noise SPD.
- “More effective SNR / less interference” corresponds to PSD increases in Loewner order.
- The log‑det proxy is standard for Gaussian MI and common as a control/estimation surrogate.

Questionable?
- For non‑Gaussian or heavy‑tailed channels, log‑det may bound but not equal MI; still a defensible proxy.
- If singular covariances arise (pure PSD without PD), strict log may need regularization (εI) and a limit.

Critiques/Alternatives
- Replace log‑det by generalized log‑det on the image (pseudodeterminant) or add εI and pass to the limit.
- For indefinite models: require an explicit PSD comparison of the “effective SNR” matrices post‑whitening.

Verification obligations
- Map concrete NOC objects to matrices A,B; show B − A ⪰ 0.
- Justify I + A, I + B ≻ 0 (noise PSD/PD + PSD A,B usually suffice).
- If using non‑Gaussian models, state the exact role of log‑det (proxy vs bound) in the argument.

Notes for Lean (impl)
- Whitening: R := sqrt(I + A), S := R⁻¹; prove S*(I + B)*S = I + M with M := Sᴴ(B − A)S ⪰ 0.
- Spectral: M Hermitian PSD ⇒ det(I + M) = ∏(1 + λᵢ) ≥ 1.
- Determinant: det(I + B) = det(R)^2 · det(I + M) ≥ det(R)^2 = det(I + A) ⇒ log monotone.
- Robust proof uses explicit congrArg + a local “sandwich_add” lemma; avoids fragile simp paths.

-------------------------------------------------------------------------------
Template — fill for each future lemma/file

Lemma: <Label> — <Short name>
File(s): <path1>, <path2>, …

Statement (summary)
- <1–2 lines>

Hypotheses
- <math hypotheses>
- <Lean-level technical hypotheses>

Why needed
- <what each hypothesis enables>

Fit to NOC
- <how it matches the NOC modeling>

Questionable?
- <possible over‑assumptions or regimes where it may not hold>

Critiques/Alternatives
- <standard critiques and relaxations>

Verification obligations
- <what a user must prove/instantiate>

Notes for Lean (impl)
- <proof‑engineering tips or required helper lemmas>

