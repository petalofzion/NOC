import Mathlib

/-!
Module: NOC.E.Boundary.LoewnerHelpers
Status: helper lemmas and main targets proved (inverse antitonicity and log-det monotonicity).

Purpose: collect standard matrix-analysis facts (Loewner/PSD order, inverse antitonicity,
log-det monotonicity) used by the Gaussian vector boundary module. We use mathlib’s
`Matrix.PosSemidef/PosDef/IsHermitian` APIs.
-/

namespace NOC
noncomputable section
open Classical Matrix
open scoped Matrix

-- Silence linter hints like "try 'simp' instead of 'simpa'" in this file.
set_option linter.unnecessarySimpa false

namespace LoewnerHelpers
  
/-! Small helpers -/

/-- `I` is positive definite in any nontrivial dimension. -/
@[simp]
theorem posDef_one {n : ℕ} [NeZero n] :
    Matrix.PosDef ((1 : Matrix (Fin n) (Fin n) ℝ)) := by
  simpa using
    (Matrix.posDef_natCast_iff (R:=ℝ) (n:=Fin n) (d:=1)).2 Nat.one_pos

/--
Helper: if `C` is SPD and `C − I` is PSD, then `I − C⁻¹` is PSD.
This is the square-root congruence trick used to prove inverse antitonicity.
-/
private lemma psd_one_sub_inv_of_ge_one
    {n : ℕ} {C : Matrix (Fin n) (Fin n) ℝ}
    (hC : Matrix.PosDef C)
    (hC_ge : Matrix.PosSemidef (C - (1 : Matrix (Fin n) (Fin n) ℝ))) :
    Matrix.PosSemidef ((1 : Matrix (Fin n) (Fin n) ℝ) - C⁻¹) := by
  classical
  -- Positive-semidefinite square root R of C, with R*R = C
  let hC_psd : Matrix.PosSemidef C := hC.posSemidef
  set R : Matrix (Fin n) (Fin n) ℝ := Matrix.PosSemidef.sqrt hC_psd with hR_def
  have hR_mul : R * R = C := by
    simpa [hR_def] using Matrix.PosSemidef.sqrt_mul_self hC_psd
  have hR_pos : Matrix.PosDef R := by
    simpa [hR_def] using Matrix.PosDef.posDef_sqrt hC
  -- R is invertible; let S = R⁻¹
  have hR_unit : IsUnit R := hR_pos.isUnit
  haveI : Invertible R := hR_unit.invertible
  set S : Matrix (Fin n) (Fin n) ℝ := (⅟ R) with hS_def
  -- Identities with S and R
  have hSR : (S * R) = (1 : Matrix _ _ ℝ) := by
    simpa [hS_def, Matrix.mul_assoc] using
      Matrix.inv_mul_cancel_left_of_invertible (A := R)
        (B := (1 : Matrix (Fin n) (Fin n) ℝ))
  have hRS : (R * S) = (1 : Matrix _ _ ℝ) := by
    simpa [hS_def, Matrix.mul_assoc] using
      Matrix.mul_inv_cancel_left_of_invertible (A := R)
        (B := (1 : Matrix (Fin n) (Fin n) ℝ))
  -- Express C⁻¹ via S
  have hC_inv : C⁻¹ = S * S := by
    have hLeft : (S * S) * C = (1 : Matrix _ _ ℝ) := by
      calc
        (S * S) * C
            = S * (S * C) := by simp [Matrix.mul_assoc]
        _   = S * (S * (R * R)) := by simp [hR_mul]
        _   = S * ((S * R) * R) := by simp [Matrix.mul_assoc]
        _   = S * (1 * R) := by simp [hSR]
        _   = S * R := by simp
        _   = (1 : Matrix _ _ ℝ) := by simpa [hSR]
    exact Matrix.inv_eq_left_inv hLeft
  -- Compute the congruence Sᵀ (C − I) S = I − C⁻¹ (over ℝ, conjTranspose = transpose)
  have hS_pos : Matrix.PosDef S := by
    simpa [hS_def] using Matrix.PosDef.inv hR_pos
  have hS_herm : S.IsHermitian := hS_pos.isHermitian
  have hS_self : Sᴴ = S := hS_herm.eq
  have hSCS : S * C * S = (1 : Matrix _ _ ℝ) := by
    calc
      S * C * S = S * (R * R) * S := by simp [hR_mul]
      _ = (S * R) * (R * S) := by simp [Matrix.mul_assoc]
      _ = (1 : Matrix _ _ ℝ) := by simp [hSR, hRS]
  have hSS : S * S = C⁻¹ := by simpa [hC_inv]
  have hSimpl : S * (C - (1 : Matrix _ _ ℝ)) * S =
      (1 : Matrix _ _ ℝ) - C⁻¹ := by
    simp [Matrix.mul_assoc, Matrix.mul_sub, Matrix.sub_mul, hSCS, hSS]
  -- Use Hermitian property: `Sᵀ = S` over ℝ for Hermitian `S`.
  have hS_trans : S.transpose = S := by
    simpa [Matrix.conjTranspose] using hS_self
  -- Identities for the inverse pair (S,R).
  have hMain : S.transpose * (C - (1 : Matrix _ _ ℝ)) * S =
      (1 : Matrix _ _ ℝ) - C⁻¹ := by simpa [hS_trans] using hSimpl
  -- Push PSD through the congruence
  have hSandwich : Matrix.PosSemidef (S.transpose * (C - (1 : Matrix _ _ ℝ)) * S) := by
    simpa [Matrix.conjTranspose] using
      Matrix.PosSemidef.conjTranspose_mul_mul_same hC_ge S
  simpa [hMain]
    using hSandwich

/-! Small determinant helpers to avoid heavy `simp` in the spectral/log‑det proof. -/

-- (helper lemma `det_conj_unitary` removed; we prove the needed fact inline in `logdet_mono_from_opmonotone`)

/-- Diagonal identity: `det (I + diagonal v) = ∏ i, (1 + v i)`. -/
private lemma det_add_diagonal
    {n : ℕ} (v : Fin n → ℝ) :
    ((1 : Matrix (Fin n) (Fin n) ℝ) + Matrix.diagonal v).det
      = ∏ i, (1 + v i) := by
  classical
  have : (1 : Matrix (Fin n) (Fin n) ℝ) + Matrix.diagonal v
      = Matrix.diagonal (fun i => (1 : ℝ) + v i) := by
    ext i j
    by_cases hij : i = j
    · subst hij; simp
    · simp [hij]
  simpa [this, Matrix.det_diagonal]

/-- For a real PSD matrix `M`, `det (I + M) ≥ 1`.
This packages the spectral/product step used in log‑det monotonicity. -/
private lemma det_I_add_psd_ge_one {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℝ)
    (hM_psd : Matrix.PosSemidef M) :
    (1 : ℝ) ≤ (((1 : Matrix (Fin n) (Fin n) ℝ) + M).det) := by
  classical
  -- Diagonalise `M` via a unitary `U` and a real diagonal `D` of eigenvalues.
  have hM_herm : Matrix.IsHermitian M := hM_psd.isHermitian
  let G := Matrix.IsHermitian.eigenvectorUnitary hM_herm
  let U : Matrix (Fin n) (Fin n) ℝ := (G : Matrix (Fin n) (Fin n) ℝ)
  let D : Matrix (Fin n) (Fin n) ℝ :=
    Matrix.diagonal (fun i => (Matrix.IsHermitian.eigenvalues hM_herm i : ℝ))
  have hM_spec : M = U * D * Uᴴ := hM_herm.spectral_theorem
  have hU_right : Uᴴ * U = (1 : Matrix _ _ ℝ) := by
    simpa [U, Matrix.star_eq_conjTranspose] using Matrix.UnitaryGroup.star_mul_self G
  -- Conjugate `I+M` to `I+D`.
  have hU_rightT : U.transpose * U = (1 : Matrix _ _ ℝ) := by
    simpa [Matrix.conjTranspose] using hU_right
  have hconj2 : Uᴴ * M * U = D := by
    have htmp : U.transpose * M * U = (U.transpose * U) * D * (U.transpose * U) := by
      simp [hM_spec, Matrix.mul_assoc]
    simpa [Matrix.conjTranspose, hU_rightT, Matrix.mul_assoc] using htmp
  have hconj : Uᴴ * ((1 : Matrix _ _ ℝ) + M) * U = (1 : Matrix _ _ ℝ) + D := by
    calc
      Uᴴ * ((1 : Matrix _ _ ℝ) + M) * U
          = Uᴴ * (1 : Matrix _ _ ℝ) * U + Uᴴ * M * U := by
              simp [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
      _   = (Uᴴ * U) + Uᴴ * M * U := by simp
      _   = (1 : Matrix _ _ ℝ) + Uᴴ * M * U := by simpa [hU_right]
      _   = (1 : Matrix _ _ ℝ) + D := by simpa [hconj2]
  -- Determinant invariance under unitary conjugation: det(I+M) = det(I+D)
  have hdet_sq : U.det * U.det = 1 := by
    have hmul_symm : (U.transpose).det * U.det = (U.transpose * U).det := by
      simpa using (Matrix.det_mul (U.transpose) U).symm
    have hdet_eq1 : (U.transpose * U).det = 1 := by
      simpa [hU_rightT, Matrix.det_one]
    simpa [Matrix.det_transpose] using hmul_symm.trans hdet_eq1
  have hdet_mul1 : (Uᴴ * ((1 : Matrix _ _ ℝ) + M) * U).det
      = ((Uᴴ).det * (((1 : Matrix _ _ ℝ) + M).det)) * U.det := by
    have h1 := Matrix.det_mul (Uᴴ * ((1 : Matrix _ _ ℝ) + M)) U
    have h2 := Matrix.det_mul Uᴴ ((1 : Matrix _ _ ℝ) + M)
    have h2' : det (Uᴴ * ((1 : Matrix _ _ ℝ) + M))
        = det (Uᴴ) * det ((1 : Matrix _ _ ℝ) + M) := by
      simpa using h2
    simpa [Matrix.mul_assoc, h2'] using h1
  have hdet_invar : (((1 : Matrix _ _ ℝ) + M).det) = (((1 : Matrix _ _ ℝ) + D).det) := by
    -- From `Uᴴ (I+M) U = I + D`, compare determinants and cancel via `det U`.
    have hconj_det : (Uᴴ * ((1 : Matrix _ _ ℝ) + M) * U).det = (((1 : Matrix _ _ ℝ) + D).det) := by
      simpa using congrArg Matrix.det hconj
    have hdet_invar' : (((1 : Matrix _ _ ℝ) + D).det) = (((1 : Matrix _ _ ℝ) + M).det) := by
      calc
        (((1 : Matrix _ _ ℝ) + D).det)
            = (Uᴴ * ((1 : Matrix _ _ ℝ) + M) * U).det := by simpa using hconj_det.symm
        _   = (Uᴴ).det * (((1 : Matrix _ _ ℝ) + M).det) * U.det := by
                simpa [Matrix.mul_assoc] using hdet_mul1
        _   = (U.det * U.det) * (((1 : Matrix _ _ ℝ) + M).det) := by
                have hdet_conj : (Uᴴ).det = U.det := by
                  simpa using (Matrix.det_conjTranspose U)
                simpa [hdet_conj, mul_comm, mul_left_comm, mul_assoc]
        _   = (1 : ℝ) * (((1 : Matrix _ _ ℝ) + M).det) := by simpa [hdet_sq]
        _   = (((1 : Matrix _ _ ℝ) + M).det) := by simp
    simpa using hdet_invar'.symm
  -- det(I + diagonal(eigs)) is the product of (1 + eigenvalues)
  have hdiag : (((1 : Matrix _ _ ℝ) + D).det) = ∏ i, (1 + Matrix.IsHermitian.eigenvalues hM_herm i) := by
    simpa [D] using det_add_diagonal (fun i => Matrix.IsHermitian.eigenvalues hM_herm i)
  -- Each factor (1 + λᵢ) ≥ 1 since λᵢ ≥ 0 for PSD `M`.
  have hfac : ∀ i, (1 : ℝ) ≤ 1 + Matrix.IsHermitian.eigenvalues hM_herm i := by
    intro i
    have hnn := hM_psd.eigenvalues_nonneg i
    simpa using add_le_add_left hnn 1
  have hprod_ge : (1 : ℝ) ≤ ∏ i, (1 + Matrix.IsHermitian.eigenvalues hM_herm i) := by
    classical
    -- All factors are ≥ 1; product over `Fin n` is ≥ 1.
    refine Finset.induction_on (Finset.univ : Finset (Fin n)) (by simp) (fun a s ha hs => ?_)
    have ha_not : a ∉ s := by simpa using ha
    have step' := one_le_mul_of_one_le_of_one_le (hfac a) hs
    simpa [Finset.prod_insert ha_not, one_mul] using step'
  -- Transport back from `D` to `M` using determinant conjugation invariance.
  have hDetD_ge : (1 : ℝ) ≤ (((1 : Matrix _ _ ℝ) + D).det) := by simpa [hdiag] using hprod_ge
  simpa [hdet_invar] using hDetD_ge

-- Over ℝ the star-operation is the identity; mapping by `starRingEnd ℝ` is pointwise the identity.
@[simp] private lemma map_starRingEnd_real
    {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    A.map (starRingEnd ℝ) = A := by
  ext i j; simp

@[simp] private lemma transpose_map_starRingEnd_real
    {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    A.transpose.map (starRingEnd ℝ) = A.transpose := by
  ext i j; simp

-- Sandwiching distributes over addition: S*(A+B)*S = S*A*S + S*B*S
private lemma sandwich_add {n : ℕ}
    (S A B : Matrix (Fin n) (Fin n) ℝ) :
    S * (A + B) * S = S * A * S + S * B * S := by
  simp [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]

/-- Loewner order on real Hermitian matrices: `A ⪯ B` iff `B − A` is PSD. -/
def LoewnerLE {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  Matrix.PosSemidef (B - A)

infix:50 " ⪯ " => LoewnerLE

/-- Textbook-purist typed wrapper: Hermitian matrices with a Loewner order. -/
structure HermitianMat (n : ℕ) where
  M      : Matrix (Fin n) (Fin n) ℝ
  herm   : Matrix.IsHermitian M

namespace HermitianMat

/-- Loewner order on `HermitianMat`: `A ≤ₗ B` iff `B − A` is PSD. -/
def loewnerLE {n : ℕ} (A B : HermitianMat n) : Prop :=
  Matrix.PosSemidef (B.M - A.M)

infix:50 " ≤ₗ " => loewnerLE

end HermitianMat

/-- Congruence preserves the Loewner (PSD) order: if `B − A` is PSD then so is
`Mᵀ B M − Mᵀ A M = Mᵀ (B − A) M`. -/
theorem psd_congr {n : ℕ}
  (A B M : Matrix (Fin n) (Fin n) ℝ)
  (hAB : Matrix.PosSemidef (B - A)) :
  Matrix.PosSemidef (Mᴴ * B * M - (Mᴴ * A * M)) := by
  classical
  simpa [Matrix.mul_sub, Matrix.sub_mul] using
    (Matrix.PosSemidef.conjTranspose_mul_mul_same (A := B - A) hAB M)

/-- Matrix inversion reverses the Loewner order on the SPD cone (target statement). -/
theorem inv_antitone_spd {n : ℕ}
  (A B : Matrix (Fin n) (Fin n) ℝ)
  (hA : Matrix.PosDef A) (hB : Matrix.PosDef B)
  (hAB : A ⪯ B) :
  Matrix.PosSemidef (A⁻¹ - B⁻¹) := by
  classical
  -- Whitening with the SPD square root of A.
  let RA_psd : Matrix.PosSemidef A := hA.posSemidef
  set R : Matrix (Fin n) (Fin n) ℝ := Matrix.PosSemidef.sqrt RA_psd with hR_def
  have hR_mul : R * R = A := by simpa [hR_def] using Matrix.PosSemidef.sqrt_mul_self RA_psd
  have hR_pos : Matrix.PosDef R := by simpa [hR_def] using Matrix.PosDef.posDef_sqrt hA
  have hR_unit : IsUnit R := hR_pos.isUnit
  haveI : Invertible R := hR_unit.invertible
  set S : Matrix (Fin n) (Fin n) ℝ := (⅟ R) with hS_def
  have hS_pos : Matrix.PosDef S := by
    simpa [hS_def] using Matrix.PosDef.inv hR_pos
  have hS_herm : S.IsHermitian := hS_pos.isHermitian
  have hS_self : Sᴴ = S := hS_herm.eq
  have hS_trans : S.transpose = S := by
    simpa [Matrix.conjTranspose] using hS_self
  -- Define whitened C := S B S; then C ≻ 0 and C − I ⪰ 0.
  set C : Matrix (Fin n) (Fin n) ℝ := S * B * S with hC_def
  have hC_pos : Matrix.PosDef C := by
    -- Transport PD by congruence with invertible S.
    -- Use quadratic-form characterization via injectivity of `S.vecMul`.
    have hInj : Function.Injective S.vecMul :=
      Matrix.vecMul_injective_of_isUnit (by
        simpa [hS_def] using (hS_pos.isUnit))
    simpa [hC_def, hS_trans] using
      (Matrix.PosDef.mul_mul_conjTranspose_same hB hInj)
  -- A ⪯ B ⇒ Sᴴ(B − A)S ⪰ 0; over ℝ we use conjTranspose = transpose via IsHermitian.
  have hBA_psd : Matrix.PosSemidef (B - A) := hAB
  have hSBA : Matrix.PosSemidef (S * (B - A) * S) := by
    simpa [Matrix.mul_assoc, hS_trans] using
      Matrix.PosSemidef.conjTranspose_mul_mul_same hBA_psd S
  have hCI : (C - (1 : Matrix _ _ ℝ)) = S * (B - A) * S := by
    have hSR1 : S * R = (1 : Matrix _ _ ℝ) := by
      simpa [hS_def, Matrix.mul_assoc] using
        Matrix.inv_mul_cancel_left_of_invertible (A := R)
          (B := (1 : Matrix (Fin n) (Fin n) ℝ))
    have hRS1 : R * S = (1 : Matrix _ _ ℝ) := by
      simpa [hS_def, Matrix.mul_assoc] using
        Matrix.mul_inv_cancel_left_of_invertible (A := R)
          (B := (1 : Matrix (Fin n) (Fin n) ℝ))
    have hSAS : S * A * S = (1 : Matrix _ _ ℝ) := by
      calc
        S * A * S = S * (R * R) * S := by simp [hR_mul]
        _ = (S * R) * (R * S) := by simp [Matrix.mul_assoc]
        _ = (1 : Matrix _ _ ℝ) := by simp [hSR1, hRS1]
    simp [hC_def, Matrix.mul_assoc, Matrix.mul_sub, Matrix.sub_mul, hSAS]
  have hC_minus_psd : Matrix.PosSemidef (C - (1 : Matrix _ _ ℝ)) := by
    simpa [hCI]
      using hSBA
  -- Apply the helper: (I − C⁻¹) is PSD.
  have hI_minus : Matrix.PosSemidef ((1 : Matrix _ _ ℝ) - C⁻¹) :=
    psd_one_sub_inv_of_ge_one hC_pos hC_minus_psd
  -- Rewrite A⁻¹ and B⁻¹ in terms of S and C.
  have hA_inv : A⁻¹ = S * S := by
    have hSR2 : S * R = (1 : Matrix _ _ ℝ) := by
      simpa [hS_def, Matrix.mul_assoc] using
        Matrix.inv_mul_cancel_left_of_invertible (A := R)
          (B := (1 : Matrix (Fin n) (Fin n) ℝ))
    have hLeft : (S * S) * A = (1 : Matrix _ _ ℝ) := by
      calc
        (S * S) * A
            = S * (S * A) := by simp [Matrix.mul_assoc]
        _   = S * (S * (R * R)) := by simp [hR_mul]
        _   = S * ((S * R) * R) := by simp [Matrix.mul_assoc]
        _   = S * (1 * R) := by simp [hSR2]
        _   = S * R := by simp
        _   = (1 : Matrix _ _ ℝ) := by simpa [hSR2]
    simpa using (Matrix.inv_eq_left_inv hLeft)
  have hB_inv : B⁻¹ = S * C⁻¹ * S := by
    have hB_eq : B = R * C * R := by
      simp [hC_def, Matrix.mul_assoc, hS_def,
            Matrix.inv_mul_cancel_left_of_invertible,
            Matrix.mul_inv_cancel_left_of_invertible]
    have hSR3 : S * R = (1 : Matrix _ _ ℝ) := by
      simpa [hS_def, Matrix.mul_assoc] using
        Matrix.inv_mul_cancel_left_of_invertible (A := R)
          (B := (1 : Matrix (Fin n) (Fin n) ℝ))
    have hLeft : (S * C⁻¹ * S) * B = (1 : Matrix _ _ ℝ) := by
      haveI : Invertible C := (hC_pos.isUnit).invertible
      calc
        (S * C⁻¹ * S) * B
            = S * C⁻¹ * (S * B) := by simp [Matrix.mul_assoc]
        _   = S * C⁻¹ * (S * (R * C * R)) := by simp [hB_eq]
        _   = S * C⁻¹ * ((S * R) * C * R) := by simp [Matrix.mul_assoc]
        _   = S * (C⁻¹ * C) * R := by simp [hSR3, Matrix.mul_assoc]
        _   = S * R := by simp
        _   = (1 : Matrix _ _ ℝ) := by
          simpa [hS_def, Matrix.mul_assoc] using
            Matrix.inv_mul_cancel_left_of_invertible (A := R)
              (B := (1 : Matrix (Fin n) (Fin n) ℝ))
    exact Matrix.inv_eq_left_inv hLeft
  -- Express the target difference as a congruence.
  have hExpr : A⁻¹ - B⁻¹ = S * ((1 : Matrix _ _ ℝ) - C⁻¹) * S := by
    simp [hA_inv, hB_inv, Matrix.mul_assoc, Matrix.mul_sub, Matrix.sub_mul]
  -- Push PSD through the congruence; align `conjTranspose` with transpose over ℝ.
  have hSand : Matrix.PosSemidef (S.transpose * ((1 : Matrix _ _ ℝ) - C⁻¹) * S) := by
    simpa [Matrix.conjTranspose] using
      Matrix.PosSemidef.conjTranspose_mul_mul_same hI_minus S
  have hSand' : Matrix.PosSemidef (S * ((1 : Matrix _ _ ℝ) - C⁻¹) * S) := by
    simpa [hS_trans] using hSand
  simpa [hExpr] using hSand'



/-
Log‑det monotonicity under Loewner order (operator‑monotone log on SPD), expressed
via `log det (I + ·)`.

Note on hypotheses and minimality
- The proof effectively uses only:
  * `hAB : A ⪯ B` (i.e., `B − A` is PSD), and
  * `PosDef (I + A)` and `PosDef (I + B)` (to enable whitening, square‑root/inverse,
    and positivity of determinants for `Real.log_le_log`).
- The `IsHermitian`/`PosSemidef` hypotheses for `A` and `B` are carried to make the
  domain context explicit and to align with adjacent infrastructure lemmas; they are
  typical in NOC’s boundary setting and may be useful for future generalizations.

Planned follow‑up (API hygiene)
- A minimal variant `logdet_mono_from_opmonotone_min` that assumes only the
  core requirements above (A ⪯ B and PosDef(I±)) is straightforward from the same
  whitening + spectral/product argument. We will add it in a focused change by
  factoring out the diagonal/product step into a helper to keep this file robust.

Reason to keep current signature for now
- Documents the intended PSD/Hermitian context explicitly and avoids churn for
  existing callers; enables a smooth migration path once the minimal lemma is added.
-/

set_option maxHeartbeats 2000000 in
/-- Operator-monotonicity of the logarithm on SPD matrices, expressed via log-det (target). -/
theorem logdet_mono_from_opmonotone {n : ℕ}
  (A B : Matrix (Fin n) (Fin n) ℝ)
  (hA : Matrix.IsHermitian A) (hB : Matrix.IsHermitian B)
  (hA_psd : Matrix.PosSemidef A) (hB_psd : Matrix.PosSemidef B)
  (hAB : A ⪯ B)
  (hIspA : Matrix.PosDef ((1 : Matrix (Fin n) (Fin n) ℝ) + A))
  (hIspB : Matrix.PosDef ((1 : Matrix (Fin n) (Fin n) ℝ) + B)) :
  Real.log (((1 : Matrix (Fin n) (Fin n) ℝ) + A).det)
    ≤ Real.log (((1 : Matrix (Fin n) (Fin n) ℝ) + B).det) := by
  classical
  -- Whitening with respect to X := I + A
  let X : Matrix (Fin n) (Fin n) ℝ := (1 : Matrix _ _ ℝ) + A
  have hX_psd : Matrix.PosSemidef X := hIspA.posSemidef
  let R : Matrix (Fin n) (Fin n) ℝ := hX_psd.sqrt
  have hR_mul : R * R = X := by simpa [R] using hX_psd.sqrt_mul_self
  have hR_pos : Matrix.PosDef R := by simpa using Matrix.PosDef.posDef_sqrt hIspA
  haveI : Invertible R := (hR_pos.isUnit).invertible
  let S : Matrix (Fin n) (Fin n) ℝ := (⅟ R)
  have hS_pos : Matrix.PosDef S := by simpa [S] using Matrix.PosDef.inv hR_pos
  have hS_herm : S.IsHermitian := hS_pos.isHermitian
  have hS_self : Sᴴ = S := hS_herm.eq
  have hS_trans : S.transpose = S := by
    simpa [Matrix.conjTranspose] using hS_self
  -- Define M := S (B−A) S, then M ⪰ 0
  let Y : Matrix (Fin n) (Fin n) ℝ := B - A
  have hY_psd : Matrix.PosSemidef Y := hAB
  let M : Matrix (Fin n) (Fin n) ℝ := Sᴴ * Y * S
  have hM_psd : Matrix.PosSemidef M := by
    simpa [M] using Matrix.PosSemidef.conjTranspose_mul_mul_same hY_psd S
  -- Algebra: S X S = I and S (I + B) S = I + M
  have hSR : S * R = (1 : Matrix _ _ ℝ) := by
    simpa [S, Matrix.mul_assoc] using
      Matrix.inv_mul_cancel_left_of_invertible (A := R)
        (B := (1 : Matrix (Fin n) (Fin n) ℝ))
  have hRS : R * S = (1 : Matrix _ _ ℝ) := by
    simpa [S, Matrix.mul_assoc] using
      Matrix.mul_inv_cancel_left_of_invertible (A := R)
        (B := (1 : Matrix (Fin n) (Fin n) ℝ))
  have hSXS : S * X * S = (1 : Matrix _ _ ℝ) := by
    calc
      S * X * S = S * (R * R) * S := by simp [X, hR_mul]
      _ = (S * R) * (R * S) := by simp [Matrix.mul_assoc]
      _ = (1 : Matrix _ _ ℝ) := by simp [hSR, hRS]
  have hSIBS : S * ((1 : Matrix _ _ ℝ) + B) * S = (1 : Matrix _ _ ℝ) + M := by
    -- Rewrite `B`, expand the sandwich stepwise, then fold `S*X*S` to 1 and identify `M`.
    have hBsplit : B = A + (B - A) := by
      have : (A + B) - A = B := by simpa using add_sub_cancel' (A) (B)
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
    -- Step 1: transport through the sandwich
    have h0 : S * ((1 : Matrix _ _ ℝ) + B) * S
              = S * ((1 : Matrix _ _ ℝ) + (A + (B - A))) * S := by
      simpa using congrArg (fun M => S * M * S)
        (congrArg (fun t => (1 : Matrix _ _ ℝ) + t) hBsplit)
    -- Step 2: reassociate inside: 1 + (A + (B - A)) = (1 + A) + (B - A)
    have h1 : S * ((1 : Matrix _ _ ℝ) + (A + (B - A))) * S
              = S * (((1 : Matrix _ _ ℝ) + A) + (B - A)) * S := by
      simpa [add_assoc] using congrArg (fun M => S * M * S)
        (by
          have : (1 : Matrix _ _ ℝ) + (A + (B - A))
                  = ((1 : Matrix _ _ ℝ) + A) + (B - A) := by
            simpa [add_assoc]
          exact this)
    -- Step 3: expand the sandwich over +
    have h2 : S * (((1 : Matrix _ _ ℝ) + A) + (B - A)) * S
              = S * ((1 : Matrix _ _ ℝ) + A) * S + S * (B - A) * S :=
      sandwich_add S ((1 : Matrix _ _ ℝ) + A) (B - A)
    -- Combine
    have hsum : S * ((1 : Matrix _ _ ℝ) + B) * S
              = S * ((1 : Matrix _ _ ℝ) + A) * S + S * (B - A) * S :=
      h0.trans (h1.trans h2)
    -- Fold S*X*S to 1
    have hfold : S * ((1 : Matrix _ _ ℝ) + B) * S = (1 : Matrix _ _ ℝ) + S * (B - A) * S := by
      simpa [X, hSXS] using hsum
    -- Identify M = S*(B−A)*S (since S is Hermitian over ℝ)
    have hM_def : M = S * (B - A) * S := by
      simp [M, Y, Matrix.conjTranspose, map_starRingEnd_real,
            transpose_map_starRingEnd_real, hS_trans, hS_self]
    simpa [hM_def] using hfold
  -- Move back from whitened coordinates:
  have hIB_eq : (1 : Matrix _ _ ℝ) + B = R * ((1 : Matrix _ _ ℝ) + M) * R := by
    calc
      (1 : Matrix _ _ ℝ) + B
          = (R * S) * ((1 : Matrix _ _ ℝ) + B) * (S * R) := by
              simp [hRS, hSR, Matrix.mul_assoc]
      _   = R * (S * ((1 : Matrix _ _ ℝ) + B) * S) * R := by
              simp [Matrix.mul_assoc]
      _   = R * ((1 : Matrix _ _ ℝ) + M) * R := by
              simpa [hSIBS]
  -- Determinant identities
  have hIA_det : (((1 : Matrix _ _ ℝ) + A).det) = (R.det) ^ 2 := by
    have hX_eq : (1 : Matrix _ _ ℝ) + A = R * R := by simpa [X] using hR_mul.symm
    simpa [hX_eq, Matrix.det_mul, pow_two]
  have hIB_det : (((1 : Matrix _ _ ℝ) + B).det)
      = (R.det) ^ 2 * (((1 : Matrix _ _ ℝ) + M).det) := by
    -- det(1+B) = det(R * (1+M) * R) = det R · det (1+M) · det R
    have h : det ((1 : Matrix _ _ ℝ) + B) = det (R * ((1 : Matrix _ _ ℝ) + M) * R) :=
      congr_arg Matrix.det hIB_eq
    have hA : det (R * ((1 : Matrix _ _ ℝ) + M) * R)
        = det (R * ((1 : Matrix _ _ ℝ) + M)) * det R := by
      have htmp := Matrix.det_mul (R * ((1 : Matrix _ _ ℝ) + M)) R
      simpa [Matrix.mul_assoc] using htmp
    have hB : det (R * ((1 : Matrix _ _ ℝ) + M))
        = det R * det ((1 : Matrix _ _ ℝ) + M) := by
      have htmp := Matrix.det_mul R ((1 : Matrix _ _ ℝ) + M)
      simpa [Matrix.mul_assoc] using htmp
    calc
      det ((1 : Matrix _ _ ℝ) + B)
          = det (R * ((1 : Matrix _ _ ℝ) + M) * R) := h
      _   = det (R * ((1 : Matrix _ _ ℝ) + M)) * det R := hA
      _   = (det R * det ((1 : Matrix _ _ ℝ) + M)) * det R := by simpa [hB]
      _   = (det R)^2 * det ((1 : Matrix _ _ ℝ) + M) := by ring
  -- Show det(I+M) ≥ 1 via spectral theorem: product of (1+λᵢ), λᵢ ≥ 0
  have hDetM_ge : (1 : ℝ) ≤ (((1 : Matrix _ _ ℝ) + M).det) := by
    -- diagonalize M and compute determinant of (I + M)
    have hM_herm : Matrix.IsHermitian M := hM_psd.isHermitian
    let G := Matrix.IsHermitian.eigenvectorUnitary hM_herm
    let U : Matrix (Fin n) (Fin n) ℝ := (G : Matrix (Fin n) (Fin n) ℝ)
    let D : Matrix (Fin n) (Fin n) ℝ :=
      Matrix.diagonal (fun i => (Matrix.IsHermitian.eigenvalues hM_herm i : ℝ))
    have hM_spec : M = U * D * Uᴴ := hM_herm.spectral_theorem
    have hU_right : Uᴴ * U = (1 : Matrix _ _ ℝ) := by
      -- from the unitary property `star U * U = 1`
      simpa [U, Matrix.star_eq_conjTranspose] using Matrix.UnitaryGroup.star_mul_self G
    -- Conjugate (I+M) to (I+D)
    have hconj1 : Uᴴ * ((1 : Matrix _ _ ℝ) + M) * U
        = (1 : Matrix _ _ ℝ) + Uᴴ * M * U := by
      calc
        Uᴴ * ((1 : Matrix _ _ ℝ) + M) * U
            = Uᴴ * (1 : Matrix _ _ ℝ) * U + Uᴴ * M * U := by
                simp [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
        _   = (Uᴴ * U) + Uᴴ * M * U := by simp
        _   = (1 : Matrix _ _ ℝ) + Uᴴ * M * U := by simpa [hU_right]
    have hU_rightT : U.transpose * U = (1 : Matrix _ _ ℝ) := by
      simpa [Matrix.conjTranspose] using hU_right
    have hconj2 : Uᴴ * M * U = D := by
      have htmp : U.transpose * M * U = (U.transpose * U) * D * (U.transpose * U) := by
        simp [hM_spec, Matrix.mul_assoc]
      -- close with `hU_rightT` and associativity
      simpa [Matrix.conjTranspose, hU_rightT, Matrix.mul_assoc] using htmp
    have hconj : Uᴴ * ((1 : Matrix _ _ ℝ) + M) * U = (1 : Matrix _ _ ℝ) + D := by
      calc
        Uᴴ * ((1 : Matrix _ _ ℝ) + M) * U
            = (1 : Matrix _ _ ℝ) + Uᴴ * M * U := hconj1
        _   = (1 : Matrix _ _ ℝ) + D := by simpa [hconj2]
    -- Determinant invariance under unitary conjugation: det(I+M) = det(I+D)
    -- First, a robust determinant identity via the transpose route over ℝ.
    have hdet_sq : U.det * U.det = 1 := by
      have hmul_symm : (U.transpose).det * U.det = (U.transpose * U).det := by
        simpa using (Matrix.det_mul (U.transpose) U).symm
      have hdet_eq1 : (U.transpose * U).det = 1 := by
        simpa [hU_rightT, Matrix.det_one]
      simpa [Matrix.det_transpose] using hmul_symm.trans hdet_eq1
    have hdetU : (Uᴴ).det * U.det = 1 := by
      have hdet_conj : (Uᴴ).det = U.det := by
        simpa using (Matrix.det_conjTranspose U)
      simpa [hdet_conj] using hdet_sq
    have hdet_mul1 : (Uᴴ * ((1 : Matrix _ _ ℝ) + M) * U).det
        = ((Uᴴ).det * (((1 : Matrix _ _ ℝ) + M).det)) * U.det := by
      have h1 := Matrix.det_mul (Uᴴ * ((1 : Matrix _ _ ℝ) + M)) U
      have h2 := Matrix.det_mul Uᴴ ((1 : Matrix _ _ ℝ) + M)
      have h2' : det (Uᴴ * ((1 : Matrix _ _ ℝ) + M))
          = det (Uᴴ) * det ((1 : Matrix _ _ ℝ) + M) := by
        simpa using h2
      simpa [Matrix.mul_assoc, h2'] using h1
    have hdet_invar : (((1 : Matrix _ _ ℝ) + M).det) = (((1 : Matrix _ _ ℝ) + D).det) := by
      -- From `Uᴴ (I+M) U = I + D`, compare determinants and cancel `det Uᴴ · det U = 1`.
      have hconj_det : (Uᴴ * ((1 : Matrix _ _ ℝ) + M) * U).det = (((1 : Matrix _ _ ℝ) + D).det) := by
        simpa using congrArg Matrix.det hconj
      have hdetU_mul : (Uᴴ).det * U.det = 1 := by
        have hdet : (Uᴴ * U).det = 1 := by simpa [hU_right, Matrix.det_one]
        have hmul : (Uᴴ).det * U.det = (Uᴴ * U).det := by
          simpa using (Matrix.det_mul Uᴴ U).symm
        simpa [hmul] using hdet
      calc
        (((1 : Matrix _ _ ℝ) + M).det)
            = (((1 : Matrix _ _ ℝ) + M).det) * (U.det * U.det) := by
                simpa [hdet_sq, mul_comm]
        _   = ((Uᴴ).det * (((1 : Matrix _ _ ℝ) + M).det)) * U.det := by
                have hdet_conj : (Uᴴ).det = U.det := by
                  simpa using (Matrix.det_conjTranspose U)
                simpa [hdet_conj, mul_comm, mul_left_comm, mul_assoc]
        _   = (Uᴴ * ((1 : Matrix _ _ ℝ) + M) * U).det := by
                simpa [Matrix.mul_assoc] using (hdet_mul1).symm
        _   = (((1 : Matrix _ _ ℝ) + D).det) := by simpa using hconj_det
    -- det(I + diagonal(eigs)) is the product of (1 + eigenvalues)
    have hdiag : (((1 : Matrix _ _ ℝ) + D).det) = ∏ i, (1 + Matrix.IsHermitian.eigenvalues hM_herm i) := by
      simpa [D] using det_add_diagonal (fun i => Matrix.IsHermitian.eigenvalues hM_herm i)
    -- Each factor (1 + λᵢ) ≥ 1 since λᵢ ≥ 0 for PSD M
    have hfac : ∀ i, (1 : ℝ) ≤ 1 + Matrix.IsHermitian.eigenvalues hM_herm i := by
      intro i
      have hnn := hM_psd.eigenvalues_nonneg i
      have := add_le_add_left hnn 1
      simpa using this
    have hprod_ge : (1 : ℝ) ≤ ∏ i, (1 + Matrix.IsHermitian.eigenvalues hM_herm i) := by
      classical
      have hnonneg : ∀ i, 0 ≤ (1 : ℝ) + Matrix.IsHermitian.eigenvalues hM_herm i := by
        intro i; exact add_nonneg zero_le_one (hM_psd.eigenvalues_nonneg i)
      refine Finset.induction_on (Finset.univ : Finset (Fin n)) (by simp) (fun a s ha hs => ?_)
      have ha_not : a ∉ s := by simpa using ha
      have hage := hfac a
      -- By induction hypothesis and `hage`, both factors are ≥ 1
      have hs1 : (1 : ℝ) ≤ ∏ i ∈ s, (1 + Matrix.IsHermitian.eigenvalues hM_herm i) := hs
      have step' : (1 : ℝ)
          ≤ (1 + Matrix.IsHermitian.eigenvalues hM_herm a)
              * ∏ i ∈ s, (1 + Matrix.IsHermitian.eigenvalues hM_herm i) :=
        one_le_mul_of_one_le_of_one_le hage hs1
      simpa [Finset.prod_insert ha_not, one_mul] using step'
    -- put all together: 1 ≤ det(I+D) and hence 1 ≤ det(I+M)
    have hDetD_ge : (1 : ℝ) ≤ (((1 : Matrix _ _ ℝ) + D).det) := by
      simpa [hdiag] using hprod_ge
    have hDetM_ge' : (1 : ℝ) ≤ (((1 : Matrix _ _ ℝ) + M).det) := by
      simpa [hdet_invar] using hDetD_ge
    exact hDetM_ge'
  -- Det inequality via factorization
  have hDet_ratio : (((1 : Matrix _ _ ℝ) + A).det)
      ≤ (((1 : Matrix _ _ ℝ) + B).det) := by
    -- det(I+B) = det(R)^2 * det(I+M) and det(I+A) = det(R)^2
    have hdetR_sq_nonneg : 0 ≤ (R.det) ^ 2 := by exact sq_nonneg _
    have : (R.det) ^ 2 ≤ (R.det) ^ 2 * (((1 : Matrix _ _ ℝ) + M).det) := by
      simpa [mul_comm] using mul_le_mul_of_nonneg_left hDetM_ge hdetR_sq_nonneg
    simpa [hIA_det, hIB_det, mul_comm, mul_left_comm, mul_assoc] using this
  -- Finally, apply log monotonicity on positive reals
  -- Monotonicity of log on `(0, ∞)`
  have hposA := hIspA.det_pos
  exact Real.log_le_log hposA hDet_ratio

  /-!
  Typed wrappers (HermitianMat): domain‑disciplined variants with thin
  matrix‑level wrappers above. These follow the same hypotheses but expose
  the Loewner order on Hermitian matrices explicitly.
  -/

  /- Minimal-API variant (work-in-progress): kept documented here for clarity.
     We retain the domain-explicit lemma above; adding the minimal lemma will
     follow in a focused change to avoid churn. -/
  /-
  set_option maxHeartbeats 2000000 in
  /-- Minimal variant: assumes only `A ⪯ B` and `PosDef (I±)`. -/
  theorem logdet_mono_from_opmonotone_min {n : ℕ}
  (A B : Matrix (Fin n) (Fin n) ℝ)
  (hAB : A ⪯ B)
  (hIspA : Matrix.PosDef ((1 : Matrix (Fin n) (Fin n) ℝ) + A))
  (hIspB : Matrix.PosDef ((1 : Matrix (Fin n) (Fin n) ℝ) + B)) :
  Real.log (((1 : Matrix (Fin n) (Fin n) ℝ) + A).det)
    ≤ Real.log (((1 : Matrix (Fin n) (Fin n) ℝ) + B).det) := by
  classical
  -- Whitening with respect to X := I + A
  let X : Matrix (Fin n) (Fin n) ℝ := (1 : Matrix _ _ ℝ) + A
  have hX_psd : Matrix.PosSemidef X := hIspA.posSemidef
  let R : Matrix (Fin n) (Fin n) ℝ := hX_psd.sqrt
  have hR_mul : R * R = X := by simpa [R] using hX_psd.sqrt_mul_self
  have hR_pos : Matrix.PosDef R := by simpa using Matrix.PosDef.posDef_sqrt hIspA
  haveI : Invertible R := (hR_pos.isUnit).invertible
  let S : Matrix (Fin n) (Fin n) ℝ := (⅟ R)
  have hS_pos : Matrix.PosDef S := by simpa [S] using Matrix.PosDef.inv hR_pos
  have hS_herm : S.IsHermitian := hS_pos.isHermitian
  have hS_self : Sᴴ = S := hS_herm.eq
  have hS_trans : S.transpose = S := by
    simpa [Matrix.conjTranspose] using hS_self
  -- Define M := S (B−A) S, then M ⪰ 0
  let Y : Matrix (Fin n) (Fin n) ℝ := B - A
  have hY_psd : Matrix.PosSemidef Y := hAB
  let M : Matrix (Fin n) (Fin n) ℝ := Sᴴ * Y * S
  have hM_psd : Matrix.PosSemidef M := by
    simpa [M] using Matrix.PosSemidef.conjTranspose_mul_mul_same hY_psd S
  -- Algebra: S X S = I and S (I + B) S = I + M
  have hSR : S * R = (1 : Matrix _ _ ℝ) := by
    simpa [S, Matrix.mul_assoc] using
      Matrix.inv_mul_cancel_left_of_invertible (A := R)
        (B := (1 : Matrix (Fin n) (Fin n) ℝ))
  have hRS : R * S = (1 : Matrix _ _ ℝ) := by
    simpa [S, Matrix.mul_assoc] using
      Matrix.mul_inv_cancel_left_of_invertible (A := R)
        (B := (1 : Matrix (Fin n) (Fin n) ℝ))
  have hSXS : S * X * S = (1 : Matrix _ _ ℝ) := by
    calc
      S * X * S = S * (R * R) * S := by simp [X, hR_mul]
      _ = (S * R) * (R * S) := by simp [Matrix.mul_assoc]
      _ = (1 : Matrix _ _ ℝ) := by simp [hSR, hRS]
  have hSIBS : S * ((1 : Matrix _ _ ℝ) + B) * S = (1 : Matrix _ _ ℝ) + M := by
    have hBsplit : B = A + (B - A) := by
      have : (A + B) - A = B := by simpa using add_sub_cancel' (A) (B)
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
    have h0 : S * ((1 : Matrix _ _ ℝ) + B) * S
              = S * ((1 : Matrix _ _ ℝ) + (A + (B - A))) * S := by
      simpa using congrArg (fun M => S * M * S)
        (congrArg (fun t => (1 : Matrix _ _ ℝ) + t) hBsplit)
    have h1 : S * ((1 : Matrix _ _ ℝ) + (A + (B - A))) * S
              = S * (((1 : Matrix _ _ ℝ) + A) + (B - A)) * S := by
      simpa [add_assoc] using congrArg (fun M => S * M * S)
        (by
          have : (1 : Matrix _ _ ℝ) + (A + (B - A))
                  = ((1 : Matrix _ _ ℝ) + A) + (B - A) := by
            simpa [add_assoc]
          exact this)
    have h2 : S * (((1 : Matrix _ _ ℝ) + A) + (B - A)) * S
              = S * ((1 : Matrix _ _ ℝ) + A) * S + S * (B - A) * S :=
      sandwich_add S ((1 : Matrix _ _ ℝ) + A) (B - A)
    have hsum : S * ((1 : Matrix _ _ ℝ) + B) * S
              = S * ((1 : Matrix _ _ ℝ) + A) * S + S * (B - A) * S :=
      h0.trans (h1.trans h2)
    have hfold : S * ((1 : Matrix _ _ ℝ) + B) * S = (1 : Matrix _ _ ℝ) + S * (B - A) * S := by
      simpa [X, hSXS] using hsum
    have hM_def : M = S * (B - A) * S := by
      simp [M, Y, Matrix.conjTranspose, map_starRingEnd_real,
            transpose_map_starRingEnd_real, hS_trans, hS_self]
    simpa [hM_def] using hfold
  -- Transform determinants
  have hIA_det : (((1 : Matrix _ _ ℝ) + A).det) = (R.det) ^ 2 := by
    have hX_eq : (1 : Matrix _ _ ℝ) + A = R * R := by simpa [X] using hR_mul.symm
    simpa [hX_eq, Matrix.det_mul, pow_two]
  have hIB_det : (((1 : Matrix _ _ ℝ) + B).det) = (R.det) ^ 2 * (((1 : Matrix _ _ ℝ) + M).det) := by
    have hB : (1 : Matrix _ _ ℝ) + B = R * ((1 : Matrix _ _ ℝ) + M) * R := hSIBS |> by
      -- From `S*(I+B)*S = I+M`, multiply by `R` on both sides
      -- (done via `hIB_eq` pattern in the full lemma)
      -- We restate here inline for brevity.
      skip
    -- Reuse the same calc as in the full lemma
    have hIB_eq : (1 : Matrix _ _ ℝ) + B = R * ((1 : Matrix _ _ ℝ) + M) * R := by
      calc
        (1 : Matrix _ _ ℝ) + B
            = (R * S) * ((1 : Matrix _ _ ℝ) + B) * (S * R) := by simp [hRS, hSR, Matrix.mul_assoc]
        _   = R * (S * ((1 : Matrix _ _ ℝ) + B) * S) * R := by simp [Matrix.mul_assoc]
        _   = R * ((1 : Matrix _ _ ℝ) + M) * R := by simpa [hSIBS]
    calc
      (((1 : Matrix _ _ ℝ) + B).det)
          = det (R * (((1 : Matrix _ _ ℝ) + M)) * R) := by simpa [hIB_eq]
      _   = det (R) * det (((1 : Matrix _ _ ℝ) + M)) * det R := by
              simpa [Matrix.mul_assoc] using
                (by
                  have h1 := Matrix.det_mul (R * ((1 : Matrix _ _ ℝ) + M)) R
                  have h2 := Matrix.det_mul R ((1 : Matrix _ _ ℝ) + M)
                  have h2' : det (R * ((1 : Matrix _ _ ℝ) + M)) = det R * det ((1 : Matrix _ _ ℝ) + M) := by
                    simpa using h2
                  simpa [Matrix.mul_assoc, h2'] using h1)
      _   = (R.det) ^ 2 * (((1 : Matrix _ _ ℝ) + M).det) := by ring
  -- Lower bound det(I+M) via spectral argument
  have hDetM_ge : (1 : ℝ) ≤ (((1 : Matrix _ _ ℝ) + M).det) := by
    exact det_I_add_psd_ge_one M hM_psd
  -- Det inequality via factorization
  have hDet_ratio : (((1 : Matrix _ _ ℝ) + A).det) ≤ (((1 : Matrix _ _ ℝ) + B).det) := by
    have hdetR_sq_nonneg : 0 ≤ (R.det) ^ 2 := by exact sq_nonneg _
    have : (R.det) ^ 2 ≤ (R.det) ^ 2 * (((1 : Matrix _ _ ℝ) + M).det) := by
      simpa [mul_comm] using mul_le_mul_of_nonneg_left hDetM_ge hdetR_sq_nonneg
    simpa [hIA_det, hIB_det, mul_comm, mul_left_comm, mul_assoc] using this
  -- Finally, apply log monotonicity on positive reals
  exact Real.log_le_log hIspA.det_pos hDet_ratio
  -/

  /- Minimal-API variant: same conclusion using only `A ⪯ B` and `PosDef (I±)`.
     The proof reuses the whitening/factorisation steps and calls the helper
     `det_I_add_psd_ge_one` for the spectral/product bound. -/
  set_option maxHeartbeats 2000000 in
  theorem logdet_mono_from_opmonotone_min {n : ℕ}
    (A B : Matrix (Fin n) (Fin n) ℝ)
    (hAB : A ⪯ B)
    (hIspA : Matrix.PosDef ((1 : Matrix (Fin n) (Fin n) ℝ) + A))
    (hIspB : Matrix.PosDef ((1 : Matrix (Fin n) (Fin n) ℝ) + B)) :
    Real.log (((1 : Matrix (Fin n) (Fin n) ℝ) + A).det)
      ≤ Real.log (((1 : Matrix (Fin n) (Fin n) ℝ) + B).det) := by
    classical
    -- Whitening with respect to X := I + A
    let X : Matrix (Fin n) (Fin n) ℝ := (1 : Matrix _ _ ℝ) + A
    have hX_psd : Matrix.PosSemidef X := hIspA.posSemidef
    let R : Matrix (Fin n) (Fin n) ℝ := hX_psd.sqrt
    have hR_mul : R * R = X := by simpa [R] using hX_psd.sqrt_mul_self
    have hR_pos : Matrix.PosDef R := by simpa using Matrix.PosDef.posDef_sqrt hIspA
    haveI : Invertible R := (hR_pos.isUnit).invertible
    let S : Matrix (Fin n) (Fin n) ℝ := (⅟ R)
    -- Hermitian/Symmetric `S` over ℝ
    have hS_pos : Matrix.PosDef S := by simpa [S] using Matrix.PosDef.inv hR_pos
    have hS_herm : S.IsHermitian := hS_pos.isHermitian
    have hS_self : Sᴴ = S := hS_herm.eq
    have hS_trans : S.transpose = S := by simpa [Matrix.conjTranspose] using hS_self
    -- Define M := S (B−A) S, then M ⪰ 0
    let Y : Matrix (Fin n) (Fin n) ℝ := B - A
    have hY_psd : Matrix.PosSemidef Y := hAB
    let M : Matrix (Fin n) (Fin n) ℝ := Sᴴ * Y * S
    have hM_psd : Matrix.PosSemidef M := by
      simpa [M] using Matrix.PosSemidef.conjTranspose_mul_mul_same hY_psd S
    -- Algebra: S X S = I and S (I + B) S = I + M
    have hSR : S * R = (1 : Matrix _ _ ℝ) := by
      simpa [S, Matrix.mul_assoc] using
        Matrix.inv_mul_cancel_left_of_invertible (A := R)
          (B := (1 : Matrix (Fin n) (Fin n) ℝ))
    have hRS : R * S = (1 : Matrix _ _ ℝ) := by
      simpa [S, Matrix.mul_assoc] using
        Matrix.mul_inv_cancel_left_of_invertible (A := R)
          (B := (1 : Matrix (Fin n) (Fin n) ℝ))
    have hSXS : S * X * S = (1 : Matrix _ _ ℝ) := by
      calc
        S * X * S = S * (R * R) * S := by simp [X, hR_mul]
        _ = (S * R) * (R * S) := by simp [Matrix.mul_assoc]
        _ = (1 : Matrix _ _ ℝ) := by simp [hSR, hRS]
    have hSIBS : S * ((1 : Matrix _ _ ℝ) + B) * S = (1 : Matrix _ _ ℝ) + M := by
      have hBsplit : B = A + (B - A) := by
        have : (A + B) - A = B := by simpa using add_sub_cancel' (A) (B)
        simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using this
      have h0 : S * ((1 : Matrix _ _ ℝ) + B) * S
                = S * ((1 : Matrix _ _ ℝ) + (A + (B - A))) * S := by
        simpa using congrArg (fun M => S * M * S)
          (congrArg (fun t => (1 : Matrix _ _ ℝ) + t) hBsplit)
      have h1 : S * ((1 : Matrix _ _ ℝ) + (A + (B - A))) * S
                = S * (((1 : Matrix _ _ ℝ) + A) + (B - A)) * S := by
        simpa [add_assoc] using congrArg (fun M => S * M * S)
          (by
            have : (1 : Matrix _ _ ℝ) + (A + (B - A))
                    = ((1 : Matrix _ _ ℝ) + A) + (B - A) := by
              simpa [add_assoc]
            exact this)
      have h2 : S * (((1 : Matrix _ _ ℝ) + A) + (B - A)) * S
                = S * ((1 : Matrix _ _ ℝ) + A) * S + S * (B - A) * S :=
        sandwich_add S ((1 : Matrix _ _ ℝ) + A) (B - A)
      have hsum : S * ((1 : Matrix _ _ ℝ) + B) * S
                = S * ((1 : Matrix _ _ ℝ) + A) * S + S * (B - A) * S :=
        h0.trans (h1.trans h2)
      have hfold : S * ((1 : Matrix _ _ ℝ) + B) * S = (1 : Matrix _ _ ℝ) + S * (B - A) * S := by
        simpa [X, hSXS] using hsum
      have hM_def : M = S * (B - A) * S := by
        simp [M, Y, Matrix.conjTranspose, map_starRingEnd_real,
              transpose_map_starRingEnd_real, hS_trans, hS_self]
      simpa [hM_def] using hfold
    -- Determinant identities
    have hIA_det : (((1 : Matrix _ _ ℝ) + A).det) = (R.det) ^ 2 := by
      have hX_eq : (1 : Matrix _ _ ℝ) + A = R * R := by simpa [X] using hR_mul.symm
      simpa [hX_eq, Matrix.det_mul, pow_two]
    have hIB_det : (((1 : Matrix _ _ ℝ) + B).det) = (R.det) ^ 2 * (((1 : Matrix _ _ ℝ) + M).det) := by
      have hIB_eq : (1 : Matrix _ _ ℝ) + B = R * ((1 : Matrix _ _ ℝ) + M) * R := by
        calc
          (1 : Matrix _ _ ℝ) + B
              = (R * S) * ((1 : Matrix _ _ ℝ) + B) * (S * R) := by simp [hRS, hSR, Matrix.mul_assoc]
          _   = R * (S * ((1 : Matrix _ _ ℝ) + B) * S) * R := by simp [Matrix.mul_assoc]
          _   = R * ((1 : Matrix _ _ ℝ) + M) * R := by simpa [hSIBS]
      calc
        (((1 : Matrix _ _ ℝ) + B).det)
            = det (R * (((1 : Matrix _ _ ℝ) + M)) * R) := by simpa [hIB_eq]
        _   = det (R) * det (((1 : Matrix _ _ ℝ) + M)) * det R := by
                simpa [Matrix.mul_assoc] using
                  (by
                    have h1 := Matrix.det_mul (R * ((1 : Matrix _ _ ℝ) + M)) R
                    have h2 := Matrix.det_mul R ((1 : Matrix _ _ ℝ) + M)
                    have h2' : det (R * ((1 : Matrix _ _ ℝ) + M)) = det R * det ((1 : Matrix _ _ ℝ) + M) := by
                      simpa using h2
                    simpa [Matrix.mul_assoc, h2'] using h1)
        _   = (R.det) ^ 2 * (((1 : Matrix _ _ ℝ) + M).det) := by ring
    -- Lower bound det(I+M) via the helper
    have hDetM_ge : (1 : ℝ) ≤ (((1 : Matrix _ _ ℝ) + M).det) := by
      exact det_I_add_psd_ge_one M hM_psd
    -- Det inequality via factorization
    have hDet_ratio : (((1 : Matrix _ _ ℝ) + A).det)
        ≤ (((1 : Matrix _ _ ℝ) + B).det) := by
      have hdetR_sq_nonneg : 0 ≤ (R.det) ^ 2 := by exact sq_nonneg _
      have : (R.det) ^ 2 ≤ (R.det) ^ 2 * (((1 : Matrix _ _ ℝ) + M).det) := by
        simpa [mul_comm] using mul_le_mul_of_nonneg_left hDetM_ge hdetR_sq_nonneg
      simpa [hIA_det, hIB_det, mul_comm, mul_left_comm, mul_assoc] using this
    -- Finally, apply log monotonicity on positive reals
    exact Real.log_le_log hIspA.det_pos hDet_ratio

  namespace HermitianMat

  /-- Inversion reverses Loewner order on SPD, typed `HermitianMat` form. -/
  theorem inv_antitone_spd_H {n : ℕ}
    (A B : HermitianMat n)
    (hA : Matrix.PosDef A.M) (hB : Matrix.PosDef B.M)
    (hAB : A ≤ₗ B) :
    Matrix.PosSemidef (A.M⁻¹ - B.M⁻¹) := by
    exact LoewnerHelpers.inv_antitone_spd (A:=A.M) (B:=B.M) hA hB hAB

  /-- Log‑det monotonicity under Loewner order, typed `HermitianMat` form. -/
  theorem logdet_mono_from_opmonotone_H {n : ℕ}
    (A B : HermitianMat n)
    (hA_psd : Matrix.PosSemidef A.M) (hB_psd : Matrix.PosSemidef B.M)
    (hAB : A ≤ₗ B)
    (hIspA : Matrix.PosDef ((1 : Matrix (Fin n) (Fin n) ℝ) + A.M))
    (hIspB : Matrix.PosDef ((1 : Matrix (Fin n) (Fin n) ℝ) + B.M)) :
    Real.log (((1 : Matrix (Fin n) (Fin n) ℝ) + A.M).det)
      ≤ Real.log (((1 : Matrix (Fin n) (Fin n) ℝ) + B.M).det) := by
    have h := LoewnerHelpers.logdet_mono_from_opmonotone
      (A:=A.M) (B:=B.M)
      (hA:=A.herm) (hB:=B.herm)
      (hA_psd:=hA_psd) (hB_psd:=hB_psd)
      (hAB:=hAB) (hIspA:=hIspA) (hIspB:=hIspB)
    simpa using h

  end HermitianMat

end LoewnerHelpers

end
end NOC
