import Mathlib

/-!
Module: NOC.E.Boundary.LoewnerHelpers
Status: scaffolding (one lemma proved, two left as targets).

Purpose: collect standard matrix-analysis facts (Loewner/PSD order, inverse antitonicity,
log-det monotonicity) used by the Gaussian vector boundary module. We use mathlib’s
`Matrix.PosSemidef/PosDef/IsHermitian` APIs.
-/

namespace NOC
noncomputable section
open Classical Matrix
open scoped Matrix

namespace LoewnerHelpers

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
  have hSR : S * R = (1 : Matrix _ _ ℝ) := by
    simpa [hS_def, Matrix.mul_assoc] using
      Matrix.inv_mul_cancel_left_of_invertible (A := R)
        (B := (1 : Matrix (Fin n) (Fin n) ℝ))
  have hRS : R * S = (1 : Matrix _ _ ℝ) := by
    simpa [hS_def, Matrix.mul_assoc] using
      Matrix.mul_inv_cancel_left_of_invertible (A := R)
        (B := (1 : Matrix (Fin n) (Fin n) ℝ))
  -- Basic identities with `S = R⁻¹`.
  have hSR : S * R = (1 : Matrix _ _ ℝ) := by
    simpa [hS_def, Matrix.mul_assoc] using
      Matrix.inv_mul_cancel_left_of_invertible (A := R)
        (B := (1 : Matrix (Fin n) (Fin n) ℝ))
  have hRS : R * S = (1 : Matrix _ _ ℝ) := by
    simpa [hS_def, Matrix.mul_assoc] using
      Matrix.mul_inv_cancel_left_of_invertible (A := R)
        (B := (1 : Matrix (Fin n) (Fin n) ℝ))
  have hMain : S.transpose * (C - (1 : Matrix _ _ ℝ)) * S =
      (1 : Matrix _ _ ℝ) - C⁻¹ := by simpa [hS_trans] using hSimpl
  -- Push PSD through the congruence
  have hSandwich : Matrix.PosSemidef (S.transpose * (C - (1 : Matrix _ _ ℝ)) * S) := by
    simpa [Matrix.conjTranspose] using
      Matrix.PosSemidef.conjTranspose_mul_mul_same hC_ge S
  simpa [hMain]
    using hSandwich

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
  (hA : Matrix.IsHermitian A) (hB : Matrix.IsHermitian B)
  (hA_psd : Matrix.PosSemidef A) (hB_psd : Matrix.PosSemidef B)
  (hAB : A ⪯ B) :
  Matrix.PosSemidef ((M.transpose * B * M) - (M.transpose * A * M)) := by
  classical
  have hdiff : Matrix.PosSemidef (B - A) := hAB
  have hcongr := Matrix.PosSemidef.conjTranspose_mul_mul_same hdiff M
  simpa [Matrix.mul_sub, Matrix.sub_mul] using hcongr

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
  let R : Matrix (Fin n) (Fin n) ℝ := Matrix.PosSemidef.sqrt hX_psd
  have hR_mul : R * R = X := by simpa using Matrix.PosSemidef.sqrt_mul_self hX_psd
  have hR_pos : Matrix.PosDef R := by simpa using Matrix.PosDef.posDef_sqrt hIspA
  haveI : Invertible R := (hR_pos.isUnit).invertible
  let S : Matrix (Fin n) (Fin n) ℝ := (⅟ R)
  have hS_pos : Matrix.PosDef S := by simpa [S] using Matrix.PosDef.inv hR_pos
  have hS_herm : S.IsHermitian := hS_pos.isHermitian
  have hS_self : Sᴴ = S := hS_herm.eq
  -- Define M := S (B−A) S, then M ⪰ 0
  let Y : Matrix (Fin n) (Fin n) ℝ := B - A
  have hY_psd : Matrix.PosSemidef Y := hAB
  let M : Matrix (Fin n) (Fin n) ℝ := S * Y * S
  have hM_psd : Matrix.PosSemidef M := by
    simpa [M, Matrix.mul_assoc, hS_self] using
      Matrix.PosSemidef.conjTranspose_mul_mul_same hY_psd S
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
    simp [X, Matrix.mul_assoc, hR_mul, hSR, hRS]
  have hSIBS : S * ((1 : Matrix _ _ ℝ) + B) * S
      = (1 : Matrix _ _ ℝ) + M := by
    -- since (I+B) = X + (B−A)
    have : (1 : Matrix _ _ ℝ) + B = X + Y := by
      simp [X, Y, add_comm, add_left_comm, add_assoc]
    simp [this, M, Matrix.mul_add, Matrix.add_mul, hSXS, Matrix.mul_assoc, hS_self]
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
    have hX_eq : (1 : Matrix _ _ ℝ) + A = R * R := by simpa [X] using hR_mul
    simpa [hX_eq, Matrix.det_mul, pow_two]
  have hIB_det : (((1 : Matrix _ _ ℝ) + B).det)
      = (R.det) ^ 2 * (((1 : Matrix _ _ ℝ) + M).det) := by
    -- det(I+B) = det(R) * det(I+M) * det(R)
    have := congr_arg Matrix.det hIB_eq
    -- rewrite det of triple product to isolate det(I+M)
    -- det (R * ((1+M)) * R) = det (R * R * (1+M)) by det_mul_right_comm
    have hrot := Matrix.det_mul_right_comm R ((1 : Matrix _ _ ℝ) + M) R
    -- combine
    simpa [Matrix.mul_assoc, Matrix.det_mul, pow_two] using hrot.symm.trans this
  -- Show det(I+M) ≥ 1 via spectral theorem: product of (1+λᵢ), λᵢ ≥ 0
  have hDetM_ge : (1 : ℝ) ≤ (((1 : Matrix _ _ ℝ) + M).det) := by
    -- diagonalize M and compute determinant of (I + M)
    -- Build the unitary diagonalization data for M
    have hM_herm : Matrix.IsHermitian M := hM_psd.isHermitian
    let U : Matrix (Fin n) (Fin n) ℝ := (Matrix.IsHermitian.eigenvectorUnitary hM_herm :
      Matrix (Fin n) (Fin n) ℝ)
    let D : Matrix (Fin n) (Fin n) ℝ :=
      Matrix.diagonal (fun i => (Matrix.IsHermitian.eigenvalues hM_herm i : ℝ))
    -- Using the spectral theorem to rewrite (I + M)
    have hM_spec : M = U * D * Uᴴ := hM_herm.spectral_theorem
    have hU : U * Uᴴ = (1 : Matrix _ _ ℝ) ∧ Uᴴ * U = (1 : Matrix _ _ ℝ) :=
      (Matrix.mem_unitaryGroup_iff).mp (Matrix.IsHermitian.eigenvectorUnitary hM_herm).2
    have hIplusM : (1 : Matrix _ _ ℝ) + M = U * ((1 : Matrix _ _ ℝ) + D) * Uᴴ := by
      -- (I + M) = U*I*U† + U*D*U† = U*(I + D)*U†
      have h1 : U * Uᴴ = (1 : Matrix _ _ ℝ) := hU.2
      simp [hM_spec, h1, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
    -- determinant invariance under unitary similarity
    have hdet_eq : (((1 : Matrix _ _ ℝ) + M).det)
        = (((1 : Matrix _ _ ℝ) + D).det) := by
      -- det(U*(I+D)*U†) = det(U*U†*(I+D)) = det(I*(I+D)) = det(I+D)
      have h := congr_arg Matrix.det hIplusM
      have hrot := Matrix.det_mul_right_comm U ((1 : Matrix _ _ ℝ) + D) Uᴴ
      simpa [Matrix.mul_assoc, hU.2, one_mul] using hrot.trans h
    -- det(I + D) is a product of (1 + eigenvalues)
    have hdiag : (((1 : Matrix _ _ ℝ) + D).det)
        = ∏ i, (1 + Matrix.IsHermitian.eigenvalues hM_herm i) := by
      -- `I + diagonal v = diagonal (fun i => 1 + v i)`
      have : (1 : Matrix _ _ ℝ) + D
          = Matrix.diagonal (fun i => (1 : ℝ) + Matrix.IsHermitian.eigenvalues hM_herm i) := by
        ext i j
        by_cases hij : i = j
        · subst hij; simp [D]
        · simp [D, hij]
      simpa [this, Matrix.det_diagonal]
    -- Each factor (1 + λᵢ) ≥ 1 since λᵢ ≥ 0 for PSD M
    have hfac : ∀ i, (1 : ℝ) ≤ 1 + Matrix.IsHermitian.eigenvalues hM_herm i := by
      intro i; have := hM_psd.eigenvalues_nonneg i; exact add_le_add_left this 1
    have hprod_ge : (1 : ℝ) ≤ ∏ i, (1 + Matrix.IsHermitian.eigenvalues hM_herm i) := by
      -- product of ≥1 terms is ≥ 1
      classical
      have hnonneg : ∀ i, 0 ≤ (1 : ℝ) + Matrix.IsHermitian.eigenvalues hM_herm i := by
        intro i; exact add_nonneg zero_le_one (hM_psd.eigenvalues_nonneg i)
      refine Finset.induction_on (Finset.univ : Finset (Fin n)) ?base ?step
      · simp
      · intro a s ha hs
        have ha_not : a ∉ s := by simpa using ha
        have hage := hfac a
        have hs_ge := hs
        have hs_nonneg : 0 ≤ ∏ i ∈ s, (1 + Matrix.IsHermitian.eigenvalues hM_herm i) :=
          Finset.prod_nonneg (by intro _ _; exact hnonneg _)
        have := mul_le_mul hage hs_ge (by norm_num) (hnonneg a)
        simpa [Finset.prod_insert ha_not, one_mul] using this
    -- put all together
    simpa [hdet_eq, hdiag] using hprod_ge
  -- Det inequality via factorization
  have hDet_ratio : (((1 : Matrix _ _ ℝ) + A).det)
      ≤ (((1 : Matrix _ _ ℝ) + B).det) := by
    -- det(I+B) = det(R)^2 * det(I+M) and det(I+A) = det(R)^2
    have hdetR_sq_nonneg : 0 ≤ (R.det) ^ 2 := by exact sq_nonneg _
    have : (R.det) ^ 2 ≤ (R.det) ^ 2 * (((1 : Matrix _ _ ℝ) + M).det) := by
      simpa [mul_comm] using mul_le_mul_of_nonneg_left hDetM_ge hdetR_sq_nonneg
    simpa [hIA_det, hIB_det, mul_comm, mul_left_comm, mul_assoc] using this
  -- Finally, apply log monotonicity on positive reals
  exact Real.log_le_log hIspA.det_pos hIspB.det_pos hDet_ratio

end LoewnerHelpers

end
end NOC
