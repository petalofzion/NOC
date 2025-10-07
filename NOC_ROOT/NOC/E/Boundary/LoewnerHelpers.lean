import Mathlib

/-!
Module: NOC.E.Boundary.LoewnerHelpers
Status: scaffolding (sorrys present).

Purpose: collect standard matrix-analysis facts (Loewner/PSD order, inverse
antitonicity, log-det monotonicity) used by the Gaussian vector boundary module.
Fill these lemmas with mathlib proofs when ready.
-/

namespace NOC
noncomputable section
open Classical Matrix
open scoped Matrix ComplexOrder

namespace LoewnerHelpers

section helpers

/-- Congruence by a positive-definite square root sends `(C - I)` to `(I - C⁻¹)`. -/
lemma psd_one_sub_inv_of_ge_one
    {n : ℕ} {C : Matrix (Fin n) (Fin n) ℝ}
    (hC : C.PosDef)
    (hC_ge : Matrix.PosSemidef (C - (1 : Matrix (Fin n) (Fin n) ℝ))) :
    Matrix.PosSemidef ((1 : Matrix (Fin n) (Fin n) ℝ) - C⁻¹) := by
  classical
  let hC_psd : Matrix.PosSemidef C := hC.posSemidef
  let R := hC_psd.sqrt
  have hR_psd : Matrix.PosSemidef R := hC_psd.posSemidef_sqrt
  have hR_herm : R.IsHermitian := hR_psd.1
  have hR_mul : R ⬝ R = C := by
    simpa [R] using Matrix.PosSemidef.sqrt_mul_self hC_psd
  have hdetC_pos : 0 < Matrix.det C := hC.det_pos
  have hdetC_ne : Matrix.det C ≠ 0 := ne_of_gt hdetC_pos
  have hdetR_ne : Matrix.det R ≠ 0 := by
    have hdet_eq : Matrix.det C = Matrix.det R * Matrix.det R := by
      simpa [hR_mul] using Matrix.det_mul R R
    intro hR_det
    have : Matrix.det C = 0 := by simpa [hdet_eq, hR_det]
    exact hdetC_ne this
  haveI : Invertible R := Matrix.invertibleOfDetNeZero hdetR_ne
  let S : Matrix (Fin n) (Fin n) ℝ := (⅟ R)
  have hS_conj : Sᴴ = ⅟ R := by
    simpa [S, hR_herm.eq] using Matrix.conjTranspose_invOf (A := R)
  have hEq : Sᴴ ⬝ (C - (1 : Matrix _ _ ℝ)) ⬝ S
      = (1 : Matrix _ _ ℝ) - C⁻¹ := by
    calc
      Sᴴ ⬝ (C - (1 : Matrix _ _ ℝ)) ⬝ S
          = Sᴴ ⬝ (R ⬝ R - (1 : Matrix _ _ ℝ)) ⬝ S := by simpa [hR_mul]
      _   = Sᴴ ⬝ (R ⬝ R) ⬝ S - Sᴴ ⬝ S := by
              simp [Matrix.mul_sub, Matrix.sub_mul, sub_eq_add_neg]
      _   = (1 : Matrix _ _ ℝ) - Sᴴ ⬝ S := by
              have : Sᴴ ⬝ (R ⬝ R) ⬝ S = (1 : Matrix _ _ ℝ) := by
                simp [S, hS_conj, Matrix.mul_assoc]
              simpa [this]
      _   = (1 : Matrix _ _ ℝ) - ((R ⬝ R)⁻¹) := by
              have h_inv_left : ((⅟ R) ⬝ (⅟ R)) ⬝ (R ⬝ R) = (1 : Matrix _ _ ℝ) := by
                simp [Matrix.mul_assoc]
              have hInv : (R ⬝ R)⁻¹ = (⅟ R) ⬝ (⅟ R) := Matrix.inv_eq_left_inv h_inv_left
              have h1 : Sᴴ ⬝ S = (R ⬝ R)⁻¹ := by
                simpa [S, hS_conj] using hInv.symm
              simpa [h1]
      _   = (1 : Matrix _ _ ℝ) - C⁻¹ := by simpa [hR_mul]
  simpa [hEq] using Matrix.PosSemidef.conjTranspose_mul_mul_same hC_ge S

end helpers

/-- Congruence preserves the Loewner (PSD) order. -/
theorem psd_congr {n : ℕ}
  (A B M : Matrix (Fin n) (Fin n) ℝ)
  (hA : Matrix.IsHermitian A) (hB : Matrix.IsHermitian B)
  (hA_psd : Matrix.PosSemidef A) (hB_psd : Matrix.PosSemidef B)
  (hAB : Matrix.PosSemidef (B - A)) :
  Matrix.PosSemidef ((M.transpose * B * M) - (M.transpose * A * M)) := by
  classical
  have hdiff : Matrix.PosSemidef (B - A) := hAB
  have hcongr :=
    Matrix.PosSemidef.conjTranspose_mul_mul_same hdiff M
  simpa [Matrix.mul_sub, Matrix.sub_mul]
    using hcongr

/-- Matrix inversion reverses the Loewner order on the SPD cone. -/
theorem inv_antitone_spd {n : ℕ}
  (A B : Matrix (Fin n) (Fin n) ℝ)
  (hA : Matrix.PosDef A) (hB : Matrix.PosDef B)
  (hAB : Matrix.PosSemidef (B - A)) :
  Matrix.PosSemidef (A⁻¹ - B⁻¹) := by
  classical
  -- Positive semidefinite square root of `A`.
  let hA_psd : Matrix.PosSemidef A := hA.posSemidef
  let R := hA_psd.sqrt
  have hR_psd : Matrix.PosSemidef R := hA_psd.posSemidef_sqrt
  have hR_herm : R.IsHermitian := hR_psd.1
  have hR_mul : R ⬝ R = A := by
    simpa [R] using Matrix.PosSemidef.sqrt_mul_self hA_psd
  have hdetA_ne : Matrix.det A ≠ 0 := ne_of_gt hA.det_pos
  have hdetR_ne : Matrix.det R ≠ 0 := by
    have hdet_eq : Matrix.det A = Matrix.det R * Matrix.det R := by
      simpa [hR_mul] using Matrix.det_mul R R
    intro hR_det
    have : Matrix.det A = 0 := by simpa [hdet_eq, hR_det]
    exact hdetA_ne this
  haveI : Invertible R := Matrix.invertibleOfDetNeZero hdetR_ne
  -- Whitening matrix `S := (sqrt A)⁻¹`.
  let S : Matrix (Fin n) (Fin n) ℝ := (⅟ R)
  have hS_pos : Matrix.PosDef S := Matrix.PosDef.inv (Matrix.PosDef.posDef_sqrt hA)
  have hS_herm : S.IsHermitian := hS_pos.isHermitian
  have hS_conj : Sᴴ = S := hS_herm.eq
  -- Whitened matrix `C`.
  let C : Matrix (Fin n) (Fin n) ℝ := S ⬝ B ⬝ S
  have hC_pos : C.PosDef := by
    have := hB.congr S
    simpa [C, hS_conj] using this
  -- Show `C - I` is PSD via congruence applied to `B - A`.
  have hSAS : S ⬝ A ⬝ S = (1 : Matrix _ _ ℝ) := by
    have h_left : S ⬝ R = (1 : Matrix _ _ ℝ) := by simp [S, Matrix.mul_assoc]
    have h_right : R ⬝ S = (1 : Matrix _ _ ℝ) := by simp [S, Matrix.mul_assoc]
    calc
      S ⬝ A ⬝ S = S ⬝ (R ⬝ R) ⬝ S := by simpa [hR_mul]
      _ = (S ⬝ R) ⬝ (R ⬝ S) := by simp [Matrix.mul_assoc]
      _ = (1 : Matrix _ _ ℝ) := by simp [h_left, h_right]
  have hC_minus : Matrix.PosSemidef (C - (1 : Matrix _ _ ℝ)) := by
    have hpsd : Matrix.PosSemidef (S ⬝ (B - A) ⬝ S) := by
      simpa [hS_conj, Matrix.mul_assoc] using
        Matrix.PosSemidef.conjTranspose_mul_mul_same hAB S
    have hEq : C - (1 : Matrix _ _ ℝ) = S ⬝ (B - A) ⬝ S := by
      calc
        C - (1 : Matrix _ _ ℝ)
            = S ⬝ B ⬝ S - (1 : Matrix _ _ ℝ) := rfl
        _   = S ⬝ (B - A) ⬝ S + S ⬝ A ⬝ S - (1 : Matrix _ _ ℝ) := by
                simp [Matrix.mul_add, Matrix.add_mul, sub_eq_add_neg]
        _   = S ⬝ (B - A) ⬝ S := by simpa [hSAS]
    simpa [hEq] using hpsd
  -- `I - C⁻¹` is positive semidefinite by the helper lemma.
  have hI_minus : Matrix.PosSemidef ((1 : Matrix _ _ ℝ) - C⁻¹) :=
    psd_one_sub_inv_of_ge_one hC_pos hC_minus
  -- Compute `A⁻¹` and `B⁻¹` in the whitened coordinates.
  have hSId : S ⬝ (1 : Matrix _ _ ℝ) ⬝ S = A⁻¹ := by
    have hInv : (R ⬝ R)⁻¹ = (⅟ R) ⬝ (⅟ R) := by
      have h_left : ((⅟ R) ⬝ (⅟ R)) ⬝ (R ⬝ R) = (1 : Matrix _ _ ℝ) := by
        simp [Matrix.mul_assoc]
      exact (Matrix.inv_eq_left_inv h_left).symm
    simpa [Matrix.mul_assoc, hR_mul, S, hInv]
  have hSinv : (⅟ S) = R := Matrix.invOf_invOf (A := R)
  have hC_inv : C⁻¹ = (⅟ S) ⬝ B⁻¹ ⬝ (⅟ S) := by
    have h_left : ((⅟ S) ⬝ B⁻¹ ⬝ (⅟ S)) ⬝ C = (1 : Matrix _ _ ℝ) := by
      simp [C, Matrix.mul_assoc]
    exact Matrix.inv_eq_left_inv h_left
  have hSCinv : S ⬝ C⁻¹ ⬝ S = B⁻¹ := by
    simp [hC_inv, hSinv, Matrix.mul_assoc, S]
  -- Express the target as a congruence of `(1 - C⁻¹)`.
  have hExpr : A⁻¹ - B⁻¹ = S ⬝ ((1 : Matrix _ _ ℝ) - C⁻¹) ⬝ S := by
    simp [Matrix.mul_sub, Matrix.sub_mul, sub_eq_add_neg,
      Matrix.mul_assoc, hSId, hSCinv]
  simpa [hExpr, hS_conj] using
    Matrix.PosSemidef.conjTranspose_mul_mul_same hI_minus S

/-- Operator-monotonicity of the logarithm on SPD matrices, expressed via log-det. -/
theorem logdet_mono_from_opmonotone {n : ℕ}
  (A B : Matrix (Fin n) (Fin n) ℝ)
  (hA : Matrix.IsHermitian A) (hB : Matrix.IsHermitian B)
  (hA_psd : Matrix.PosSemidef A) (hB_psd : Matrix.PosSemidef B)
  (hAB : Matrix.PosSemidef (B - A))
  (hIspA : Matrix.PosDef ((1 : Matrix (Fin n) (Fin n) ℝ) + A))
  (hIspB : Matrix.PosDef ((1 : Matrix (Fin n) (Fin n) ℝ) + B)) :
  Real.log (((1 : Matrix (Fin n) (Fin n) ℝ) + A).det)
    ≤ Real.log (((1 : Matrix (Fin n) (Fin n) ℝ) + B).det) := by
  sorry

end LoewnerHelpers

end
end NOC
