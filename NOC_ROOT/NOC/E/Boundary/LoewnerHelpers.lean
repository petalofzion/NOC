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

/-- Loewner order on real Hermitian matrices: `A ⪯ B` iff `B − A` is PSD. -/
def LoewnerLE {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  Matrix.PosSemidef (B - A)

infix:50 " ⪯ " => LoewnerLE

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
  -- Whiten by the positive square root of A.
  let R : Matrix (Fin n) (Fin n) ℝ := hA.posSemidef.sqrt
  have hR_mul : R * R = A := by
    simpa using hA.posSemidef.sqrt_mul_self
  have hR_pos : Matrix.PosDef R := by
    simpa using Matrix.PosDef.posDef_sqrt hA
  -- Invertible structure for R and its inverse `S`.
  have hR_unit : IsUnit R := hR_pos.isUnit
  have _instR : Invertible R := hR_unit.invertible
  let S : Matrix (Fin n) (Fin n) ℝ := (⅟ R)
  have hS_pos : Matrix.PosDef S := by
    simpa [S] using Matrix.PosDef.inv hR_pos
  have hS_herm : S.IsHermitian := hS_pos.isHermitian
  have hS_self : Sᴴ = S := hS_herm.eq
  -- Define the whitened matrix C = S * B * S. It is SPD by congruence.
  let C : Matrix (Fin n) (Fin n) ℝ := S * B * S
  have hInj : Function.Injective S.vecMul :=
    Matrix.vecMul_injective_of_isUnit (by simpa [S] using hS_pos.isUnit)
  have hC_pos : Matrix.PosDef C := by
    -- Use PosDef.mul_mul_conjTranspose_same with S hermitian so Sᴴ = S.
    simpa [C, hS_self] using
      (Matrix.PosDef.mul_mul_conjTranspose_same (A := B) hB hInj)
  -- Show that C − I is PSD by congruence applied to (B − A) and algebraic rewrites using R⁻¹.
  have hSR : S * R = (1 : Matrix _ _ ℝ) := by simpa [S] using invOf_mul_self R
  have hRS : R * S = (1 : Matrix _ _ ℝ) := by simpa [S] using mul_invOf_self R
  have hSAS : S * A * S = (1 : Matrix _ _ ℝ) := by
    calc
      S * A * S = S * (R * R) * S := by simpa [hR_mul]
      _ = (S * R) * (R * S) := by simp [Matrix.mul_assoc]
      _ = (1 : Matrix _ _ ℝ) * (1 : Matrix _ _ ℝ) := by simpa [hSR, hRS]
      _ = (1 : Matrix _ _ ℝ) := by simp
  have hC_minus : Matrix.PosSemidef (C - (1 : Matrix _ _ ℝ)) := by
    -- (C − I) = S*(B − A)*S, so PSD by congruence applied to `B − A`.
    have hpsd : Matrix.PosSemidef (Sᴴ * (B - A) * S) :=
      Matrix.PosSemidef.conjTranspose_mul_mul_same (A := (B - A)) hAB S
    -- Replace Sᴴ by S (Hermitian) and linearize.
    simpa [C, hS_self, Matrix.mul_sub, Matrix.sub_mul, hSAS]
      using hpsd
  -- From `C − I` PSD and `C` SPD, deduce `I − C⁻¹` PSD via congruence by the square root of `C`.
  -- Let Y be the PSD square root of C, and W its inverse; then `Wᴴ (C − I) W = I − C⁻¹`.
  have hC_psd : Matrix.PosSemidef C := hC_pos.posSemidef
  let Y : Matrix (Fin n) (Fin n) ℝ := hC_psd.sqrt
  have hY_mul : Y * Y = C := by simpa using hC_psd.sqrt_mul_self
  have hY_pos : Matrix.PosDef Y := by simpa using Matrix.PosDef.posDef_sqrt hC_pos
  have hY_unit : IsUnit Y := hY_pos.isUnit
  have _instY : Invertible Y := hY_unit.invertible
  let W : Matrix (Fin n) (Fin n) ℝ := (⅟ Y)
  have hW_herm : W.IsHermitian := by
    have hW_pos : Matrix.PosDef W := by simpa [W] using Matrix.PosDef.inv hY_pos
    exact hW_pos.isHermitian
  have hW_self : Wᴴ = W := hW_herm.eq
  have hWY : W * Y = (1 : Matrix _ _ ℝ) := by simpa [W] using invOf_mul_self Y
  have hYW : Y * W = (1 : Matrix _ _ ℝ) := by simpa [W] using mul_invOf_self Y
  have hC_inv : C⁻¹ = W * W := by
    -- (W * W) is a left inverse for `C = Y * Y`.
    have hLeft : (W * W) * C = (1 : Matrix _ _ ℝ) := by
      calc
        (W * W) * C = (W * W) * (Y * Y) := by simpa [hY_mul]
        _ = ((W * W) * Y) * Y := by simp [Matrix.mul_assoc]
        _ = (W * (W * Y)) * Y := by simp [Matrix.mul_assoc]
        _ = (W * (1 : Matrix _ _ ℝ)) * Y := by simpa [hWY]
        _ = W * Y := by simp [Matrix.mul_assoc]
        _ = (1 : Matrix _ _ ℝ) := by simpa [hWY]
    -- Use left-inverse characterization of inverse.
    exact (Matrix.inv_eq_left_inv hLeft).symm
  have hI_minus : Matrix.PosSemidef ((1 : Matrix _ _ ℝ) - C⁻¹) := by
    -- `(1 - C⁻¹) = Wᴴ * (C - 1) * W`.
    have hEq : Wᴴ * (C - (1 : Matrix _ _ ℝ)) * W = (1 : Matrix _ _ ℝ) - C⁻¹ := by
      -- Expand and use `W * Y = 1 = Y * W` and `Y * Y = C` to rewrite.
      have : W * C * W = (1 : Matrix _ _ ℝ) := by
        calc
          W * C * W = W * (Y * Y) * W := by simpa [hY_mul]
          _ = (W * Y) * (Y * W) := by simp [Matrix.mul_assoc]
          _ = (1 : Matrix _ _ ℝ) * (1 : Matrix _ _ ℝ) := by simpa [hWY, hYW]
          _ = (1 : Matrix _ _ ℝ) := by simp
      have : W * (C - (1 : Matrix _ _ ℝ)) * W
          = (1 : Matrix _ _ ℝ) - (W * (1 : Matrix _ _ ℝ) * W) := by
        simp [Matrix.mul_sub, Matrix.sub_mul, this]
      -- Replace `Wᴴ` with `W` (Hermitian), and compute `W * 1 * W = W * W`.
      simpa [hW_self, hC_inv, Matrix.mul_assoc] using this
    -- Apply congruence PSD preservation.
    simpa [hW_self] using
      (Matrix.PosSemidef.conjTranspose_mul_mul_same (A := (C - (1 : Matrix _ _ ℝ))) hC_minus W)
  -- Finally, `A⁻¹ - B⁻¹ = S * (I - C⁻¹) * S` by algebra on inverses.
  have hA_inv : A⁻¹ = S * S := by
    have hLeft : (S * S) * A = (1 : Matrix _ _ ℝ) := by
      simp [Matrix.mul_assoc, hSR, hR_mul]
    exact (Matrix.inv_eq_left_inv hLeft).symm
  have hB_eq : B = R * C * R := by
    -- From `C = S * B * S` multiply by `R` on both sides.
    calc
      B = (R * S) * B * (S * R) := by simpa [hSR, hRS, Matrix.mul_assoc]
      _ = R * (S * B * S) * R := by simp [Matrix.mul_assoc]
      _ = R * C * R := by rfl
  have hB_inv : B⁻¹ = S * C⁻¹ * S := by
    -- Left inverse characterization for `S * C⁻¹ * S`.
    have hLeft : (S * C⁻¹ * S) * B = (1 : Matrix _ _ ℝ) := by
      simp [hB_eq, Matrix.mul_assoc, hSR]
    exact Matrix.inv_eq_left_inv hLeft
  -- Conclude by congruence.
  have hTarget : A⁻¹ - B⁻¹ = S * ((1 : Matrix _ _ ℝ) - C⁻¹) * S := by
    simp [hA_inv, hB_inv, Matrix.mul_assoc, Matrix.mul_sub, Matrix.sub_mul]
  simpa [hTarget, hS_self] using
    (Matrix.PosSemidef.conjTranspose_mul_mul_same (A := ((1 : Matrix _ _ ℝ) - C⁻¹)) hI_minus S)

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
  -- TODO: Fill via spectral theorem or cite operator-monotone log once available.
  admit

end LoewnerHelpers

end
end NOC
