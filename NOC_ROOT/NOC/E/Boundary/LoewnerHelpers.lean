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
open scoped Matrix

namespace LoewnerHelpers

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
  (hA : Matrix.IsHermitian A) (hB : Matrix.IsHermitian B)
  (hA_spd : Matrix.PosDef A) (hB_spd : Matrix.PosDef B)
  (hAB : Matrix.PosSemidef (B - A)) :
  Matrix.PosSemidef (A⁻¹ - B⁻¹) := by
  sorry

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
