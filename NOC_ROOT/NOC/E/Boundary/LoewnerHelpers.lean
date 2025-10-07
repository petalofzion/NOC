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

notation:50 A " ⪯ " B => Matrix.PosSemidef (B - A)

namespace LoewnerHelpers

/-- Congruence preserves the Loewner (PSD) order. -/
theorem psd_congr {n : ℕ}
  (A B M : Matrix (Fin n) (Fin n) ℝ)
  (hA : Matrix.IsHermitian A) (hB : Matrix.IsHermitian B)
  (hA_psd : Matrix.PosSemidef A) (hB_psd : Matrix.PosSemidef B)
  (hAB : A ⪯ B) :
  (M.transpose * A * M) ⪯ (M.transpose * B * M) := by
  sorry

/-- Matrix inversion reverses the Loewner order on the SPD cone. -/
theorem inv_antitone_spd {n : ℕ}
  (A B : Matrix (Fin n) (Fin n) ℝ)
  (hA : Matrix.IsHermitian A) (hB : Matrix.IsHermitian B)
  (hA_spd : Matrix.PosDef A) (hB_spd : Matrix.PosDef B)
  (hAB : A ⪯ B) :
  B⁻¹ ⪯ A⁻¹ := by
  sorry

/-- Operator-monotonicity of the logarithm on SPD matrices, expressed via log-det. -/
theorem logdet_mono_from_opmonotone {n : ℕ}
  (A B : Matrix (Fin n) (Fin n) ℝ)
  (hA : Matrix.IsHermitian A) (hB : Matrix.IsHermitian B)
  (hA_psd : Matrix.PosSemidef A) (hB_psd : Matrix.PosSemidef B)
  (hAB : A ⪯ B)
  (hIspA : Matrix.PosDef ((1 : Matrix (Fin n) (Fin n) ℝ) + A))
  (hIspB : Matrix.PosDef ((1 : Matrix (Fin n) (Fin n) ℝ) + B)) :
  Real.log (((1 : Matrix (Fin n) (Fin n) ℝ) + A).det)
    ≤ Real.log (((1 : Matrix (Fin n) (Fin n) ℝ) + B).det) := by
  sorry

end LoewnerHelpers

end
end NOC
