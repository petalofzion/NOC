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
  -- TODO: fill (whitening + spectral argument), or cite a mathlib lemma when available.
  admit

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
