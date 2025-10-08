import Mathlib
import NOC.E.Boundary.LoewnerHelpers
import NOC.E.Boundary.GaussianVector

/-!
Module: NOC.E.Boundary.GaussianVectorExamples
Status: small examples (no sorrys).

Purpose: sanity examples for the vector Gaussian boundary lemmas, using simple
choices that make the PSD/PD obligations immediate.
-/

namespace NOC
noncomputable section
open Classical Matrix LoewnerHelpers
open scoped Matrix

variable {n : ℕ}

/-- With identity noise, PSD interference, and PSD input covariance, the vector
ablation inequality holds for any channel `H`. This packages standard choices of
Σₙ, Σᵢ, Σₓ that make the hypotheses immediate. -/
theorem mi_after_ablation_logdet_id_noise
  [NeZero n]
  (H R R₂ : Matrix (Fin n) (Fin n) ℝ) :
  let SigmaN := (1 : Matrix (Fin n) (Fin n) ℝ)
  let SigmaI := R₂.transpose * R₂
  let SigmaX := R.transpose * R
  mi_logdet (GaussianVector.snrMatNoisy SigmaN SigmaI H SigmaX)
    ≤ mi_logdet (GaussianVector.snrMatClean SigmaN H SigmaX) := by
  classical
  intro SigmaN SigmaI SigmaX
  -- Hypotheses: ΣN ≻ 0, ΣI ⪰ 0, ΣX ⪰ 0
  have hSigmaN : Matrix.PosDef SigmaN := by
    simpa using LoewnerHelpers.posDef_one (n:=n)
  have hI_psd : Matrix.PosSemidef ((1 : Matrix (Fin n) (Fin n) ℝ)) := hSigmaN.posSemidef
  have hSigmaI : Matrix.PosSemidef SigmaI := by
    -- R₂ᵀ * I * R₂ is PSD; over ℝ, conjTranspose = transpose
    have := Matrix.PosSemidef.conjTranspose_mul_mul_same (A:=(1 : Matrix (Fin n) (Fin n) ℝ)) hI_psd R₂
    simpa [SigmaI, Matrix.mul_assoc, Matrix.conjTranspose] using this
  have hSigmaX : Matrix.PosSemidef SigmaX := by
    have := Matrix.PosSemidef.conjTranspose_mul_mul_same (A:=(1 : Matrix (Fin n) (Fin n) ℝ)) hI_psd R
    simpa [SigmaX, Matrix.mul_assoc, Matrix.conjTranspose] using this
  -- Apply the main vector inequality
  exact GaussianVector.mi_after_ablation_logdet (SigmaN:=SigmaN) (SigmaI:=SigmaI)
    (SigmaX:=SigmaX) H hSigmaN hSigmaI hSigmaX

end
end NOC

/-!
Small 2×2 diagonal specialization (identity noise): demonstrates a concrete setup
where the vector ablation inequality applies, with all matrices diagonal.
-/

namespace NOC
noncomputable section
open Classical Matrix LoewnerHelpers
open scoped Matrix

/-- 2×2 diagonal example with identity noise. -/
theorem mi_after_ablation_logdet_diag2_id_noise
  [NeZero (2)]
  (h1 h2 r1 r2 s1 s2 : ℝ) :
  let H      : Matrix (Fin 2) (Fin 2) ℝ := Matrix.diagonal ![h1, h2]
  let R      : Matrix (Fin 2) (Fin 2) ℝ := Matrix.diagonal ![r1, r2]
  let R₂     : Matrix (Fin 2) (Fin 2) ℝ := Matrix.diagonal ![s1, s2]
  let SigmaN : Matrix (Fin 2) (Fin 2) ℝ := (1 : Matrix (Fin 2) (Fin 2) ℝ)
  let SigmaI : Matrix (Fin 2) (Fin 2) ℝ := R₂.transpose * R₂
  let SigmaX : Matrix (Fin 2) (Fin 2) ℝ := R.transpose * R
  mi_logdet (GaussianVector.snrMatNoisy SigmaN SigmaI H SigmaX)
    ≤ mi_logdet (GaussianVector.snrMatClean SigmaN H SigmaX) := by
  classical
  intro H R R₂ SigmaN SigmaI SigmaX
  -- Identity noise: PD
  have hSigmaN : Matrix.PosDef SigmaN := by
    simpa using LoewnerHelpers.posDef_one (n:=2)
  -- PSD sandwiches for SigmaI and SigmaX
  have hI_psd : Matrix.PosSemidef ((1 : Matrix (Fin 2) (Fin 2) ℝ)) := hSigmaN.posSemidef
  have hSigmaI : Matrix.PosSemidef SigmaI := by
    simpa [SigmaI, Matrix.mul_assoc, Matrix.conjTranspose]
      using Matrix.PosSemidef.conjTranspose_mul_mul_same (A:=(1 : Matrix (Fin 2) (Fin 2) ℝ)) hI_psd R₂
  have hSigmaX : Matrix.PosSemidef SigmaX := by
    simpa [SigmaX, Matrix.mul_assoc, Matrix.conjTranspose]
      using Matrix.PosSemidef.conjTranspose_mul_mul_same (A:=(1 : Matrix (Fin 2) (Fin 2) ℝ)) hI_psd R
  -- Apply the vector ablation inequality
  exact GaussianVector.mi_after_ablation_logdet (SigmaN:=SigmaN) (SigmaI:=SigmaI)
    (SigmaX:=SigmaX) H hSigmaN hSigmaI hSigmaX

end
end NOC
