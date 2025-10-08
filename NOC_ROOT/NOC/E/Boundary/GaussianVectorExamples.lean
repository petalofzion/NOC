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

/-!
Vector→scalar reduction (diagonal case): when the effective SNR matrices are
diagonal with nonnegative entries, `mi_logdet` monotonicity reduces to the
componentwise scalar SNR monotonicity via the Loewner order.
-/

namespace NOC
noncomputable section
open Classical Matrix LoewnerHelpers
open scoped Matrix

variable {n : ℕ}

/-- Diagonal monotonicity: if `a i ≤ b i` and all entries are nonnegative, then
`mi_logdet (diag a) ≤ mi_logdet (diag b)`. -/
theorem mi_logdet_diagonal_mono
  [NeZero n]
  (a b : Fin n → ℝ)
  (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i)
  (hcomp : ∀ i, a i ≤ b i) :
  mi_logdet (Matrix.diagonal a) ≤ mi_logdet (Matrix.diagonal b) := by
  classical
  -- Hermitian/PSD for diagonal matrices
  have hA_herm : Matrix.IsHermitian (Matrix.diagonal a) := by
    simpa using (Matrix.isHermitian_diagonal (v := a))
  have hB_herm : Matrix.IsHermitian (Matrix.diagonal b) := by
    simpa using (Matrix.isHermitian_diagonal (v := b))
  have hA_psd : Matrix.PosSemidef (Matrix.diagonal a) := by
    -- PSD(diag a) iff ∀ i, 0 ≤ a i
    simpa using (Matrix.PosSemidef.diagonal (h := ha))
  have hB_psd : Matrix.PosSemidef (Matrix.diagonal b) := by
    simpa using (Matrix.PosSemidef.diagonal (h := hb))
  -- Loewner: diag(b) − diag(a) = diag(b − a), with nonnegative diagonal
  have hBA_psd : Matrix.PosSemidef (Matrix.diagonal b - Matrix.diagonal a) := by
    -- rewrite as diagonal of (b − a)
    have hdiff : Matrix.diagonal b - Matrix.diagonal a
        = Matrix.diagonal (fun i => b i - a i) := by
      ext i j; by_cases hij : i = j
      · subst hij; simp
      · simp [hij]
    -- show PSD of diagonal with nonnegative entries
    have hnn : ∀ i, 0 ≤ b i - a i := by intro i; exact sub_nonneg.mpr (hcomp i)
    simpa [hdiff] using (Matrix.PosSemidef.diagonal (h := hnn))
  -- PD(I + diag a) and PD(I + diag b)
  have hIspA : Matrix.PosDef ((1 : Matrix (Fin n) (Fin n) ℝ) + Matrix.diagonal a) := by
    -- diagonal ((1 + a i)); each entry strictly positive since a i ≥ 0
    have hpos : ∀ i, 0 < (1 : ℝ) + a i := by
      intro i; have := add_pos_of_nonneg_of_pos (ha i) zero_lt_one; simpa [add_comm] using this
    -- PosDef(diagonal d) ↔ ∀ i, 0 < d i
    simpa using (Matrix.posDef_diagonal_iff (d := fun i => (1 : ℝ) + a i)).2 hpos
  have hIspB : Matrix.PosDef ((1 : Matrix (Fin n) (Fin n) ℝ) + Matrix.diagonal b) := by
    have hpos : ∀ i, 0 < (1 : ℝ) + b i := by
      intro i; have := add_pos_of_nonneg_of_pos (hb i) zero_lt_one; simpa [add_comm] using this
    simpa using (Matrix.posDef_diagonal_iff (d := fun i => (1 : ℝ) + b i)).2 hpos
  -- Assemble A ⪯ B and apply the vector monotonicity lemma
  have hAB : LoewnerLE (Matrix.diagonal a) (Matrix.diagonal b) := by
    -- A ⪯ B means PSD(B − A)
    simpa [LoewnerLE] using hBA_psd
  -- Apply the main lemma
  exact GaussianVector.loewner_logdet_mono
    (A := Matrix.diagonal a) (B := Matrix.diagonal b)
    (hA := hA_herm) (hB := hB_herm)
    (hA_psd := hA_psd) (hB_psd := hB_psd)
    (hAB := hAB) (hIspA := hIspA) (hIspB := hIspB)

end
end NOC
