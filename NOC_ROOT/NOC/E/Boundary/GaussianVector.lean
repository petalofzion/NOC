import Mathlib
import NOC.E.Boundary.LoewnerHelpers

/-!
Module: NOC.E.Boundary.GaussianVector
Status: scaffolding (sorrys present).

Purpose: vector Gaussian boundary (log-det form). Mirrors the scalar inequality in
`GaussianMAC.lean`, preparing the ground for a small-dimensional matrix example.
-/

namespace NOC
noncomputable section
open Classical Matrix LoewnerHelpers
open scoped Matrix

variable {n : ℕ}

/-- Mutual-information proxy via `(1/2)·log det (I + A)` for an effective SNR matrix `A`. -/
def mi_logdet (A : Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  (1 / 2 : ℝ) * Real.log (((1 : Matrix (Fin n) (Fin n) ℝ) + A).det)

/-
Effective SNR (clean case): standard log‑det proxy uses a single left inverse
`SigmaN⁻¹ * H * SigmaX * Hᵀ`. This form aligns with the Sylvester determinant
identity (`det (I + AB) = det (I + BA)`) and the usual Gaussian MI formula.
-/
def snrMatClean
  (SigmaN H SigmaX : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  SigmaN⁻¹ * H * SigmaX * H.transpose

/-
Effective SNR when interference `SigmaI` is treated as additional noise: use
`(SigmaN + SigmaI)⁻¹ * H * SigmaX * Hᵀ`.
-/
def snrMatNoisy
  (SigmaN SigmaI H SigmaX : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  (SigmaN + SigmaI)⁻¹ * H * SigmaX * H.transpose

/-- Log-det monotonicity: if `A ⪯ B`, then the MI proxy is monotone. -/
theorem loewner_logdet_mono
  (A B : Matrix (Fin n) (Fin n) ℝ)
  (hA : Matrix.IsHermitian A) (hB : Matrix.IsHermitian B)
  (hA_psd : Matrix.PosSemidef A) (hB_psd : Matrix.PosSemidef B)
  (hAB : A ⪯ B)
  (hIspA : Matrix.PosDef ((1 : Matrix (Fin n) (Fin n) ℝ) + A))
  (hIspB : Matrix.PosDef ((1 : Matrix (Fin n) (Fin n) ℝ) + B)) :
  mi_logdet A ≤ mi_logdet B := by
  -- Reduce to the scalar log inequality then scale by 1/2 (nonnegative).
  have hlog := LoewnerHelpers.logdet_mono_from_opmonotone
    (A:=A) (B:=B) hA hB hA_psd hB_psd hAB hIspA hIspB
  have hhalf : 0 ≤ (1 / 2 : ℝ) := by norm_num
  simpa [mi_logdet, mul_comm, mul_left_comm, mul_assoc] using
    (mul_le_mul_of_nonneg_left hlog hhalf)

/-- Vector Gaussian boundary: removing interference (SigmaI ⪰ 0) improves the MI proxy. -/
theorem mi_after_ablation_logdet [NeZero n]
  (SigmaN SigmaI SigmaX : Matrix (Fin n) (Fin n) ℝ)
  (H : Matrix (Fin n) (Fin n) ℝ)
  (hSigmaN : Matrix.PosDef SigmaN)
  (hSigmaI : Matrix.PosSemidef SigmaI)
  (hSigmaX : Matrix.PosSemidef SigmaX) :
  mi_logdet (snrMatNoisy SigmaN SigmaI H SigmaX)
    ≤ mi_logdet (snrMatClean SigmaN H SigmaX) := by
  classical
  -- Let R be a PSD square root of SigmaX: SigmaX = R * R.
  let SigmaX_psd : Matrix.PosSemidef SigmaX := hSigmaX
  let R : Matrix (Fin n) (Fin n) ℝ := SigmaX_psd.sqrt
  have hRR : R * R = SigmaX := by simpa [R] using SigmaX_psd.sqrt_mul_self
  have hR_psd : Matrix.PosSemidef R := by simpa [R] using SigmaX_psd.posSemidef_sqrt
  have hR_sym : R.transpose = R := by
    simpa [Matrix.conjTranspose] using hR_psd.isHermitian.eq
  -- SPD for SigmaN + SigmaI: PD + PSD is PD.
  have hSum_pos : Matrix.PosDef (SigmaN + SigmaI) := hSigmaN.add_posSemidef hSigmaI
  -- Inverse is antitone on SPD: (SigmaN + SigmaI)⁻¹ ⪯ SigmaN⁻¹.
  have hInv_psd := LoewnerHelpers.inv_antitone_spd (A:=SigmaN) (B:=SigmaN + SigmaI)
    hSigmaN hSum_pos (by
      -- Loewner: SigmaN ⪯ SigmaN + SigmaI because SigmaI ⪰ 0.
      simpa [LoewnerHelpers.LoewnerLE, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
        using (by
          -- (SigmaN + SigmaI) - SigmaN = SigmaI is PSD
          simpa [sub_eq_add_neg, add_comm] using hSigmaI))
  -- Transport the PSD difference through congruence by M := H * R.
  have hPSD_congr :=
    (LoewnerHelpers.psd_congr (A:=((SigmaN + SigmaI)⁻¹)) (B:=SigmaN⁻¹)
      (M:=H * R) hInv_psd)
  -- Unfold the congruence shape: Mᴴ * (B − A) * M = (H R)ᵀ·(SigmaN⁻¹ − (SigmaN+SigmaI)⁻¹)·(H R).
  -- Hence Rᵀ Hᵀ (SigmaN + SigmaI)⁻¹ H R ⪯ Rᵀ Hᵀ SigmaN⁻¹ H R.
  have hAB : LoewnerHelpers.LoewnerLE
      (R.transpose * H.transpose * (SigmaN + SigmaI)⁻¹ * H * R)
      (R.transpose * H.transpose * SigmaN⁻¹ * H * R) := by
    -- Re-express psd_congr conclusion as a Loewner order between the symmetric forms.
    -- psd_congr yields PosSemidef ( (H R)ᴴ * SigmaN⁻¹ * (H R) - (H R)ᴴ * (SigmaN + SigmaI)⁻¹ * (H R) )
    -- which is exactly LoewnerLE between Rᵀ Hᵀ (SigmaN + SigmaI)⁻¹ H R and Rᵀ Hᵀ SigmaN⁻¹ H R.
    simpa [LoewnerHelpers.LoewnerLE, Matrix.conjTranspose,
          Matrix.transpose_mul, Matrix.mul_assoc]
      using hPSD_congr
  -- Now apply log‑det monotonicity on the symmetric forms:
  -- det(I + (SigmaN + SigmaI)⁻¹ H ΣX Hᵀ) = det(I + Rᵀ Hᵀ (SigmaN + SigmaI)⁻¹ H R), similarly for SigmaN.
  -- Invoke the scalar log lemma and scale by 1/2.
  have hlog_sym :
    Real.log (det ((1 : Matrix (Fin n) (Fin n) ℝ) +
      (R.transpose * H.transpose * (SigmaN + SigmaI)⁻¹ * H * R)))
    ≤ Real.log (det ((1 : Matrix (Fin n) (Fin n) ℝ) +
      (R.transpose * H.transpose * SigmaN⁻¹ * H * R))) := by
    -- Both are PSD by construction (M Mᵀ shape).
    have hPSD_noisy : Matrix.PosSemidef
        (R.transpose * H.transpose * (SigmaN + SigmaI)⁻¹ * H * R) := by
      -- (H R)ᵀ (SigmaN + SigmaI)⁻¹ (H R) is PSD
      simpa [Matrix.mul_assoc] using
        Matrix.PosSemidef.conjTranspose_mul_mul_same (A:=(SigmaN + SigmaI)⁻¹) (by
          -- inverse of PD is PSD
          exact (Matrix.PosDef.posSemidef (Matrix.PosDef.inv hSum_pos))) (H * R)
    have hPSD_clean : Matrix.PosSemidef
        (R.transpose * H.transpose * SigmaN⁻¹ * H * R) := by
      simpa [Matrix.mul_assoc] using
        Matrix.PosSemidef.conjTranspose_mul_mul_same (A:=SigmaN⁻¹)
          (by exact (Matrix.PosDef.posSemidef (Matrix.PosDef.inv hSigmaN))) (H * R)
    -- Hermitian follows from PSD.
    have hHerm_noisy : Matrix.IsHermitian
        (R.transpose * H.transpose * (SigmaN + SigmaI)⁻¹ * H * R) := hPSD_noisy.isHermitian
    have hHerm_clean : Matrix.IsHermitian
        (R.transpose * H.transpose * SigmaN⁻¹ * H * R) := hPSD_clean.isHermitian
    -- PD witnesses for I + (·), using that 1 is PD and add_posSemidef
    have hI_pos : Matrix.PosDef ((1 : Matrix (Fin n) (Fin n) ℝ)) := by
      simpa using
        (Matrix.posDef_natCast_iff (R:=ℝ) (n:=Fin n) (d:=1)).2 Nat.one_pos
    have hPos_noisy : Matrix.PosDef ((1 : Matrix (Fin n) (Fin n) ℝ) +
        (R.transpose * H.transpose * (SigmaN + SigmaI)⁻¹ * H * R)) :=
      Matrix.PosDef.add_posSemidef hI_pos hPSD_noisy
    have hPos_clean : Matrix.PosDef ((1 : Matrix (Fin n) (Fin n) ℝ) +
        (R.transpose * H.transpose * SigmaN⁻¹ * H * R)) :=
      Matrix.PosDef.add_posSemidef hI_pos hPSD_clean
    -- Apply monotonicity to the symmetric forms.
    have hcore := LoewnerHelpers.logdet_mono_from_opmonotone
      (A:=R.transpose * H.transpose * (SigmaN + SigmaI)⁻¹ * H * R)
      (B:=R.transpose * H.transpose * SigmaN⁻¹ * H * R)
      (hA:=hHerm_noisy) (hB:=hHerm_clean)
      (hA_psd:=hPSD_noisy) (hB_psd:=hPSD_clean)
      (hAB:=hAB)
      (hIspA:=hPos_noisy) (hIspB:=hPos_clean)
    exact hcore
  -- Re-express determinants back to the original SNR forms via Sylvester identity.
  have hSylv_noisy :
    det ((1 : Matrix (Fin n) (Fin n) ℝ) + snrMatNoisy SigmaN SigmaI H SigmaX)
      = det ((1 : Matrix (Fin n) (Fin n) ℝ) +
        (R.transpose * H.transpose * (SigmaN + SigmaI)⁻¹ * H * R)) := by
    -- Bring snr into AB form
    have hAB :
        snrMatNoisy SigmaN SigmaI H SigmaX
          = ((SigmaN + SigmaI)⁻¹ * H * R) * (R.transpose * H.transpose) := by
      calc
        snrMatNoisy SigmaN SigmaI H SigmaX
            = (SigmaN + SigmaI)⁻¹ * H * SigmaX * H.transpose := rfl
        _   = (SigmaN + SigmaI)⁻¹ * H * (R * R) * H.transpose := by simp [hRR]
        _   = ((SigmaN + SigmaI)⁻¹ * H * R) * (R * H.transpose) := by
              simp [Matrix.mul_assoc]
        _   = ((SigmaN + SigmaI)⁻¹ * H * R) * (R.transpose * H.transpose) := by
              simpa [hR_sym]
    -- Apply Sylvester’s identity
    have hdet := Matrix.det_one_add_mul_comm
      (A:=((SigmaN + SigmaI)⁻¹ * H * R)) (B:=(R.transpose * H.transpose))
    simpa [hAB, Matrix.mul_assoc]
      using hdet
  have hSylv_clean :
    det ((1 : Matrix (Fin n) (Fin n) ℝ) + snrMatClean SigmaN H SigmaX)
      = det ((1 : Matrix (Fin n) (Fin n) ℝ) +
        (R.transpose * H.transpose * SigmaN⁻¹ * H * R)) := by
    have hAB :
        snrMatClean SigmaN H SigmaX
          = (SigmaN⁻¹ * H * R) * (R.transpose * H.transpose) := by
      calc
        snrMatClean SigmaN H SigmaX
            = SigmaN⁻¹ * H * SigmaX * H.transpose := rfl
        _   = SigmaN⁻¹ * H * (R * R) * H.transpose := by simp [hRR]
        _   = (SigmaN⁻¹ * H * R) * (R * H.transpose) := by simp [Matrix.mul_assoc]
        _   = (SigmaN⁻¹ * H * R) * (R.transpose * H.transpose) := by
              simpa [hR_sym]
    have hdet := Matrix.det_one_add_mul_comm
      (A:=(SigmaN⁻¹ * H * R)) (B:=(R.transpose * H.transpose))
    simpa [hAB, Matrix.mul_assoc] using hdet
  -- Conclude for mi_logdet via the two determinant equalities and `hlog_sym`.
  have hhalf : 0 ≤ (1 / 2 : ℝ) := by norm_num
  have : mi_logdet (snrMatNoisy SigmaN SigmaI H SigmaX)
        ≤ mi_logdet (snrMatClean SigmaN H SigmaX) := by
    -- rewrite logs using hSylv_* and apply scaling
    have hlog' :
      Real.log (det ((1 : Matrix (Fin n) (Fin n) ℝ) + snrMatNoisy SigmaN SigmaI H SigmaX))
        ≤ Real.log (det ((1 : Matrix (Fin n) (Fin n) ℝ) + snrMatClean SigmaN H SigmaX)) := by
      simpa [hSylv_noisy, hSylv_clean]
        using hlog_sym
    simpa [mi_logdet, mul_comm, mul_left_comm, mul_assoc]
      using (mul_le_mul_of_nonneg_left hlog' hhalf)
  exact this

end
end NOC
