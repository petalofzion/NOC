import Mathlib

/-!
Module: NOC.E.Boundary.GaussianMAC
Status: scaffolding (with proof plan).

Purpose: counterexample‑style boundary rider for Lemma E. In multi‑input interference
channels (e.g., Gaussian MAC), ablating a partner can (under some conditioning/objective
choices) increase a DI/MI proxy, illustrating the regime where the conditional DI–DPI
premises are violated (post‑processing/NCC fails).

High‑level construction plan:
1) Consider Y = X₁ + X₂ + N with independent Gaussian N ~ N(0, σ_n²) and inputs X₁, X₂.
2) Fix X₂’s behavior (e.g., a deterministic policy or adversarial jamming) that makes
   the effective channel for X₁ non‑degraded compared to the ablated case; pick parameters
   so that the “garbling/post‑processing” assumption of DI–DPI is false.
3) Compare a DI/MI proxy for agent 1 before vs. after ablating agent 2.
   Under certain correlations/power allocations, removing X₂ can increase the measured DI/MI.
4) Provide exact Gaussian formulas (capacity/SNR comparisons) once the objective is pinned.

Tactic outline:
- Encode the parameters and regularity as a small record; choose a simple regime (zero mean,
  given powers, nontrivial interference). Use known Gaussian MI formulas to compute differences.
- Keep the lemma a placeholder here; when ready, replace with a concrete parameter instance
  and a short analytic proof.
-/

namespace NOC
noncomputable section
open Classical

/-- Parameters for a toy Gaussian MAC (mean-zero, variances; placeholders). -/
structure GaussianMAC where
  σn : ℝ  -- noise std
  P1 : ℝ  -- power constraint user 1
  P2 : ℝ  -- power constraint user 2
  valid : Prop

/-- Mutual information of a real AWGN scalar channel at SNR (nats), up to constants. -/
def mi_of_snr (snr : ℝ) : ℝ := (1 / 2) * Real.log (1 + snr)

/-- SNR with and without interference for a simple Gaussian MAC model. -/
def snr_with_interference (σn P1 P2 : ℝ) : ℝ :=
  P1 / (σn ^ 2 + P2)

def snr_after_ablation (σn P1 : ℝ) : ℝ :=
  P1 / (σn ^ 2)

/-- Monotonicity of the MI proxy: `mi_of_snr` is strictly increasing in SNR on `snr ≥ 0`. -/
lemma mi_of_snr_strict_mono {s1 s2 : ℝ}
  (hs1 : 0 ≤ s1) (hs2 : 0 ≤ s2) (hgt : s1 < s2) :
  mi_of_snr s1 < mi_of_snr s2 := by
  unfold mi_of_snr
  have hpos1 : 0 < 1 + s1 := by
    have := add_pos_of_nonneg_of_pos hs1 zero_lt_one
    simpa [add_comm] using this
  have hpos2 : 0 < 1 + s2 := by
    have := add_pos_of_nonneg_of_pos hs2 zero_lt_one
    simpa [add_comm] using this
  have hlt' : 1 + s1 < 1 + s2 := by simpa using add_lt_add_left hgt 1
  have hlog : Real.log (1 + s1) < Real.log (1 + s2) :=
    Real.log_lt_log hpos1 hlt'
  have hhalf : 0 < (1 / 2 : ℝ) := by norm_num
  simpa [mul_comm, mul_left_comm, mul_assoc]
    using (mul_lt_mul_of_pos_left hlog hhalf)

/-- In the AWGN MAC, removing interference (P2 > 0) strictly increases the MI proxy for user 1.
Assuming positive noise variance and power, the SNR without interference is strictly larger. -/
theorem mi_after_ablation_strict
  {σn P1 P2 : ℝ}
  (hσ : 0 < σn) (hP1 : 0 < P1) (hP2 : 0 < P2) :
  mi_of_snr (snr_with_interference σn P1 P2)
    < mi_of_snr (snr_after_ablation σn P1) := by
  have hσsq_pos : 0 < σn ^ 2 := by
    have : 0 < σn * σn := mul_pos hσ hσ
    simpa [pow_two] using this
  have hden_pos : 0 < σn ^ 2 + P2 := by
    have : 0 ≤ σn ^ 2 := sq_nonneg σn
    have := add_pos_of_nonneg_of_pos this hP2
    simpa using this
  have hlt : σn ^ 2 < σn ^ 2 + P2 := by
    have : 0 < P2 := hP2
    linarith
  have hone_div : (1 : ℝ) / (σn ^ 2 + P2) < 1 / (σn ^ 2) :=
    one_div_lt_one_div_of_lt hσsq_pos hlt
  have hsnr_lt : snr_with_interference σn P1 P2
      < snr_after_ablation σn P1 := by
    unfold snr_with_interference snr_after_ablation
    have := mul_lt_mul_of_pos_left hone_div hP1
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using this
  have hsnr_nonneg : 0 ≤ snr_with_interference σn P1 P2 := by
    unfold snr_with_interference
    exact div_nonneg (le_of_lt hP1) (le_of_lt hden_pos)
  have hsnr_nonneg' : 0 ≤ snr_after_ablation σn P1 := by
    unfold snr_after_ablation
    exact div_nonneg (le_of_lt hP1) (le_of_lt hσsq_pos)
  exact mi_of_snr_strict_mono hsnr_nonneg hsnr_nonneg' hsnr_lt

/-- Non-strict variant: removing interference does not decrease the MI proxy. -/
theorem mi_after_ablation_ge_with_interference
  {σn P1 P2 : ℝ}
  (hσ : 0 < σn) (hP1 : 0 ≤ P1) (hP2 : 0 ≤ P2) :
  mi_of_snr (snr_with_interference σn P1 P2)
    ≤ mi_of_snr (snr_after_ablation σn P1) := by
  have hσsq_pos : 0 < σn ^ 2 := by
    have : 0 < σn * σn := mul_pos hσ hσ
    simpa [pow_two] using this
  have hden_nonneg : 0 ≤ σn ^ 2 + P2 := add_nonneg (sq_nonneg σn) hP2
  have hle : σn ^ 2 ≤ σn ^ 2 + P2 := by linarith [hP2]
  have hone_div : (1 : ℝ) / (σn ^ 2 + P2) ≤ 1 / (σn ^ 2) :=
    one_div_le_one_div_of_le hσsq_pos hle
  have hsnr_le : snr_with_interference σn P1 P2
      ≤ snr_after_ablation σn P1 := by
    unfold snr_with_interference snr_after_ablation
    have := mul_le_mul_of_nonneg_left hone_div hP1
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using this
  have hsnr_nonneg : 0 ≤ snr_with_interference σn P1 P2 := by
    unfold snr_with_interference
    exact div_nonneg hP1 hden_nonneg
  have hsnr_nonneg' : 0 ≤ snr_after_ablation σn P1 := by
    unfold snr_after_ablation
    exact div_nonneg hP1 (le_of_lt hσsq_pos)
  unfold mi_of_snr
  have hpos1 : 0 < 1 + snr_with_interference σn P1 P2 := by
    have := add_pos_of_pos_of_nonneg zero_lt_one hsnr_nonneg
    simpa [add_comm] using this
  have hpos2 : 0 < 1 + snr_after_ablation σn P1 := by
    have := add_pos_of_pos_of_nonneg zero_lt_one hsnr_nonneg'
    simpa [add_comm] using this
  have hlog :
      Real.log (1 + snr_with_interference σn P1 P2)
        ≤ Real.log (1 + snr_after_ablation σn P1) :=
    Real.log_le_log hpos1 (by simpa using add_le_add_left hsnr_le 1)
  have hhalf : 0 ≤ (1 / 2 : ℝ) := by norm_num
  exact (mul_le_mul_of_nonneg_left hlog hhalf)

/-- Skeleton: in a chosen parameter regime, MI/DI proxy for user 1 increases after ablating user 2. -/
theorem mi_increase_after_ablation (_M : GaussianMAC) :
  True := by
  -- Placeholder proof: once the concrete MAC parameters are fixed we
  -- will compare the SNR-based MI proxy before/after ablation. For now
  -- we acknowledge the statement and keep the file compiling.
  trivial

/-- Statement sketch (placeholder): exhibit parameters where an MI/DI proxy increases after an
“ablation” move, showing that unconditional monotonicity fails in interference regimes. -/
theorem interference_counterexample (_M : GaussianMAC) : True := by
  trivial

/-- Concrete scalar instance (non‑strict): with σn=1, P1=1, P2=1, removing interference
increases the MI proxy (at least weakly). -/
theorem scalar_instance_ge :
  mi_of_snr (snr_with_interference (σn:=1) (P1:=1) (P2:=1))
    ≤ mi_of_snr (snr_after_ablation (σn:=1) (P1:=1)) := by
  have hσ : 0 < (1 : ℝ) := by norm_num
  have hP1 : 0 ≤ (1 : ℝ) := by norm_num
  have hP2 : 0 ≤ (1 : ℝ) := by norm_num
  simpa using mi_after_ablation_ge_with_interference (σn:=1) (P1:=1) (P2:=1) hσ hP1 hP2

/-- Concrete scalar instance (strict): with σn=1, P1=1, P2=1, the MI proxy strictly increases
after removing interference. -/
theorem scalar_instance_strict :
  mi_of_snr (snr_with_interference (σn:=1) (P1:=1) (P2:=1))
    < mi_of_snr (snr_after_ablation (σn:=1) (P1:=1)) := by
  have hσ : 0 < (1 : ℝ) := by norm_num
  have hP1 : 0 < (1 : ℝ) := by norm_num
  have hP2 : 0 < (1 : ℝ) := by norm_num
  simpa using mi_after_ablation_strict (σn:=1) (P1:=1) (P2:=1) hσ hP1 hP2

end
end NOC
