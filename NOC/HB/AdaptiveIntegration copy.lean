/-
  NOC/HB/AdaptiveIntegration.lean
  
  The "Gold Standard" Integration Test: Heavy Ball Physics with Adaptive Step Sizes.
  
  Purpose:
  Proves that Heavy Ball acceleration is positive for *any* curvature `lam > 0`,
  provided the agent respects the physical stability limit `hb_rhoStar(τ, γ)`.
  
  This generalizes `NOC/HB/Integration.lean` (which checked a fixed step size for a fixed range)
  to an **Adaptive Policy** (Option 3: Functional Choice). It confirms the NOC Meta-Learning 
  hypothesis: if the agent learns the correct step size (β), it always accelerates.
-/

import Mathlib
import NOC.HB.CloseLoop
import NOC.B.Expectation

namespace NOC
noncomputable section
open Classical
open scoped BigOperators

/-! ## 1. Setup: The Adaptive Ensemble -/

/-- Agent parameters (fixed damping/learning rate base). 
    We only require standard stability bounds on these. -/
structure AdaptiveParams where
  η : ℝ
  γ : ℝ
  hEta : 0 < η
  hGamma : 0 ≤ γ ∧ γ < 1

/-- 
  A General Scenario.
  Unlike `Integration.lean`, we do NOT bound `lam`. 
  We allow any `lam` such that the discrete time constant `τ < 2` (stability limit).
  
  Crucially, the step size constraint `hStep` is FUNCTIONAL:
  It depends on `hb_rhoStar` calculated from the specific `lam`.
-/
structure AdaptiveScenario (p : AdaptiveParams) where
  lam    : ℝ
  x      : ℝ
  x_prev : ℝ
  xstar  : ℝ
  hLam   : 0 < lam
  hTau   : p.η * lam < 2  -- Only physical limit: sampling rate < Nyquist/2 approx
  hStep  : |x - x_prev| ≤ 0.9 * hb_rhoStar (p.η * lam) p.γ * |x - xstar|
  -- We use 0.9 as a safety margin (epsilon = 0.1)

/-- The support set. -/
def AdaptiveScenarios (p : AdaptiveParams) (l : List (AdaptiveScenario p)) : Finset (AdaptiveScenario p) := 
  l.toFinset

/-! ## 2. Setup: The Physics -/

def cap_a : ℝ := 10.0
def cap_b : ℝ := 1.0
lemma cap_b_pos : 0 < cap_b := by simp [cap_b]; norm_num

/-- The gap coefficient is now dynamic: it depends on the task `s`. -/
def adaptive_gap_coeff (p : AdaptiveParams) (s : AdaptiveScenario p) : ℝ :=
  let τ := p.η * s.lam
  let eps := 0.1
  eps * (s.lam / 2) * τ * (2 - τ)

/-! ## 3. Pointwise Adaptive Acceleration Proof -/

/--
  Theorem: For ANY valid adaptive scenario, acceleration is positive.
  This proves that the "Physics Engine" works universally if the "Control Engine" (Adaptive Step) works.
-/
theorem adaptive_pointwise_acceleration (p : AdaptiveParams) (s : AdaptiveScenario p) :
    let U_next := (cap_a - cap_b * f_at s.lam (hbStep ⟨p.η, p.γ, p.hEta, p.hGamma⟩ s.lam s.x s.x_prev s.xstar) s.xstar)
    let U_curr := (cap_a - cap_b * f_at s.lam s.x s.xstar)
    let U_prev := (cap_a - cap_b * f_at s.lam s.x_prev s.xstar)
    delta2 U_next U_curr U_prev ≥ cap_b * (adaptive_gap_coeff p s) * (s.x - s.xstar)^2 := by
  
  -- 1. Unpack Physics Requirements
  let hb_p : HBParams := ⟨p.η, p.γ, p.hEta, p.hGamma⟩
  let τ := p.η * s.lam
  
  have hτlo : 0 < τ := mul_pos p.hEta s.hLam
  have hτhi : τ < 2 := s.hTau
  
  -- 2. Apply Gap Lemma from CloseLoop
  -- We pass the functional constraint `s.hStep` directly.
  -- We assume eps = 0.1.
  -- s.hStep says |d| ≤ 0.9 * ρ⋆ * |e|.
  -- 0.9 = 1 - 0.1.
  -- So this matches `delta2_f_gap_under_rho` with eps=0.1 exactly.
  
  have h_f := delta2_f_gap_under_rho
    (p := hb_p)
    (lam := s.lam) (x := s.x) (x_prev := s.x_prev) (xstar := s.xstar)
    (ρ := 0.9 * hb_rhoStar τ p.γ) -- We instantiate ρ exactly at the limit
    (eps := 0.1)
    (hρlo := by 
      -- Prove ρ = 0.9 * hb_rhoStar ≥ 0
      apply mul_nonneg (by norm_num)
      -- Expand hb_rhoStar to show it is non-negative given τ ∈ (0,2)
      simp only [hb_rhoStar]
      apply div_nonneg
      · -- Numerator: τ * (2 - τ)
        apply mul_nonneg (le_of_lt hτlo)
        linarith [hτhi]
      · -- Denominator: (1 + γ^2) + 2(1+|γ|)
        have hSq : 0 ≤ p.γ ^ 2 := sq_nonneg _
        have hAbs : 0 ≤ |p.γ| := abs_nonneg _
        nlinarith) 
    (hConv := le_of_lt s.hLam)
    (hτlo := hτlo) (hτhi := hτhi)
    (heps0 := by norm_num) (heps1 := by norm_num)
    (hρcap := by norm_num; exact le_refl _) -- 0.9 = 1 - 0.1
    (hbound := s.hStep)

  -- 3. Rearrange to match goal
  
  -- We prove the inequality using a calculation chain starting from the goal's LHS structure.
  -- We first unfold the local definitions implicitly by starting the calc with their values.
  
  calc
    delta2 (cap_a - cap_b * f_at s.lam (hbStep hb_p s.lam s.x s.x_prev s.xstar) s.xstar)
           (cap_a - cap_b * f_at s.lam s.x s.xstar)
           (cap_a - cap_b * f_at s.lam s.x_prev s.xstar)
      = -cap_b * delta2 (f_at s.lam (hbStep hb_p s.lam s.x s.x_prev s.xstar) s.xstar) 
                        (f_at s.lam s.x s.xstar) 
                        (f_at s.lam s.x_prev s.xstar) := by 
          simp [delta2, f_at, sub_eq_add_neg, mul_add, mul_comm, mul_left_comm, add_comm, add_left_comm, add_assoc]
          ring
    _ ≥ -cap_b * (-0.1 * (s.lam / 2) * (p.η * s.lam) * (2 - (p.η * s.lam)) * (s.x - s.xstar) ^ 2) := by
        -- We multiply h_f (≤) by -cap_b (≤ 0) to get (≥)
        apply mul_le_mul_of_nonpos_left h_f
        exact neg_nonpos.mpr (le_of_lt cap_b_pos)
    _ = cap_b * adaptive_gap_coeff p s * (s.x - s.xstar)^2 := by simp [adaptive_gap_coeff]; ring

/-! ## 4. Aggregate Adaptive Expectation -/

def adaptive_d2U_func (p : AdaptiveParams) (s : AdaptiveScenario p) : ℝ :=
  let hb_p : HBParams := ⟨p.η, p.γ, p.hEta, p.hGamma⟩
  let U_next := (cap_a - cap_b * f_at s.lam (hbStep hb_p s.lam s.x s.x_prev s.xstar) s.xstar)
  let U_curr := (cap_a - cap_b * f_at s.lam s.x s.xstar)
  let U_prev := (cap_a - cap_b * f_at s.lam s.x_prev s.xstar)
  delta2 U_next U_curr U_prev

def adaptive_energy_func (p : AdaptiveParams) (s : AdaptiveScenario p) : ℝ :=
  cap_b * (adaptive_gap_coeff p s) * (s.x - s.xstar)^2

/--
  Gold Standard Theorem:
  For any list of scenarios where each scenario respects its OWN stability limit,
  the aggregate system accelerates.
-/
theorem adaptive_average_positive (p : AdaptiveParams) (l : List (AdaptiveScenario p)) (hl : l ≠ []) :
  avg (AdaptiveScenarios p l) (adaptive_d2U_func p) ≥ avg (AdaptiveScenarios p l) (adaptive_energy_func p) := by
  let S := AdaptiveScenarios p l
  apply avg_mono S
  · simp [S, AdaptiveScenarios]
    cases l
    . contradiction
    . simp
  
  intro s _
  exact adaptive_pointwise_acceleration p s

end
end NOC
