import Mathlib
import NOC.C.CPrime

/-!
Module: NOC.E.ConversionVsAblation
Status: scaffolding (with proof plan and tactic outline).

ROI inequality for “Conversion > Ablation”. We record the parameters that connect
utility scales (γ per‑nat weight on Σ, ζ for cost) and express the boxed inequality
used in the v5 blueprint. The algebraic proof will be filled once empirical premises
are stabilized; for now, we expose a clean lemma name and assumptions.

High‑level proof plan:
1) Start from a Σ‑law (C′ or C): dSigma ≥ c₁·X − λΞ·xiLoss (X is ΔU or Δ²U depending on regime).
2) Convert to utility scale using weights: Utility gain from Σ is γ·dSigma; cost increase is ζ·dJ.
3) Sufficient condition for “conversion dominates ablation”: γ·dSigma ≥ ζ·dJ (optionally
   plus λΞ terms if they’re kept explicit). Using the Σ‑law, it suffices that
   γ·(c₁·X − λΞ·xiLoss) ≥ ζ·dJ.
4) In practice X will be bounded below by a model‑specific term (e.g., from Lemma B),
   and xiLoss is either measured or upper‑bounded. Plugging those provides verifiable
   sufficient conditions on γ/ζ (and λΞ if present).

Tactic outline:
- Keep this file parameterized and algebraic; the actual bounds enter via hypotheses in
  callers. Provide the inequality in a one‑shot lemma that callers can instantiate after
  deriving c₁, λΞ, and the needed lower bounds on X.
-/

namespace NOC
noncomputable section
open Classical

/-- Parameters that place ΔΣ and ΔJ on the same utility scale. -/
structure ROIParams where
  γ : ℝ      -- per-nat weight on Σ
  ζ : ℝ      -- per-unit weight on actuation/complexity cost J
  γ_nonneg : 0 ≤ γ
  ζ_nonneg : 0 ≤ ζ

/-- Context for a conversion-vs-ablation decision at a fixed step. -/
structure ROIContext where
  P : ROIParams
  dSigma : ℝ    -- ΔΣ
  dJ : ℝ        -- ΔJ
  xiLoss : ℝ    -- Ξ_loss (optional)
  premises : Prop   -- placeholder for regularity/calibration premises

/-- Sufficient condition: from a Σ‑law and a γ,ζ‑weighted inequality on the Σ‑law RHS. -/
theorem roi_from_sigma_law
  (P : ROIParams) {dSigma dJ X xiLoss c1 lambdaXi : ℝ}
  (hSigma : dSigma ≥ c1 * X - lambdaXi * xiLoss)
  (hSufficient : P.γ * (c1 * X - lambdaXi * xiLoss) ≥ P.ζ * dJ) :
  P.γ * dSigma ≥ P.ζ * dJ := by
  calc
    P.γ * dSigma ≥ P.γ * (c1 * X - lambdaXi * xiLoss) :=
      mul_le_mul_of_nonneg_left hSigma P.γ_nonneg
    _             ≥ P.ζ * dJ :=
      hSufficient

/-- Skeleton: packaging a practical ROI condition using a measured/estimated X lower bound. -/
theorem roi_sufficient_conditions (ctx : ROIContext)
  (Ps : SigmaLawParams) {X Xlb : ℝ}
  (hSigmaLaw : ctx.dSigma ≥ Ps.c1 * X - Ps.lambdaXi * ctx.xiLoss)
  (hXlb : X ≥ Xlb)
  (hROI : ctx.P.γ * (Ps.c1 * Xlb - Ps.lambdaXi * ctx.xiLoss) ≥ ctx.P.ζ * ctx.dJ) :
  ctx.P.γ * ctx.dSigma ≥ ctx.P.ζ * ctx.dJ := by
  -- Monotonicity of the c1·X term using c1 ≥ 0 from SigmaLawParams
  have hmono : Ps.c1 * Xlb ≤ Ps.c1 * X :=
    mul_le_mul_of_nonneg_left hXlb Ps.c1_nonneg
  -- Shift by the same subtraction (λΞ·Ξ_loss) on both sides
  have hshift : Ps.c1 * Xlb - Ps.lambdaXi * ctx.xiLoss ≤ Ps.c1 * X - Ps.lambdaXi * ctx.xiLoss := by
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
      (sub_le_sub_right hmono (Ps.lambdaXi * ctx.xiLoss))
  -- Reorient the Σ‑law bound to `≤` form for chaining
  have hSigma_le : (Ps.c1 * X - Ps.lambdaXi * ctx.xiLoss) ≤ ctx.dSigma := by
    simpa [ge_iff_le] using hSigmaLaw
  -- Combine: (c1*Xlb − λΞ*Ξ) ≤ (c1*X − λΞ*Ξ) ≤ dSigma
  have hchain : Ps.c1 * Xlb - Ps.lambdaXi * ctx.xiLoss ≤ ctx.dSigma :=
    le_trans hshift hSigma_le
  -- Multiply by γ ≥ 0 and finish with the ROI threshold
  have hγ : 0 ≤ ctx.P.γ := ctx.P.γ_nonneg
  have hleft : ctx.P.γ * (Ps.c1 * Xlb - Ps.lambdaXi * ctx.xiLoss) ≤ ctx.P.γ * ctx.dSigma := by
    exact mul_le_mul_of_nonneg_left hchain hγ
  -- Chain the ROI threshold with the Σ-law bound widened via γ ≥ 0
  have hROI_le : ctx.P.ζ * ctx.dJ ≤
      ctx.P.γ * (Ps.c1 * Xlb - Ps.lambdaXi * ctx.xiLoss) := by
    simpa [ge_iff_le] using hROI
  have hgoal_le : ctx.P.ζ * ctx.dJ ≤ ctx.P.γ * ctx.dSigma :=
    le_trans hROI_le hleft
  exact (by simpa [ge_iff_le] using hgoal_le)

/-- Wrapper: once the Σ-law premises, the X lower bound, and the ROI threshold hold,
the conversion move beats ablation on utility grounds (`γ·ΔΣ ≥ ζ·ΔJ`). -/
theorem conversion_beats_ablation (ctx : ROIContext)
  (Ps : SigmaLawParams) {X Xlb : ℝ}
  (hSigmaLaw : ctx.dSigma ≥ Ps.c1 * X - Ps.lambdaXi * ctx.xiLoss)
  (hXlb : X ≥ Xlb)
  (hROI : ctx.P.γ * (Ps.c1 * Xlb - Ps.lambdaXi * ctx.xiLoss) ≥ ctx.P.ζ * ctx.dJ) :
  ctx.P.γ * ctx.dSigma ≥ ctx.P.ζ * ctx.dJ :=
  roi_sufficient_conditions (ctx := ctx) (Ps := Ps) (X := X) (Xlb := Xlb)
    hSigmaLaw hXlb hROI

end
end NOC
