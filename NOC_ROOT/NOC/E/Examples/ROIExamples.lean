import Mathlib
import NOC.E.ConversionVsAblation
import NOC.C.CPrime

/-!
Module: NOC.E.Examples.ROIExamples
Status: small examples (no sorrys).

Purpose: demonstrate the ROI inequality lemmas (`roi_from_sigma_law`,
`roi_sufficient_conditions`, `conversion_beats_ablation`) on concrete numbers.
-/

namespace NOC
noncomputable section
open Classical

/-- Simple ROI example via C′: choose `c1=1`, `λΞ=0`, `Xlb=1`, no loss `Ξ=0`.
If the Σ‑law holds with these parameters and the ROI threshold is met, then
`γ·ΔΣ ≥ ζ·ΔJ`. -/
theorem roi_example_simple :
  let Ps : SigmaLawParams := { c1 := 1, lambdaXi := 0,
                                c1_nonneg := by norm_num,
                                lambdaXi_nonneg := by norm_num }
  let P  : ROIParams := { γ := 2, ζ := 1,
                           γ_nonneg := by norm_num,
                           ζ_nonneg := by norm_num }
  let ctx : ROIContext := { P := P, dSigma := 2, dJ := 1, xiLoss := 0, premises := True }
  let X := 1
  have hSigmaLaw : ctx.dSigma ≥ Ps.c1 * X - Ps.lambdaXi * ctx.xiLoss := by
    -- 2 ≥ 1 * 1 - 0 * 0
    simp [ctx, Ps]
  have hXlb : X ≥ (1 : ℝ) := by norm_num
  have hROI : ctx.P.γ * (Ps.c1 * (1 : ℝ) - Ps.lambdaXi * ctx.xiLoss) ≥ ctx.P.ζ * ctx.dJ := by
    -- 2 * (1 * 1 - 0 * 0) ≥ 1 * 1
    simp [ctx, Ps]
  ctx.P.γ * ctx.dSigma ≥ ctx.P.ζ * ctx.dJ := by
    -- Apply the sufficient-condition wrapper
    simpa [ctx, Ps]
      using conversion_beats_ablation (ctx := ctx) (Ps := Ps) (X := X) (Xlb := 1)
        hSigmaLaw hXlb hROI

end
end NOC

