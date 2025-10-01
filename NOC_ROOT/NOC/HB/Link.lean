import Mathlib
import NOC.B.Expectation
import NOC.Bridge.UpperLinkToSigma
import NOC.D.Interfaces  -- optional now; we no longer use the predicate shorthands but keeping it is harmless

/-!
Module: NOC.HB.Link
Summary: Model-side scaffolding for HB (or other dynamics). Bundle the two links and reuse D→C′.
-/

namespace NOC
noncomputable section
open Classical
open scoped BigOperators

universe u

/-! ### Global bundle: links hold for all `ω` -/

/-- Package **global** upper link + SDPI for a model.
The fields `A, B, dU, dSigma : Ω → ℝ` are *your* model quantities.
We store the two D-premises directly as `∀`-form proofs to avoid any inference pitfalls. -/
structure HBLinkBundle (Ω : Type u) where
  A : Ω → ℝ
  B : Ω → ℝ
  dU : Ω → ℝ
  dSigma : Ω → ℝ
  p : DUpperLinkParams
  upper : ∀ ω, dU ω ≤ p.cU * A ω - p.κU * B ω
  sdpi  : ∀ ω, dSigma ω ≥ p.α * A ω - p.β * B ω

namespace HBLinkBundle

/-- From a global bundle, get the **pointwise** C′ inequality (`Ξloss := B`). -/
lemma pointwise_Cprime {Ω : Type u} (H : HBLinkBundle Ω) :
  ∀ (ω : Ω), H.dSigma ω
        ≥ H.p.toSigmaLawParams.c1 * (H.dU ω)
          - H.p.toSigmaLawParams.lambdaXi * (H.B ω) := by
  intro ω
  have := DUpperLinkParams.sigma_from_upper (p := H.p)
              (A := H.A ω) (B := H.B ω) (dU := H.dU ω) (dSigma := H.dSigma ω)
              (hLinkU := H.upper ω) (hSDPI := H.sdpi ω)
  simpa [DUpperLinkParams.toSigmaLawParams] using this

end HBLinkBundle

/-! ### Subset bundle: links hold only on `G ⊆ S` -/

/-- Package **restricted** links on a finite subset `G`. -/
structure HBLinkBundleOn (Ω : Type u) (G : Finset Ω) where
  A : Ω → ℝ
  B : Ω → ℝ
  dU : Ω → ℝ
  dSigma : Ω → ℝ
  p : DUpperLinkParams
  upper : ∀ ω ∈ G, dU ω ≤ p.cU * A ω - p.κU * B ω
  sdpi  : ∀ ω ∈ G, dSigma ω ≥ p.α * A ω - p.β * B ω

namespace HBLinkBundleOn

/-- From a restricted bundle, get the **pointwise** C′ inequality on `G`. -/
lemma pointwise_Cprime_on {Ω : Type u} {G : Finset Ω}
  (H : HBLinkBundleOn Ω G) :
  ∀ (ω : Ω), ω ∈ G →
      H.dSigma ω
        ≥ H.p.toSigmaLawParams.c1 * (H.dU ω)
          - H.p.toSigmaLawParams.lambdaXi * (H.B ω) := by
  intro ω hω
  have := DUpperLinkParams.sigma_from_upper (p := H.p)
              (A := H.A ω) (B := H.B ω) (dU := H.dU ω) (dSigma := H.dSigma ω)
              (hLinkU := H.upper ω hω) (hSDPI := H.sdpi ω hω)
  simpa [DUpperLinkParams.toSigmaLawParams] using this

/-! ### Expectation wrappers (reuse D → C′) -/

/-- Finitary expectation from a restricted bundle plus a floor on the complement. -/
theorem expectation_finitary {Ω : Type u} {G S : Finset Ω}
  (H : HBLinkBundleOn Ω G)
  (hGS : G ⊆ S) (hS : 0 < S.card)
  {MSigma : ℝ}
  (hBad : ∀ ω ∈ S \ G, H.dSigma ω ≥ -MSigma) :
  avg S H.dSigma ≥
    ((G.card : ℝ) / (S.card : ℝ)) *
      (H.p.toSigmaLawParams.c1 * avg G H.dU
        - H.p.toSigmaLawParams.lambdaXi * avg G H.B)
    + (((S.card - G.card : ℕ) : ℝ) / (S.card : ℝ)) * (-MSigma) := by
  classical
  simpa using
    (DUpperLinkParams.lemmaD_expectation_finitary
      (S := S) (G := G)
      (A := H.A) (B := H.B) (dU := H.dU) (dSigma := H.dSigma)
      (hGS := hGS) (hS := hS) (p := H.p) (MSigma := MSigma)
      (hLinkU := H.upper) (hSDPI := H.sdpi) (hBad := hBad))

/-- Expectation with coverage lower bound `p0` from a restricted bundle. -/
theorem expectation_with_fraction {Ω : Type u} {G S : Finset Ω}
  (H : HBLinkBundleOn Ω G)
  (hGS : G ⊆ S) (hS : 0 < S.card)
  {MSigma p0 : ℝ}
  (hBad : ∀ ω ∈ S \ G, H.dSigma ω ≥ -MSigma)
  (hSlope : 0 ≤ (H.p.toSigmaLawParams.c1 * avg G H.dU
                - H.p.toSigmaLawParams.lambdaXi * avg G H.B) + MSigma)
  (hp0 : p0 ≤ (G.card : ℝ) / (S.card : ℝ)) :
  avg S H.dSigma ≥
    p0 * (H.p.toSigmaLawParams.c1 * avg G H.dU
          - H.p.toSigmaLawParams.lambdaXi * avg G H.B)
    - (1 - p0) * MSigma := by
  classical
  simpa using
    (DUpperLinkParams.lemmaD_expectation_with_fraction
      (S := S) (G := G)
      (A := H.A) (B := H.B) (dU := H.dU) (dSigma := H.dSigma)
      (hGS := hGS) (hS := hS) (p := H.p)
      (MSigma := MSigma) (p0 := p0)
      (hLinkU := H.upper) (hSDPI := H.sdpi) (hBad := hBad)
      (hSlope := hSlope) (hp0 := hp0))

end HBLinkBundleOn

end
end NOC
