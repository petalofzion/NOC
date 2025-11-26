import Mathlib
import NOC.A.Helpers
import NOC.B.Expectation
import NOC.C.CPrime
import NOC.Bridge.SigmaBridge

/-!
Module: NOC.D.Interfaces
Summary: Light-weight glue to *use* the D-bridge. Declare link predicates,
derive pointwise C′ from them, and reuse the D→C′ expectation lemmas.
-/

namespace NOC
noncomputable section
open Classical
open scoped BigOperators

/-! ### Link predicates (everywhere or restricted to a subset) -/

/-- Upper link **on a subset** `G`: `dU ≤ p.cU*A − p.κU*B` for all `ω ∈ G`. -/
def UpperLinkOn {Ω : Type*} (G : Finset Ω)
  (A B dU : Ω → ℝ) (p : SigmaBridgeParams) : Prop :=
  ∀ ω ∈ G, dU ω ≤ p.cU * A ω - p.κU * B ω

/-- SDPI link **on a subset** `G`: `dSigma ≥ p.α*A − p.β*B` for all `ω ∈ G`. -/
def SDPILinkOn {Ω : Type*} (G : Finset Ω)
  (A B dSigma : Ω → ℝ) (p : SigmaBridgeParams) : Prop :=
  ∀ ω ∈ G, dSigma ω ≥ p.α * A ω - p.β * B ω

/-- Upper link **globally**: `dU ≤ p.cU*A − p.κU*B` for all `ω`. -/
def UpperLink {Ω : Type*} (A B dU : Ω → ℝ) (p : SigmaBridgeParams) : Prop :=
  ∀ ω, dU ω ≤ p.cU * A ω - p.κU * B ω

/-- SDPI link **globally**: `dSigma ≥ p.α*A − p.β*B` for all `ω`. -/
def SDPILink {Ω : Type*} (A B dSigma : Ω → ℝ) (p : SigmaBridgeParams) : Prop :=
  ∀ ω, dSigma ω ≥ p.α * A ω - p.β * B ω

/-! ### Small conveniences for the C′ coefficients extracted from D -/
@[simp] lemma toSigmaLawParams_c1 (p : SigmaBridgeParams) :
  p.toSigmaLawParams.c1 = p.α / p.cU := rfl

@[simp] lemma toSigmaLawParams_lambdaXi (p : SigmaBridgeParams) :
  p.toSigmaLawParams.lambdaXi = p.β - p.α * p.κU / p.cU := rfl

/-! ### Pointwise C′ from the two D-premises -/

/-- If the two links hold **globally**, eliminate `A` and get pointwise C′ (with `Ξloss := B`). -/
lemma pointwise_Cprime_from_D {Ω : Type*}
  (A B dU dSigma : Ω → ℝ) (p : SigmaBridgeParams)
  (hU : UpperLink A B dU p)
  (hS : SDPILink A B dSigma p) :
  ∀ ω, dSigma ω
        ≥ p.toSigmaLawParams.c1 * dU ω
          - p.toSigmaLawParams.lambdaXi * B ω := by
  intro ω
  have := SigmaBridgeParams.sigma_from_upper (p := p)
              (A := A ω) (B := B ω) (dU := dU ω) (dSigma := dSigma ω)
              (hLinkU := hU ω) (hSDPI := hS ω)
  simpa [SigmaBridgeParams.toSigmaLawParams] using this

/-- If the two links hold **on a subset** `G`, eliminate `A` and get pointwise C′ on `G`. -/
lemma pointwise_Cprime_on_from_D {Ω : Type*}
  (G : Finset Ω) (A B dU dSigma : Ω → ℝ) (p : SigmaBridgeParams)
  (hU : UpperLinkOn G A B dU p)
  (hS : SDPILinkOn G A B dSigma p) :
  ∀ ω ∈ G, dSigma ω
        ≥ p.toSigmaLawParams.c1 * dU ω
          - p.toSigmaLawParams.lambdaXi * B ω := by
  intro ω hω
  have := SigmaBridgeParams.sigma_from_upper (p := p)
              (A := A ω) (B := B ω) (dU := dU ω) (dSigma := dSigma ω)
              (hLinkU := hU ω hω) (hSDPI := hS ω hω)
  simpa [SigmaBridgeParams.toSigmaLawParams] using this

/-! ### Expectation wrappers (pure reuse of your D → C′ lemmas) -/

/-- Expectation (finitary) via D→C′: reuse `lemmaBridge_expectation_finitary`. -/
theorem expectation_from_links
  {Ω : Type*} (S G : Finset Ω)
  (A B dU dSigma : Ω → ℝ)
  (hGS : G ⊆ S) (hS : 0 < S.card)
  (p : SigmaBridgeParams)
  {MSigma : ℝ}
  (hU : UpperLinkOn G A B dU p)
  (hSdp : SDPILinkOn G A B dSigma p)
  (hBad   : ∀ ω ∈ S \ G, dSigma ω ≥ -MSigma) :
  avg S dSigma ≥
    ((G.card : ℝ) / (S.card : ℝ)) *
      (p.toSigmaLawParams.c1 * avg G dU - p.toSigmaLawParams.lambdaXi * avg G B)
    + (((S.card - G.card : ℕ) : ℝ) / (S.card : ℝ)) * (-MSigma) := by
  classical
  -- Directly reuse the D→C′ finitary lemma
  simpa using
    (SigmaBridgeParams.lemmaBridge_expectation_finitary (S := S) (G := G)
      (A := A) (B := B) (dU := dU) (dSigma := dSigma)
      (hGS := hGS) (hS := hS) (p := p) (MSigma := MSigma)
      (hLinkU := hU) (hSDPI := hSdp) (hBad := hBad))

/-- Expectation with a coverage lower bound `p0`: reuse `lemmaBridge_expectation_with_fraction`. -/
theorem expectation_with_fraction_from_links
  {Ω : Type*} (S G : Finset Ω)
  (A B dU dSigma : Ω → ℝ)
  (hGS : G ⊆ S) (hS : 0 < S.card)
  (p : SigmaBridgeParams)
  {MSigma p0 : ℝ}
  (hU : UpperLinkOn G A B dU p)
  (hSdp : SDPILinkOn G A B dSigma p)
  (hBad   : ∀ ω ∈ S \ G, dSigma ω ≥ -MSigma)
  (hSlope : 0 ≤ (p.toSigmaLawParams.c1 * avg G dU
                - p.toSigmaLawParams.lambdaXi * avg G B) + MSigma)
  (hp0    : p0 ≤ (G.card : ℝ) / (S.card : ℝ)) :
  avg S dSigma ≥
    p0 * (p.toSigmaLawParams.c1 * avg G dU
          - p.toSigmaLawParams.lambdaXi * avg G B)
    - (1 - p0) * MSigma := by
  classical
  simpa using
    (SigmaBridgeParams.lemmaBridge_expectation_with_fraction (S := S) (G := G)
      (A := A) (B := B) (dU := dU) (dSigma := dSigma)
      (hGS := hGS) (hS := hS) (p := p)
      (MSigma := MSigma) (p0 := p0)
      (hLinkU := hU) (hSDPI := hSdp) (hBad := hBad)
      (hSlope := hSlope) (hp0 := hp0))

end
end NOC
