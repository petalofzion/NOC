import Mathlib
import NOC.AHelpers
import NOC.B.Core
import NOC.B.Expectation
import NOC.C.CPrime

/-!
Module: NOC.Bridge.SigmaBridge
Summary: Sigma-bridge — eliminate intermediates to get the Sigma-law (C′) pointwise and lift to expectations.

**Idea.** Suppose per sample we have:
  • an **upper link** on `Δ²U`:        `Δ2U ≤ cU*A − κU*B`, with `cU>0`, `κU≥0`,
  • an **SDPI/Dobrushin** inequality:  `dSigma ≥ α*A − β*B`, with `α≥0`, `β≥0`.

Eliminate `A` using the upper link to obtain a direct **Sigma‑law**:
`dSigma ≥ (α/cU) * Δ2U − (β − α*κU/cU) * B`,
provided the tradeoff `β ≥ α*κU/cU` (so `λΞ := β − α*κU/cU ≥ 0`).

Setting `Ξloss := B`, we get a pointwise C′ form `dSigma ≥ c1*dU − λΞ * Ξloss`,
with `c1 = α/cU`, `λΞ = β − α*κU/cU`. Expectation wrappers follow from C′ lemmas.
-/

namespace NOC
noncomputable section
open Classical
open scoped BigOperators

/-- Parameters for the D‑bridge (upper link + SDPI). -/
structure SigmaBridgeParams where
  cU : ℝ
  κU : ℝ
  α  : ℝ
  β  : ℝ
  cU_pos     : 0 < cU
  α_nonneg   : 0 ≤ α
  κU_nonneg  : 0 ≤ κU
  trade      : β ≥ α * κU / cU   -- ensures λΞ ≥ 0

namespace SigmaBridgeParams

/-- Package the resulting C′ coefficients. -/
def toSigmaLawParams (p : SigmaBridgeParams) : SigmaLawParams :=
{ c1 := p.α / p.cU
, lambdaXi := p.β - p.α * p.κU / p.cU
, c1_nonneg := by
    have : 0 ≤ p.α / p.cU := div_nonneg p.α_nonneg (le_of_lt p.cU_pos)
    simpa using this
, lambdaXi_nonneg := by
    -- from β ≥ α κU / cU we get 0 ≤ β - α κU / cU
    have h : p.α * p.κU / p.cU ≤ p.β := by
      simpa [ge_iff_le] using p.trade
    exact sub_nonneg.mpr h
}

/-- **Pointwise elimination (upper‑link case).**
From `Δ2U ≤ cU*A − κU*B` and `dSigma ≥ α*A − β*B`, conclude
`dSigma ≥ (α/cU) * Δ2U − (β − α*κU/cU) * B`. -/
lemma sigma_from_upper
  (p : SigmaBridgeParams)
  {A B dU dSigma : ℝ}
  (hLinkU : dU ≤ p.cU * A - p.κU * B)
  (hSDPI  : dSigma ≥ p.α * A - p.β * B) :
  dSigma ≥ (p.α / p.cU) * dU - (p.β - p.α * p.κU / p.cU) * B := by
  -- From the upper link, get a *lower bound* on A.
  have h' : dU + p.κU * B ≤ p.cU * A := by
    -- add κU*B to both sides of `dU ≤ cU*A - κU*B`
    have : dU ≤ p.cU * A + (-(p.κU * B)) := by simpa [sub_eq_add_neg] using hLinkU
    have := add_le_add_right this (p.κU * B)
    simpa [add_comm, add_left_comm, add_assoc] using this
  have hA_lb : (dU + p.κU * B) / p.cU ≤ A :=
    div_le_of_le_mul_pos p.cU_pos h'

  -- Push through α≥0 and subtract βB.
  have hαA_lb :
      p.α * ((dU + p.κU * B) / p.cU) - p.β * B ≤ p.α * A - p.β * B := by
    have := mul_le_mul_of_nonneg_left hA_lb p.α_nonneg
    exact sub_le_sub_right this (p.β * B)

  -- `dSigma ≥ α*A - β*B` ⇒ `α*A - β*B ≤ dSigma`
  have horder : p.α * A - p.β * B ≤ dSigma := by
    simpa [ge_iff_le] using hSDPI

  -- Chain the inequalities.
  have hchain :
      p.α * ((dU + p.κU * B) / p.cU) - p.β * B ≤ dSigma :=
    le_trans hαA_lb horder

  -- Reassociate the LHS into the target shape.
  have hL :
    p.α * ((dU + p.κU * B) / p.cU) - p.β * B
      = (p.α / p.cU) * dU - (p.β - p.α * p.κU / p.cU) * B := by
    -- First, factor (α/cU) and distribute;
    -- then re-associate the B-term into (α*κU/cU) * B.
    have h1 :
      p.α * ((dU + p.κU * B) / p.cU)
        = (p.α / p.cU) * dU + (p.α * p.κU / p.cU) * B := by
      calc
        p.α * ((dU + p.κU * B) / p.cU)
            = (p.α / p.cU) * (dU + p.κU * B) := by
                simp [div_eq_mul_inv, mul_comm, mul_left_comm]
        _   = (p.α / p.cU) * dU + (p.α / p.cU) * (p.κU * B) := by
                ring
        _   = (p.α / p.cU) * dU + ((p.α / p.cU) * p.κU) * B := by
                ring
        _   = (p.α / p.cU) * dU + (p.α * p.κU / p.cU) * B := by
                simp [div_eq_mul_inv, mul_comm, mul_assoc]
    calc
      p.α * ((dU + p.κU * B) / p.cU) - p.β * B
          = ((p.α / p.cU) * dU + (p.α * p.κU / p.cU) * B) - p.β * B := by
                simp [h1]
      _ = (p.α / p.cU) * dU - (p.β - p.α * p.κU / p.cU) * B := by
                ring

  -- Done: rewrite the inequality using `hL` and flip back to `≥`.
  have : (p.α / p.cU) * dU - (p.β - p.α * p.κU / p.cU) * B ≤ dSigma := by
    simpa [hL] using hchain
  simpa [ge_iff_le] using this
/-! ### Expectation wrappers via C′ -/

/-- **D → C′ (finitary expectation).**
On the good set `G ⊆ S`, assume:
  * an upper link `dU ≤ p.cU*A − p.κU*B`,
  * an SDPI/Dobrushin inequality `dSigma ≥ p.α*A − p.β*B`.
On the complement, assume the floor `dSigma ≥ −MSigma`.
Then `avg_S dSigma ≥ (|G|/|S|)*(P.c1*avg_G dU − P.lambdaXi*avg_G B) + ((|S|-|G|)/|S|)*(−MSigma)`,
where `P = p.toSigmaLawParams` and `Ξloss := B`. -/
theorem lemmaBridge_expectation_finitary
  {Ω : Type*} (S G : Finset Ω)
  (A B dU dSigma : Ω → ℝ)
  (hGS : G ⊆ S) (hS : 0 < S.card)
  (p : SigmaBridgeParams)
  {MSigma : ℝ}
  (hLinkU : ∀ ω ∈ G, dU ω ≤ p.cU * A ω - p.κU * B ω)
  (hSDPI  : ∀ ω ∈ G, dSigma ω ≥ p.α * A ω - p.β * B ω)
  (hBad   : ∀ ω ∈ S \ G, dSigma ω ≥ -MSigma) :
  avg S dSigma ≥
    ((G.card : ℝ) / (S.card : ℝ)) *
      (p.toSigmaLawParams.c1 * avg G dU - p.toSigmaLawParams.lambdaXi * avg G B)
    + (((S.card - G.card : ℕ) : ℝ) / (S.card : ℝ)) * (-MSigma) := by
  classical
  -- Build the C′-shape pointwise inequality on G by eliminating A.
  have hGoodC : ∀ ω ∈ G,
    dSigma ω ≥ p.toSigmaLawParams.c1 * dU ω - p.toSigmaLawParams.lambdaXi * B ω := by
    intro ω hω
    have h := SigmaBridgeParams.sigma_from_upper
      (p := p) (A := A ω) (B := B ω) (dU := dU ω) (dSigma := dSigma ω)
      (hLinkU := hLinkU ω hω) (hSDPI := hSDPI ω hω)
    simpa [SigmaBridgeParams.toSigmaLawParams] using h
  -- Reuse the C′ expectation lemma with xiLoss := B.
  simpa using
    (lemmaCprime_expectation_finitary
      (S := S) (G := G)
      (dSigma := dSigma) (dU := dU) (xiLoss := B)
      (hGS := hGS) (hS := hS) (P := p.toSigmaLawParams)
      (MSigma := MSigma)
      (hGood := hGoodC) (hBad := hBad))

/-- **D → C′ (finitary expectation with a mass lower bound `p0`).**
Same set‑up as `lemmaBridge_expectation_finitary`; additionally assume the slope condition
`0 ≤ (P.c1 * avg_G dU − P.lambdaXi * avg_G B) + MSigma` and a coverage lower bound
`p0 ≤ |G|/|S|`. Then
`avg_S dSigma ≥ p0*(P.c1*avg_G dU) − p0*(P.lambdaXi*avg_G B) − (1−p0)*MSigma`. -/
theorem lemmaBridge_expectation_with_fraction
  {Ω : Type*} (S G : Finset Ω)
  (A B dU dSigma : Ω → ℝ)
  (hGS : G ⊆ S) (hS : 0 < S.card)
  (p : SigmaBridgeParams)
  {MSigma p0 : ℝ}
  (hLinkU : ∀ ω ∈ G, dU ω ≤ p.cU * A ω - p.κU * B ω)
  (hSDPI  : ∀ ω ∈ G, dSigma ω ≥ p.α * A ω - p.β * B ω)
  (hBad   : ∀ ω ∈ S \ G, dSigma ω ≥ -MSigma)
  (hSlope : 0 ≤ (p.toSigmaLawParams.c1 * avg G dU
                - p.toSigmaLawParams.lambdaXi * avg G B) + MSigma)
  (hp0    : p0 ≤ (G.card : ℝ) / (S.card : ℝ)) :
  avg S dSigma ≥
    p0 * (p.toSigmaLawParams.c1 * avg G dU
          - p.toSigmaLawParams.lambdaXi * avg G B)
    - (1 - p0) * MSigma := by
  classical
  -- Pointwise C′ shape on G
  have hGoodC : ∀ ω ∈ G,
    dSigma ω ≥ p.toSigmaLawParams.c1 * dU ω - p.toSigmaLawParams.lambdaXi * B ω := by
    intro ω hω
    have h := SigmaBridgeParams.sigma_from_upper
      (p := p) (A := A ω) (B := B ω) (dU := dU ω) (dSigma := dSigma ω)
      (hLinkU := hLinkU ω hω) (hSDPI := hSDPI ω hω)
    simpa [SigmaBridgeParams.toSigmaLawParams] using h
  -- Expectation via the C′ fraction form
  simpa using
    (lemmaCprime_expectation_with_fraction
      (S := S) (G := G)
      (dSigma := dSigma) (dU := dU) (xiLoss := B)
      (hGS := hGS) (hS := hS) (P := p.toSigmaLawParams)
      (MSigma := MSigma) (p0 := p0)
      (hGood := hGoodC) (hBad := hBad)
      (hSlope := hSlope) (hp0 := hp0))

@[simp] lemma c1_from_bridge (p : SigmaBridgeParams) :
  p.toSigmaLawParams.c1 = p.α / p.cU := rfl

@[simp] lemma lambdaXi_from_bridge (p : SigmaBridgeParams) :
  p.toSigmaLawParams.lambdaXi = p.β - p.α * p.κU / p.cU := rfl

end SigmaBridgeParams
end
end NOC
