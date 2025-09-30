import Mathlib
import NOC.AHelpers
import NOC.B.Expectation
import NOC.C.CPrime
import NOC.D.Core

/-!
Module: NOC.C
Summary: Σ-law (acceleration). Expectation layer via C′ and a clean pointwise interface.

This file provides a *pointwise interface* for the acceleration form (ΔΣ ≥ c₁·Δ²U − λΞ·Ξ_loss)
plus a finitary expectation wrapper built by *reusing* the C′ average lemma. The actual
pointwise proof (HB/PL geometry → SDPI link → acceleration) will be filled in later.
-/

namespace NOC
noncomputable section
open Classical
open scoped BigOperators

/-- Parameters for the acceleration Σ-law. Extends the C′ parameters with a
Lipschitz/smoothness constant that converts velocity differences into channel separation. -/
structure SigmaAccelParams extends SigmaLawParams where
  L_vel   : ℝ
  L_vel_nonneg : 0 ≤ L_vel

/-- **Pointwise Σ-law (acceleration form, interface).**
`ΔΣ ≥ P.c1 * Δ²U − P.lambdaXi * Ξloss`.  This is an interface lemma: to *use* it now,
pass the pointwise inequality you derive from your HB/PL premises; later we will
prove such an inequality from the dynamics. -/
@[simp]
theorem lemmaC_pointwise
    {dSigma d2U xiLoss : ℝ} (P : SigmaAccelParams)
    (h : dSigma ≥ P.c1 * d2U - P.lambdaXi * xiLoss) :
    dSigma ≥ P.c1 * d2U - P.lambdaXi * xiLoss := h

/-- **Acceleration Σ-law (finitary expectation).**
If on `G ⊆ S` we have the *acceleration* pointwise inequality
`dSigma ≥ P.c1 * d2U − P.lambdaXi * xiLoss` and on the complement we only know
`dSigma ≥ −MSigma`, then the uniform average obeys avg S dSigma ≥ (|G|/|S|) * (P.c1 * avg_G d2U − P.lambdaXi * avg_G xiLoss)
+ ((|S|−|G|)/|S|) * (−MSigma). This is a straight reuse of `lemmaCprime_expectation_finitary` with `dU := d2U`.
-/
 theorem lemmaC_expectation_finitary
  {Ω : Type*} (S G : Finset Ω)
  (dSigma d2U xiLoss : Ω → ℝ)
  (hGS : G ⊆ S) (hS : 0 < S.card)
  (P : SigmaAccelParams)
  {MSigma : ℝ}
  (hGood : ∀ ω ∈ G, dSigma ω ≥ P.c1 * d2U ω - P.lambdaXi * xiLoss ω)
  (hBad  : ∀ ω ∈ S \ G, dSigma ω ≥ -MSigma) :
  avg S dSigma ≥
    ((G.card : ℝ) / (S.card : ℝ)) * (P.c1 * avg G d2U - P.lambdaXi * avg G xiLoss) +
    (((S.card - G.card : ℕ) : ℝ) / (S.card : ℝ)) * (-MSigma) := by
  -- Reuse the C′ expectation lemma (with `dU := d2U`).
  have :=
    lemmaCprime_expectation_finitary
      (S := S) (G := G)
      (dSigma := dSigma) (dU := d2U) (xiLoss := xiLoss)
      (hGS := hGS) (hS := hS) (P := P.toSigmaLawParams)
      (MSigma := MSigma) (hGood := hGood) (hBad := hBad)
  simpa using this

/-- **Acceleration Σ-law (expectation) with a mass lower bound `p0`.**
Reuse the C′ fraction form with `dU := d2U`.
-/
theorem lemmaC_expectation_with_fraction
  {Ω : Type*} (S G : Finset Ω)
  (dSigma d2U xiLoss : Ω → ℝ)
  (hGS : G ⊆ S) (hS : 0 < S.card)
  (P : SigmaAccelParams)
  {MSigma p0 : ℝ}
  (hGood : ∀ ω ∈ G, dSigma ω ≥ P.c1 * d2U ω - P.lambdaXi * xiLoss ω)
  (hBad  : ∀ ω ∈ S \ G, dSigma ω ≥ -MSigma)
  (hSlope : 0 ≤ (P.c1 * avg G d2U - P.lambdaXi * avg G xiLoss) + MSigma)
  (hp0  : p0 ≤ (G.card : ℝ) / (S.card : ℝ)) :
  avg S dSigma ≥
    p0 * (P.c1 * avg G d2U - P.lambdaXi * avg G xiLoss) - (1 - p0) * MSigma := by
  -- immediate reuse of C′
  simpa using
    lemmaCprime_expectation_with_fraction
      (S := S) (G := G)
      (dSigma := dSigma) (dU := d2U) (xiLoss := xiLoss)
      (hGS := hGS) (hS := hS) (P := P.toSigmaLawParams)
      (MSigma := MSigma) (p0 := p0)
      (hGood := hGood) (hBad := hBad)
      (hSlope := hSlope) (hp0 := hp0)

-- ──────────────────────────────────────────────────────────────────────────────
-- Convenience: derive C (acceleration) **pointwise** and **expectation** directly from D
-- by just renaming dU := d2U and reusing the D→C′ bridge.
-- ──────────────────────────────────────────────────────────────────────────────

noncomputable section
open Classical
open scoped BigOperators

/-- **Pointwise C (from D).**
If for some auxiliary `A,B` and parameters `p : DUpperLinkParams` we have
`d2U ≤ p.cU*A − p.κU*B` and `dSigma ≥ p.α*A − p.β*B`, then
`dSigma ≥ (p.α/p.cU) * d2U − (p.β − p.α*p.κU/p.cU) * B`. -/
theorem lemmaC_pointwise_from_D
    {A B d2U dSigma : ℝ} (p : DUpperLinkParams)
    (hLinkU : d2U ≤ p.cU * A - p.κU * B)
    (hSDPI  : dSigma ≥ p.α * A - p.β * B) :
    dSigma ≥ p.toSigmaLawParams.c1 * d2U
             - p.toSigmaLawParams.lambdaXi * B := by
  -- This is exactly sigma_from_upper with dU := d2U.
  simpa [DUpperLinkParams.toSigmaLawParams] using
    (DUpperLinkParams.sigma_from_upper (p := p)
      (A := A) (B := B) (dU := d2U) (dSigma := dSigma)
      (hLinkU := hLinkU) (hSDPI := hSDPI))

/-- **C (expectation, finitary) from D.**
Assume the two D‑premises on `G ⊆ S` and a floor on `S\G`. Then the average (C) inequality holds. -/
theorem lemmaC_expectation_from_D
  {Ω : Type*} (S G : Finset Ω)
  (A B d2U dSigma : Ω → ℝ)
  (hGS : G ⊆ S) (hS : 0 < S.card)
  (p : DUpperLinkParams)
  {MSigma : ℝ}
  (hLinkU : ∀ ω ∈ G, d2U ω ≤ p.cU * A ω - p.κU * B ω)
  (hSDPI  : ∀ ω ∈ G, dSigma ω ≥ p.α * A ω - p.β * B ω)
  (hBad   : ∀ ω ∈ S \ G, dSigma ω ≥ -MSigma) :
  avg S dSigma ≥
    ((G.card : ℝ) / (S.card : ℝ)) *
      (p.toSigmaLawParams.c1 * avg G d2U - p.toSigmaLawParams.lambdaXi * avg G B)
    + (((S.card - G.card : ℕ) : ℝ) / (S.card : ℝ)) * (-MSigma) := by
  -- D→C′ finitary lemma with dU := d2U
  simpa using
    (DUpperLinkParams.lemmaD_expectation_finitary
      (S := S) (G := G)
      (A := A) (B := B) (dU := d2U) (dSigma := dSigma)
      (hGS := hGS) (hS := hS) (p := p) (MSigma := MSigma)
      (hLinkU := hLinkU) (hSDPI := hSDPI) (hBad := hBad))

/-- **C (expectation with fraction) from D.**
Same set‑up, plus a slope condition and a coverage lower bound `p0 ≤ |G|/|S|`. -/
theorem lemmaC_expectation_with_fraction_from_D
  {Ω : Type*} (S G : Finset Ω)
  (A B d2U dSigma : Ω → ℝ)
  (hGS : G ⊆ S) (hS : 0 < S.card)
  (p : DUpperLinkParams)
  {MSigma p0 : ℝ}
  (hLinkU : ∀ ω ∈ G, d2U ω ≤ p.cU * A ω - p.κU * B ω)
  (hSDPI  : ∀ ω ∈ G, dSigma ω ≥ p.α * A ω - p.β * B ω)
  (hBad   : ∀ ω ∈ S \ G, dSigma ω ≥ -MSigma)
  (hSlope : 0 ≤ (p.toSigmaLawParams.c1 * avg G d2U
                - p.toSigmaLawParams.lambdaXi * avg G B) + MSigma)
  (hp0    : p0 ≤ (G.card : ℝ) / (S.card : ℝ)) :
  avg S dSigma ≥
    p0 * (p.toSigmaLawParams.c1 * avg G d2U
          - p.toSigmaLawParams.lambdaXi * avg G B)
    - (1 - p0) * MSigma := by
  simpa using
    (DUpperLinkParams.lemmaD_expectation_with_fraction
      (S := S) (G := G)
      (A := A) (B := B) (dU := d2U) (dSigma := dSigma)
      (hGS := hGS) (hS := hS) (p := p)
      (MSigma := MSigma) (p0 := p0)
      (hLinkU := hLinkU) (hSDPI := hSDPI) (hBad := hBad)
      (hSlope := hSlope) (hp0 := hp0))

/-- **C (acceleration) on all of `S`.**
If the pointwise C inequality holds on `S`, then
`avg S dSigma ≥ P.c1 * avg S d2U - P.lambdaXi * avg S xiLoss`. -/
theorem lemmaC_expectation_allGood
  {Ω : Type*} (S : Finset Ω)
  (dSigma d2U xiLoss : Ω → ℝ)
  (hS : 0 < S.card)
  (P : SigmaAccelParams)
  (hGood : ∀ ω ∈ S, dSigma ω ≥ P.c1 * d2U ω - P.lambdaXi * xiLoss ω) :
  avg S dSigma ≥ P.c1 * avg S d2U - P.lambdaXi * avg S xiLoss := by
  -- immediate reuse of the C′ all-good corollary with dU := d2U
  simpa using
    (lemmaCprime_expectation_allGood
      (S := S) (dSigma := dSigma) (dU := d2U) (xiLoss := xiLoss)
      (hS := hS) (P := P.toSigmaLawParams) (hGood := hGood))

end
end
end NOC
