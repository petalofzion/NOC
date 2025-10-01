import Mathlib
import NOC.B.Expectation
import NOC.Bridge.UpperLinkToSigma
import NOC.D.Interfaces      -- (UpperLink/SDPILink predicates + expectation wrappers)
import NOC.HB.Link           -- (optional) bundle-style API

/-!
# Example: Using the D‑path (upper link + SDPI ⇒ C′ ⇒ expectation)

This file shows **how to call** the D‑path lemmas with your model’s `A, B, dU, dSigma`.
You keep your actual proofs of the two links and the floor outside and pass them here
as hypotheses.
-/

namespace NOC
noncomputable section
open Classical
open scoped BigOperators

universe u
variable {Ω : Type u}

/-! ## A. Pointwise C′ directly from D (global links) -/

/-- If your two D‑links hold for **all** `ω`, you get the C′ pointwise inequality on all `ω`. -/
theorem Dpath_pointwise_Cprime
    (A B dU dSigma : Ω → ℝ) (p : DUpperLinkParams)
    (hU : UpperLink  A B dU    p)      -- ∀ω, dU ≤ p.cU*A − p.κU*B
    (hS : SDPILink  A B dSigma p) :    -- ∀ω, dSigma ≥ p.α*A − p.β*B
  ∀ ω, dSigma ω
        ≥ p.toSigmaLawParams.c1 * dU ω
          - p.toSigmaLawParams.lambdaXi * B ω :=
  pointwise_Cprime_from_D A B dU dSigma p hU hS


/-! ## B. Expectation on a finite support with a “good” subset G (predicate API) -/

/-- **Finitary expectation** via D→C′ (predicate API).
Give:
  * a support `S` and “good” subset `G ⊆ S`,
  * the two D‑links on `G`,
  * a floor `dSigma ≥ −MSigma` on `S \ G`.
Conclusion:
  `avg S dSigma ≥ (|G|/|S|) * (p.c1*avg_G dU − p.lambdaXi*avg_G B) + ((|S|-|G|)/|S|)*(-MSigma)`. -/
theorem Dpath_expectation_finitary
    (S G : Finset Ω)
    (A B dU dSigma : Ω → ℝ)
    (p : DUpperLinkParams)
    (hGS : G ⊆ S) (hS : 0 < S.card)
    {MSigma : ℝ}
    (hU   : UpperLinkOn  G A B dU    p)   -- ∀ω∈G, dU ≤ p.cU*A − p.κU*B
    (hSdp : SDPILinkOn  G A B dSigma p)   -- ∀ω∈G, dSigma ≥ p.α*A − p.β*B
    (hBad : ∀ ω ∈ S \ G, dSigma ω ≥ -MSigma) :
  avg S dSigma ≥
    ((G.card : ℝ) / (S.card : ℝ)) *
      (p.toSigmaLawParams.c1 * avg G dU
        - p.toSigmaLawParams.lambdaXi * avg G B)
    + (((S.card - G.card : ℕ) : ℝ) / (S.card : ℝ)) * (-MSigma) :=
  expectation_from_links S G A B dU dSigma hGS hS p (MSigma := MSigma) hU hSdp hBad

/-- Same as above but with a **coverage lower bound** `p0 ≤ |G|/|S|`
and a **slope** condition `0 ≤ (p.c1*avg_G dU − p.lambdaXi*avg_G B) + MSigma`. -/
theorem Dpath_expectation_with_fraction
    (S G : Finset Ω)
    (A B dU dSigma : Ω → ℝ)
    (p : DUpperLinkParams)
    (hGS : G ⊆ S) (hS : 0 < S.card)
    {MSigma p0 : ℝ}
    (hU   : UpperLinkOn  G A B dU    p)
    (hSdp : SDPILinkOn  G A B dSigma p)
    (hBad : ∀ ω ∈ S \ G, dSigma ω ≥ -MSigma)
    (hSlope : 0 ≤ (p.toSigmaLawParams.c1 * avg G dU
                  - p.toSigmaLawParams.lambdaXi * avg G B) + MSigma)
    (hp0    : p0 ≤ (G.card : ℝ) / (S.card : ℝ)) :
  avg S dSigma ≥
    p0 * (p.toSigmaLawParams.c1 * avg G dU
          - p.toSigmaLawParams.lambdaXi * avg G B)
    - (1 - p0) * MSigma :=
  expectation_with_fraction_from_links
    S G A B dU dSigma hGS hS p (MSigma := MSigma) (p0 := p0)
    hU hSdp hBad hSlope hp0


/-! ## C. (Optional) The same, using the HB *bundle* API

If you like to bundle your links as data, build:
def H : HBLinkBundleOn Ω G :=
{ A := A, B := B, dU := dU, dSigma := dSigma, p := p,
upper := hU, sdpi := hSdp }
and then call `H.expectation_finitary …` / `H.expectation_with_fraction …`.
-/

end
end NOC
