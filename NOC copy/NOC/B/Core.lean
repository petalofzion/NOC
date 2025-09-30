import Mathlib

/-!
Module: NOC.B.Core
Summary: Lemma B core — quadratic supports ⇒ link; bridge to Δ²U ≥ 0; local and δ-form wrappers.
Public entry points: `lemmaB_link_from_quadratic_supports`, `lemmaB_bridge_nonneg`, `lemmaB_local_nonneg`, `lemmaB_local_nonneg_abs`.
-/

namespace NOC
noncomputable section
open Classical

/-
  Lemma B (core): link from quadratic supports, algebraic bridge,
  deterministic local form, and δ‑form convenience.
-/

/-- **Lemma B₀ (affine link warmup).** If `U = a - b·f`, `b>0`, and `Δ²f<0` then `Δ²U>0`. -/
theorem lemmaB_affine_link
    {a b fPrev f fNext : ℝ}
    (hbpos : 0 < b)
    (hacc  : fNext - 2 * f + fPrev < 0) :
    (a - b * fNext) - 2 * (a - b * f) + (a - b * fPrev) > 0 := by
  have hrepr :
      (a - b * fNext) - 2 * (a - b * f) + (a - b * fPrev)
        = (-b) * (fNext - 2 * f + fPrev) := by
    ring
  have hprod : 0 < (-b) * (fNext - 2 * f + fPrev) :=
    mul_pos_of_neg_of_neg (by linarith) hacc
  simpa [hrepr] using hprod

/--
**Lemma B_bridge (algebraic transfer).**
From a link `c*(-Δ2f) - κ*(dPrev^2+dNext^2) ≤ Δ2U`, with `Δ2f ≤ -α`, `dPrev^2+dNext^2 ≤ ε`,
`0≤c, 0≤κ`, and `κ ε ≤ c α`, conclude `Δ2U ≥ 0`.
-/
theorem lemmaB_bridge_nonneg
    {Δ2U Δ2f dPrev dNext c κ α ε : ℝ}
    (hlink   : c * (-Δ2f) - κ * (dPrev^2 + dNext^2) ≤ Δ2U)
    (hΔ2f    : Δ2f ≤ -α)
    (hsq     : dPrev^2 + dNext^2 ≤ ε)
    (hc      : 0 ≤ c)
    (hκ      : 0 ≤ κ)
    (htrade  : κ * ε ≤ c * α) :
    Δ2U ≥ 0 := by
  have hneg : α ≤ -Δ2f := by simpa using (neg_le_neg hΔ2f)
  have h1   : c * α ≤ c * (-Δ2f) := mul_le_mul_of_nonneg_left hneg hc
  have h2   : κ * (dPrev^2 + dNext^2) ≤ κ * ε := mul_le_mul_of_nonneg_left hsq hκ
  have h2'  : -(κ * ε) ≤ -(κ * (dPrev^2 + dNext^2)) := by simpa using (neg_le_neg h2)
  have hsum : c * α - κ * ε ≤ c * (-Δ2f) - κ * (dPrev^2 + dNext^2) := by
    simpa [sub_eq_add_neg] using add_le_add h1 h2'
  have hlow : c * α - κ * ε ≤ Δ2U := le_trans hsum hlink
  have hz   : 0 ≤ c * α - κ * ε := sub_nonneg.mpr htrade
  have : 0 ≤ Δ2U := le_trans hz hlow
  simpa [ge_iff_le] using this

/-- From two local quadratic **supports** for `U` around `f`, derive the standard link. -/
theorem lemmaB_link_from_quadratic_supports
    {Uprev U Unext fprev f fnext c κ : ℝ}
    (hNext : Unext ≥ U + c * (f - fnext) - κ * (fnext - f) ^ 2)
    (hPrev : Uprev ≥ U + c * (f - fprev) - κ * (fprev - f) ^ 2) :
    c * (-(fnext - 2 * f + fprev)) - κ * ((f - fprev) ^ 2 + (fnext - f) ^ 2)
      ≤ Unext - 2 * U + Uprev := by
  have hN' : c * (f - fnext) - κ * (fnext - f) ^ 2 ≤ Unext - U := by linarith
  have hP' : c * (f - fprev) - κ * (fprev - f) ^ 2 ≤ Uprev - U := by linarith
  have hsum0 :
      (c * (f - fnext) - κ * (fnext - f) ^ 2) +
      (c * (f - fprev) - κ * (fprev - f) ^ 2)
      ≤ (Unext - U) + (Uprev - U) := add_le_add hN' hP'
  have hleft :
      (c * (f - fnext) - κ * (fnext - f) ^ 2) +
      (c * (f - fprev) - κ * (fprev - f) ^ 2)
      = c * ((f - fnext) + (f - fprev))
        - κ * ((fnext - f) ^ 2 + (fprev - f) ^ 2) := by
    ring
  have hR : (Unext - U) + (Uprev - U) = Unext - 2 * U + Uprev := by ring
  have hsum1 :
      c * ((f - fnext) + (f - fprev))
        - κ * ((fnext - f) ^ 2 + (fprev - f) ^ 2)
      ≤ Unext - 2 * U + Uprev := by
    simpa [hleft, hR] using hsum0
  have hlin : (f - fnext) + (f - fprev) = -(fnext - 2 * f + fprev) := by ring
  have hsum2 :
      c * (-(fnext - 2 * f + fprev))
        - κ * ((fnext - f) ^ 2 + (fprev - f) ^ 2)
      ≤ Unext - 2 * U + Uprev := by
    simpa [hlin] using hsum1
  have hsq : (fprev - f) ^ 2 = (f - fprev) ^ 2 := by ring
  have hsum3 :
      c * (-(fnext - 2 * f + fprev))
        - κ * ((f - fprev) ^ 2 + (fnext - f) ^ 2)
      ≤ Unext - 2 * U + Uprev := by
    simpa [hsq, add_comm] using hsum2
  exact hsum3

/--
**Lemma B (deterministic local form).**
If supports + negative Δ²f + small steps + `κ ε ≤ c α` hold, then `Δ²U ≥ 0`.
-/
theorem lemmaB_local_nonneg
    {Uprev U Unext fprev f fnext c κ α ε : ℝ}
    (hNext : Unext ≥ U + c * (f - fnext) - κ * (fnext - f) ^ 2)
    (hPrev : Uprev ≥ U + c * (f - fprev) - κ * (fprev - f) ^ 2)
    (hΔ2f  : fnext - 2 * f + fprev ≤ -α)
    (hsteps : (f - fprev) ^ 2 + (fnext - f) ^ 2 ≤ ε)
    (hc : 0 ≤ c) (hκ : 0 ≤ κ)
    (htrade : κ * ε ≤ c * α) :
    Unext - 2 * U + Uprev ≥ 0 := by
  have hlink :=
    lemmaB_link_from_quadratic_supports (Uprev:=Uprev) (U:=U) (Unext:=Unext)
      (fprev:=fprev) (f:=f) (fnext:=fnext) (c:=c) (κ:=κ) hNext hPrev
  have := lemmaB_bridge_nonneg
            (Δ2U := Unext - 2 * U + Uprev)
            (Δ2f := fnext - 2 * f + fprev)
            (dPrev := f - fprev) (dNext := fnext - f)
            (c := c) (κ := κ) (α := α) (ε := ε)
            (hlink := hlink)
            (hΔ2f := hΔ2f)
            (hsq := hsteps)
            (hc := hc) (hκ := hκ) (htrade := htrade)
  simpa using this

/--
Bundle per‑step absolute bounds into the squared‑sum budget used by `lemmaB_local_nonneg`.
If `|f - fprev| ≤ δ` and `|fnext - f| ≤ δ` with `δ ≥ 0`, then
`(f - fprev)^2 + (fnext - f)^2 ≤ 2 * δ^2`.
-/
theorem stepSquares_le_two_delta_sq
    {fprev f fnext δ : ℝ}
    (hPrev : |f - fprev| ≤ δ)
    (hNext : |fnext - f| ≤ δ)
    (hδ    : 0 ≤ δ) :
    (f - fprev) ^ 2 + (fnext - f) ^ 2 ≤ 2 * δ ^ 2 := by
  have h1_abs : |f - fprev| ≤ |δ| := by simpa [abs_of_nonneg hδ] using hPrev
  have h2_abs : |fnext - f| ≤ |δ| := by simpa [abs_of_nonneg hδ] using hNext
  have h1_sq : (f - fprev) ^ 2 ≤ δ ^ 2 := by
    have := (sq_le_sq.mpr h1_abs)
    simpa [abs_of_nonneg hδ] using this
  have h2_sq : (fnext - f) ^ 2 ≤ δ ^ 2 := by
    have := (sq_le_sq.mpr h2_abs)
    simpa [abs_of_nonneg hδ] using this
  have : (f - fprev) ^ 2 + (fnext - f) ^ 2 ≤ δ ^ 2 + δ ^ 2 :=
    add_le_add h1_sq h2_sq
  simpa [two_mul] using this

/--
`U = g ∘ f` convenience: if `g fnext ≥ g f + c*(f - fnext) - κ*(fnext - f)^2`
and `g fprev ≥ g f + c*(f - fprev) - κ*(fprev - f)^2`,
then the link inequality holds for `Δ²U = g fnext - 2*g f + g fprev`.
-/
theorem lemmaB_link_for_composed
    (g : ℝ → ℝ)
    {fprev f fnext c κ : ℝ}
    (hNext : g fnext ≥ g f + c * (f - fnext) - κ * (fnext - f) ^ 2)
    (hPrev : g fprev ≥ g f + c * (f - fprev) - κ * (fprev - f) ^ 2) :
    c * (-(fnext - 2 * f + fprev)) - κ * ((f - fprev) ^ 2 + (fnext - f) ^ 2)
      ≤ (g fnext) - 2 * (g f) + (g fprev) := by
  simpa using
    (lemmaB_link_from_quadratic_supports
      (Uprev := g fprev) (U := g f) (Unext := g fnext)
      (fprev := fprev) (f := f) (fnext := fnext) (c := c) (κ := κ)
      (hNext := hNext) (hPrev := hPrev))

/--
Convenience wrapper for Lemma B (δ‑form hypothesis).
Uses per‑step absolute bounds `|f - fprev| ≤ δ` and `|fnext - f| ≤ δ`,
sets `ε := 2*δ^2`, and applies `lemmaB_local_nonneg`.
-/
theorem lemmaB_local_nonneg_abs
    {Uprev U Unext fprev f fnext c κ α δ : ℝ}
    (hNext : Unext ≥ U + c * (f - fnext) - κ * (fnext - f) ^ 2)
    (hPrev : Uprev ≥ U + c * (f - fprev) - κ * (fprev - f) ^ 2)
    (hΔ2f  : fnext - 2 * f + fprev ≤ -α)
    (hAbsPrev : |f - fprev| ≤ δ)
    (hAbsNext : |fnext - f| ≤ δ)
    (hδ : 0 ≤ δ)
    (hc : 0 ≤ c) (hκ : 0 ≤ κ)
    (htradeδ : κ * (2 * δ ^ 2) ≤ c * α) :
    Unext - 2 * U + Uprev ≥ 0 := by
  have hsteps : (f - fprev) ^ 2 + (fnext - f) ^ 2 ≤ 2 * δ ^ 2 :=
    stepSquares_le_two_delta_sq (fprev := fprev) (f := f) (fnext := fnext)
      (δ := δ) (hPrev := hAbsPrev) (hNext := hAbsNext) (hδ := hδ)
  exact
    lemmaB_local_nonneg
      (Uprev := Uprev) (U := U) (Unext := Unext)
      (fprev := fprev) (f := f) (fnext := fnext)
      (c := c) (κ := κ) (α := α) (ε := 2 * δ ^ 2)
      hNext hPrev hΔ2f hsteps hc hκ (by simpa using htradeδ)

end
end NOC
