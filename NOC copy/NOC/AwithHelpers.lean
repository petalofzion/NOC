import Mathlib
import NOC.AHelpers
set_option pp.all true  -- 👀 enables verbose “x-ray” printing in infoview

/-!
Module: NOC.A
Summary: Lemma A (capacity‑compatible drift) — product and ratio forms.
Public entry points: `lemmaA_freeEnergy_nonneg_product`, `lemmaA_freeEnergy_nonneg_ratio`.
-/

namespace NOC
noncomputable section
open Classical

/-
  Lemma A (capacity‑compatible drift).
  This module contains the arithmetic core used in the free‑energy argument.
-/

/-- **Lemma A (capacity‑compatible drift, product form).** -/
theorem lemmaA_freeEnergy_nonneg_product
    {ΔER ΔKL ΔU m L β : ℝ}
    (hER   : m * ΔU ≤ ΔER)
    (hKL   : ΔKL ≤ L * ΔU)
    (hU    : 0 ≤ ΔU)
    (hβpos : 0 < β)
    (hProd : L ≤ β * m) :
    ΔER - (ΔKL / β) ≥ 0 :=
by
  have h := KL_div_beta_le_ER_of_bounds hER hKL hU hβpos hProd
  exact sub_nonneg.mpr h

/-- Convert the ratio bound `β ≥ L/m` into the product form `L ≤ β*m`. -/
theorem betaChoice_ratio_to_product
    {L m β : ℝ} (hm : 0 < m) (hβratio : β ≥ L / m) :
    L ≤ β * m :=
by
  exact (betaChoice_ratio_iff_product hm).mp hβratio

/-- **Lemma A (ratio form)**, derived from the product form. -/
theorem lemmaA_freeEnergy_nonneg_ratio
    {ΔER ΔKL ΔU m L β : ℝ}
    (hER   : m * ΔU ≤ ΔER)
    (hKL   : ΔKL ≤ L * ΔU)
    (hU    : 0 ≤ ΔU)
    (hmpos : 0 < m)
    (hβpos : 0 < β)
    (hβratio : β ≥ L / m) :
    ΔER - (ΔKL / β) ≥ 0 :=
  lemmaA_freeEnergy_nonneg_product hER hKL hU hβpos
    (betaChoice_ratio_to_product hmpos hβratio)

end
end NOC
