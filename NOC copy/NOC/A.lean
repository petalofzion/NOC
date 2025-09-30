import Mathlib
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
    ΔER - (ΔKL / β) ≥ 0 := by
  -- L*ΔU ≤ β*m*ΔU
  have hLβmU : L * ΔU ≤ β * m * ΔU := by
    have := mul_le_mul_of_nonneg_right hProd hU
    simpa [mul_comm, mul_left_comm] using this
  -- ΔKL ≤ β*m*ΔU
  have hKL_le_βmU : ΔKL ≤ β * m * ΔU := le_trans hKL hLβmU
  -- β*(m*ΔU) ≤ β*ΔER
  have hβ_nonneg : 0 ≤ β := le_of_lt hβpos
  have hβmU : β * (m * ΔU) ≤ β * ΔER := by
    have := mul_le_mul_of_nonneg_left hER hβ_nonneg
    simpa [mul_comm, mul_left_comm] using this
  -- chain to β*ΔER
  have hβm_assoc : β * m * ΔU = β * (m * ΔU) := by ring
  have hKL_le_βER : ΔKL ≤ β * ΔER :=
    le_trans hKL_le_βmU (by simpa [hβm_assoc] using hβmU)
  -- divide by β>0
  have hbne : β ≠ 0 := ne_of_gt hβpos
  have h_div : β * (ΔKL / β) ≤ β * ΔER := by
    simpa [div_eq_mul_inv, hbne, mul_comm, mul_left_comm] using hKL_le_βER
  have h_final : ΔKL / β ≤ ΔER := (le_of_mul_le_mul_left h_div hβpos)
  exact (sub_nonneg.mpr h_final)

/-- Convert the ratio bound `β ≥ L/m` into the product form `L ≤ β*m`. -/
theorem betaChoice_ratio_to_product
    {L m β : ℝ} (hm : 0 < m) (hβratio : β ≥ L / m) :
    L ≤ β * m := by
  have hmnn : 0 ≤ m := le_of_lt hm
  have h1 : (L / m) * m ≤ β * m := by
    exact mul_le_mul_of_nonneg_right hβratio hmnn
  have hmne : m ≠ 0 := ne_of_gt hm
  simpa [div_mul_eq_mul_div, hmne] using h1

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
