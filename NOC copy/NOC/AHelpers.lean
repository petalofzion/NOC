import Mathlib

/-!
Module: NOC.AHelpers
Summary: Small algebra/inequality lemmas that factor the "capacity‑compatible drift" proof
         into reusable steps. These are written to match the moves used in Lemma A.
Public entry points:
  • `mul_right_mono_nonneg`
  • `mul_left_mono_nonneg`
  • `div_le_of_le_mul_pos`
  • `betaChoice_product_to_ratio`
  • `betaChoice_ratio_iff_product`
  • `KL_div_beta_le_ER_of_bounds`

These helpers intentionally avoid re-proving Lemma A; instead they package the standard
monotonicity and choice‑equivalence steps that the A‑proof uses.
-/

namespace NOC
noncomputable section
open Classical

/-- Monotone scaling on the *right* by a nonnegative scalar: if `a ≤ b` and `0 ≤ u`
then `a*u ≤ b*u`. Thin wrapper around `mul_le_mul_of_nonneg_right` for readability. -/
lemma mul_right_mono_nonneg {a b u : ℝ} (h : a ≤ b) (hu : 0 ≤ u) :
    a * u ≤ b * u :=
  mul_le_mul_of_nonneg_right h hu

/-- Monotone scaling on the *left* by a nonnegative scalar: if `a ≤ b` and `0 ≤ β`
then `β*a ≤ β*b`. Thin wrapper around `mul_le_mul_of_nonneg_left`. -/
lemma mul_left_mono_nonneg {a b β : ℝ} (h : a ≤ b) (hβ : 0 ≤ β) :
    β * a ≤ β * b :=
  mul_le_mul_of_nonneg_left h hβ

/-- Divide a bound by a *positive* scalar on the left.
From `a ≤ β*b` and `0 < β` we deduce `a/β ≤ b`. -/
lemma div_le_of_le_mul_pos {a b β : ℝ} (hβpos : 0 < β) (h : a ≤ β * b) :
    a / β ≤ b := by
  have hbne : β ≠ 0 := ne_of_gt hβpos
  -- rewrite `a` as `β * (a/β)` then cancel `β>0`
  have h_mul : β * (a / β) ≤ β * b := by
    simpa [div_eq_mul_inv, hbne, mul_comm, mul_left_comm, mul_assoc] using h
  exact (le_of_mul_le_mul_left h_mul hβpos)

/-- Convert the *product* choice into the *ratio* choice (for `m>0`).
If `L ≤ β*m` and `0 < m`, then `β ≥ L/m`. -/
lemma betaChoice_product_to_ratio {L m β : ℝ} (hmpos : 0 < m)
    (hProd : L ≤ β * m) : β ≥ L / m := by
  have hmne : m ≠ 0 := ne_of_gt hmpos
  have h_mul : (L / m) * m ≤ β * m := by
    simpa [div_mul_eq_mul_div, hmne] using hProd
  have h_ratio : L / m ≤ β := le_of_mul_le_mul_right h_mul hmpos
  simpa [ge_iff_le] using h_ratio

/-- Equivalence of product and ratio forms of the β‑choice when `m>0`. -/
lemma betaChoice_ratio_iff_product {L m β : ℝ} (hmpos : 0 < m) :
    (β ≥ L / m) ↔ (L ≤ β * m) := by
  constructor
  · -- ratio → product
    intro hβratio
    have hmnn : 0 ≤ m := le_of_lt hmpos
    have : (L / m) * m ≤ β * m :=
      mul_le_mul_of_nonneg_right hβratio hmnn
    -- `(L/m)*m = L` because `m ≠ 0`.
    have hmne : m ≠ 0 := ne_of_gt hmpos
    simpa [div_mul_eq_mul_div, hmne] using this
  · -- product → ratio
    intro hProd
    exact betaChoice_product_to_ratio hmpos hProd

/-- **Helper chain for Lemma A.**
From the four structural bounds used in Lemma A
`hER : m*ΔU ≤ ΔER`, `hKL : ΔKL ≤ L*ΔU`, `hU : 0 ≤ ΔU`, `hβpos : 0 < β`, together with the
β‑choice in product form `hProd : L ≤ β*m`, deduce the key comparison `ΔKL/β ≤ ΔER`.
This is the arithmetic heart of the free‑energy step. -/
lemma KL_div_beta_le_ER_of_bounds
    {ΔER ΔKL ΔU m L β : ℝ}
    (hER   : m * ΔU ≤ ΔER)
    (hKL   : ΔKL ≤ L * ΔU)
    (hU    : 0 ≤ ΔU)
    (hβpos : 0 < β)
    (hProd : L ≤ β * m) :
    ΔKL / β ≤ ΔER := by
  -- 1) push `L ≤ β*m` through a nonnegative `ΔU`.
  have hLβmU : L * ΔU ≤ (β * m) * ΔU :=
    mul_right_mono_nonneg hProd hU
  -- 2) combine with the KL‑bound.
  have hKL_le : ΔKL ≤ (β * m) * ΔU := le_trans hKL hLβmU
  -- 3) scale the ER‑bound by nonnegative β.
  have hβ_nonneg : 0 ≤ β := le_of_lt hβpos
  have hβmU : β * (m * ΔU) ≤ β * ΔER :=
    mul_left_mono_nonneg hER hβ_nonneg
  -- 4) reassociate `(β*m)*ΔU = β*(m*ΔU)` to chain the inequalities.
  have hassoc : (β * m) * ΔU = β * (m * ΔU) := by
    simp [mul_assoc]
  have hKL_le_βER : ΔKL ≤ β * ΔER := by
    have : ΔKL ≤ β * (m * ΔU) := by simpa [hassoc] using hKL_le
    exact le_trans this hβmU
  -- 5) divide by β>0.
  exact div_le_of_le_mul_pos hβpos hKL_le_βER

end
end NOC
