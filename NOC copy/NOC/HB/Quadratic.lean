import Mathlib

/-!
Module: NOC.HB.Quadratic
Summary: Heavy‑ball on a 1D quadratic — parameters, update, Δ² operator, and value‑difference bounds.
Public entry points: `HBParams`, `hbStep`, `delta2`, `f_at`, `delta2_f_hb_closed_form`, `quad_f_step_abs_le`, `quad_f_stepSquares_le`.
-/

namespace NOC
noncomputable section
open Classical

/-! ## Path‑B calibration helpers: heavy‑ball on a 1D quadratic -/

/-- Heavy‑ball parameters. -/
structure HBParams where
  η : ℝ
  γ : ℝ
  η_pos : 0 < η
  γ_range : 0 ≤ γ ∧ γ < 1

/-- One-step heavy-ball update for a scalar state (proxy for a 1D quadratic). -/
def hbStep (p : HBParams) (lam : ℝ) (x x_prev xstar : ℝ) : ℝ :=
  let e := x - xstar
  let e_prev := x_prev - xstar
  -- next error: e_{t+1} = (1 - η·lam + γ) e_t - γ e_{t-1}
  (1 - p.η * lam + p.γ) * e - p.γ * e_prev + xstar

/-- Convenience: discrete second difference of a scalar sequence. -/
def delta2 (x_next x x_prev : ℝ) : ℝ := x_next - 2 * x + x_prev

/-- Quadratic `f` around `x⋆`. -/
def f_at (lam : ℝ) (x xstar : ℝ) : ℝ := (lam / 2) * (x - xstar) ^ 2

@[simp] lemma hb_error_next_eq (p : HBParams) (lam x x_prev xstar : ℝ) :
  hbStep p lam x x_prev xstar - xstar
    = (1 - p.η * lam + p.γ) * (x - xstar) - p.γ * (x_prev - xstar) := by
  simp [hbStep]

/-- Pull out the linear factor `(lam/2)` in `Δ² f`. -/
lemma delta2_f_at_eq (lam x_next x x_prev xstar : ℝ) :
  delta2 (f_at lam x_next xstar) (f_at lam x xstar) (f_at lam x_prev xstar)
    = (lam / 2) *
        ((x_next - xstar) ^ 2 - 2 * (x - xstar) ^ 2 + (x_prev - xstar) ^ 2) := by
  simp [delta2, f_at]; ring

/-- Closed‑form `Δ² f` for HB on the 1D quadratic (pure algebra). -/
lemma delta2_f_hb_closed_form
    (p : HBParams) (lam x x_prev xstar : ℝ) :
  let a  := 1 - p.η * lam + p.γ
  let e  := x - xstar
  let ep := x_prev - xstar
  delta2 (f_at lam (hbStep p lam x x_prev xstar) xstar)
         (f_at lam x xstar) (f_at lam x_prev xstar)
    = (lam / 2) * ((a ^ 2 - 2) * e ^ 2 - 2 * a * p.γ * e * ep + (1 + p.γ ^ 2) * ep ^ 2) := by
  intro a e ep
  have : delta2 (f_at lam (hbStep p lam x x_prev xstar) xstar)
                 (f_at lam x xstar) (f_at lam x_prev xstar)
         = (lam / 2) * ((hbStep p lam x x_prev xstar - xstar) ^ 2
                      - 2 * (x - xstar) ^ 2 + (x_prev - xstar) ^ 2) := by
    simpa using delta2_f_at_eq lam (hbStep p lam x x_prev xstar) x x_prev xstar
  have h := hb_error_next_eq (p := p) lam x x_prev xstar
  -- substitute `e_{t+1}` and expand the square
  simpa [this, h, a, e, ep] using
    show (lam / 2) * (((a * e - p.γ * ep) ^ 2) - 2 * e ^ 2 + ep ^ 2)
          = (lam / 2) * ((a ^ 2 - 2) * e ^ 2 - 2 * a * p.γ * e * ep + (1 + p.γ ^ 2) * ep ^ 2) from by
      ring

/-- Value‐difference bound for the quadratic (no radius yet).
`|f(y)-f(x)| ≤ (|lam|/2) · (|y-x⋆|+|x-x⋆|) · |y-x|`. -/
lemma quad_f_step_abs_le_general
    (lam x y xstar : ℝ) :
  |f_at lam y xstar - f_at lam x xstar|
    ≤ (|lam| / 2) * (|y - xstar| + |x - xstar|) * |y - x| := by
  -- pull the constant factor (lam/2) to the right, then take absolute values
  have h0lin :
      f_at lam y xstar - f_at lam x xstar
        = (lam / 2) * ((y - xstar) ^ 2 - (x - xstar) ^ 2) := by
    simp [f_at, sub_eq_add_neg, mul_comm, ]; ring
  have h0 :
      |f_at lam y xstar - f_at lam x xstar|
        = |lam / 2| * |(y - xstar) ^ 2 - (x - xstar) ^ 2| := by
    have : |(lam / 2) * ((y - xstar) ^ 2 - (x - xstar) ^ 2)|
           = |lam / 2| * |(y - xstar) ^ 2 - (x - xstar) ^ 2| := by
      simp [abs_mul]
    simpa [h0lin] using this
  -- factor the difference of squares and bound the sum by triangle inequality
  have hfac :
      (y - xstar) ^ 2 - (x - xstar) ^ 2
        = ((y - xstar) - (x - xstar)) * ((y - xstar) + (x - xstar)) := by
    ring
  have hdiff : |(y - xstar) - (x - xstar)| = |y - x| := by
    have : (y - xstar) - (x - xstar) = y - x := by ring
    simp [this]
  have hsum : |(y - xstar) + (x - xstar)|
                ≤ |y - xstar| + |x - xstar| := by
    simpa using (abs_add (y - xstar) (x - xstar))
  have hprod :
      |(y - xstar) ^ 2 - (x - xstar) ^ 2|
        ≤ |y - x| * (|y - xstar| + |x - xstar|) := by
    have : |(y - xstar) ^ 2 - (x - xstar) ^ 2|
             = |(y - xstar) - (x - xstar)| * |(y - xstar) + (x - xstar)| := by
      simp [hfac, abs_mul]
    calc
      |(y - xstar) ^ 2 - (x - xstar) ^ 2|
          = |(y - xstar) - (x - xstar)| * |(y - xstar) + (x - xstar)| := this
      _ ≤ |(y - xstar) - (x - xstar)| * (|y - xstar| + |x - xstar|) := by
          exact mul_le_mul_of_nonneg_left hsum (abs_nonneg _)
      _ = |y - x| * (|y - xstar| + |x - xstar|) := by
          simp
  -- multiply the previous bound by |lam/2| and normalize |lam/2| = |lam|/2
  have hhalf : |lam / 2| = |lam| / 2 := by
    have : |(2 : ℝ)| = (2 : ℝ) := by norm_num
    simp [abs_div]
  have : |lam / 2| * |(y - xstar) ^ 2 - (x - xstar) ^ 2|
           ≤ |lam / 2| * (|y - x| * (|y - xstar| + |x - xstar|)) :=
    mul_le_mul_of_nonneg_left hprod (abs_nonneg _)
  -- repackage everything in the target shape
  simpa [h0, hhalf, mul_comm, mul_left_comm, mul_assoc] using this

/-- Lipschitz‐type radius corollary:
If `|x−x⋆|, |y−x⋆| ≤ R` then `|f(y)−f(x)| ≤ |lam|·R·|y−x|`. -/
lemma quad_f_step_abs_le
    (lam x y xstar R : ℝ)
    (hx : |x - xstar| ≤ R) (hy : |y - xstar| ≤ R) :
  |f_at lam y xstar - f_at lam x xstar| ≤ |lam| * R * |y - x| := by
  -- start from the general bound
  have h := quad_f_step_abs_le_general lam x y xstar
  -- bound the middle factor by `R + R`
  have hmid :
      (|lam| / 2) * (|y - xstar| + |x - xstar|) * |y - x|
        ≤ (|lam| / 2) * (R + R) * |y - x| := by
    have hnn : 0 ≤ (|lam| / 2) := div_nonneg (abs_nonneg _) (by norm_num)
    have : (|y - xstar| + |x - xstar|) ≤ R + R := add_le_add hy hx
    exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left this hnn)
            (abs_nonneg _)
  -- (|lam|/2) * (R+R) = |lam| * R
  have hscale : (|lam| / 2) * (R + R) * |y - x|
              = |lam| * R * |y - x| := by
    -- rewrite `R + R = 2 * R` and cancel the 2
    have : R + R = 2 * R := by ring
    simp [this, mul_comm, mul_left_comm, mul_assoc, div_eq_mul_inv]
  exact h.trans (by simpa [hscale] using hmid)


/-- Squared form convenient for feeding `lemmaB_local_nonneg_abs`. -/
lemma quad_f_stepSquares_le
    (lam x_prev x x_next xstar R : ℝ)
    (hprev : |x_prev - xstar| ≤ R)
    (hcur  : |x      - xstar| ≤ R)
    (hnext : |x_next - xstar| ≤ R) :
  (f_at lam x xstar - f_at lam x_prev xstar) ^ 2
  + (f_at lam x_next xstar - f_at lam x xstar) ^ 2
  ≤ (|lam| * R) ^ 2 * ((x - x_prev) ^ 2 + (x_next - x) ^ 2) := by
  -- radius nonnegativity
  have hR : 0 ≤ R := le_trans (abs_nonneg _) hcur
  -- two radius corollaries
  have h1 := quad_f_step_abs_le lam x_prev x xstar R hprev hcur
  have h2 := quad_f_step_abs_le lam x x_next xstar R hcur  hnext

  -- package the common constant
  set C : ℝ := |lam| * R
  have hCnn : 0 ≤ C := mul_nonneg (abs_nonneg _) hR

  -- square the two bounds via `sq_le_sq.mpr`, feeding it an absolute on the RHS
  have h1sq :
      (f_at lam x xstar - f_at lam x_prev xstar) ^ 2
        ≤ (C * |x - x_prev|) ^ 2 := by
    refine (sq_le_sq.mpr ?_)
    have : |f_at lam x xstar - f_at lam x_prev xstar| ≤ C * |x - x_prev| := by
      simpa [C, mul_comm, mul_left_comm, mul_assoc] using h1
    simpa [abs_of_nonneg (mul_nonneg hCnn (abs_nonneg _))] using this

  have h2sq :
      (f_at lam x_next xstar - f_at lam x xstar) ^ 2
        ≤ (C * |x_next - x|) ^ 2 := by
    refine (sq_le_sq.mpr ?_)
    have : |f_at lam x_next xstar - f_at lam x xstar| ≤ C * |x_next - x| := by
      simpa [C, mul_comm, mul_left_comm, mul_assoc] using h2
    simpa [abs_of_nonneg (mul_nonneg hCnn (abs_nonneg _))] using this

  -- add the two squared bounds
  have hsum := add_le_add h1sq h2sq

  -- (C*|Δx|)^2 = C^2 * (Δx)^2, and |Δx|^2 = (Δx)^2 on ℝ
  have hx1 : (C * |x - x_prev|) ^ 2 = C ^ 2 * (x - x_prev) ^ 2 := by
    simp [pow_two, mul_comm, mul_left_comm, mul_assoc, ]
  have hx2 : (C * |x_next - x|) ^ 2 = C ^ 2 * (x_next - x) ^ 2 := by
    simp [pow_two, mul_comm, mul_left_comm, mul_assoc, ]

  -- finish: factor out C^2 with `mul_add`
  simpa [C, hx1, hx2, mul_add] using hsum

end
end NOC
