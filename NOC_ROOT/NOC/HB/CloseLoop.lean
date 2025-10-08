/-
  HB_CloseLoop.lean
  Heavy-ball closed-loop algebra + one-variable reduction for Δ²f on a 1D quadratic.

  Depends on:
    - NOC.QuadraticHB (for HBParams, hbStep, f_at, delta2, and HB algebraic helpers)
-/
import Mathlib
import NOC.HB.Quadratic
import NOC.B.Core

namespace NOC
noncomputable section
open Classical

-- Silence linter hints like "try 'simp' instead of 'simpa'" in this file.
set_option linter.unnecessarySimpa false



/-! ## Notation & reminders

We work with the 1D quadratic `f_at lam x x⋆ = (lam/2) * (x-x⋆)^2`.
HB update:
  e_{t+1} = (1 - η·lam + γ) e_t - γ e_{t-1},  where e_t := x_t - x⋆.
We also denote the "velocity" (relative step) d_t := x_t - x_{t-1} = e_t - e_{t-1}.
-/

/-- Shorthand: the "HB curvature scale" `τ = η·lam`. -/
@[simp] def tau (p : HBParams) (lam : ℝ) : ℝ := p.η * lam

/-- Algebraic identity: the velocity is the error difference. -/
@[simp] lemma d_eq_e_sub_ep (x x_prev xstar : ℝ) :
  (x - x_prev) = (x - xstar) - (x_prev - xstar) := by ring

/-- Closed form for `Δ² f` in `(e,d)` variables:
`Δ²f = (lam/2) * [ τ(τ-2) e^2 + 2(γ(1-τ)-1) e d + (1+γ^2) d^2 ]`
with `τ := η·lam`.
-/
lemma delta2_f_hb_in_e_d
    (p : HBParams) (lam x x_prev xstar : ℝ) :
  let τ := tau p lam
  let γ := p.γ
  let e := x - xstar
  let d := x - x_prev
  delta2 (f_at lam (hbStep p lam x x_prev xstar) xstar)
         (f_at lam x xstar) (f_at lam x_prev xstar)
    = (lam / 2) *
        (τ * (τ - 2) * e^2
          + 2 * (γ * (1 - τ) - 1) * e * d
          + (1 + γ^2) * d^2) := by
  -- open the lets
  intro τ γ e d
  classical
  -- start from the (e,ep) closed form
  have hclosed :=
    delta2_f_hb_closed_form (p := p) lam x x_prev xstar
  -- establish ep = e - d in the correct direction
  have hd : x_prev - xstar = e - d := by
    have : d = e - (x_prev - xstar) := by
      simp [e, d]
    have : d + (x_prev - xstar) = e :=
      (eq_sub_iff_add_eq).1 this
    exact (eq_sub_iff_add_eq).2 (by simpa [add_comm] using this)

  -- polynomial identity after substituting `a = 1 - τ + γ` and `ep = e - d`
  have poly :
      ((1 - τ + γ) ^ 2 - 2) * e ^ 2
      - 2 * (1 - τ + γ) * γ * e * (e - d)
      + (1 + γ ^ 2) * (e - d) ^ 2
    =
      τ * (τ - 2) * e ^ 2
      + 2 * (γ * (1 - τ) - 1) * e * d
      + (1 + γ ^ 2) * d ^ 2 := by
    ring_nf

  -- scale the identity
  have hscale_poly :
      (lam / 2) *
        ( ((1 - τ + γ) ^ 2 - 2) * e ^ 2
        - 2 * (1 - τ + γ) * γ * e * (e - d)
        + (1 + γ ^ 2) * (e - d) ^ 2)
      =
      (lam / 2) *
        ( τ * (τ - 2) * e ^ 2
        + 2 * (γ * (1 - τ) - 1) * e * d
        + (1 + γ ^ 2) * d ^ 2) :=
    congrArg (fun t => (lam / 2) * t) poly

  -- rewrite `a` and `ep` in the closed form, then compose
  have h0 :
      delta2 (f_at lam (hbStep p lam x x_prev xstar) xstar)
             (f_at lam x xstar) (f_at lam x_prev xstar)
      =
      (lam / 2) *
        ( ((1 - τ + γ) ^ 2 - 2) * e ^ 2
        - 2 * (1 - τ + γ) * γ * e * (e - d)
        + (1 + γ ^ 2) * (e - d) ^ 2) := by
    simpa [tau, hd, sub_eq_add_neg] using hclosed

  exact h0.trans hscale_poly

/-- One-variable reduction:
If `ρ ≥ 0` and `|d| ≤ ρ |e|`, then
`Δ²f ≤ (lam/2) * [ τ(τ-2) + 2|γ(1-τ)-1| ρ + (1+γ^2) ρ^2 ] * e^2`.
-/
/-
NOTE (convexity of the quadratic):
We assume `0 ≤ lam`, so the 1D quadratic `f_at lam x x⋆ = (lam/2) * (x-x⋆)^2` is convex.
In this lemma we only use this to ensure `(lam/2) ≥ 0`, so multiplying inequalities by
`(lam/2)` does not flip their direction. This matches the “HB under PL / convex quadratic”
regime used in Lemma B and downstream results; the `lam = 0` edge case is trivial.
-/
lemma delta2_f_upper_bound_via_rho
    (p : HBParams) (lam x x_prev xstar ρ : ℝ)
    (hρ : 0 ≤ ρ) (hConv : 0 ≤ lam) :
  let τ := tau p lam
  let γ := p.γ
  let e := x - xstar
  let d := x - x_prev
  |d| ≤ ρ * |e| →
  delta2 (f_at lam (hbStep p lam x x_prev xstar) xstar)
         (f_at lam x xstar) (f_at lam x_prev xstar)
    ≤ (lam / 2) *
        (τ * (τ - 2) + 2 * |γ * (1 - τ) - 1| * ρ + (1 + γ^2) * ρ^2) * e^2 := by
  intro τ γ e d hbound
  have h := delta2_f_hb_in_e_d (p := p) lam x x_prev xstar

  -- |e*d| ≤ ρ * e^2
  have h_ed : |e * d| ≤ ρ * e ^ 2 := by
    have h := mul_le_mul_of_nonneg_left hbound (abs_nonneg e)
    -- |e||d| ≤ |e|(ρ|e|) = ρ|e|^2 = ρ e^2
    simpa [abs_mul, mul_comm, mul_left_comm, mul_assoc, sq_abs, pow_two] using h

  -- d^2 ≤ ρ^2 * e^2
  have h_d2 : d ^ 2 ≤ ρ ^ 2 * e ^ 2 := by
    -- put the hypothesis in the `|a| ≤ |b|` form that `sq_le_sq` expects,
    -- avoiding the `||` token entirely
    have hb' : |d| ≤ |ρ * abs e| := by
      -- since ρ ≥ 0, |ρ * |e|| = ρ * |e|
      simpa [abs_mul, abs_of_nonneg hρ, abs_abs, mul_comm, mul_left_comm, mul_assoc] using hbound
    -- now square both sides
    have hsq : |d| ^ 2 ≤ (ρ * abs e) ^ 2 := by
      simpa [pow_two] using (sq_le_sq.mpr hb')
    -- rewrite into the desired `d^2 ≤ ρ^2 * e^2`
    simpa [sq_abs, pow_two, mul_comm, mul_left_comm, mul_assoc] using hsq

  -- apply bound termwise to the exact equality from `h`
  have : delta2 (f_at lam (hbStep p lam x x_prev xstar) xstar)
                (f_at lam x xstar) (f_at lam x_prev xstar)
        ≤ (lam / 2) *
            (τ * (τ - 2) * e^2
             + 2 * |γ * (1 - τ) - 1| * (ρ * e^2)
             + (1 + γ^2) * (ρ^2 * e^2)) := by
    -- cross term
    have hxabs :
      |2 * (γ * (1 - τ) - 1) * (e * d)|
        ≤ 2 * |γ * (1 - τ) - 1| * (ρ * e^2) := by
      have := mul_le_mul_of_nonneg_left h_ed (by norm_num : 0 ≤ (2:ℝ) * |γ * (1 - τ) - 1|)
      -- rearrange factors
      simpa [abs_mul, mul_comm, mul_left_comm, mul_assoc] using this
    have hx :
      2 * (γ * (1 - τ) - 1) * e * d
        ≤ 2 * |γ * (1 - τ) - 1| * (ρ * e^2) :=
      le_trans (by
        -- |x| ≥ x over ℝ
        simpa [abs_mul, mul_comm, mul_left_comm, mul_assoc, two_mul] using
          (le_abs_self (2 * ((γ * (1 - τ) - 1) * (e * d))))) hxabs
    -- d^2 term
    have hy :
      (1 + γ^2) * d^2 ≤ (1 + γ^2) * (ρ^2 * e^2) :=
      mul_le_mul_of_nonneg_left h_d2 (by have := p.γ_range.1; nlinarith [this])
    -- combine and scale by (lam/2) ≥ 0 (we’ll use this only later)
    -- combine the two non-constant terms, then add the d^2 term, then scale by (lam/2) ≥ 0
    have hsum₁ :
      τ * (τ - 2) * e^2 + 2 * (γ * (1 - τ) - 1) * e * d
        ≤ τ * (τ - 2) * e^2 + 2 * |γ * (1 - τ) - 1| * (ρ * e^2) :=
      add_le_add le_rfl hx

    have hsum :
      τ * (τ - 2) * e^2 + 2 * (γ * (1 - τ) - 1) * e * d + (1 + γ^2) * d^2
        ≤ τ * (τ - 2) * e^2 + 2 * |γ * (1 - τ) - 1| * (ρ * e^2) + (1 + γ^2) * (ρ^2 * e^2) := by
      -- rearrangement: (A + B) + C and (A + B') + C'
      simpa [add_assoc] using add_le_add hsum₁ hy
    -- now scale by (lam/2) ≥ 0 and rewrite the LHS using the exact identity `h`
    have hmul :
      (lam / 2) *
          (τ * (τ - 2) * e^2 + 2 * (γ * (1 - τ) - 1) * e * d + (1 + γ^2) * d^2)
        ≤ (lam / 2) *
          (τ * (τ - 2) * e^2 + 2 * |γ * (1 - τ) - 1| * (ρ * e^2) + (1 + γ^2) * (ρ^2 * e^2)) :=
      mul_le_mul_of_nonneg_left hsum (by nlinarith [hConv])

    simpa [h] using hmul


  -- repackage the RHS into (lam/2) * [ ... ] * e^2
  have hrw :
      (lam / 2) *
        (τ * (τ - 2) * e ^ 2
          + 2 * |γ * (1 - τ) - 1| * (ρ * e ^ 2)
          + (1 + γ ^ 2) * (ρ ^ 2 * e ^ 2))
    =
      (lam / 2) *
        (τ * (τ - 2) + 2 * |γ * (1 - τ) - 1| * ρ + (1 + γ ^ 2) * ρ ^ 2) * e ^ 2 := by
    -- factor out e^2 algebraically once, then scale by lam/2
    have :
        τ * (τ - 2) * e ^ 2
          + 2 * |γ * (1 - τ) - 1| * (ρ * e ^ 2)
          + (1 + γ ^ 2) * (ρ ^ 2 * e ^ 2)
      =
        (τ * (τ - 2) + 2 * |γ * (1 - τ) - 1| * ρ + (1 + γ ^ 2) * ρ ^ 2) * e ^ 2 := by
      ring
    simpa [mul_add, mul_comm, mul_left_comm, mul_assoc]
      using congrArg (fun t => (lam / 2) * t) this

  have htmp := this
  simpa [hrw] using htmp

/-- A *sufficient* (and explicit) small-relative-step condition that forces `Δ²f ≤ 0`.
We give one convenient choice of `ρ⋆(τ,γ)`, any smaller `ρ` also works. -/
def hb_rhoStar (τ γ : ℝ) : ℝ :=
  -- conservative choice: see `hb_bracket_nonpos` below
  τ * (2 - τ) / ( (1 + γ^2) + 2 * (1 + |γ|) )


/-- Helper inequality: the polynomial bracket is ≤ 0 for ρ ≤ ρ⋆. -/
lemma hb_bracket_nonpos
    {τ γ ρ : ℝ}
    (hτlo : 0 < τ) (hτhi : τ < 2)
    (hρlo : 0 ≤ ρ) (hρhi : ρ ≤ hb_rhoStar τ γ) :
  τ * (τ - 2) + 2 * |γ * (1 - τ) - 1| * ρ + (1 + γ ^ 2) * ρ ^ 2 ≤ 0 := by
  -- τ in (0,2) ⇒ basic bounds we will reuse
  have hτnn : 0 ≤ τ := le_of_lt hτlo
  have hTpos : 0 < τ * (2 - τ) := by
    have : 0 < (2 - τ) := sub_pos.mpr hτhi
    exact mul_pos hτlo this
  have hTle1 : τ * (2 - τ) ≤ 1 := by
    have hsq : 0 ≤ (τ - 1)^2 := sq_nonneg (τ - 1)
    have : τ * (2 - τ) = 1 - (τ - 1)^2 := by ring
    nlinarith
  have h_abs1τ : |1 - τ| ≤ (1 : ℝ) := by
    have h1 : -1 ≤ 1 - τ := by have := le_of_lt hτlo; linarith
    have h2 : 1 - τ ≤ 1   := by have := le_of_lt hτhi; linarith
    exact abs_le.mpr ⟨by simpa using h1, by simpa using h2⟩

  -- abbreviations
  set T : ℝ := τ * (2 - τ)
  set A : ℝ := 2 * (1 + |γ|)
  set B : ℝ := 1 + γ^2

  have hApos : 0 ≤ A := by have := abs_nonneg γ; nlinarith [this]
  have hBpos : 0 ≤ B := by have := sq_nonneg γ; nlinarith [this]

  -- |γ(1-τ) - 1| ≤ |γ|*|1-τ| + 1 ≤ |γ| + 1  ⇒  2|…| ≤ 2(1+|γ|) = A
  have hA :
      2 * |γ * (1 - τ) - 1| ≤ A := by
    have h1 : |γ * (1 - τ) - 1| ≤ |γ * (1 - τ)| + |(1 : ℝ)| := by
      simpa [sub_eq_add_neg] using (abs_add (γ * (1 - τ)) (-1))
    have h2 : |γ * (1 - τ)| = |γ| * |1 - τ| := by simp [abs_mul]
    have h3 : |(1 : ℝ)| = 1 := by norm_num
    have h4 : |γ * (1 - τ) - 1| ≤ |γ| * |1 - τ| + 1 := by simpa [h2, h3] using h1
    have h5 : |γ * (1 - τ) - 1| ≤ |γ| + 1 := le_trans h4 (by nlinarith [h_abs1τ, abs_nonneg γ])
    nlinarith [h5]

  ----------------------------------------------------------------
  -- Step 1: compare the bracket to  -T + Aρ + Bρ²
  ----------------------------------------------------------------
  have hbnd :
    τ * (τ - 2) + 2 * |γ * (1 - τ) - 1| * ρ + (1 + γ ^ 2) * ρ ^ 2
      ≤ -T + A * ρ + B * ρ ^ 2 := by
    -- Middle term: 2|…|·ρ ≤ A·ρ
    have hmid : 2 * |γ * (1 - τ) - 1| * ρ ≤ A * ρ :=
      mul_le_mul_of_nonneg_right hA hρlo
    -- Build the inequality termwise, then rewrite with T,A,B
    have hstep :
      τ * (τ - 2) + 2 * |γ * (1 - τ) - 1| * ρ + (1 + γ ^ 2) * ρ ^ 2
        ≤ τ * (τ - 2) + A * ρ + (1 + γ ^ 2) * ρ ^ 2 :=
      add_le_add (add_le_add le_rfl hmid) le_rfl
    -- Identify τ(τ−2) = −T explicitly; simp will use this lemma
    have hTneg : τ * (τ - 2) = -T := by
      have : τ * (τ - 2) = -(τ * (2 - τ)) := by ring
      simpa [T] using this
    -- Now the rewrite is straightforward
    simpa [hTneg, A, B] using hstep



  ----------------------------------------------------------------
  -- Step 2: bound  Aρ + Bρ²  by  T  using ρ ≤ T/(B+A)  and monotonicity
  ----------------------------------------------------------------
  -- Re-express ρ⋆; keep the simp args minimal to avoid linter warnings.
  have hρcap : ρ ≤ T / (B + A) := by
    have : hb_rhoStar τ γ = T / (B + A) := by
      simp [hb_rhoStar, T, A, B, add_comm, add_assoc,
            mul_comm, ]
    simpa [this] using hρhi

  -- Since ρ ≥ 0, we have ρ² ≤ ρ * (T/(B+A)).
  have hρsq : ρ ^ 2 ≤ ρ * (T / (B + A)) := by
    have := mul_le_mul_of_nonneg_left hρcap hρlo
    simpa [pow_two, mul_comm, mul_left_comm, mul_assoc] using this

  -- Hence Aρ + Bρ² ≤ ρ*(A + B*T/(B+A)).
  have hsum_le : A * ρ + B * ρ ^ 2 ≤ ρ * (A + B * (T / (B + A))) := by
    have : B * ρ ^ 2 ≤ B * (ρ * (T / (B + A))) :=
      mul_le_mul_of_nonneg_left hρsq hBpos
    nlinarith [this]

  -- And T/(B+A) ≤ 1 since T ≤ B + A and B + A > 0.
  have hratio_le_one : T / (B + A) ≤ 1 := by
    have hTleAB : T ≤ B + A := by
      have : (1 : ℝ) ≤ B + A := by nlinarith [hApos, hBpos]
      exact le_trans hTle1 this
    have hpos : 0 < B + A := by
      have : (1 : ℝ) ≤ B + A := by nlinarith [hApos, hBpos]
      exact lt_of_lt_of_le (by norm_num) this
    -- monotone division by a positive denom; no `div_le_iff` needed
    have h := div_le_div_of_nonneg_right hTleAB (le_of_lt hpos)
    simpa [div_self (ne_of_gt hpos)] using h

  -- Collapse the coefficient using T/(B+A) ≤ 1, then push ρ ≤ T/(B+A).
  have hsum_le_T : A * ρ + B * ρ ^ 2 ≤ T := by
    have hAB' : A + B * (T / (B + A)) ≤ A + B := by
      nlinarith [hratio_le_one, hBpos]
    have h0 : ρ * (A + B * (T / (B + A))) ≤ ρ * (A + B) :=
      mul_le_mul_of_nonneg_left hAB' hρlo
    have h1 : A * ρ + B * ρ ^ 2 ≤ ρ * (A + B) := le_trans hsum_le h0
    have hABnonneg : 0 ≤ A + B := by nlinarith [hApos, hBpos]
    have h2 : ρ * (A + B) ≤ (T / (B + A)) * (A + B) :=
      mul_le_mul_of_nonneg_right hρcap hABnonneg
    -- (T/(B+A))*(A+B) = T (commutativity + cancel)
    have hmul : (T / (B + A)) * (A + B) = T := by
      have hpos : 0 < B + A := by
        have : (1 : ℝ) ≤ B + A := by nlinarith [hApos, hBpos]
        exact lt_of_lt_of_le (by norm_num) this
      have hne : B + A ≠ 0 := ne_of_gt hpos
      calc
        (T / (B + A)) * (A + B)
            = (T / (B + A)) * (B + A) := by simp [add_comm]
        _ = (T * (B + A)) / (B + A)  := by
              simpa [mul_comm, mul_left_comm, mul_assoc]
                using (div_mul_eq_mul_div T (B + A) (B + A))
        _ = T := by simpa [hne] using (mul_div_cancel T hne)
    exact le_trans h1 (by simpa [hmul] using h2)

  ----------------------------------------------------------------
  -- Step 3: combine
  ----------------------------------------------------------------
  have : (-T) + A * ρ + B * ρ ^ 2 ≤ 0 := by
    -- just rearrange `Aρ + Bρ² ≤ T`
    have : A * ρ + B * ρ ^ 2 ≤ T := hsum_le_T
    linarith
  exact le_trans hbnd this

/-- If `0 < τ < 2`, `0 ≤ lam`, and `0 ≤ ρ ≤ hb_rhoStar τ γ`, then the bracket is nonpositive,
hence `Δ²f ≤ 0` for the 1D convex quadratic. -/
lemma hb_delta2f_nonpos_of_small_rel_step
    (p : HBParams) {lam ρ : ℝ}
    (hτlo : 0 < tau p lam) (hτhi : tau p lam < 2)
    (hConv : 0 ≤ lam)
    (hρlo : 0 ≤ ρ) (hρhi : ρ ≤ hb_rhoStar (tau p lam) p.γ)
    (x x_prev xstar : ℝ)
    (hrel : |x - x_prev| ≤ ρ * |x - xstar|) :
  delta2 (f_at lam (hbStep p lam x x_prev xstar) xstar)
         (f_at lam x xstar) (f_at lam x_prev xstar)
  ≤ 0 := by
  -- Reduce to the one-variable bound and sign of factors
  have hupper :=
    delta2_f_upper_bound_via_rho (p := p) lam x x_prev xstar ρ hρlo hConv hrel
  -- bound the quadratic bracket by ≤ 0 for ρ ≤ ρ⋆
  have hquad :=
    hb_bracket_nonpos (τ := tau p lam) (γ := p.γ) (ρ := ρ)
      hτlo hτhi hρlo hρhi
  -- e^2 is nonnegative; lam/2 is ≥ 0 by convexity
  have he2 : 0 ≤ (x - xstar) ^ 2 := by nlinarith
  have hscale : 0 ≤ lam / 2 := by nlinarith
  -- Thus RHS ≤ 0; so Δ²f ≤ 0.
  have hrhs_nonpos :
      (lam / 2) *
        (tau p lam * (tau p lam - 2) + 2 * |p.γ * (1 - tau p lam) - 1| * ρ
           + (1 + p.γ ^ 2) * ρ ^ 2) * (x - xstar) ^ 2 ≤ 0 := by
    -- first scale the nonpositive bracket by (lam/2) ≥ 0
    have h1 :
        (lam / 2) *
          (tau p lam * (tau p lam - 2) + 2 * |p.γ * (1 - tau p lam) - 1| * ρ
             + (1 + p.γ ^ 2) * ρ ^ 2)
        ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hscale hquad
    -- then multiply by e^2 ≥ 0
    exact mul_nonpos_of_nonpos_of_nonneg h1 he2
  exact le_trans hupper hrhs_nonpos

/-- Close Lemma B for the **affine** capacity `U = a - b f` with `b > 0`:
under the HB small-relative-step condition on a 1D quadratic (convex λ ≥ 0),
we get `Δ²U ≥ 0` deterministically. -/
theorem lemmaB_HB_affine_capacity
    (p : HBParams) {lam a b ρ : ℝ}
    (hτlo : 0 < tau p lam) (hτhi : tau p lam < 2)
    (_hγ : 0 ≤ p.γ ∧ p.γ < 1)
    (hConv : 0 ≤ lam) (hbpos : 0 < b)
    (x x_prev xstar : ℝ)
    (hρlo : 0 ≤ ρ) (hρhi : ρ ≤ hb_rhoStar (tau p lam) p.γ)
    (hrel : |x - x_prev| ≤ ρ * |x - xstar|) :
  let f := f_at lam
  let U := fun x => a - b * f x xstar
  delta2 (U (hbStep p lam x x_prev xstar)) (U x) (U x_prev) ≥ 0 := by
  intro f U

  -- From previous lemma: Δ²f ≤ 0
  have hnonpos :=
    hb_delta2f_nonpos_of_small_rel_step (p := p)
      (lam := lam) (ρ := ρ) hτlo hτhi hConv hρlo hρhi x x_prev xstar hrel
  -- Δ²U = -b * Δ²f; with b>0, this is ≥ 0.
  have hbnn : (-b) ≤ 0 := by have := hbpos; linarith
  have hUeq :
      delta2 (U (hbStep p lam x x_prev xstar)) (U x) (U x_prev)
        = -b *
          delta2 (f (hbStep p lam x x_prev xstar) xstar) (f x xstar) (f x_prev xstar) := by
    simp [delta2, U, f, sub_eq_add_neg, mul_add, mul_comm, mul_left_comm, add_comm, add_left_comm, add_assoc]; ring
  have : delta2 (U (hbStep p lam x x_prev xstar)) (U x) (U x_prev) ≥ 0 := by
    have := mul_nonneg_of_nonpos_of_nonpos hbnn hnonpos
    simpa [hUeq, mul_comm] using this
  simpa using this

/-- **Nonpositivity under the ρ-cap.**
If `0 ≤ ρ ≤ ρ⋆(τ,γ)`, `0 ≤ lam`, `τ:=η·lam ∈ (0,2)`, and `|d| ≤ ρ|e|`,
then `Δ²f ≤ 0`.  Here `e := x−x⋆`, `d := x−x_prev`. -/
lemma delta2_f_nonpos_under_rho
    (p : HBParams) (lam x x_prev xstar ρ : ℝ)
    (hρlo : 0 ≤ ρ) (hConv : 0 ≤ lam)
    (hτlo : 0 < tau p lam) (hτhi : tau p lam < 2)
    (hρcap : ρ ≤ hb_rhoStar (tau p lam) p.γ)
    (hbound : |(x - x_prev)| ≤ ρ * |(x - xstar)|) :
  delta2 (f_at lam (hbStep p lam x x_prev xstar) xstar)
         (f_at lam x xstar) (f_at lam x_prev xstar) ≤ 0 := by
  -- Upper bound via ρ:
  have hUB :=
    delta2_f_upper_bound_via_rho (p := p) lam x x_prev xstar ρ hρlo hConv hbound
  -- The bracket at ρ is ≤ 0 when ρ ≤ ρ⋆:
  have hB :=
    hb_bracket_nonpos (τ := tau p lam) (γ := p.γ) (ρ := ρ)
      hτlo hτhi hρlo hρcap
  -- Since (lam/2) ≥ 0 and e² ≥ 0, RHS ≤ 0.
  -- First record `0 ≤ lam / 2` cleanly, then use it twice below.
  have hlam_nonneg : 0 ≤ lam / 2 := by
    have h2 : 0 ≤ (2 : ℝ) := by norm_num
    exact div_nonneg hConv h2
  have hconst : 0 ≤ (lam / 2) * (x - xstar) ^ 2 :=
    mul_nonneg hlam_nonneg (sq_nonneg _)
  have hRHS_nonpos :
      (lam / 2) *
        ((tau p lam) * ((tau p lam) - 2) + 2 * |p.γ * (1 - tau p lam) - 1| * ρ
           + (1 + p.γ ^ 2) * ρ ^ 2)
        * (x - xstar) ^ 2 ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonneg_of_nonpos
        hlam_nonneg
        hB)
      (sq_nonneg _)
  exact (le_trans hUB hRHS_nonpos)

set_option maxHeartbeats 800000

/-- **Gap version.**
If `0 ≤ eps ≤ 1` and `ρ ≤ (1−eps)·ρ⋆(τ,γ)`, then the bracket admits a margin
`≤ −eps·τ(2−τ)`.  Consequently, under the same HB/ρ hypotheses as above,
Δ²f ≤ − eps * (lam/2) * τ * (2−τ) * e^2 .
-/
lemma delta2_f_gap_under_rho
    (p : HBParams) (lam x x_prev xstar ρ eps : ℝ)
    (hρlo : 0 ≤ ρ) (hConv : 0 ≤ lam)
    (hτlo : 0 < tau p lam) (hτhi : tau p lam < 2)
    (heps0 : 0 ≤ eps) (heps1 : eps ≤ 1)
    (hρcap : ρ ≤ (1 - eps) * hb_rhoStar (tau p lam) p.γ)
    (hbound : |(x - x_prev)| ≤ ρ * |(x - xstar)|) :
  delta2 (f_at lam (hbStep p lam x x_prev xstar) xstar)
         (f_at lam x xstar) (f_at lam x_prev xstar)
  ≤ -(eps) * (lam / 2) * (tau p lam) * (2 - tau p lam) * (x - xstar) ^ 2 := by
  -- Start from the generic ρ-bound
  have hUB :=
    delta2_f_upper_bound_via_rho (p := p) lam x x_prev xstar ρ hρlo hConv hbound
  -- Abbreviations
  set τ := tau p lam
  set γ := p.γ
  set e := x - xstar
  -- Define the quadratic bracket b(r)
  let b : ℝ → ℝ :=
    fun r => τ * (τ - 2) + 2 * |γ * (1 - τ) - 1| * r + (1 + γ ^ 2) * r ^ 2
  -- Write ρ' := (1−eps) ρ⋆ and show b(ρ) ≤ b(ρ')
  -- Use an ASCII identifier for ρ⋆ to avoid unicode parsing issues.
  set rhoStar := hb_rhoStar τ γ
  set ρ'  := (1 - eps) * rhoStar
  -- rhoStar ≥ 0 as in the nonpos proof
  have hrhoStar_nonneg : 0 ≤ rhoStar := by
    have hA : 0 ≤ (1 + γ^2) := by nlinarith [sq_nonneg γ]
    have hC : 0 ≤ (2 * (1 + |γ|)) := by nlinarith [abs_nonneg γ]
    have hBApos : 0 < (1 + γ^2) + (2 * (1 + |γ|)) := by
      have : (1 : ℝ) ≤ (1 + γ^2) + (2 * (1 + |γ|)) := by nlinarith [hA, hC]
      exact lt_of_lt_of_le (by norm_num) this
    have hTnn : 0 ≤ τ * (2 - τ) := by
      have : 0 ≤ (2 - τ) := le_of_lt (sub_pos.mpr hτhi)
      exact mul_nonneg (le_of_lt hτlo) this
    have hdiv := div_nonneg hTnn (le_of_lt hBApos)
    simpa [rhoStar, hb_rhoStar, add_comm, add_left_comm, add_assoc,
           mul_comm, mul_left_comm, mul_assoc] using hdiv
  have hρ'nn : 0 ≤ ρ' := mul_nonneg (sub_nonneg.mpr heps1) hrhoStar_nonneg
  have hmono :
      b ρ ≤ b ρ' := by
    have hρle : ρ ≤ ρ' := hρcap
    have h1 :
      2 * |γ * (1 - τ) - 1| * ρ
        ≤ 2 * |γ * (1 - τ) - 1| * ρ' :=
      mul_le_mul_of_nonneg_left hρle
        (by have := abs_nonneg (γ * (1 - τ) - 1); nlinarith)
    have h2sq : ρ ^ 2 ≤ ρ' ^ 2 := by
      have : |ρ| ≤ |ρ'| := by
        simpa [abs_of_nonneg hρlo, abs_of_nonneg hρ'nn] using hρle
      exact (sq_le_sq.mpr this)
    have h2 :
      (1 + γ ^ 2) * ρ ^ 2 ≤ (1 + γ ^ 2) * ρ' ^ 2 :=
      mul_le_mul_of_nonneg_left h2sq (by nlinarith [sq_nonneg γ])
    dsimp [b]
    exact add_le_add (add_le_add le_rfl h1) h2

  -- Value at ρ⋆ gives:  -τ(2−τ) + [2|…|ρ⋆ + (1+γ²)ρ⋆²] ≤ 0 ⇒ the bracket ≤ τ(2−τ).
  have hStar_nonpos :
      τ * (τ - 2) + 2 * |γ * (1 - τ) - 1| * rhoStar + (1 + γ ^ 2) * rhoStar ^ 2 ≤ 0 :=
    hb_bracket_nonpos (τ := τ) (γ := γ) (ρ := rhoStar)
      hτlo hτhi hrhoStar_nonneg (by simp [rhoStar])

  have h_comb_le_T :
      2 * |γ * (1 - τ) - 1| * rhoStar + (1 + γ ^ 2) * rhoStar ^ 2
        ≤ τ * (2 - τ) := by
    -- Rewrite the bracket to -(τ(2−τ)) + (...) ≤ 0, then add τ(2−τ) to both sides.
    have hTneg : τ * (τ - 2) = -(τ * (2 - τ)) := by ring
    have h' :
        -(τ * (2 - τ)) + (2 * |γ * (1 - τ) - 1| * rhoStar + (1 + γ ^ 2) * rhoStar ^ 2) ≤ 0 := by
      simpa [hTneg, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc]
        using hStar_nonpos
    have := add_le_add_right h' (τ * (2 - τ))
    -- simplify: (−T + X) + T ≤ 0 + T  ⇒  X ≤ T
    simpa [add_comm, add_left_comm, add_assoc] using this

  -- Bound `b ρ'` using `(1 − eps) ≤ 1` and `(1 − eps)^2 ≤ (1 − eps)`.
  have hpow : (1 - eps) ^ 2 ≤ (1 - eps) := by
    have hle1 : (1 - eps) ≤ 1 := by nlinarith
    have hh := (mul_le_mul_of_nonneg_left hle1 (sub_nonneg.mpr heps1)
                : (1 - eps) * (1 - eps) ≤ (1 - eps) * 1)
    simpa [pow_two] using hh
  have hbρ'_le :
      b ρ' ≤ -(τ * (2 - τ)) + (1 - eps) *
        (2 * |γ * (1 - τ) - 1| * rhoStar + (1 + γ ^ 2) * rhoStar ^ 2) := by
    -- bounds for the positive terms at ρ'
    have h1 :
        2 * |γ * (1 - τ) - 1| * ρ'
          ≤ (1 - eps) * (2 * |γ * (1 - τ) - 1| * rhoStar) := by
      have hconst : 0 ≤ 2 * |γ * (1 - τ) - 1| := by
        have := abs_nonneg (γ * (1 - τ) - 1); nlinarith
      simpa [ρ', mul_comm, mul_left_comm, mul_assoc] using
        (mul_le_mul_of_nonneg_left
          (by simp [ρ', mul_comm, mul_left_comm, mul_assoc]) hconst)
    have h2 :
        (1 + γ ^ 2) * ρ' ^ 2
          ≤ (1 - eps) * ((1 + γ ^ 2) * rhoStar ^ 2) := by
      have : ρ' ^ 2 ≤ (1 - eps) * rhoStar ^ 2 := by
        -- (1−eps)^2 ≤ (1−eps)
        simpa [ρ', pow_two, mul_comm, mul_left_comm, mul_assoc]
          using mul_le_mul_of_nonneg_right hpow (sq_nonneg rhoStar)
      have hBnonneg : 0 ≤ 1 + γ ^ 2 := by
        have : 0 ≤ γ ^ 2 := sq_nonneg γ
        nlinarith [this]
      -- Reassociate to match the target shape
      simpa [mul_comm, mul_left_comm, mul_assoc] using
        (mul_le_mul_of_nonneg_left this hBnonneg)
    -- gather the terms and rewrite to the desired form
    have :
        τ * (τ - 2) + 2 * |γ * (1 - τ) - 1| * ρ' + (1 + γ ^ 2) * ρ' ^ 2
          ≤ τ * (τ - 2) + (1 - eps) * (2 * |γ * (1 - τ) - 1| * rhoStar)
              + (1 - eps) * ((1 + γ ^ 2) * rhoStar ^ 2) :=
      add_le_add (add_le_add le_rfl h1) h2
    -- Convert to the target shape step by step
    have hb_raw :
        b ρ' ≤ τ * (τ - 2)
                + (1 - eps) * (2 * |γ * (1 - τ) - 1| * rhoStar)
                + (1 - eps) * ((1 + γ ^ 2) * rhoStar ^ 2) := by
      dsimp [b]
      exact this
    have hTneg : τ * (τ - 2) = -(τ * (2 - τ)) := by ring
    have hfact :
        (1 - eps) * (2 * |γ * (1 - τ) - 1| * rhoStar)
          + (1 - eps) * ((1 + γ ^ 2) * rhoStar ^ 2)
        =
        (1 - eps) *
          (2 * |γ * (1 - τ) - 1| * rhoStar + (1 + γ ^ 2) * rhoStar ^ 2) := by
      -- just factor (1 - eps)
      ring
    -- rewrite the RHS accordingly, avoiding heavy simp
    have hb2 := hb_raw
    -- rewrite τ(τ−2) to −τ(2−τ)
    rw [hTneg] at hb2
    -- reassociate to group the two positive terms together
    rw [add_assoc] at hb2
    -- factor (1−eps) from the grouped terms
    rw [hfact] at hb2
    exact hb2

  -- Collapse with the ρ⋆ bound:  2|…|ρ⋆ + (1+γ²)ρ⋆² ≤ τ(2−τ)
  have hbρ'_final :
      b ρ' ≤ -(eps) * (τ * (2 - τ)) := by
    -- scale the M ≤ T inequality by (1−eps) ≥ 0 then add −T to both sides
    have step' := mul_le_mul_of_nonneg_left h_comb_le_T (sub_nonneg.mpr heps1)
    have hadd := add_le_add_left step' (-(τ * (2 - τ)))
    -- chain with the upper bound at ρ'
    have hstep :
        b ρ' ≤ -(τ * (2 - τ)) + (1 - eps) * (τ * (2 - τ)) :=
      le_trans hbρ'_le hadd
    -- algebra: −T + (1−eps)T = −eps·T
    have hlin :
        -(τ * (2 - τ)) + (1 - eps) * (τ * (2 - τ))
          = -(eps) * (τ * (2 - τ)) := by ring
    -- rewrite explicitly to avoid simp timeouts
    have hstep' := hstep
    rw [hlin] at hstep'
    exact hstep'

  -- monotonicity b(ρ) ≤ b(ρ') and the previous bound
  have hbracket_gap : b ρ ≤ -(eps) * (τ * (2 - τ)) := le_trans hmono hbρ'_final

  -- Push this margin through the (lam/2)*…*e² scaling
  have hlam_nonneg : 0 ≤ lam / 2 := by
    have : 0 ≤ (2:ℝ) := by norm_num
    exact div_nonneg hConv this
  have he2_nonneg : 0 ≤ e ^ 2 := sq_nonneg _
  have hscaled :
      (lam / 2) * b ρ * e ^ 2
        ≤ (lam / 2) * (-(eps) * (τ * (2 - τ))) * e ^ 2 :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hbracket_gap hlam_nonneg)
      he2_nonneg

  -- Combine with the generic upper bound and clean up the RHS form
  have := le_trans hUB hscaled
  -- RHS simplification: (lam/2) * (-(eps)*T) * e^2 = -(eps) * (lam/2) * T * e^2
  simpa [b, τ, γ, e, mul_comm, mul_left_comm, mul_assoc, sub_eq_add_neg] using this

end
end NOC
/-!
Module: NOC.HB.CloseLoop
Summary: HB closed‑loop Δ²f algebra; one‑variable reduction via relative step; Δ²f≤0 ⇒ Δ²U≥0 for affine capacity.
Public entry points: `delta2_f_hb_in_e_d`, `delta2_f_upper_bound_via_rho`, `hb_rhoStar`, `hb_delta2f_nonpos_of_small_rel_step`, `lemmaB_HB_affine_capacity`.
-/
