import Mathlib
import Mathlib.Probability.Martingale.Basic
import Mathlib.Probability.Martingale.Convergence

-- Silence common linter warnings for this file
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unusedSectionVars false

/-!
Module: NOC.Prob.RobbinsSiegmund
Status: scaffolding (no axioms). Declares a 1D almost-supermartingale
convergence lemma as a named target. The proof will be provided once the
supermartingale API is selected.

Mathlib toolkit to finish the 1D Robbins–Siegmund lemma here:
- Conditional expectation algebra (Real):
  * `MeasureTheory.condExp_smul`, `MeasureTheory.condExp_congr_ae`,
    `MeasureTheory.integral_condExp`,
    `MeasureTheory.condExp_mul_of_stronglyMeasurable_left`
    (file: MeasureTheory/Function/ConditionalExpectation/Real.lean)
- Super/submartingale constructors and convergence:
  * `ProbabilityTheory.martingale_of_condExp_sub_eq_zero_nat`
    (file: Probability/Martingale/Basic.lean)
  * Upcrossing + a.e. limit (if needed):
    `MeasureTheory.Submartingale.ae_tendsto_limitProcess`
    (file: Probability/Martingale/Convergence.lean)

The classical RS proof in 1D can also be done directly by normalizing
`Y_n` with a predictable product and showing a supermartingale with a
summable drift term; the above API suffices for either route.
-- end of commented RS_vsum_partial_bound
-/

namespace NOC.Prob
noncomputable section
open Classical MeasureTheory Filter
open scoped ENNReal BigOperators

/-- A lightweight hypothesis record for a 1D Robbins–Siegmund setup. -/
structure RSHypotheses where
  filtration      : Prop
  adapted_nonneg  : Prop      -- `Y_n ≥ 0`, adapted
  ineq            : Prop      -- E[Y_{n+1}|𝓕_n] ≤ (1+u_n)Y_n − v_n + w_n
  summable_u      : Prop
  summable_w      : Prop

/-- Robbins–Siegmund convergence: placeholder statement returning a
conclusion `Prop` so callers can choose the exact convergence style. -/
structure RSConclusion where
  v_sum_finite : Prop
  Y_converges  : Prop

def robbins_siegmund
  (H : RSHypotheses) : RSConclusion :=
  -- Placeholder: to be proved with the selected supermartingale library.
  { v_sum_finite := True, Y_converges := True }

/-!
Auxiliary: Supermartingale a.e. convergence under an L¹ bound.

This is a convenience wrapper around mathlib’s submartingale convergence, applied
to the negation of a supermartingale. It will be useful when instantiating the
Robbins–Siegmund pipeline once we normalize the almost‑supermartingale.
-- end of commented RS_vsum_partial_bound
-/
theorem supermartingale_exists_ae_tendsto_of_bdd
    {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
    {ℱ : Filtration ℕ m0}
    [IsFiniteMeasure μ]
    (f : ℕ → Ω → ℝ)
    (hf : Supermartingale f ℱ μ)
    (R : NNReal)
    (hbdd : ∀ n, eLpNorm (f n) (1 : ℝ≥0∞) μ ≤ (R : ℝ≥0∞)) :
    ∀ᵐ ω ∂ μ, ∃ c, Tendsto (fun n => f n ω) atTop (nhds c) := by
  -- Turn a supermartingale into a submartingale via negation
  have hsub : Submartingale (fun n => - f n) ℱ μ := hf.neg
  -- The L¹ bound is preserved by negation
  have hbdd' : ∀ n, eLpNorm (fun ω => - f n ω) (1 : ℝ≥0∞) μ ≤ (R : ℝ≥0∞) := by
    intro n
    have h_eq :
        eLpNorm (fun ω => - f n ω) (1 : ℝ≥0∞) μ
          = eLpNorm (f n) (1 : ℝ≥0∞) μ := by
      -- switch to `-(f n)` and apply `eLpNorm_neg`
      change eLpNorm (-(f n)) (1 : ℝ≥0∞) μ = eLpNorm (f n) (1 : ℝ≥0∞) μ
      simpa [eLpNorm_neg]
    simpa [h_eq] using hbdd n
  -- Apply the a.e. convergence lemma to the submartingale `-f`
  have hneg :=
    MeasureTheory.Submartingale.exists_ae_tendsto_of_bdd
      (μ := μ) (ℱ := ℱ) (f := fun n => - f n) (R := R) hsub hbdd'
  -- Transport the convergence through the continuous negation map
  filter_upwards [hneg] with ω hω
  rcases hω with ⟨c, hc⟩
  have hcont : Tendsto (fun x : ℝ => - x) (nhds c) (nhds (-c)) :=
    (continuous_neg.tendsto c)
  have : Tendsto (fun n => (fun x : ℝ => - x) (- f n ω)) atTop (nhds (-c)) :=
    hcont.comp hc
  -- Simplify the composed map to obtain a limit for `f n ω`
  exact ⟨-c, by
    -- `fun n => (fun x => -x) (- f n ω)) = fun n => f n ω`
    simpa using this⟩

end
-- end of first NOC.Prob section
 
/-!
## RS normalization wrapper (scaffold)

Provides a small wrapper to carry a supermartingale and an L¹ bound, and to
conclude a.e. convergence via the lemma above. This isolates the purely
martingale‑convergence part from the problem‑specific normalization step.
-- end of commented RS_vsum_partial_bound
-/

namespace NOC.Prob
noncomputable section
open Classical MeasureTheory Filter
open scoped ENNReal

structure RSNormalization
    {Ω : Type*} {m0 : MeasurableSpace Ω} (μ : Measure Ω)
    (ℱ : Filtration ℕ m0) [IsFiniteMeasure μ] where
  g     : ℕ → Ω → ℝ
  super : Supermartingale g ℱ μ
  R     : NNReal
  l1bdd : ∀ n, eLpNorm (g n) (1 : ℝ≥0∞) μ ≤ (R : ℝ≥0∞)

namespace RSNormalization

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
variable {ℱ : Filtration ℕ m0} [IsFiniteMeasure μ]

theorem ae_converges (N : RSNormalization (μ := μ) (ℱ := ℱ)) :
    ∀ᵐ ω ∂ μ, ∃ c, Tendsto (fun n => N.g n ω) atTop (nhds c) :=
  supermartingale_exists_ae_tendsto_of_bdd (f := N.g) N.super N.R N.l1bdd

end RSNormalization

end
end NOC.Prob


/-!
## RS weights and v-sum partial bound

We provide a simple unconditional-expectation route for the Robbins–Siegmund
v-sum bound. We work under a probability measure to avoid carrying `μ univ`.
-/

namespace NOC.Prob
noncomputable section
open Classical MeasureTheory
open scoped BigOperators ENNReal

variable {Ω : Type*} {m0 : MeasurableSpace Ω}
variable (μ : Measure Ω) (ℱ : Filtration ℕ m0)

/-- Deterministic normalization weight: `W n = ∏_{k<n} (1 + u k)`. -/
def RSWeight (u : ℕ → ℝ) (n : ℕ) : ℝ :=
  (Finset.range n).prod (fun k => (1 + u k))

lemma RSWeight_zero (u : ℕ → ℝ) : RSWeight u 0 = 1 := by
  simp [RSWeight]

lemma RSWeight_succ (u : ℕ → ℝ) (n : ℕ) :
    RSWeight u (n+1) = RSWeight u n * (1 + u n) := by
  simpa [RSWeight, mul_comm] using
    (Finset.prod_range_succ (fun k => (1 + u k)) n)

lemma RSWeight_pos_of_nonneg (u : ℕ → ℝ)
    (hu : ∀ k, 0 ≤ u k) (n : ℕ) :
    0 < RSWeight u n := by
  classical
  induction' n with n ih
  · simpa [RSWeight] using (zero_lt_one : (0 : ℝ) < 1)
  · have hpos : 0 < 1 + u n := by
      have one_le : 1 ≤ 1 + u n := by
        have : (0 : ℝ) ≤ u n := hu n
        simpa using add_le_add_left this 1
      exact lt_of_lt_of_le (zero_lt_one : (0 : ℝ) < 1) one_le
    simpa [RSWeight_succ u n, mul_pos, ih, hpos]

section VSUM

variable [IsProbabilityMeasure μ]

variable {Y : ℕ → Ω → ℝ} {u v w : ℕ → ℝ}

lemma RS_expectation_step
    (n : ℕ)
    (hu : ∀ k, 0 ≤ u k)
    (hYn : Integrable (Y n) μ)
    (hYnp1 : Integrable (Y (n+1)) μ)
    (hRS : μ[ Y (n+1) | ℱ n ]
            ≤ᵐ[μ] (fun ω => (1 + u n) * Y n ω - v n + w n)) :
    (∫ ω, Y (n+1) ω ∂ μ) / RSWeight u (n+1)
      ≤ (∫ ω, Y n ω ∂ μ) / RSWeight u n
        - v n / RSWeight u (n+1)
        + w n / RSWeight u (n+1) := by
  have h_int_rhs : Integrable (fun ω => (1 + u n) * Y n ω - v n + w n) μ := by
    have h1 : Integrable (fun ω => (1 + u n) * Y n ω) μ :=
      (hYn.smul (1 + u n))
    have : Integrable (fun _ : Ω => (- v n + w n)) μ := integrable_const _
    -- (1+u)Y - v + w = (1+u)Y + (-v+w)
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h1.add this
  -- Integrate both sides; left simplifies by `integral_condExp`.
  have h_int :=
    (integral_mono_ae (hf := integrable_condExp) (hg := h_int_rhs) (μ := μ) hRS)
  have hLHS : ∫ (ω), μ[ Y (n+1) | ℱ n] ω ∂ μ = ∫ (ω), Y (n+1) ω ∂ μ := by
    simpa using
      (integral_condExp (μ := μ) (m := ℱ n) (hm := (ℱ.le n)) (f := Y (n+1)))
  -- Rewrite the right integral using linearity and constants
  have hRHS :
      ∫ (ω), ((1 + u n) * Y n ω - v n + w n) ∂ μ
        = (1 + u n) * ∫ (ω), Y n ω ∂ μ - v n + w n := by
    have hint1 : Integrable (fun ω => (1 + u n) * Y n ω) μ := (hYn.smul (1 + u n))
    have hint2 : Integrable (fun _ : Ω => (- v n + w n)) μ := integrable_const _
    have h1 : ∫ (ω), (1 + u n) * Y n ω ∂ μ = (1 + u n) * ∫ (ω), Y n ω ∂ μ := by
      simpa using (integral_const_mul (μ := μ) (r := (1 + u n)) (f := fun ω => Y n ω))
    have hconst : ∫ (ω), (- v n + w n) ∂ μ = (- v n + w n) := by
      simpa using integral_const (μ := μ) (- v n + w n)
    have hadd :=
      (integral_add (μ := μ) (f := fun ω => (1 + u n) * Y n ω)
        (g := fun _ => (- v n + w n)) hint1 hint2)
    -- rewrite both integrals
    have hadd' :
        ∫ (ω), (1 + u n) * Y n ω + (- v n + w n) ∂ μ
          = (1 + u n) * ∫ (ω), Y n ω ∂ μ + (- v n + w n) := by
      simpa [h1, hconst]
        using hadd
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hadd'
  -- Combine the integral inequality and divide by the weight
  have hineq :
      (∫ (ω), Y (n+1) ω ∂ μ)
        ≤ (1 + u n) * ∫ (ω), Y n ω ∂ μ - v n + w n := by
    simpa [hLHS, hRHS] using h_int
  -- Divide by `W_{n+1}` and use `W_{n+1} = (1+u n) * W_n`
  have hWpos : 0 < RSWeight u (n+1) := RSWeight_pos_of_nonneg u hu (n+1)
  have hWpos' : 0 < RSWeight u n := RSWeight_pos_of_nonneg u hu n
  have hWsucc := RSWeight_succ u n
  -- rewrite and finish with field algebra
  have hdiv := (div_le_div_of_nonneg_right hineq (le_of_lt hWpos))
  -- simplify the right side divisions
  have hne : (1 + u n) ≠ 0 := ne_of_gt (by
    have one_le : 1 ≤ 1 + u n := by
      have : (0 : ℝ) ≤ u n := hu n
      simpa using add_le_add_left this 1
    exact lt_of_lt_of_le (zero_lt_one : (0 : ℝ) < 1) one_le)
  -- rewrite each term
  have := hdiv
  -- apply rewriting by `hWsucc'` on the first term; constants divide trivially
  have h1 :
      ((1 + u n) * ∫ (ω), Y n ω ∂ μ) / RSWeight u (n+1)
        = (∫ (ω), Y n ω ∂ μ) / RSWeight u n := by
    -- rewrite using `mul_div_mul_right` and `RSWeight_succ`
    have := mul_div_mul_right (∫ (ω), Y n ω ∂ μ) (RSWeight u n) hne
    -- `(∫ Y n) * (1+u n) / ((RSWeight u n) * (1+u n)) = (∫ Y n) / RSWeight u n`
    simpa [mul_comm, mul_left_comm, mul_assoc, RSWeight_succ u n] using this
  have h2 : (- v n + w n) / RSWeight u (n+1)
      = -(v n / RSWeight u (n+1)) + w n / RSWeight u (n+1) := by
    have : (- v n + w n) / RSWeight u (n+1)
        = (- v n) / RSWeight u (n+1) + (w n) / RSWeight u (n+1) := by
      simpa using (add_div (- v n) (w n) (RSWeight u (n+1)))
    simpa [neg_div] using this
  -- Split the RHS division and simplify
  have hsplit :
      ((1 + u n) * ∫ (ω), Y n ω ∂ μ - v n + w n)
        / RSWeight u (n+1)
        = ((1 + u n) * ∫ (ω), Y n ω ∂ μ) / RSWeight u (n+1)
          + ((- v n + w n) / RSWeight u (n+1)) := by
    -- use `(a + b)/c = a/c + b/c`
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
      (add_div ((1 + u n) * ∫ (ω), Y n ω ∂ μ)
        (- v n + w n) (RSWeight u (n+1)))
  -- apply the split to the inequality RHS
  have hdiv' :
      (∫ (ω), Y (n+1) ω ∂ μ) / RSWeight u (n+1)
        ≤ ((1 + u n) * ∫ (ω), Y n ω ∂ μ) / RSWeight u (n+1)
          + ((- v n + w n) / RSWeight u (n+1)) := by
    simpa [hsplit] using hdiv
  -- conclude by rewriting with `h1` and `h2`
  simpa [h1, h2, sub_eq_add_neg, add_assoc] using hdiv'

/-- Telescoping partial-sum bound for `∑ v_n / W_{n+1}` via the RS step.
Assumes `Y_n ≥ 0` a.e. for all `n` to drop the terminal term. -/
lemma RS_vsum_partial_bound
    (N : ℕ)
    (hu : ∀ k, 0 ≤ u k)
    (hY_nonneg : ∀ n, 0 ≤ᵐ[μ] fun ω => Y n ω)
    (hInt : ∀ n ≤ N, Integrable (Y n) μ)
    (hRS : ∀ n < N,
      μ[ Y (n+1) | ℱ n ] ≤ᵐ[μ] (fun ω => (1 + u n) * Y n ω - v n + w n)) :
    ((Finset.range N).sum (fun k => v k / RSWeight u (k+1)))
      ≤ (∫ ω, Y 0 ω ∂ μ) / RSWeight u 0
        + ((Finset.range N).sum (fun k => w k / RSWeight u (k+1))) := by
  classical
  -- Normalized expectations and partial sums
  let S : ℕ → ℝ := fun n => (∫ ω, Y n ω ∂ μ) / RSWeight u n
  let Vsum : ℕ → ℝ := fun n => (Finset.range n).sum (fun k => v k / RSWeight u (k+1))
  let Wsum : ℕ → ℝ := fun n => (Finset.range n).sum (fun k => w k / RSWeight u (k+1))
  -- For all n ≤ N: S n + Vsum n ≤ S 0 + Wsum n
  have hT : ∀ n, n ≤ N → S n + Vsum n ≤ S 0 + Wsum n := by
    intro n
    induction' n with n ih
    · intro _; simp [S, Vsum, Wsum, RSWeight_zero u]
    · intro hle
      have hleN : n ≤ N := Nat.le_trans (Nat.le_succ n) hle
      have hInt_n : Integrable (Y n) μ := hInt n hleN
      have hInt_np1 : Integrable (Y (n+1)) μ := hInt (n+1) hle
      have hltN : n < N := Nat.lt_of_lt_of_le (Nat.lt_succ_self n) hle
      have hstep :=
        RS_expectation_step (μ := μ) (ℱ := ℱ)
          (Y := Y) (u := u) (v := v) (w := w)
          n hu hInt_n hInt_np1 (hRS n hltN)
      have hV : Vsum (n+1) = Vsum n + v n / RSWeight u (n+1) := by
        simp [Vsum, Finset.sum_range_succ, add_comm, add_left_comm, add_assoc]
      have hW : Wsum (n+1) = Wsum n + w n / RSWeight u (n+1) := by
        simp [Wsum, Finset.sum_range_succ, add_comm, add_left_comm, add_assoc]
      have ih' := ih hleN
      calc
        S (n+1) + Vsum (n+1)
            ≤ (S n - v n / RSWeight u (n+1) + w n / RSWeight u (n+1))
                + Vsum (n+1) := by exact add_le_add_right hstep _
        _ = S n + Vsum n + w n / RSWeight u (n+1) := by
              -- rearrange and cancel `-A + A`
              have :
                  (- (v n / RSWeight u (n+1)) + w n / RSWeight u (n+1)) + (Vsum n + v n / RSWeight u (n+1))
                    = Vsum n + w n / RSWeight u (n+1) := by
                have := neg_add_cancel_right (Vsum n + w n / RSWeight u (n+1)) (v n / RSWeight u (n+1))
                -- -A + ((V + B) + A) = V + B
                simpa [add_comm, add_left_comm, add_assoc] using this
              simpa [hV, sub_eq_add_neg, add_comm, add_left_comm, add_assoc, this]
        _ ≤ S 0 + Wsum n + w n / RSWeight u (n+1) := by
              exact add_le_add_right ih' _
        _ = S 0 + Wsum (n+1) := by simpa [hW, add_comm, add_left_comm, add_assoc]
  -- Conclude at n = N
  have hSN_nonneg : 0 ≤ S N := by
    have : 0 ≤ ∫ ω, Y N ω ∂ μ := integral_nonneg_of_ae (hY_nonneg N)
    have hWpos : 0 < RSWeight u N := RSWeight_pos_of_nonneg u hu N
    exact div_nonneg this (le_of_lt hWpos)
  have hTN := hT N (le_rfl)
  -- From `S N + Vsum N ≤ S 0 + Wsum N`, subtract `S N` and drop it using nonnegativity.
  have hV1 : Vsum N ≤ S 0 + Wsum N - S N := by
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using (sub_le_sub_right hTN (S N))
  have : Vsum N ≤ S 0 + Wsum N := by
    have hnegSN : - S N ≤ (0 : ℝ) := by simpa using (neg_nonpos.mpr hSN_nonneg)
    have h2 : S 0 + Wsum N - S N ≤ S 0 + Wsum N := by
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
        (add_le_add_right hnegSN (S 0 + Wsum N))
    exact le_trans hV1 h2
  -- Unfold and finish
  simpa [Vsum, Wsum, S]

end VSUM

/-!
Summability corollary. If the normalized perturbations `(w n / W_{n+1})` form a
summable nonnegative series, then so do the normalized useful-decrease terms
`(v n / W_{n+1})`, under the RS hypotheses.
-/

section VSUM_SUMMABLE

variable [IsProbabilityMeasure μ]

variable {Y : ℕ → Ω → ℝ} {u v w : ℕ → ℝ}

lemma RS_vsum_summable_of_w_summable
    (hu : ∀ k, 0 ≤ u k)
    (hv : ∀ k, 0 ≤ v k)
    (hw : ∀ k, 0 ≤ w k)
    (hY_nonneg : ∀ n, 0 ≤ᵐ[μ] fun ω => Y n ω)
    (hInt : ∀ n, Integrable (Y n) μ)
    (hRS : ∀ n,
      μ[ Y (n+1) | ℱ n ] ≤ᵐ[μ] (fun ω => (1 + u n) * Y n ω - v n + w n))
    (hWsum : Summable (fun k => w k / RSWeight u (k+1))) :
    Summable (fun k => v k / RSWeight u (k+1)) := by
  classical
  -- Nonnegativity of the normalized v/w terms
  have hv_nonneg : ∀ n, 0 ≤ v n / RSWeight u (n+1) := by
    intro n
    have hWpos : 0 < RSWeight u (n+1) := RSWeight_pos_of_nonneg u hu (n+1)
    exact div_nonneg (hv n) (le_of_lt hWpos)
  have hw_nonneg : ∀ n, 0 ≤ w n / RSWeight u (n+1) := by
    intro n
    have hWpos : 0 < RSWeight u (n+1) := RSWeight_pos_of_nonneg u hu (n+1)
    exact div_nonneg (hw n) (le_of_lt hWpos)
  -- For each N, bound the partial sums of v/W by a constant plus the partial sums of w/W
  -- using the RS telescope.
  have h_bound_partial : ∀ N,
      (Finset.range N).sum (fun k => v k / RSWeight u (k+1))
        ≤ (∫ ω, Y 0 ω ∂ μ) / RSWeight u 0
          + (Finset.range N).sum (fun k => w k / RSWeight u (k+1)) := by
    intro N
    have hInt' : ∀ n ≤ N, Integrable (Y n) μ := fun n _ => hInt n
    have hRS' : ∀ n < N,
        μ[ Y (n+1) | ℱ n ] ≤ᵐ[μ] (fun ω => (1 + u n) * Y n ω - v n + w n) := by
      intro n hn; exact hRS n
    simpa using
      (RS_vsum_partial_bound (μ := μ) (ℱ := ℱ)
        (Y := Y) (u := u) (v := v) (w := w)
        N hu hY_nonneg hInt' hRS')
  -- Turn the bound into a uniform upper bound using `tsum` of w/W on the right.
  have hw_tsum_bound : ∀ N,
      (Finset.range N).sum (fun k => w k / RSWeight u (k+1))
        ≤ ∑' k, (w k / RSWeight u (k+1)) := by
    intro N
    simpa using
      (hWsum.sum_le_tsum (s := Finset.range N) (by intro _ _; exact hw_nonneg _))
  -- Combine the two bounds.
  have h_partial_le_c : ∀ N,
      (Finset.range N).sum (fun k => v k / RSWeight u (k+1))
        ≤ (∫ ω, Y 0 ω ∂ μ) / RSWeight u 0 + ∑' k, (w k / RSWeight u (k+1)) := by
    intro N
    have := h_bound_partial N
    exact this.trans <| by
      have := hw_tsum_bound N
      exact add_le_add_left this _
  -- Apply the real-analysis criterion: nonnegative terms with uniformly bounded partial sums are summable.
  -- We use `summable_of_sum_range_le` with constant `c = (∫ Y 0)/W 0 + ∑' w/W`.
  refine (summable_of_sum_range_le
      (f := fun k => v k / RSWeight u (k+1))
      (c := (∫ ω, Y 0 ω ∂ μ) / RSWeight u 0 + ∑' k, (w k / RSWeight u (k+1)))
      (hf := hv_nonneg) (h := ?_))
  intro N
  -- `summable_of_sum_range_le` expects a bound on `∑ i ∈ range N, f i`.
  -- Our `h_partial_le_c` is stated with `Finset.sum (range N) f`.
  simpa [Finset.sum_range] using h_partial_le_c N

end VSUM_SUMMABLE

/-!
Uniform L¹ bound for the normalized drifted process. We define

  Zₙ(ω) := Yₙ(ω) / Wₙ,    with Wₙ = RSWeight u n,
  Vsumₙ := ∑_{k<n} v_k / W_{k+1},
  Wsumₙ := ∑_{k<n} w_k / W_{k+1},
  Gₙ(ω) := Zₙ(ω) + Vsumₙ − Wsumₙ.

Under the RS inequality, nonnegativity Yₙ ≥ 0 a.e., and summability of w/W,
the family (Gₙ) has a uniform L¹ bound.
-/

section VSUM_L1BOUND

variable [IsProbabilityMeasure μ]

variable {Y : ℕ → Ω → ℝ} {u v w : ℕ → ℝ}

/- Helpers: normalized process and drifted version -/
def RSZ (u : ℕ → ℝ) (Y : ℕ → Ω → ℝ) (n : ℕ) : Ω → ℝ :=
  ((RSWeight u n)⁻¹) • (Y n)

def RSVsum (u : ℕ → ℝ) (v : ℕ → ℝ) (n : ℕ) : ℝ :=
  (Finset.range n).sum (fun k => v k / RSWeight u (k+1))

def RSWsum (u : ℕ → ℝ) (w : ℕ → ℝ) (n : ℕ) : ℝ :=
  (Finset.range n).sum (fun k => w k / RSWeight u (k+1))

def RSDrifted (u : ℕ → ℝ) (Y : ℕ → Ω → ℝ) (v w : ℕ → ℝ) (n : ℕ) : Ω → ℝ :=
  fun ω => RSZ u Y n ω + (RSVsum u v n - RSWsum u w n)

lemma RSDrifted_l1_uniform_bound_of_w_summable
    (hu : ∀ k, 0 ≤ u k)
    (hv : ∀ k, 0 ≤ v k)
    (hw : ∀ k, 0 ≤ w k)
    (hY_nonneg : ∀ n, 0 ≤ᵐ[μ] fun ω => Y n ω)
    (hInt : ∀ n, Integrable (Y n) μ)
    (hRS : ∀ n,
      μ[ Y (n+1) | ℱ n ] ≤ᵐ[μ] (fun ω => (1 + u n) * Y n ω - v n + w n))
    (hWsum : Summable (fun k => w k / RSWeight u (k+1))) :
    ∃ R : NNReal, ∀ n : ℕ,
      eLpNorm (RSDrifted u Y v w n) (1 : ENNReal) μ ≤ (R : ENNReal) := by
  classical
  -- Shorthands
  let S : ℕ → ℝ := fun n => (∫ ω, Y n ω ∂ μ) / RSWeight u n
  have hS_nonneg : ∀ n, 0 ≤ S n := by
    intro n
    have : 0 ≤ ∫ ω, Y n ω ∂ μ := integral_nonneg_of_ae (hY_nonneg n)
    have hWpos : 0 < RSWeight u n := RSWeight_pos_of_nonneg u hu n
    exact div_nonneg this (le_of_lt hWpos)
  -- RS telescope: for all N, S N + Vsum N ≤ S 0 + Wsum N
  -- We reprove the induction used in `RS_vsum_partial_bound` here to obtain the stronger form.
  have hSVW : ∀ N, S N + RSVsum u v N ≤ S 0 + RSWsum u w N := by
    classical
    intro N
    -- Define partial sums to mirror the RS step
    let Vsum : ℕ → ℝ := fun n => (Finset.range n).sum (fun k => v k / RSWeight u (k+1))
    let Wsum : ℕ → ℝ := fun n => (Finset.range n).sum (fun k => w k / RSWeight u (k+1))
    have hVsum_def : ∀ n, Vsum n = RSVsum u v n := by intro n; rfl
    have hWsum_def : ∀ n, Wsum n = RSWsum u w n := by intro n; rfl
    -- Main induction building the telescope inequality up to N
    have hT : ∀ n ≤ N, S n + Vsum n ≤ S 0 + Wsum n := by
      intro n
      induction' n with n ih
      · intro _; simp [S, Vsum, Wsum, RSWeight_zero u]
      · intro hle
        have hleN : n ≤ N := Nat.le_trans (Nat.le_succ n) hle
        have hInt_n : Integrable (Y n) μ := hInt n
        have hInt_np1 : Integrable (Y (n+1)) μ := hInt (n+1)
        have hltN : n < N := Nat.lt_of_lt_of_le (Nat.lt_succ_self n) hle
        have hstep :=
          RS_expectation_step (μ := μ) (ℱ := ℱ)
            (Y := Y) (u := u) (v := v) (w := w)
            n hu hInt_n hInt_np1 (hRS n)
        have hV : Vsum (n+1) = Vsum n + v n / RSWeight u (n+1) := by
          simp [Vsum, Finset.sum_range_succ, add_comm, add_left_comm, add_assoc]
        have hW : Wsum (n+1) = Wsum n + w n / RSWeight u (n+1) := by
          simp [Wsum, Finset.sum_range_succ, add_comm, add_left_comm, add_assoc]
        have ih' := ih hleN
        calc
          S (n+1) + Vsum (n+1)
              ≤ (S n - v n / RSWeight u (n+1) + w n / RSWeight u (n+1))
                  + Vsum (n+1) := by exact add_le_add_right hstep _
          _ = S n + Vsum n + w n / RSWeight u (n+1) := by
                -- rearrange and cancel `-A + A`
                have :
                    (- (v n / RSWeight u (n+1)) + w n / RSWeight u (n+1)) + (Vsum n + v n / RSWeight u (n+1))
                      = Vsum n + w n / RSWeight u (n+1) := by
                  have := neg_add_cancel_right (Vsum n + w n / RSWeight u (n+1)) (v n / RSWeight u (n+1))
                  -- -A + ((V + B) + A) = V + B
                  simpa [add_comm, add_left_comm, add_assoc]
                    using this
                simpa [hV, sub_eq_add_neg, add_comm, add_left_comm, add_assoc, this]
          _ ≤ S 0 + Wsum n + w n / RSWeight u (n+1) := by
                exact add_le_add_right ih' _
          _ = S 0 + Wsum (n+1) := by simpa [hW, add_comm, add_left_comm, add_assoc]
    -- Conclude at n = N and rewrite back to RSVsum/RSWsum
    simpa [hVsum_def, hWsum_def] using hT N (le_rfl)
  -- Triangle inequality in L¹ to bound the drifted normalized process
  have hbound : ∀ n,
      eLpNorm (RSDrifted u Y v w n) (1 : ENNReal) μ
        ≤ ENNReal.ofReal (S n + RSVsum u v n + RSWsum u w n) := by
    intro n
    -- measurability pieces
    have hz_int : Integrable (RSZ u Y n) μ := by
      -- `Integrable.smul` applies to the function `Y n` pointwise.
      -- Note `RSZ u Y n = (RSWeight u n)⁻¹ • (Y n)` definally.
      simpa [RSZ, one_div] using (hInt n).smul ((RSWeight u n)⁻¹)
    have hz_meas : AEStronglyMeasurable (RSZ u Y n) μ := hz_int.aestronglyMeasurable
    have hconstV_meas : AEStronglyMeasurable (fun _ => RSVsum u v n) μ := aestronglyMeasurable_const
    have hconstW_meas : AEStronglyMeasurable (fun _ => RSWsum u w n) μ := aestronglyMeasurable_const
    -- eLpNorm(f) ≤ eLpNorm(Z) + eLpNorm(const V) + eLpNorm(const W)
    have h1 :
        eLpNorm (RSDrifted u Y v w n) (1 : ENNReal) μ
          ≤ eLpNorm (fun ω => RSZ u Y n ω + RSVsum u v n) 1 μ
              + eLpNorm (fun _ => RSWsum u w n) 1 μ := by
      have hsum :
          eLpNorm ((fun ω => RSZ u Y n ω + RSVsum u v n) + (fun _ => - RSWsum u w n)) 1 μ
            ≤ eLpNorm (fun ω => RSZ u Y n ω + RSVsum u v n) 1 μ
                + eLpNorm (fun _ => - RSWsum u w n) 1 μ :=
        eLpNorm_add_le (hf := (hz_meas.add hconstV_meas)) (hg := aestronglyMeasurable_const) (hp1 := by norm_num)
      have hadd : (fun ω => RSZ u Y n ω + RSVsum u v n) + (fun _ => - RSWsum u w n)
            = RSDrifted u Y v w n := by
        funext ω; simp [RSDrifted, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
      have hneg_eval :
          eLpNorm (fun _ => - RSWsum u w n) 1 μ = ENNReal.ofReal |RSWsum u w n| := by
        simpa [measure_univ, ENNReal.toReal_one, Real.enorm_eq_ofReal_abs, abs_neg]
          using (eLpNorm_const' (μ := μ) (p := (1 : ENNReal)) (c := - RSWsum u w n)
            (h0 := by simp) (h_top := by simp))
      have hpos_eval :
          eLpNorm (fun _ => RSWsum u w n) 1 μ = ENNReal.ofReal |RSWsum u w n| := by
        simpa [measure_univ, ENNReal.toReal_one, Real.enorm_eq_ofReal_abs]
          using (eLpNorm_const' (μ := μ) (p := (1 : ENNReal)) (c := RSWsum u w n)
            (h0 := by simp) (h_top := by simp))
      have hneg :
          eLpNorm (fun _ => - RSWsum u w n) 1 μ = eLpNorm (fun _ => RSWsum u w n) 1 μ := by
        simpa [hpos_eval] using hneg_eval
      have : eLpNorm (RSDrifted u Y v w n) 1 μ
            ≤ eLpNorm (fun ω => RSZ u Y n ω + RSVsum u v n) 1 μ + eLpNorm (fun _ => RSWsum u w n) 1 μ := by
        have := hsum
        simpa [hadd, hneg] using this
      exact this
    have h2 :
        eLpNorm (fun ω => RSZ u Y n ω + RSVsum u v n) 1 μ
          ≤ eLpNorm (RSZ u Y n) 1 μ + eLpNorm (fun _ => RSVsum u v n) 1 μ := by
      exact eLpNorm_add_le (hf := hz_meas) (hg := hconstV_meas) (hp1 := by norm_num)
    have hsum_eLp : eLpNorm (RSDrifted u Y v w n) 1 μ
        ≤ eLpNorm (RSZ u Y n) 1 μ
            + eLpNorm (fun _ => RSVsum u v n) 1 μ
            + eLpNorm (fun _ => RSWsum u w n) 1 μ := by
      have h12 := add_le_add_right h2 (eLpNorm (fun _ => RSWsum u w n) 1 μ)
      -- combine with h1
      exact h1.trans <| by simpa [add_comm, add_left_comm, add_assoc] using h12
    -- evaluate the three terms
    have hZ_eval : eLpNorm (RSZ u Y n) 1 μ = ENNReal.ofReal (S n) := by
      have hwpos : 0 < RSWeight u n := RSWeight_pos_of_nonneg u hu n
      have hnonneg : 0 ≤ᵐ[μ] RSZ u Y n :=
        (hY_nonneg n).mono (fun ω hω => by
          have : 0 ≤ (RSWeight u n)⁻¹ := by simpa using (inv_nonneg.mpr (le_of_lt hwpos))
          simpa [RSZ, smul_eq_mul, mul_comm] using mul_nonneg this hω)
      -- Compare `∫⁻ ofReal |RSZ|` to `∫⁻ ofReal RSZ` using nonnegativity a.e.
      have h_eq_abs :
          (fun ω => ENNReal.ofReal |RSZ u Y n ω|)
            =ᵐ[μ] (fun ω => ENNReal.ofReal (RSZ u Y n ω)) := by
        refine hnonneg.mono ?_
        intro ω hω; simp [abs_of_nonneg hω]
      have hlin := ofReal_integral_eq_lintegral_ofReal (μ := μ) (f := RSZ u Y n) hz_int hnonneg
      have h_abs_eLp : eLpNorm (RSZ u Y n) 1 μ
          = ∫⁻ ω, ENNReal.ofReal |RSZ u Y n ω| ∂ μ := by
        simp [eLpNorm_one_eq_lintegral_enorm, Real.enorm_eq_ofReal_abs]
      have h_eLp : eLpNorm (RSZ u Y n) 1 μ
          = ∫⁻ ω, ENNReal.ofReal (RSZ u Y n ω) ∂ μ := by
        simpa [h_abs_eLp] using (lintegral_congr_ae h_eq_abs)
      -- compute the integral of RSZ and align with S n
      have hintZ : ∫ ω, RSZ u Y n ω ∂ μ = (RSWeight u n)⁻¹ * ∫ ω, Y n ω ∂ μ := by
        simpa [RSZ, smul_eq_mul] using
          (integral_const_mul (μ := μ) (r := (RSWeight u n)⁻¹) (f := fun ω => Y n ω))
      have : eLpNorm (RSZ u Y n) 1 μ = ENNReal.ofReal ((RSWeight u n)⁻¹ * ∫ ω, Y n ω ∂ μ) := by
        -- from `h_eLp` and `hlin.symm` we get `eLpNorm = ofReal (∫ RSZ)`
        have : eLpNorm (RSZ u Y n) 1 μ = ENNReal.ofReal (∫ ω, RSZ u Y n ω ∂ μ) := by
          simpa [h_eLp] using hlin.symm
        simpa [hintZ]
          using this
      -- rewrite `(RSWeight u n)⁻¹ * ∫ Y n` as `(∫ Y n) / RSWeight u n` to match `S n`
      simpa [S, one_div, mul_comm] using this
    -- Evaluate constants in L¹; drop absolute values using nonnegativity
    have hV_nonneg : 0 ≤ RSVsum u v n := by
      classical
      refine Finset.sum_nonneg ?_
      intro k hk
      have hkpos := RSWeight_pos_of_nonneg u hu (k+1)
      exact div_nonneg (hv k) (le_of_lt hkpos)
    have hW_nonneg : 0 ≤ RSWsum u w n := by
      classical
      refine Finset.sum_nonneg ?_
      intro k hk
      have hkpos := RSWeight_pos_of_nonneg u hu (k+1)
      exact div_nonneg (hw k) (le_of_lt hkpos)
    have hV_eval_abs :
        eLpNorm (fun _ => RSVsum u v n) 1 μ = ENNReal.ofReal |RSVsum u v n| := by
      simpa [measure_univ, ENNReal.toReal_one, Real.enorm_eq_ofReal_abs]
        using (eLpNorm_const' (μ := μ) (p := (1 : ENNReal)) (c := RSVsum u v n)
          (h0 := by simp) (h_top := by simp))
    have hW_eval_abs :
        eLpNorm (fun _ => RSWsum u w n) 1 μ = ENNReal.ofReal |RSWsum u w n| := by
      simpa [measure_univ, ENNReal.toReal_one, Real.enorm_eq_ofReal_abs]
        using (eLpNorm_const' (μ := μ) (p := (1 : ENNReal)) (c := RSWsum u w n)
          (h0 := by simp) (h_top := by simp))
    have hV_eval : eLpNorm (fun _ => RSVsum u v n) 1 μ = ENNReal.ofReal (RSVsum u v n) := by
      simpa [abs_of_nonneg hV_nonneg] using hV_eval_abs
    have hW_eval : eLpNorm (fun _ => RSWsum u w n) 1 μ = ENNReal.ofReal (RSWsum u w n) := by
      simpa [abs_of_nonneg hW_nonneg] using hW_eval_abs
    have htrip : eLpNorm (RSDrifted u Y v w n) 1 μ
        ≤ ENNReal.ofReal (S n) + ENNReal.ofReal (RSVsum u v n) + ENNReal.ofReal (RSWsum u w n) := by
      -- rewrite the three terms in the `hsum_eLp` bound using evaluations, then reorder additions
      have : eLpNorm (RSDrifted u Y v w n) 1 μ
          ≤ ENNReal.ofReal (RSVsum u v n)
              + (ENNReal.ofReal (S n) + ENNReal.ofReal (RSWsum u w n)) := by
        simpa [hZ_eval, hV_eval, hW_eval, add_comm, add_left_comm, add_assoc] using hsum_eLp
      -- reorder to `(ofReal S) + (ofReal RSVsum) + (ofReal RSWsum)`
      simpa [add_comm, add_left_comm, add_assoc]
        using this
    have hS_nonneg' : 0 ≤ S n := hS_nonneg n
    -- fold the triple sum into a single ofReal via two applications of `ofReal_add`
    have hvw_nonneg : 0 ≤ S n + RSVsum u v n := add_nonneg hS_nonneg' hV_nonneg
    have hstep1 :
        ENNReal.ofReal (S n) + ENNReal.ofReal (RSVsum u v n)
          = ENNReal.ofReal (S n + RSVsum u v n) := by
      simpa [ENNReal.ofReal_add hS_nonneg' hV_nonneg]
    have hstep2 :
        ENNReal.ofReal (S n + RSVsum u v n) + ENNReal.ofReal (RSWsum u w n)
          = ENNReal.ofReal (S n + RSVsum u v n + RSWsum u w n) := by
      simpa [add_comm, add_left_comm, add_assoc]
        using (ENNReal.ofReal_add hvw_nonneg hW_nonneg).symm
    -- Convert the triple-ofReal bound into a single ofReal using two `ofReal_add` steps
    have hsumLe :
        eLpNorm (RSDrifted u Y v w n) 1 μ
          ≤ ENNReal.ofReal (S n + RSVsum u v n + RSWsum u w n) := by
      -- start from `htrip` and rewrite the RHS via `hstep1` and `hstep2`
      have :
          ENNReal.ofReal (S n) + ENNReal.ofReal (RSVsum u v n) + ENNReal.ofReal (RSWsum u w n)
            = ENNReal.ofReal (S n + RSVsum u v n + RSWsum u w n) := by
        -- fold (A + B) then fold with C
        calc
          ENNReal.ofReal (S n) + ENNReal.ofReal (RSVsum u v n) + ENNReal.ofReal (RSWsum u w n)
              = (ENNReal.ofReal (S n) + ENNReal.ofReal (RSVsum u v n)) + ENNReal.ofReal (RSWsum u w n) := by
                    simp [add_comm, add_left_comm, add_assoc]
          _   = ENNReal.ofReal (S n + RSVsum u v n) + ENNReal.ofReal (RSWsum u w n) := by
                    simpa [hstep1]
          _   = ENNReal.ofReal (S n + RSVsum u v n + RSWsum u w n) := by
                    have h := ENNReal.ofReal_add hvw_nonneg hW_nonneg
                    simpa [add_comm, add_left_comm, add_assoc] using h.symm
      simpa [this] using htrip
    exact hsumLe
  -- Upgrade to a uniform bound using RS telescope and summability of w/W.
  have hWsum_le : ∀ n, RSWsum u w n ≤ ∑' k, w k / RSWeight u (k+1) := by
    intro n
    simpa using
      (hWsum.sum_le_tsum (s := Finset.range n)
        (by intro k hk; have hkpos := RSWeight_pos_of_nonneg u hu (k+1); exact div_nonneg (hw k) (le_of_lt hkpos)))
  have hS0 : S 0 = (∫ ω, Y 0 ω ∂ μ) / RSWeight u 0 := rfl
  -- Define the final constant and package it as NNReal
  let Cfin : ℝ≥0∞ :=
    ENNReal.ofReal ((∫ ω, Y 0 ω ∂ μ) / RSWeight u 0)
      + (2 : ℝ≥0∞) * ENNReal.ofReal (∑' k, w k / RSWeight u (k+1))
  have hC_finite : Cfin < ∞ := by
    -- all terms are finite in probability measure with integrable Y and summable w/W
    have : (ENNReal.ofReal ((∫ ω, Y 0 ω ∂ μ) / RSWeight u 0)) < ∞ := by simp
    have : (2 : ℝ≥0∞) * ENNReal.ofReal (∑' k, w k / RSWeight u (k+1)) < ∞ := by
      -- 2 * ofReal < ∞ since ofReal finite
      have : ENNReal.ofReal (∑' k, w k / RSWeight u (k+1)) < ∞ := by simp
      exact ENNReal.mul_lt_top_iff.2 (Or.inl ⟨by simp, this⟩)
    exact ENNReal.add_lt_top.mpr ⟨by simp, this⟩
  have hC_top : Cfin ≠ ∞ := ne_of_lt hC_finite
  let R : NNReal := ENNReal.toNNReal Cfin
  have hR_coe : (R : ℝ≥0∞) = Cfin := ENNReal.coe_toNNReal hC_top
  -- Final uniform bound
  refine ⟨R, ?_⟩
  intro n
  -- from hbound and RS telescope: S n + Vsum n ≤ S 0 + Wsum n
  have : ENNReal.ofReal (S n + RSVsum u v n + RSWsum u w n)
      ≤ ENNReal.ofReal (S 0 + 2 * RSWsum u w n) := by
    have := hSVW n
    -- S n + Vsum n ≤ S 0 + Wsum n ⇒ S n + Vsum n + Wsum n ≤ S 0 + 2 Wsum n
    have : S n + RSVsum u v n + RSWsum u w n ≤ S 0 + 2 * RSWsum u w n := by
      have := add_le_add_right this (RSWsum u w n)
      simpa [two_mul, add_comm, add_left_comm, add_assoc, sub_eq_add_neg]
        using this
    exact ENNReal.ofReal_le_ofReal this
  have h_le_split : eLpNorm (RSDrifted u Y v w n) (1 : ENNReal) μ
      ≤ ENNReal.ofReal (S 0) + (2 : ℝ≥0∞) * ENNReal.ofReal (RSWsum u w n) := by
    -- rewrite `ofReal (S0 + 2 * Wsum)` into `ofReal S0 + 2 * ofReal Wsum`
    have hS0_nonneg : 0 ≤ S 0 := by
      have : 0 ≤ ∫ ω, Y 0 ω ∂ μ := integral_nonneg_of_ae (hY_nonneg 0)
      have hW0pos : 0 < RSWeight u 0 := RSWeight_pos_of_nonneg u hu 0
      exact div_nonneg this (le_of_lt hW0pos)
    have hW_nonneg' : 0 ≤ RSWsum u w n := by
      classical
      refine Finset.sum_nonneg ?_
      intro k hk; have hkpos := RSWeight_pos_of_nonneg u hu (k+1); exact div_nonneg (hw k) (le_of_lt hkpos)
    have h2nonneg : 0 ≤ (2 : ℝ) := by norm_num
    have h_ofAdd :
        ENNReal.ofReal (S 0 + 2 * RSWsum u w n)
          = ENNReal.ofReal (S 0) + ENNReal.ofReal (2 * RSWsum u w n) := by
      simpa [ENNReal.ofReal_add hS0_nonneg (mul_nonneg h2nonneg hW_nonneg')]
    have h_ofMul : ENNReal.ofReal (2 * RSWsum u w n)
        = (2 : ℝ≥0∞) * ENNReal.ofReal (RSWsum u w n) := by
      simpa [ENNReal.ofReal_mul, h2nonneg, hW_nonneg']
    have hrewrite : ENNReal.ofReal (S 0 + 2 * RSWsum u w n)
        = ENNReal.ofReal (S 0) + (2 : ℝ≥0∞) * ENNReal.ofReal (RSWsum u w n) := by
      simpa [h_ofAdd, h_ofMul]
    -- combine with the previous bound
    have hprev : eLpNorm (RSDrifted u Y v w n) (1 : ENNReal) μ
        ≤ ENNReal.ofReal (S 0 + 2 * RSWsum u w n) := (hbound n).trans this
    simpa [hrewrite]
      using hprev
  -- replace Wsum n by its tsum upper bound and fold into C_final
  have : eLpNorm (RSDrifted u Y v w n) (1 : ENNReal) μ
      ≤ ENNReal.ofReal (S 0) + (2 : ℝ≥0∞) * ENNReal.ofReal (∑' k, w k / RSWeight u (k+1)) := by
    -- monotonicity of ofReal and multiplication by 2 in ℝ≥0∞
    have hmono : ENNReal.ofReal (RSWsum u w n) ≤ ENNReal.ofReal (∑' k, w k / RSWeight u (k+1)) :=
      ENNReal.ofReal_le_ofReal (hWsum_le n)
    exact h_le_split.trans (add_le_add_left (mul_le_mul_left' hmono (2 : ℝ≥0∞)) _)
  -- cast to final constant Cb
  simpa [hR_coe, hS0, add_comm, add_left_comm, add_assoc]

end VSUM_L1BOUND

end
end NOC.Prob


/-!
## RS supermartingale wiring and convergence helper

We now connect the RS inequality to a supermartingale structure on the
normalized, drifted process `Gₙ := Zₙ + Vsumₙ − Wsumₙ` and provide a
normalization constructor to obtain a.e. convergence under the L¹ bound.
-/

namespace NOC.Prob
noncomputable section
open Classical MeasureTheory Filter
open scoped ENNReal

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
variable {ℱ : Filtration ℕ m0}

variable {Y : ℕ → Ω → ℝ} {u v w : ℕ → ℝ}

-- Small algebraic helper: cancel symmetric ±a and ±b around a core term
private lemma add_cancel_combo (a b c d : ℝ) :
    a + (b + (c + (-b + (-a + d)))) = c + d := by
  ring

/-- Under RS hypotheses and adaptedness/integrability of `Y`, the drifted normalized
process is a supermartingale. -/
lemma RSDrifted_supermartingale_of_RS
    [IsFiniteMeasure μ]
    (hAdapt : Adapted ℱ Y)
    (hInt : ∀ n, Integrable (Y n) μ)
    (hu : ∀ k, 0 ≤ u k)
    (hRS : ∀ n,
      μ[ Y (n+1) | ℱ n ] ≤ᵐ[μ] (fun ω => (1 + u n) * Y n ω - v n + w n)) :
    Supermartingale (RSDrifted (u := u) (Y := Y) (v := v) (w := w)) ℱ μ := by
  classical
  -- Unfold the process
  let G : ℕ → Ω → ℝ := fun n ω => RSZ u Y n ω + (RSVsum u v n - RSWsum u w n)
  -- Adaptedness: RSZ uses Y n with scalar; constants are measurable
  have hZ_meas : ∀ n, StronglyMeasurable[ℱ n] (RSZ u Y n) := by
    intro n
    -- (ω ↦ (RSWeight u n)⁻¹ * Y n ω) is strongly measurable
    have hc : StronglyMeasurable[ℱ n] (fun _ : Ω => (RSWeight u n)⁻¹) := by
      classical exact stronglyMeasurable_const
    simpa [RSZ, one_div, smul_eq_mul, Pi.mul_apply]
      using hc.mul (hAdapt n)
  have hG_adapted : Adapted ℱ G := by
    intro n
    have hconst : StronglyMeasurable[ℱ n] (fun _ : Ω => RSVsum u v n - RSWsum u w n) := by
      classical exact stronglyMeasurable_const
    have hsum : StronglyMeasurable[ℱ n]
        (fun ω => RSZ u Y n ω + (RSVsum u v n - RSWsum u w n)) :=
      (hZ_meas n).add hconst
    simpa [G, RSDrifted, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
      using hsum
  -- Integrability: Z from Y; constants integrable
  have hZ_int : ∀ n, Integrable (RSZ u Y n) μ := by
    intro n; simpa [RSZ, one_div] using (hInt n).smul ((RSWeight u n)⁻¹)
  have hG_int : ∀ n, Integrable (G n) μ := by
    intro n
    have hconst : Integrable (fun _ : Ω => RSVsum u v n - RSWsum u w n) μ := integrable_const _
    simpa [G, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
      using (hZ_int n).add hconst
  -- Supermartingale increment: E[G_{n+1}|ℱ n] ≤ G_n a.e.
  have hstep : ∀ n,
      μ[ G (n+1) | ℱ n ] ≤ᵐ[μ] G n := by
    intro n
    -- Expand G_{n+1} and push conditional expectation inside.
    have h1 : μ[ RSZ u Y (n+1) | ℱ n]
              =ᵐ[μ] (fun ω => (RSWeight u (n+1))⁻¹ * μ[ Y (n+1) | ℱ n ] ω) := by
      -- condExp for scalar smul
      simpa [RSZ, one_div, Pi.mul_apply, smul_eq_mul]
        using (condExp_smul (μ := μ) (m := ℱ n)
                (c := (RSWeight u (n+1))⁻¹) (f := Y (n+1)))
    -- Assemble μ[G_{n+1}|ℱ n] via linearity and constants
    have hμGnp1 : μ[ G (n+1) | ℱ n]
          =ᵐ[μ]
        (fun ω => (RSWeight u (n+1))⁻¹ * μ[ Y (n+1) | ℱ n ] ω
                    + RSVsum u v (n+1) - RSWsum u w (n+1)) := by
      -- Break G into RSZ + constV - constW and push condExp through
      have h_add1 := condExp_add
        (μ := μ) (m := ℱ n)
        (hf := (hZ_int (n+1))) (hg := integrable_const _)
        (f := RSZ u Y (n+1)) (g := fun _ => RSVsum u v (n+1))
      have h_add2 := condExp_add
        (μ := μ) (m := ℱ n)
        (hf := ((hZ_int (n+1)).add (integrable_const _))) (hg := integrable_const _)
        (f := (fun ω => RSZ u Y (n+1) ω + RSVsum u v (n+1)))
        (g := (fun _ => - RSWsum u w (n+1)))
      -- Constants under condExp
      have hconstV : μ[(fun _ => RSVsum u v (n+1)) | ℱ n]
                      =ᵐ[μ] (fun _ => RSVsum u v (n+1)) := by
        exact Filter.EventuallyEq.of_eq
          (condExp_const (μ := μ) (m := ℱ n) (hm := ℱ.le n)
            (c := RSVsum u v (n+1)))
      have hconstWneg : μ[(fun _ => - RSWsum u w (n+1)) | ℱ n]
                      =ᵐ[μ] (fun _ => - RSWsum u w (n+1)) := by
        exact Filter.EventuallyEq.of_eq
          (condExp_const (μ := μ) (m := ℱ n) (hm := ℱ.le n)
            (c := - RSWsum u w (n+1)))
      -- A simpler route: use a single constant C and one `condExp_add`
      let C : Ω → ℝ := fun _ => RSVsum u v (n+1) - RSWsum u w (n+1)
      have haddC := condExp_add
        (μ := μ) (m := ℱ n)
        (hf := (hZ_int (n+1))) (hg := integrable_const _)
        (f := RSZ u Y (n+1)) (g := C)
      have hconstC : μ[C | ℱ n] =ᵐ[μ] C :=
        Filter.EventuallyEq.of_eq
          (condExp_const (μ := μ) (m := ℱ n) (hm := ℱ.le n)
            (c := RSVsum u v (n+1) - RSWsum u w (n+1)))
      filter_upwards [haddC, h1, hconstC] with ω haddω hZω hCω
      -- Simplify the right-hand side using the AE equalities for RSZ and the constant C
      have hsum :
          μ[(fun ω => RSZ u Y (n+1) ω + C ω) | ℱ n] ω
            = (RSWeight u (n+1))⁻¹ * μ[ Y (n+1) | ℱ n ] ω + C ω := by
        -- from `haddω`, rewrite both summands using `hZω` and `hCω`
        have := haddω
        -- turn the sum of condExps into pointwise sum and rewrite pieces
        simpa [Pi.add_apply, hZω, hCω]
          using this
      -- Now rewrite back to `G (n+1)` and `C` by definition
      have : μ[ G (n+1) | ℱ n ] ω
            = (RSWeight u (n+1))⁻¹ * μ[ Y (n+1) | ℱ n ] ω
                + RSVsum u v (n+1) - RSWsum u w (n+1) := by
        simpa [G, C, sub_eq_add_neg, Pi.add_apply, add_comm, add_left_comm, add_assoc]
          using hsum
      simpa [this]
    -- Use RS inequality scaled by (W_{n+1})⁻¹
    have hRS' :
        (fun ω => (RSWeight u (n+1))⁻¹ * μ[ Y (n+1) | ℱ n ] ω)
          ≤ᵐ[μ]
        (fun ω => (RSWeight u (n+1))⁻¹ * ((1 + u n) * Y n ω - v n + w n)) := by
      refine hRS n |>.mono ?_ ; intro ω hω; exact mul_le_mul_of_nonneg_left hω (by
        -- positivity of the scalar (inverse weight)
        have hpos : 0 < RSWeight u (n+1) := RSWeight_pos_of_nonneg u hu (n+1)
        exact le_of_lt (by simpa [one_div] using inv_pos.mpr hpos))
    -- Replace μ[Y n|ℱ n] with Y n a.e. to rewrite target into G n
    have hY_eq : μ[ Y n | ℱ n] = fun ω => Y n ω := by
      -- `Y n` is ℱ n‑measurable and integrable
      have hm : StronglyMeasurable[ℱ n] (Y n) := hAdapt n
      simpa using
        (condExp_of_stronglyMeasurable (μ := μ) (m := ℱ n)
          (hm := (ℱ.le n)) (hf := hm) (hfi := hInt n))
    -- Prepare the algebra on the RHS after splitting V/W step
    have hsplitV : RSVsum u v (n+1) = RSVsum u v n + v n / RSWeight u (n+1) := by
      simp [RSVsum, Finset.sum_range_succ, add_comm, add_left_comm, add_assoc]
    have hsplitW : RSWsum u w (n+1) = RSWsum u w n + w n / RSWeight u (n+1) := by
      simp [RSWsum, Finset.sum_range_succ, add_comm, add_left_comm, add_assoc]
    -- Conclude: μ[G_{n+1}|ℱ n] ≤ G_n by bounding the Y-part and simplifying
    -- First, upgrade `hμGnp1` using `hRS'` by adding the constant term on both sides
    have hle_aux :
        μ[ G (n+1) | ℱ n ]
          ≤ᵐ[μ]
        (fun ω =>
          (RSWeight u (n+1))⁻¹ * ((1 + u n) * Y n ω - v n + w n)
            + RSVsum u v (n+1) - RSWsum u w (n+1)) := by
      filter_upwards [hμGnp1, hRS'] with ω hGω hYω_le
      -- Rewrite μ[G(n+1)|] and add the same constant `(RSVsum−RSWsum)` to both sides
      have hrewrite : μ[ G (n+1) | ℱ n ] ω
            = (RSWeight u (n+1))⁻¹ * μ[ Y (n+1) | ℱ n ] ω
                + (RSVsum u v (n+1) - RSWsum u w (n+1)) := by
        simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hGω
      -- Apply monotonicity of addition
      have hstep := add_le_add_right hYω_le (RSVsum u v (n+1) - RSWsum u w (n+1))
      simpa [hrewrite, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
        using hstep
    -- Now rewrite the RHS to `G n` pointwise
    have hWsucc : RSWeight u (n+1) = RSWeight u n * (1 + u n) := RSWeight_succ u n
    have hdiv_simplify : ∀ ω,
        (RSWeight u (n+1))⁻¹ * ((1 + u n) * Y n ω)
          = (RSWeight u n)⁻¹ * (Y n ω) := by
      intro ω
      have hne : (1 + u n) ≠ 0 := by
        have one_le : 1 ≤ 1 + u n := by
          have : (0 : ℝ) ≤ u n := hu n
          simpa using add_le_add_left this 1
        exact ne_of_gt (lt_of_lt_of_le (zero_lt_one : (0 : ℝ) < 1) one_le)
      have hdivtmp : ((1 + u n) * Y n ω) / (RSWeight u (n+1))
              = (Y n ω) / (RSWeight u n) := by
        simpa [hWsucc, mul_comm, mul_left_comm, mul_assoc] using
          (mul_div_mul_right (Y n ω) (RSWeight u n) hne)
      simpa [one_div, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hdivtmp
    -- simplify the RHS to `G n` via pointwise equality
    let rhs := fun ω =>
      (RSWeight u (n+1))⁻¹ * ((1 + u n) * Y n ω - v n + w n)
        + RSVsum u v (n+1) - RSWsum u w (n+1)
    have hR : rhs =ᵐ[μ] (fun ω => (RSWeight u n)⁻¹ * Y n ω + RSVsum u v n - RSWsum u w n) := by
      refine Filter.Eventually.of_forall ?_
      intro ω
      have hsim := hdiv_simplify ω
      -- `simp` plus `add_cancel_combo` removes the ±v/W and ±w/W pairs
      have : rhs ω
          = (RSWeight u n)⁻¹ * Y n ω + RSVsum u v n - RSWsum u w n := by
        -- expand and cancel
        have hcore :
            (v n) * (RSWeight u (n+1))⁻¹
              + ((RSWeight u (n+1))⁻¹ * (w n)
                + ((RSWeight u (n+1))⁻¹ * ((1 + u n) * Y n ω)
                  + (-(w n * (RSWeight u (n+1))⁻¹)
                    + (-((RSWeight u (n+1))⁻¹ * (v n)) + - RSWsum u w n))))
              = (RSWeight u n)⁻¹ * Y n ω + - RSWsum u w n := by
          have hc :
              (v n) * (RSWeight u (n+1))⁻¹
                + ((RSWeight u (n+1))⁻¹ * (w n)
                  + ((RSWeight u (n+1))⁻¹ * ((1 + u n) * Y n ω)
                    + (-(w n * (RSWeight u (n+1))⁻¹)
                      + (-((RSWeight u (n+1))⁻¹ * (v n)) + - RSWsum u w n))))
                = (RSWeight u (n+1))⁻¹ * ((1 + u n) * Y n ω) + - RSWsum u w n := by
            simpa [mul_comm, mul_left_comm, mul_assoc, sub_eq_add_neg]
              using add_cancel_combo
                ((v n) * (RSWeight u (n+1))⁻¹)
                ((RSWeight u (n+1))⁻¹ * (w n))
                ((RSWeight u (n+1))⁻¹ * ((1 + u n) * Y n ω))
                (- RSWsum u w n)
          simpa [hsim] using hc
        -- use the core identity inside the expanded rhs
        have := hcore
        -- finish by unfolding `rhs`, splitting sums, and rewriting the Y-term
        simpa [rhs, G, RSZ, one_div, smul_eq_mul, Pi.mul_apply, sub_eq_add_neg,
               hsplitV, hsplitW, add_comm, add_left_comm, add_assoc, hsim,
               mul_add, div_eq_mul_inv]
          using this
      simpa using this
    have hRle : rhs ≤ᵐ[μ] G n := by
      refine hR.mono ?_
      intro ω hω
      -- Rewrite both sides to the same expression and conclude by rfl
      simpa [hω, G, RSZ, one_div, smul_eq_mul, Pi.mul_apply,
             sub_eq_add_neg, add_comm, add_left_comm, add_assoc]
    exact hle_aux.trans hRle
  -- Assemble supermartingale (record literal), rewriting `G` to `RSDrifted`
  -- Field 1: adapted
  refine ⟨?hadapt, ?hcond, ?hint⟩
  · intro n
    simpa [G, RSDrifted] using hG_adapted n
  -- Field 2: supermartingale monotone field ∀ i ≤ j
  · intro i j hij
    -- Prove for k = j - i by induction on k, keeping i fixed
    have : ∀ k, μ[RSDrifted u Y v w (i + k) | ℱ i] ≤ᵐ[μ] RSDrifted u Y v w i := by
      intro k
      induction' k with k ih
      · -- k = 0
        -- condExp_of_stronglyMeasurable on G i, then rewrite to RSDrifted
        have h_eqGi : μ[G i | ℱ i] = G i :=
          condExp_of_stronglyMeasurable (μ := μ) (m := ℱ i)
            (hm := ℱ.le i) (hf := hG_adapted i) (hfi := hG_int i)
        have hEqRS : μ[RSDrifted u Y v w i | ℱ i] = RSDrifted u Y v w i := by
          simpa [G, RSDrifted] using h_eqGi
        exact (Filter.EventuallyEq.of_eq hEqRS).mono (by intro _ h; simpa [h])
      · -- step k → k+1
        -- tower with j := i + k
        have htower :
            μ[ μ[G (i + k + 1) | ℱ (i + k)] | ℱ i ]
              =ᵐ[μ] μ[ G (i + k + 1) | ℱ i ] := by
          simpa using
            (condExp_condExp_of_le (μ := μ)
              (m₁ := (ℱ i)) (m₂ := (ℱ (i + k))) (m₀ := m0)
              (hm₁₂ := ℱ.mono (Nat.le_add_right _ _))
              (hm₂ := ℱ.le (i + k)))
        -- monotonicity using the one-step bound at level i+k
        have hmono :
            μ[ μ[G (i + k + 1) | ℱ (i + k)] | ℱ i ]
              ≤ᵐ[μ] μ[ G (i + k) | ℱ i ] := by
          refine condExp_mono
            (μ := μ) (m := ℱ i)
            (hf := integrable_condExp (μ := μ) (m := ℱ (i + k)) (f := G (i + k + 1)))
            (hg := hG_int (i + k))
            (hfg := ?_)
          simpa using hstep (i + k)
        -- align μ[G (i+k)|ℱ i] with μ[RSDrifted (i+k)|ℱ i]
        have hGeqRS : (fun ω => G (i + k) ω) = (RSDrifted u Y v w (i + k)) := by
          funext ω; simp [G, RSDrifted, sub_eq_add_neg]
        have hce_congr : μ[G (i + k) | ℱ i] =ᵐ[μ] μ[RSDrifted u Y v w (i + k) | ℱ i] :=
          condExp_congr_ae (μ := μ) (m := ℱ i) (h := Filter.EventuallyEq.of_eq hGeqRS)
        -- Build AE inequalities instead of pointwise chaining
        have hstepG : μ[G (i + k + 1) | ℱ i] ≤ᵐ[μ] μ[G (i + k) | ℱ i] := by
          filter_upwards [htower, hmono] with ω ht hm
          simpa [ht] using hm
        have htoRS_k : μ[G (i + k) | ℱ i] ≤ᵐ[μ] μ[RSDrifted u Y v w (i + k) | ℱ i] :=
          (hce_congr).mono (by intro ω h; simpa [h])
        have hG_to_RS_k : μ[G (i + k + 1) | ℱ i] ≤ᵐ[μ] μ[RSDrifted u Y v w (i + k) | ℱ i] :=
          hstepG.trans htoRS_k
        have hfinalG : μ[G (i + k + 1) | ℱ i] ≤ᵐ[μ] RSDrifted u Y v w i :=
          hG_to_RS_k.trans ih
        -- Convert the left from G to RSDrifted at (i+k+1)
        have hce_congr_step : μ[G (i + k + 1) | ℱ i] =ᵐ[μ]
            μ[RSDrifted u Y v w (i + k + 1) | ℱ i] := by
          have hGeqRS' : (fun ω => G (i + k + 1) ω) = RSDrifted u Y v w (i + k + 1) := by
            funext ω; simp [G, RSDrifted, sub_eq_add_neg]
          exact condExp_congr_ae (μ := μ) (m := ℱ i) (h := Filter.EventuallyEq.of_eq hGeqRS')
        -- obtain the desired AE inequality
        have hfinalRS : μ[RSDrifted u Y v w (i + k + 1) | ℱ i] ≤ᵐ[μ] RSDrifted u Y v w i := by
          filter_upwards [hce_congr_step, hfinalG] with ω hce hle
          -- rewrite the left via the AE equality and use `hle`
          simpa [hce] using hle
        exact hfinalRS
    have hdecomp : i + (j - i) = j := Nat.add_sub_of_le hij
    simpa [hdecomp] using this (j - i)
  -- Field 3: integrable
  · intro n
    -- Unfold the RSDrifted spelling and apply Integrable.add
    change Integrable (fun ω => RSZ u Y n ω + (RSVsum u v n - RSWsum u w n)) μ
    exact (hZ_int n).add (integrable_const _)

/-- Package the RS normalization as a `RSNormalization` instance under the
summability/L¹ bound and conclude a.e. convergence for the drifted normalized
process. -/
theorem RSDrifted_ae_converges_of_RS
    [IsProbabilityMeasure μ]
    (hAdapt : Adapted ℱ Y)
    (hInt : ∀ n, Integrable (Y n) μ)
    (hY_nonneg : ∀ n, 0 ≤ᵐ[μ] fun ω => Y n ω)
    (hu : ∀ k, 0 ≤ u k) (hv : ∀ k, 0 ≤ v k) (hw : ∀ k, 0 ≤ w k)
    (hRS : ∀ n,
      μ[ Y (n+1) | ℱ n ] ≤ᵐ[μ] (fun ω => (1 + u n) * Y n ω - v n + w n))
    (hWsum : Summable (fun k => w k / RSWeight u (k+1))) :
    ∀ᵐ ω ∂ μ, ∃ c, Tendsto (fun n => RSDrifted u Y v w n ω) atTop (nhds c) := by
  classical
  -- Build the supermartingale and the L¹ bound, package into RSNormalization and conclude.
  have hSuper := RSDrifted_supermartingale_of_RS (μ := μ) (ℱ := ℱ)
                    (Y := Y) (u := u) (v := v) (w := w)
                    hAdapt hInt hu hRS
  obtain ⟨R, hL1⟩ := RSDrifted_l1_uniform_bound_of_w_summable (μ := μ) (ℱ := ℱ)
                        (Y := Y) (u := u) (v := v) (w := w)
                        hu hv hw hY_nonneg hInt hRS hWsum
  -- Package
  refine
    (RSNormalization.ae_converges
    (N := { g := RSDrifted u Y v w, super := hSuper, R := R, l1bdd := hL1 }))

end
end NOC.Prob


/-!
## TTSA wiring aliases (export RS helper under `NOC.TTSA`)

This section provides a light alias for the RS a.e. convergence helper under
the `NOC.TTSA` namespace so callers in the TTSA layer can depend on a stable
entry point without importing or qualifying the full probability module.

Why this exists
- Decouples the TTSA layer from internal names like `RSWeight`/`RSDrifted`.
- If internals move, TTSA code can keep calling this alias.

What it proves
- Given adapted/integrable nonnegative `Y : ℕ → Ω → ℝ` and sequences
  `u,v,w : ℕ → ℝ` with the RS one‑step inequality and summable
  `∑ w k / RSWeight u (k+1)`, the drifted normalized process
  `RSDrifted u Y v w` converges almost everywhere.

How to use it
- From TTSA hypotheses, instantiate `Y,u,v,w`, provide:
  1) `hAdapt`, `hInt`, `hY_nonneg`.
  2) `hu`, `hv`, `hw` (nonnegativity of u,v,w).
  3) `hRS` (the RS step inequality).
  4) `hWsum : Summable (fun k => w k / RSWeight u (k+1))`.
- Then call `NOC.TTSA.RS_drifted_ae_converges_core` to obtain the a.e. limit.
-/

namespace NOC.TTSA
noncomputable section
open Classical MeasureTheory Filter

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
variable {ℱ : Filtration ℕ m0}

/--
Core alias of `NOC.Prob.RSDrifted_ae_converges_of_RS`, exported under `NOC.TTSA`.

Purpose:
- Make the RS convergence helper available to the TTSA layer with a stable
  name and minimal qualification.

Hypotheses:
- `hAdapt`/`hInt`: `Y n` is adapted to `ℱ n` and integrable.
- `hY_nonneg`: `Y n ≥ 0` a.e.
- `hu`/`hv`/`hw`: nonnegativity of `u,v,w`.
- `hRS`: RS step `μ[Y (n+1) | ℱ n] ≤ (1+u n)Y n − v n + w n` a.e.
- `hWsum`: summability of `w` against the deterministic weight `RSWeight u`.

Conclusion:
- The drifted normalized process `RSDrifted u Y v w` converges a.e.
- This is precisely the statement returned by the probability‑layer helper.
-/
theorem RS_drifted_ae_converges_core
    [IsProbabilityMeasure μ]
    {Y : ℕ → Ω → ℝ} {u v w : ℕ → ℝ}
    (hAdapt : Adapted ℱ Y)
    (hInt : ∀ n, Integrable (Y n) μ)
    (hY_nonneg : ∀ n, 0 ≤ᵐ[μ] fun ω => Y n ω)
    (hu : ∀ k, 0 ≤ u k) (hv : ∀ k, 0 ≤ v k) (hw : ∀ k, 0 ≤ w k)
    (hRS : ∀ n,
      μ[ Y (n+1) | ℱ n ] ≤ᵐ[μ] (fun ω => (1 + u n) * Y n ω - v n + w n))
    (hWsum : Summable (fun k => w k / NOC.Prob.RSWeight u (k+1))) :
    ∀ᵐ ω ∂ μ, ∃ c, Tendsto (fun n => NOC.Prob.RSDrifted u Y v w n ω) atTop (nhds c) :=
  NOC.Prob.RSDrifted_ae_converges_of_RS (μ := μ) (ℱ := ℱ)
    (Y := Y) (u := u) (v := v) (w := w)
    hAdapt hInt hY_nonneg hu hv hw hRS hWsum

end
end NOC.TTSA
