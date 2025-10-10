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
open scoped BigOperators

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

end
end NOC.Prob
