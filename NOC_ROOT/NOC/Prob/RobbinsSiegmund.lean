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
-/

namespace NOC.Prob
noncomputable section
open Classical MeasureTheory Filter
open scoped ENNReal

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
## Deterministic normalization utilities (for RS)

We define the standard multiplicative weights `W n := ∏_{k<n} (1 + u k)` for a
deterministic nonnegative sequence `u : ℕ → ℝ`, and the corresponding
normalized process skeleton used in the classical Robbins–Siegmund proof.
-/

namespace NOC.Prob
noncomputable section
open Classical MeasureTheory Filter
open scoped BigOperators

variable (u : ℕ → ℝ)

/-- Multiplicative weight for RS normalization: `W n = ∏_{k<n} (1 + u k)`. -/
@[simp] def RSWeight (n : ℕ) : ℝ := (Finset.range n).prod (fun k => (1 + u k))

namespace RSWeight

variable {u}

@[simp] lemma zero : RSWeight u 0 = 1 := by
  simp [RSWeight]

@[simp] lemma succ (n : ℕ) : RSWeight u (n + 1) = RSWeight u n * (1 + u n) := by
  simpa [RSWeight, Finset.prod_range_succ, mul_comm, mul_left_comm, mul_assoc]

lemma pos_of_nonneg (hu : ∀ k, 0 ≤ u k) (n : ℕ) : 0 < RSWeight u n := by
  induction' n with n ih
  · simpa [zero] using (show (0 : ℝ) < 1 by norm_num)
  · have hpos : 0 < 1 + u n := by
      have h := hu n; linarith
    have : 0 < RSWeight u n * (1 + u n) := mul_pos ih hpos
    simpa [RSWeight, Finset.prod_range_succ, mul_comm, mul_left_comm, mul_assoc]
      using this

end RSWeight

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}

/-- RS normalized process skeleton for a given `Y` and drift `w` (deterministic `u`).
This definition isolates the standard combination used in the RS proof. -/
def RSNormalized (Y : ℕ → Ω → ℝ) (w : ℕ → ℝ) (n : ℕ) : Ω → ℝ :=
  fun ω => (Y n ω) / RSWeight u n + (Finset.range n).sum (fun k => w k / RSWeight u (k + 1))

end
end NOC.Prob

/-
-- Supermartingale normalization proof will be added here. The algebraic
-- normalization identities above are in place and build clean; next iteration
-- will connect the RS inequality to the conditional-expectation drift bound
-- and invoke `supermartingale_nat`.
-/
/-!
## Increment identity for the RS normalized skeleton

Purely algebraic identity expressing `RSNormalized (n+1)` in terms of
`RSNormalized n` and the increment `Y_{n+1} - (1+u_n)Y_n + w_n` scaled by the
weight `RSWeight u (n+1)`.
-/

namespace NOC.Prob
noncomputable section
open Classical MeasureTheory Filter
open scoped BigOperators ENNReal

variable (u : ℕ → ℝ)

lemma RSNormalized_succ_eq
    {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
    (Y : ℕ → Ω → ℝ) (w : ℕ → ℝ) (n : ℕ)
    (hu : ∀ k, 0 ≤ u k) :
    RSNormalized u Y w (n + 1)
      = fun ω => RSNormalized u Y w n ω
                  + ((Y (n + 1) ω) - (1 + u n) * (Y n ω) + w n)
                      / RSWeight u (n + 1) := by
  funext ω
  -- Abbreviations for products
  set Pn : ℝ := (Finset.range n).prod (fun k => (1 + u k))
  set Pnp1 : ℝ := (Finset.range (n + 1)).prod (fun k => (1 + u k))
  have hz : (1 + u n) ≠ 0 := by
    have : 0 < 1 + u n := by have := hu n; linarith
    exact ne_of_gt this
  have hYrewrite : (Y n ω) / Pn = ((Y n ω) * (1 + u n)) / Pnp1 := by
    simpa [Pn, Pnp1, Finset.prod_range_succ, mul_comm, mul_left_comm, mul_assoc]
      using (mul_div_mul_left (Y n ω) Pn hz).symm
  -- expand definitions and sums at steps n and n+1
  have hStep : RSNormalized u Y w (n + 1) ω
      = (Y (n + 1) ω) / Pnp1
        + (Finset.range n).sum (fun k => w k / (Finset.range (k + 1)).prod (fun j => (1 + u j)))
        + w n / Pnp1 := by
    simp [RSNormalized, RSWeight, Pnp1, Finset.sum_range_succ, Finset.prod_range_succ,
      add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc]
  have hNow : RSNormalized u Y w n ω
      = (Y n ω) / Pn
        + (Finset.range n).sum (fun k => w k / (Finset.range (k + 1)).prod (fun j => (1 + u j))) := by
    simp [RSNormalized, RSWeight, Pn, Finset.prod_range_succ, add_comm, add_left_comm, add_assoc]
  -- Substitute and rearrange
  calc
    RSNormalized u Y w (n + 1) ω
        = (Y (n + 1) ω) / Pnp1
          + (Finset.range n).sum (fun k => w k / (Finset.range (k + 1)).prod (fun j => (1 + u j)))
          + w n / Pnp1 := hStep
    _ = ((Y n ω) / Pn
          + (Finset.range n).sum (fun k => w k / (Finset.range (k + 1)).prod (fun j => (1 + u j))))
          + ((Y (n + 1) ω) / Pnp1 - (Y n ω) / Pn)
          + w n / Pnp1 := by ring
    _ = ((Y n ω) / Pn
          + (Finset.range n).sum (fun k => w k / (Finset.range (k + 1)).prod (fun j => (1 + u j))))
          + (((Y (n + 1) ω) / Pnp1 - ((1 + u n) * (Y n ω)) / Pnp1))
          + w n / Pnp1 := by simpa [hYrewrite, mul_comm]
    _ = ((Y n ω) / Pn
          + (Finset.range n).sum (fun k => w k / (Finset.range (k + 1)).prod (fun j => (1 + u j))))
          + ((Y (n + 1) ω) - (1 + u n) * (Y n ω)) / Pnp1
          + w n / Pnp1 := by ring
    _ = ((Y n ω) / Pn
          + (Finset.range n).sum (fun k => w k / (Finset.range (k + 1)).prod (fun j => (1 + u j))))
          + ((Y (n + 1) ω) - (1 + u n) * (Y n ω) + w n) / Pnp1 := by ring


end
end NOC.Prob

/-!
## Compensated normalization (subtracting the `w`-sum)

The classical RS proof uses the compensated normalized process

  Zₙ := Yₙ / Wₙ − ∑_{k<n} w_k / W_{k+1}

which enjoys the one-step identity with the increment `(Y_{n+1} − (1+uₙ)Yₙ − wₙ)/W_{n+1}`.
This is the variant that directly yields a supermartingale under the RS inequality.
-/

namespace NOC.Prob
noncomputable section
open Classical MeasureTheory
open scoped BigOperators

variable (u : ℕ → ℝ)

/-- RS compensated normalized process: `Z n = Y n / W n − ∑_{k<n} w k / W (k+1)`. -/
def RSNormalizedComp
    {Ω : Type*}
    (Y : ℕ → Ω → ℝ) (w : ℕ → ℝ) (n : ℕ) : Ω → ℝ :=
  fun ω => (Y n ω) / RSWeight u n - (Finset.range n).sum (fun k => w k / RSWeight u (k + 1))

lemma RSNormalizedComp_succ_eq
    {Ω : Type*}
    (Y : ℕ → Ω → ℝ) (w : ℕ → ℝ) (n : ℕ)
    (hu : ∀ k, 0 ≤ u k) :
    RSNormalizedComp u Y w (n + 1)
      = fun ω => RSNormalizedComp u Y w n ω
                  + ((Y (n + 1) ω) - (1 + u n) * (Y n ω) - w n)
                      / RSWeight u (n + 1) := by
  funext ω
  -- Abbreviations for products
  set Pn : ℝ := (Finset.range n).prod (fun k => (1 + u k))
  set Pnp1 : ℝ := (Finset.range (n + 1)).prod (fun k => (1 + u k))
  have hz : (1 + u n) ≠ 0 := by
    have : 0 < 1 + u n := by have := hu n; linarith
    exact ne_of_gt this
  have hYrewrite : (Y n ω) / Pn = ((Y n ω) * (1 + u n)) / Pnp1 := by
    simpa [Pn, Pnp1, Finset.prod_range_succ, mul_comm, mul_left_comm, mul_assoc]
      using (mul_div_mul_left (Y n ω) Pn hz).symm
  -- expand definitions and sums at steps n and n+1
  have hStep : RSNormalizedComp u Y w (n + 1) ω
      = (Y (n + 1) ω) / Pnp1
        - (Finset.range n).sum (fun k => w k / (Finset.range (k + 1)).prod (fun j => (1 + u j)))
        - w n / Pnp1 := by
    simp [RSNormalizedComp, RSWeight, Pnp1, Finset.sum_range_succ, Finset.prod_range_succ,
      add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc, sub_eq_add_neg,
      add_comm, add_left_comm, add_assoc]
  have hNow : RSNormalizedComp u Y w n ω
      = (Y n ω) / Pn
        - (Finset.range n).sum (fun k => w k / (Finset.range (k + 1)).prod (fun j => (1 + u j))) := by
    simp [RSNormalizedComp, RSWeight, Pn, Finset.prod_range_succ, add_comm, add_left_comm,
          add_assoc, sub_eq_add_neg]
  -- Substitute and rearrange
  calc
    RSNormalizedComp u Y w (n + 1) ω
        = (Y (n + 1) ω) / Pnp1
          - (Finset.range n).sum (fun k => w k / (Finset.range (k + 1)).prod (fun j => (1 + u j)))
          - w n / Pnp1 := hStep
    _ = ((Y n ω) / Pn
          - (Finset.range n).sum (fun k => w k / (Finset.range (k + 1)).prod (fun j => (1 + u j))))
          + ((Y (n + 1) ω) / Pnp1 - (Y n ω) / Pn)
          - w n / Pnp1 := by ring
    _ = ((Y n ω) / Pn
          - (Finset.range n).sum (fun k => w k / (Finset.range (k + 1)).prod (fun j => (1 + u j))))
          + (((Y (n + 1) ω) / Pnp1 - ((1 + u n) * (Y n ω)) / Pnp1))
          - w n / Pnp1 := by simpa [hYrewrite, mul_comm]
    _ = ((Y n ω) / Pn
          - (Finset.range n).sum (fun k => w k / (Finset.range (k + 1)).prod (fun j => (1 + u j))))
          + ((Y (n + 1) ω) - (1 + u n) * (Y n ω)) / Pnp1
          - w n / Pnp1 := by ring
    _ = ((Y n ω) / Pn
          - (Finset.range n).sum (fun k => w k / (Finset.range (k + 1)).prod (fun j => (1 + u j))))
          + ((Y (n + 1) ω) - (1 + u n) * (Y n ω) - w n) / Pnp1 := by ring


end
end NOC.Prob

/-!
## Increment identity with drift compensation (algebraic)

Define the compensated-and-drifted normalized process

  Gₙ := RSNormalizedComp u Y w n + ∑_{k<n} v_k / W_{k+1}.

Then `G_{n+1} = G_n + (Y_{n+1} − (1+uₙ)Yₙ − wₙ + vₙ)/W_{n+1}`.
This is a purely algebraic identity used to build a supermartingale once the
Robbins–Siegmund inequality is in place.
-/

namespace NOC.Prob
noncomputable section
open Classical
open scoped BigOperators

variable (u : ℕ → ℝ)

def RSNormalizedDrifted
    {Ω : Type*} (Y : ℕ → Ω → ℝ) (w v : ℕ → ℝ) (n : ℕ) : Ω → ℝ :=
  fun ω => RSNormalizedComp u Y w n ω
          + (Finset.range n).sum (fun k => v k / RSWeight u (k + 1))

lemma RSNormalizedDrifted_succ_eq
    {Ω : Type*}
    (Y : ℕ → Ω → ℝ) (w v : ℕ → ℝ) (n : ℕ)
    (hu : ∀ k, 0 ≤ u k) :
    RSNormalizedDrifted u Y w v (n + 1)
      = fun ω => RSNormalizedDrifted u Y w v n ω
                  + ((Y (n + 1) ω) - (1 + u n) * (Y n ω) - w n) / RSWeight u (n + 1)
                  + (v n) / RSWeight u (n + 1) := by
  funext ω
  have hbase := RSNormalizedComp_succ_eq (u:=u) (Y:=Y) (w:=w) (n:=n) (hu:=hu)
  -- Expand the drift sum at step n+1
  have hsum :
      (Finset.range (n + 1)).sum (fun k => v k / RSWeight u (k + 1))
        = (Finset.range n).sum (fun k => v k / RSWeight u (k + 1))
          + v n / RSWeight u (n + 1) := by
    simpa [Finset.sum_range_succ, Nat.succ_eq_add_one]
  -- Combine the identities step by step
  -- Expand (n+1) definition of the drifted process
  have hprev :
      RSNormalizedDrifted u Y w v n ω
        = RSNormalizedComp u Y w n ω
          + (Finset.range n).sum (fun k => v k / RSWeight u (k + 1)) := by
    simp [RSNormalizedDrifted]
  -- Expand n+1 using the pointwise version of the helper identity and regroup
  have hbase_pt : RSNormalizedComp u Y w (n + 1) ω
      = RSNormalizedComp u Y w n ω
        + ((Y (n + 1) ω) - (1 + u n) * (Y n ω) - w n) / RSWeight u (n + 1) := by
    simpa using congrArg (fun g => g ω) hbase
  have hstep1 :
      RSNormalizedDrifted u Y w v (n + 1) ω
        = (RSNormalizedComp u Y w n ω
            + ((Y (n + 1) ω) - (1 + u n) * (Y n ω) - w n) / RSWeight u (n + 1))
          + ((Finset.range n).sum (fun k => v k / RSWeight u (k + 1))
             + v n / RSWeight u (n + 1)) := by
    -- Expand (n+1) step and split the finite sum at `n`.
    simp [RSNormalizedDrifted, hbase_pt, sub_eq_add_neg,
          Finset.sum_range_succ, Nat.succ_eq_add_one,
          add_comm, add_left_comm, add_assoc]
  calc
    RSNormalizedDrifted u Y w v (n + 1) ω
        = (RSNormalizedComp u Y w n ω
            + ((Y (n + 1) ω) - (1 + u n) * (Y n ω) - w n) / RSWeight u (n + 1))
          + ((Finset.range n).sum (fun k => v k / RSWeight u (k + 1))
             + v n / RSWeight u (n + 1)) := hstep1
    _ = (RSNormalizedComp u Y w n ω
          + (Finset.range n).sum (fun k => v k / RSWeight u (k + 1)))
          + ((Y (n + 1) ω) - (1 + u n) * (Y n ω) - w n) / RSWeight u (n + 1)
          + v n / RSWeight u (n + 1) := by
          ring
    _ = RSNormalizedDrifted u Y w v n ω
          + ((Y (n + 1) ω) - (1 + u n) * (Y n ω) - w n) / RSWeight u (n + 1)
          + v n / RSWeight u (n + 1) := by
          simpa [hprev, add_comm, add_left_comm, add_assoc] 

end
end NOC.Prob

/-!
## Supermartingale from an increment bound

If the compensated normalized increment has nonpositive conditional expectation,
then the drifted normalization is a supermartingale. This isolates the CE step
from the algebraic normalization.
-/

namespace NOC.Prob
noncomputable section
open Classical MeasureTheory
open scoped BigOperators

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
variable {ℱ : Filtration ℕ m0}

variable (u : ℕ → ℝ)

def RSIncTerm
    (Y : ℕ → Ω → ℝ) (w v : ℕ → ℝ) (n : ℕ) : Ω → ℝ :=
  fun ω => ((Y (n + 1) ω) - (1 + u n) * (Y n ω) - w n) / RSWeight u (n + 1)
            + (v n) / RSWeight u (n + 1)

lemma RSNormalizedDrifted_sub_succ_eq
    (Y : ℕ → Ω → ℝ) (w v : ℕ → ℝ) (n : ℕ)
    (hu : ∀ k, 0 ≤ u k) :
    (fun ω => RSNormalizedDrifted u Y w v n ω - RSNormalizedDrifted u Y w v (n + 1) ω)
      = fun ω => - RSIncTerm (u:=u) Y w v n ω := by
  funext ω
  have h := RSNormalizedDrifted_succ_eq (u:=u) (Y:=Y) (w:=w) (v:=v) (n:=n) (hu:=hu)
  have hpt : RSNormalizedDrifted u Y w v (n + 1) ω
      = RSNormalizedDrifted u Y w v n ω
        + ((Y (n + 1) ω) - (1 + u n) * (Y n ω) - w n) / RSWeight u (n + 1)
        + (v n) / RSWeight u (n + 1) := by
    simpa using congrArg (fun g => g ω) h
  calc
    RSNormalizedDrifted u Y w v n ω - RSNormalizedDrifted u Y w v (n + 1) ω
        = RSNormalizedDrifted u Y w v n ω
          - (RSNormalizedDrifted u Y w v n ω
              + ((Y (n + 1) ω) - (1 + u n) * (Y n ω) - w n) / RSWeight u (n + 1)
              + (v n) / RSWeight u (n + 1)) := by simpa [hpt]
    _ = - ( ((Y (n + 1) ω) - (1 + u n) * (Y n ω) - w n) / RSWeight u (n + 1)
              + (v n) / RSWeight u (n + 1)) := by ring
    _ = - RSIncTerm (u:=u) Y w v n ω := rfl

/-- If the normalized compensated increment has nonpositive conditional expectation,
then the drifted normalized process is a supermartingale. -/
theorem RSNormalizedDrifted_supermartingale_of_increment_bound
    (Y : ℕ → Ω → ℝ) (w v : ℕ → ℝ) [IsFiniteMeasure μ]
    (hu : ∀ k, 0 ≤ u k)
    (hadp : Adapted ℱ Y)
    (hint : ∀ n, Integrable (Y n) μ)
    (hinc : ∀ n, μ[RSIncTerm (u:=u) Y w v n | ℱ n] ≤ᵐ[μ] 0) :
    Supermartingale (RSNormalizedDrifted (u:=u) Y w v) ℱ μ := by
  classical
  -- adaptedness
  have hadp' : Adapted ℱ (RSNormalizedDrifted (u:=u) Y w v) := by
    intro n
    have hYn := hadp n
    have hYscaled : StronglyMeasurable[ℱ n] (fun ω => (Y n ω) / RSWeight u n) := by
      simpa [one_div, div_eq_inv_mul] using hYn.const_smul ((RSWeight u n)⁻¹)
    have hconst_w : StronglyMeasurable[ℱ n]
        (fun _ : Ω => (Finset.range n).sum (fun k => w k / RSWeight u (k + 1))) :=
      stronglyMeasurable_const
    have hconst_v : StronglyMeasurable[ℱ n]
        (fun _ : Ω => (Finset.range n).sum (fun k => v k / RSWeight u (k + 1))) :=
      stronglyMeasurable_const
    have hcomp_meas : StronglyMeasurable[ℱ n] (RSNormalizedComp (u:=u) Y w n) := by
      simpa [RSNormalizedComp, sub_eq_add_neg] using (hYscaled.add hconst_w.neg)
    simpa [RSNormalizedDrifted] using hcomp_meas.add hconst_v
  -- integrability
  have hint' : ∀ n, Integrable (RSNormalizedDrifted (u:=u) Y w v n) μ := by
    intro n
    have hYscaled : Integrable (fun ω => (Y n ω) / RSWeight u n) μ := by
      simpa [one_div, div_eq_inv_mul, smul_eq_mul] using (hint n).smul ((RSWeight u n)⁻¹)
    have hconst_w : Integrable (fun _ : Ω => (Finset.range n).sum (fun k => w k / RSWeight u (k + 1))) μ :=
      integrable_const _
    have hint_comp : Integrable (RSNormalizedComp (u:=u) Y w n) μ := by
      change Integrable
        (fun ω => (Y n ω) / RSWeight u n - (Finset.range n).sum (fun k => w k / RSWeight u (k + 1))) μ
      simpa [sub_eq_add_neg] using hYscaled.add ((hconst_w).neg)
    have hconst_v : Integrable (fun _ : Ω => (Finset.range n).sum (fun k => v k / RSWeight u (k + 1))) μ :=
      integrable_const _
    change Integrable
      ((fun ω => RSNormalizedComp (u:=u) Y w n ω)
        + (fun _ : Ω => (Finset.range n).sum (fun k => v k / RSWeight u (k + 1)))) μ
    simpa [RSNormalizedDrifted] using hint_comp.add hconst_v
  -- one-step CE inequality: 0 ≤ μ[g n − g (n+1) | ℱ n]
  have hstep : ∀ n, 0 ≤ᵐ[μ]
      μ[RSNormalizedDrifted (u:=u) Y w v n - RSNormalizedDrifted (u:=u) Y w v (n + 1) | ℱ n] := by
    intro n
    -- express the difference as negation of the increment
    have hfun_eq := RSNormalizedDrifted_sub_succ_eq (u:=u) (Y:=Y) (w:=w) (v:=v) (n:=n) (hu:=hu)
    have hce_eq : μ[RSNormalizedDrifted (u:=u) Y w v n - RSNormalizedDrifted (u:=u) Y w v (n + 1) | ℱ n]
                    =ᵐ[μ] μ[(fun ω => - RSIncTerm (u:=u) Y w v n ω) | ℱ n] := by
      -- pointwise equality wrapped into AE equality for `condExp_congr_ae`
      have hpt : ∀ ω, (RSNormalizedDrifted (u:=u) Y w v n ω - RSNormalizedDrifted (u:=u) Y w v (n + 1) ω)
                        = (fun ω => - RSIncTerm (u:=u) Y w v n ω) ω := by
        intro ω; simpa using congrArg (fun f => f ω) hfun_eq
      refine condExp_congr_ae (μ:=μ) (m:=ℱ n)
        (h := (Filter.Eventually.of_forall hpt))
    have hneg : μ[(fun ω => - RSIncTerm (u:=u) Y w v n ω) | ℱ n]
                  =ᵐ[μ] - μ[RSIncTerm (u:=u) Y w v n | ℱ n] := condExp_neg ..
    -- use the assumed nonpositivity to conclude nonnegativity after negation
    filter_upwards [hce_eq, hneg, hinc n] with ω h1 h2 h3
    have hce : μ[RSNormalizedDrifted (u:=u) Y w v n - RSNormalizedDrifted (u:=u) Y w v (n + 1) | ℱ n] ω
                = - μ[RSIncTerm (u:=u) Y w v n | ℱ n] ω := by
      simpa [h1] using h2
    have hnonneg : 0 ≤ - μ[RSIncTerm (u:=u) Y w v n | ℱ n] ω := by
      exact neg_nonneg.mpr h3
    simpa [hce] using hnonneg
  -- conclude supermartingale
  exact MeasureTheory.supermartingale_of_condExp_sub_nonneg_nat hadp' hint' (by intro n; simpa using hstep n)

end
end NOC.Prob

/-!
## From RS inequality to increment bound and supermartingale

We derive the nonpositivity of the normalized compensated increment from the
Robbins–Siegmund inequality

  μ[Y_{n+1} | ℱ_n] ≤ (1 + u_n) · Y_n − v_n + w_n,

then conclude that the drifted normalization is a supermartingale.
-/

namespace NOC.Prob
noncomputable section
open Classical MeasureTheory
open scoped BigOperators

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
variable {ℱ : Filtration ℕ m0}

variable (u : ℕ → ℝ)

/- Close the small namespace before deferring the following RS block as a TODO. -/
end
end NOC.Prob

/- TODO: complete RS CE algebra to derive increment bound and convergence. -/

namespace NOC.Prob
noncomputable section
open Classical MeasureTheory
open scoped BigOperators

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
variable {ℱ : Filtration ℕ m0}

variable (u : ℕ → ℝ)

lemma RS_increment_bound_of_RS_ineq
    (Y : ℕ → Ω → ℝ) (w v : ℕ → ℝ) [IsFiniteMeasure μ]
    (hu : ∀ k, 0 ≤ u k)
    (hadp : Adapted ℱ Y)
    (hint : ∀ n, Integrable (Y n) μ)
    (hRS : ∀ n, μ[Y (n + 1)|ℱ n] ≤ᵐ[μ] (fun ω => (1 + u n) * Y n ω - v n + w n)) :
    ∀ n, μ[RSIncTerm (u:=u) Y w v n | ℱ n] ≤ᵐ[μ] 0 := by
  classical
  intro n
  -- Shorthand for the weight inverse
  set c : ℝ := (RSWeight u (n + 1))⁻¹
  have hposW : 0 < RSWeight u (n + 1) := RSWeight.pos_of_nonneg (u:=u) hu (n+1)
  have hc_nonneg : 0 ≤ c := by
    have hcpos : 0 < c := by simpa [c] using inv_pos.mpr hposW
    exact hcpos.le
  -- Scale the RS inequality by `c ≥ 0`
  let RS_rhs : Ω → ℝ := fun ω => (1 + u n) * Y n ω - v n + w n
  have hscaled : ∀ᵐ ω ∂ μ, c * (μ[Y (n + 1)|ℱ n] ω) ≤ c * RS_rhs ω := by
    exact (hRS n).mono (by intro ω hω; exact mul_le_mul_of_nonneg_left hω hc_nonneg)
  -- Conditional expectation of the RS increment in linearized form
  have hlin1 : μ[(fun ω => c • (Y (n + 1) ω))|ℱ n]
        =ᵐ[μ] fun ω => c • μ[Y (n + 1)|ℱ n] ω := by
    simpa using (condExp_smul (μ := μ) (m := ℱ n) (c := c) (f := Y (n + 1)))
  have hlin2 : μ[(fun ω => (c * (1 + u n)) • (Y n ω))|ℱ n]
        =ᵐ[μ] fun ω => (c * (1 + u n)) • μ[Y n|ℱ n] ω := by
    simpa using (condExp_smul (μ := μ) (m := ℱ n) (c := c * (1 + u n)) (f := Y n))
  have hlin3 : μ[(fun _ => c * w n)|ℱ n] = fun _ => c * w n := by
    simpa using (condExp_const (μ := μ) (hm := ℱ.le n) (c := c * w n))
  have hlin4 : μ[(fun _ => c * v n)|ℱ n] = fun _ => c * v n := by
    simpa using (condExp_const (μ := μ) (hm := ℱ.le n) (c := c * v n))
  -- Expand the definition of `RSIncTerm` through conditional expectation linearity
  have hce_inc :
      μ[RSIncTerm (u:=u) Y w v n | ℱ n]
        =ᵐ[μ] fun ω =>
          c * (μ[Y (n + 1)|ℱ n] ω - (1 + u n) * μ[Y n|ℱ n] ω - w n) + c * v n := by
    -- Let g0 := Y_{n+1} - (1+u) Y_n - w_n
    set g0 : Ω → ℝ := fun ω => Y (n + 1) ω - (1 + u n) * Y n ω - w n
    have hint_g0 : Integrable g0 μ := by
      have h1 := (hint (n + 1))
      have h2 := (hint n).smul (1 + u n)
      have hcst : Integrable (fun _ : Ω => w n) μ := integrable_const _
      simpa [g0, sub_eq_add_neg] using (h1.sub h2).sub hcst
    -- condExp of g1 := c • g0
    have hsmul : μ[(fun ω => c • g0 ω)|ℱ n] =ᵐ[μ] fun ω => c • μ[g0|ℱ n] ω :=
      condExp_smul (μ := μ) (m := ℱ n) (c := c) (f := g0)
    -- condExp of g0 splits into pieces
    have hsplit1 : μ[(fun ω => Y (n + 1) ω - (1 + u n) * Y n ω)|ℱ n]
          =ᵐ[μ] fun ω => μ[Y (n + 1)|ℱ n] ω - μ[(fun ω => (1 + u n) * Y n ω)|ℱ n] ω := by
      simpa [Pi.sub_def] using
        (condExp_sub (μ := μ) (m := ℱ n) (hf := hint (n + 1)) (hg := (hint n).smul (1 + u n)))
    have hsplit2 : μ[g0|ℱ n]
          =ᵐ[μ] fun ω => μ[Y (n + 1)|ℱ n] ω - μ[(fun ω => (1 + u n) * Y n ω)|ℱ n] ω - w n := by
      -- write g0 = (Y_{n+1} - (1+u)Y_n) - w_n and apply condExp_sub then condExp_const
      let f1 : Ω → ℝ := fun ω => Y (n + 1) ω - (1 + u n) * Y n ω
      let g1 : Ω → ℝ := fun _ : Ω => w n
      have hf1 : Integrable f1 μ := (hint (n + 1)).sub ((hint n).smul (1 + u n))
      have hg1 : Integrable g1 μ := integrable_const _
      have hfg : μ[(fun ω => f1 ω - g1 ω)|ℱ n]
            =ᵐ[μ] (fun ω => μ[f1|ℱ n] ω - μ[g1|ℱ n] ω) :=
        (condExp_sub (μ := μ) (m := ℱ n) (hf := hf1) (hg := hg1))
      -- combine with `hsplit1` and `condExp_const` for g1
      have hconst_w : μ[g1|ℱ n] = fun _ => w n := condExp_const (μ := μ) (hm := ℱ.le n) (c := w n)
      refine hfg.trans ?_
      filter_upwards [hsplit1] with ω hω
      simpa [f1, g1, Pi.sub_def, sub_eq_add_neg, hconst_w]
    -- Apply smul linearity and constants
    have hconst_v : μ[(fun _ => c * v n)|ℱ n] = fun _ => c * v n :=
      condExp_const (μ := μ) (hm := ℱ.le n) (c := c * v n)
    have hconst_w : μ[(fun _ => w n)|ℱ n] = fun _ => w n :=
      condExp_const (μ := μ) (hm := ℱ.le n) (c := w n)
    -- finalize
    -- include smul on (1+u) * Y n as well
    have hsmulYnAE := condExp_smul (μ := μ) (m := ℱ n) (c := (1 + u n)) (f := Y n)
    have haddAE := condExp_add (μ := μ) (m := ℱ n)
        (f := fun ω => c * g0 ω) (g := fun _ => c * v n)
        (hf := (hint_g0.smul c)) (hg := integrable_const _)
    -- also rewrite `μ[RSIncTerm|ℱ n]` into the affine form under conditional expectation
    have hstart_fun :
        μ[RSIncTerm (u:=u) Y w v n | ℱ n]
          =ᵐ[μ] μ[(fun ω => c * ((Y (n + 1) ω) - (1 + u n) * Y n ω - w n) + c * v n)|ℱ n] := by
      -- pointwise rewriting followed by `condExp_congr_ae`
      refine condExp_congr_ae (μ := μ) (m := ℱ n) ?hpt
      refine Filter.Eventually.of_forall ?hp
      intro ω
      simp [RSIncTerm, RSWeight, c, one_div, div_eq_inv_mul, sub_eq_add_neg, mul_add,
            add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc]
    filter_upwards [hstart_fun, hsmul, hsplit2, hsmulYnAE, haddAE] with ω hstart hsm hsp hmulyn hadd
    -- compute conditional expectations and substitute pieces
    have hsm' : μ[(fun ω => c • g0 ω)|ℱ n] ω = c * (μ[g0|ℱ n] ω) := by
      simpa [smul_eq_mul] using hsm
    have hv' : μ[(fun _ => c * v n)|ℱ n] ω = c * v n := by
      simpa using congrArg (fun f => f ω) hconst_v
    have hsplit' : μ[g0|ℱ n] ω
        = μ[Y (n + 1)|ℱ n] ω - (1 + u n) * μ[Y n|ℱ n] ω - w n := by
      -- apply `condExp_smul` to `(1+u) * Y n`
      have hsmulYn : μ[(fun ω => (1 + u n) * Y n ω)|ℱ n] ω
            = (1 + u n) * μ[Y n|ℱ n] ω := by
        simpa [smul_eq_mul] using hmulyn
      -- combine with `hsplit2`
      simpa [hsmulYn, sub_eq_add_neg] using hsp
    -- establish the needed equality at this point
    have hEqGoal : μ[RSIncTerm (u:=u) Y w v n | ℱ n] ω
        = c * (μ[Y (n + 1)|ℱ n] ω - (1 + u n) * μ[Y n|ℱ n] ω - w n) + c * v n := by
      -- derive the target equality stepwise via condExp linearity
      have hconst_v_pt : μ[(fun _ => c * v n)|ℱ n] ω = c * v n := by
        simpa using congrArg (fun f => f ω) hconst_v
      -- use the pointwise instance of `hstart_fun`
      have hstart : μ[RSIncTerm (u:=u) Y w v n | ℱ n] ω
          = μ[(fun ω => c * ((Y (n + 1) ω) - (1 + u n) * Y n ω - w n) + c * v n)|ℱ n] ω := by
        simpa using hstart
      -- linearize the sum and smul pieces
      have hcond_add :
          μ[(fun ω => c * ((Y (n + 1) ω) - (1 + u n) * Y n ω - w n) + c * v n)|ℱ n] ω
            = μ[(fun ω => c * ((Y (n + 1) ω) - (1 + u n) * Y n ω - w n))|ℱ n] ω
              + μ[(fun _ => c * v n)|ℱ n] ω := by
        simpa [Pi.add_def] using hadd
      have hsmul_g0 :
          μ[(fun ω => c * ((Y (n + 1) ω) - (1 + u n) * Y n ω - w n))|ℱ n] ω
            = c * μ[g0|ℱ n] ω := by
        simpa [g0, smul_eq_mul] using hsm
      have hsub_split :
          μ[g0|ℱ n] ω
            = μ[Y (n + 1)|ℱ n] ω - (1 + u n) * μ[Y n|ℱ n] ω - w n := by
        -- derive from `hsp` and `hmulyn`
        have hsmulYn : μ[(fun ω => (1 + u n) * Y n ω)|ℱ n] ω
              = (1 + u n) * μ[Y n|ℱ n] ω := by
          simpa [smul_eq_mul] using hmulyn
        simpa [g0, hsmulYn, sub_eq_add_neg] using hsp
      -- put everything together
      calc
        μ[RSIncTerm (u:=u) Y w v n | ℱ n] ω
            = μ[(fun ω => c * ((Y (n + 1) ω) - (1 + u n) * Y n ω - w n) + c * v n)|ℱ n] ω := hstart
        _ = μ[(fun ω => c * ((Y (n + 1) ω) - (1 + u n) * Y n ω - w n))|ℱ n] ω
              + μ[(fun _ => c * v n)|ℱ n] ω := hcond_add
        _ = c * μ[g0|ℱ n] ω + c * v n := by
              simpa [hsmul_g0, hconst_v_pt]
        _ = c * (μ[Y (n + 1)|ℱ n] ω - (1 + u n) * μ[Y n|ℱ n] ω - w n) + c * v n := by
              simpa [hsub_split]
    exact hEqGoal
  -- Use the scaled RS inequality to bound `μ[RSIncTerm|ℱ n]` by a centered term
  have hY_eq_fun : μ[Y n|ℱ n] = Y n :=
    condExp_of_stronglyMeasurable (μ := μ) (m := ℱ n) (hm := ℱ.le n) (hf := hadp n) (hfi := hint n)
  have hY_eq : μ[Y n|ℱ n] =ᵐ[μ] Y n := by
    exact Filter.Eventually.of_forall (fun ω => by simpa using congrArg (fun f => f ω) hY_eq_fun)
  have hbound : ∀ᵐ ω ∂ μ,
      c * (μ[Y (n + 1)|ℱ n] ω) - (c * (1 + u n)) * μ[Y n|ℱ n] ω - c * w n + c * v n
        ≤ c * (1 + u n) * (Y n ω - μ[Y n|ℱ n] ω) := by
    filter_upwards [hscaled] with ω hω
    -- add the same terms to both sides
    have hstep :
        c * (μ[Y (n + 1)|ℱ n] ω)
          + (-(c * (1 + u n)) * μ[Y n|ℱ n] ω - c * w n + c * v n)
        ≤ c * RS_rhs ω
          + (-(c * (1 + u n)) * μ[Y n|ℱ n] ω - c * w n + c * v n) := by
      exact add_le_add_right hω _
    have :
        c * (μ[Y (n + 1)|ℱ n] ω) - (c * (1 + u n)) * μ[Y n|ℱ n] ω - c * w n + c * v n
          ≤ c * RS_rhs ω
               - (c * (1 + u n)) * μ[Y n|ℱ n] ω - c * w n + c * v n := by
      simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc]
        using hstep
    -- simplify the RHS to the centered form
    have hR :
        c * RS_rhs ω
             - (c * (1 + u n)) * μ[Y n|ℱ n] ω - c * w n + c * v n
          = c * (1 + u n) * (Y n ω - μ[Y n|ℱ n] ω) := by
      simp [RS_rhs, sub_eq_add_neg, add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm,
            mul_assoc, mul_add, add_mul]
    exact this.trans (by simpa [hR])
  -- Since `μ[Y n|ℱ n] = Y n` a.e., the centered term is a.e. 0, hence ≤ 0
  have hcenter_le_zero : ∀ᵐ ω ∂ μ, c * (1 + u n) * (Y n ω - μ[Y n|ℱ n] ω) ≤ 0 := by
    filter_upwards [hY_eq] with ω hω
    have : Y n ω - μ[Y n|ℱ n] ω = 0 := by simpa [hω]
    simpa [this]
  -- Combine: `μ[RSIncTerm|ℱ n] ≤ centered term ≤ 0`
  filter_upwards [hce_inc, hbound, hcenter_le_zero] with ω hce hle hcen
  -- normalize the left side of `hle`
  have hLHS_form :
      c * μ[Y (n + 1)|ℱ n] ω - c * (1 + u n) * μ[Y n|ℱ n] ω - c * w n + c * v n
        = c * (μ[Y (n + 1)|ℱ n] ω - (1 + u n) * μ[Y n|ℱ n] ω - w n) + c * v n := by
    ring
  have hle' :
      c * (μ[Y (n + 1)|ℱ n] ω - (1 + u n) * μ[Y n|ℱ n] ω - w n) + c * v n
        ≤ c * (1 + u n) * (Y n ω - μ[Y n|ℱ n] ω) := by
    simpa [hLHS_form] using hle
  -- rewrite `μ[RSIncTerm|ℱ n]` using `hce` and chain inequalities
  have : μ[RSIncTerm (u:=u) Y w v n | ℱ n] ω
        ≤ c * (1 + u n) * (Y n ω - μ[Y n|ℱ n] ω) := by
    simpa [hce] using hle'
  exact le_trans this hcen

/-- From RS inequality to a supermartingale for the drifted normalization. -/
theorem RSNormalizedDrifted_supermartingale_from_RS_ineq
    (Y : ℕ → Ω → ℝ) (w v : ℕ → ℝ) [IsFiniteMeasure μ]
    (hu : ∀ k, 0 ≤ u k)
    (hadp : Adapted ℱ Y)
    (hint : ∀ n, Integrable (Y n) μ)
    (hRS : ∀ n, μ[Y (n + 1)|ℱ n] ≤ᵐ[μ] (fun ω => (1 + u n) * Y n ω - v n + w n)) :
    Supermartingale (RSNormalizedDrifted (u:=u) Y w v) ℱ μ := by
  refine RSNormalizedDrifted_supermartingale_of_increment_bound (u:=u) (μ:=μ) (ℱ:=ℱ) (Y:=Y) (w:=w) (v:=v)
    (hu:=hu) (hadp:=hadp) (hint:=hint) ?_
  exact RS_increment_bound_of_RS_ineq (u:=u) (μ:=μ) (ℱ:=ℱ) (Y:=Y) (w:=w) (v:=v)
    (hu:=hu) (hadp:=hadp) (hint:=hint) (hRS:=hRS)

/-- A.e. convergence of the drifted normalization under RS inequality and an L¹ bound. -/
theorem RSNormalizedDrifted_ae_converges
    (Y : ℕ → Ω → ℝ) (w v : ℕ → ℝ) [IsFiniteMeasure μ]
    (hu : ∀ k, 0 ≤ u k)
    (hadp : Adapted ℱ Y)
    (hint : ∀ n, Integrable (Y n) μ)
    (hRS : ∀ n, μ[Y (n + 1)|ℱ n] ≤ᵐ[μ] (fun ω => (1 + u n) * Y n ω - v n + w n))
    (R : NNReal)
    (hbdd : ∀ n, eLpNorm (RSNormalizedDrifted (u:=u) Y w v n) (1 : ENNReal) μ ≤ (R : ENNReal)) :
    ∀ᵐ ω ∂ μ, ∃ c, Filter.Tendsto (fun n => RSNormalizedDrifted (u:=u) Y w v n ω) Filter.atTop (nhds c) := by
  have hsuper := RSNormalizedDrifted_supermartingale_from_RS_ineq (u:=u) (μ:=μ) (ℱ:=ℱ)
    (Y:=Y) (w:=w) (v:=v) (hu:=hu) (hadp:=hadp) (hint:=hint) (hRS:=hRS)
  exact supermartingale_exists_ae_tendsto_of_bdd (μ := μ) (ℱ := ℱ)
    (f := RSNormalizedDrifted (u:=u) Y w v) hsuper R hbdd

end
end NOC.Prob
