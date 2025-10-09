import Mathlib
import Mathlib.Probability.Martingale.Basic

namespace NOC
namespace Prob
noncomputable section
open scoped BigOperators MeasureTheory ProbabilityTheory ENNReal
open Classical MeasureTheory

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
variable {ℱ : MeasureTheory.Filtration ℕ m0}
variable [IsFiniteMeasure μ]

structure MDSData where
  seq : ℕ → Ω → ℝ
  adapted : Adapted ℱ seq
  integrable : ∀ n, Integrable (seq n) μ
  zero_condExp : ∀ n, μ[seq (n + 1) | ℱ n] =ᵐ[μ] 0
  variance_bound : ℝ
  variance_nonneg : 0 ≤ variance_bound
  second_moment_le : ∀ n, ∫ ω, (seq (n + 1) ω) ^ 2 ∂ μ ≤ variance_bound
  square_integrable : ∀ n, Integrable (fun ω => (seq (n + 1) ω) ^ 2) μ

namespace MDSData
variable (h : MDSData (μ:=μ) (ℱ:=ℱ))

@[simp] def partialSum (b : ℕ → ℝ) (n : ℕ) : Ω → ℝ :=
  fun ω => (Finset.range n).sum (fun k => b k * h.seq (k + 1) ω)

lemma partialSum_zero (b : ℕ → ℝ) : h.partialSum b 0 = 0 := by
  ext ω; simp [partialSum]

lemma partialSum_succ (b : ℕ → ℝ) (n : ℕ) :
    h.partialSum b (n + 1)
      = fun ω => h.partialSum b n ω + b n * h.seq (n + 1) ω := by
  classical
  ext ω; simp [partialSum, Finset.sum_range_succ, add_comm, add_left_comm, add_assoc]

lemma partialSum_adapted (b : ℕ → ℝ) :
    Adapted ℱ (fun n => h.partialSum b n) := by
  classical
  intro n
  induction' n with n ih
  · simpa [partialSum_zero] using
      (stronglyMeasurable_const : StronglyMeasurable[ℱ 0] (fun _ : Ω => (0 : ℝ)))
  · have ih' : StronglyMeasurable[ℱ (n + 1)] (h.partialSum b n) :=
      ih.mono (ℱ.mono (Nat.le_succ _))
    have hξ : StronglyMeasurable[ℱ (n + 1)] (h.seq (n + 1)) := h.adapted (n + 1)
    have hconst : StronglyMeasurable[ℱ (n + 1)] (fun _ : Ω => (b n : ℝ)) :=
      stronglyMeasurable_const
    have hscaled : StronglyMeasurable[ℱ (n + 1)] (fun ω => b n * h.seq (n + 1) ω) :=
      hconst.mul hξ
    simpa [partialSum_succ, mul_comm, mul_left_comm, mul_assoc] using ih'.add hscaled

lemma partialSum_integrable (b : ℕ → ℝ) :
    ∀ n, Integrable (h.partialSum b n) μ := by
  classical
  intro n
  induction' n with n ih
  · have hf : h.partialSum b 0 = fun _ : Ω => (0 : ℝ) := by
      ext ω; simp [partialSum]
    simpa [hf] using (MeasureTheory.integrable_zero : Integrable (fun _ : Ω => (0 : ℝ)) μ)
  · have hscaled : Integrable (fun ω => b n * h.seq (n + 1) ω) μ :=
      (h.integrable (n + 1)).smul (b n)
    have hsum := h.partialSum_succ (b := b) n
    simpa [hsum, smul_eq_mul] using ih.add hscaled

@[simp] lemma partialSum_diff (b : ℕ → ℝ) (n : ℕ) :
    (fun ω => h.partialSum b (n + 1) ω - h.partialSum b n ω)
      = fun ω => b n * h.seq (n + 1) ω := by
  classical
  funext ω
  simp [partialSum, Finset.sum_range_succ, sub_eq_add_neg, add_comm, add_left_comm, add_assoc]

lemma scaled_condExp_zero (b : ℕ → ℝ) (n : ℕ) :
    μ[(fun ω => b n * h.seq (n + 1) ω) | ℱ n] =ᵐ[μ] 0 := by
  classical
  have hz := h.zero_condExp n
  have hsmul :
      μ[(fun ω => (b n) • h.seq (n + 1) ω) | ℱ n]
        =ᵐ[μ] (b n) • μ[(fun ω => h.seq (n + 1) ω) | ℱ n] :=
    condExp_smul (μ := μ) (m := ℱ n) (c := b n) (f := fun ω => h.seq (n + 1) ω)
  have hzero :
      μ[(fun ω => (b n) • h.seq (n + 1) ω) | ℱ n] =ᵐ[μ] 0 := by
    filter_upwards [hsmul, hz] with ω hω hzero
    simpa [Pi.zero_apply] using by simpa [hzero] using hω
  simpa [smul_eq_mul] using hzero

lemma partialSum_condExp_diff_zero (b : ℕ → ℝ) (n : ℕ) :
    μ[(fun ω => h.partialSum b (n + 1) ω - h.partialSum b n ω) | ℱ n]
      =ᵐ[μ] 0 := by
  classical
  have hdiffAE :
      (fun ω => h.partialSum b (n + 1) ω - h.partialSum b n ω)
        =ᵐ[μ] (fun ω => b n * h.seq (n + 1) ω) :=
    Filter.EventuallyEq.of_eq (partialSum_diff (h := h) (b := b) n)
  have hscaled := h.scaled_condExp_zero (b := b) n
  exact (MeasureTheory.condExp_congr_ae hdiffAE).trans hscaled

lemma partialSum_martingale (b : ℕ → ℝ) :
    Martingale (fun n => h.partialSum b n) ℱ μ := by
  classical
  refine martingale_of_condExp_sub_eq_zero_nat
    (hadp := h.partialSum_adapted b) (hint := h.partialSum_integrable b) ?_
  intro n
  simpa using h.partialSum_condExp_diff_zero (b := b) n

private def varianceTerm (b : ℕ → ℝ) (n : ℕ) : ℝ :=
  (Finset.range n).sum (fun k => (b k) ^ 2 * ∫ ω, (h.seq (k + 1) ω) ^ 2 ∂ μ)

private lemma varianceTerm_succ (b : ℕ → ℝ) (n : ℕ) :
    varianceTerm (h := h) (μ := μ) b (n + 1)
      = varianceTerm (h := h) (μ := μ) b n
        + (b n) ^ 2 * ∫ ω, (h.seq (n + 1) ω) ^ 2 ∂ μ := by
  classical
  unfold varianceTerm
  simp [Finset.sum_range_succ, add_comm, add_left_comm, add_assoc]

private lemma seq_sq_integrable (n : ℕ) :
    Integrable (fun ω => (h.seq (n + 1) ω) ^ 2) μ :=
  h.square_integrable n

private lemma diff_sq_integrable (b : ℕ → ℝ) (n : ℕ) :
    Integrable (fun ω => (b n * h.seq (n + 1) ω) ^ 2) μ := by
  classical
  have hsq := h.seq_sq_integrable n
  have hconst : Integrable (fun ω => (b n) ^ 2 * (h.seq (n + 1) ω) ^ 2) μ :=
    hsq.smul ((b n) ^ 2)
  have hcongr :
      (fun ω => (b n * h.seq (n + 1) ω) ^ 2)
        =ᵐ[μ] fun ω => (b n) ^ 2 * (h.seq (n + 1) ω) ^ 2 := by
    refine Filter.Eventually.of_forall ?_
    intro ω; simp [pow_two, mul_comm, mul_left_comm, mul_assoc]
  exact hconst.congr hcongr.symm

lemma partialSum_diff_sq_integral (b : ℕ → ℝ) (n : ℕ) :
    ∫ ω, (h.partialSum b (n + 1) ω - h.partialSum b n ω) ^ 2 ∂ μ
      = (b n) ^ 2 * ∫ ω, (h.seq (n + 1) ω) ^ 2 ∂ μ := by
  classical
  have hcongr :
      (fun ω => (h.partialSum b (n + 1) ω - h.partialSum b n ω) ^ 2)
        =ᵐ[μ] fun ω => (b n * h.seq (n + 1) ω) ^ 2 :=
    Filter.Eventually.of_forall (fun ω => by
      have hpoint := congrArg (fun f : Ω → ℝ => f ω)
          (partialSum_diff (h := h) (b := b) n)
      have := congrArg (fun t : ℝ => t ^ 2) hpoint
      simpa [pow_two])
  have hsq := h.seq_sq_integrable n
  have hcalc1 :
      ∫ ω, (h.partialSum b (n + 1) ω - h.partialSum b n ω) ^ 2 ∂ μ
        = ∫ ω, (b n * h.seq (n + 1) ω) ^ 2 ∂ μ :=
    integral_congr_ae hcongr
  have hrewrite :
      (fun ω => (b n * h.seq (n + 1) ω) ^ 2)
        = fun ω => (b n) ^ 2 * (h.seq (n + 1) ω) ^ 2 := by
    funext ω; simp [pow_two, mul_comm, mul_left_comm, mul_assoc]
  have hcalc2 :
      ∫ ω, (b n * h.seq (n + 1) ω) ^ 2 ∂ μ
        = (b n) ^ 2 * ∫ ω, (h.seq (n + 1) ω) ^ 2 ∂ μ := by
    simpa [hrewrite]
      using integral_const_mul (μ := μ) ((b n) ^ 2) (fun ω => (h.seq (n + 1) ω) ^ 2)
  exact hcalc1.trans hcalc2

private lemma add_sq_le_two_sq (x y : ℝ) :
    (x + y) ^ 2 ≤ 2 * (x ^ 2 + y ^ 2) := by
  have hx : (x - y) ^ 2 ≥ 0 := sq_nonneg _
  have hy : (x + y) ^ 2 ≥ 0 := sq_nonneg _
  nlinarith [hx, hy]

private lemma partialSum_sq_integrable_aux (b : ℕ → ℝ) :
    ∀ n, Integrable (fun ω => (h.partialSum b n ω) ^ 2) μ := by
  sorry

private lemma partialSum_sq_integrable (b : ℕ → ℝ) (n : ℕ) :
    Integrable (fun ω => (h.partialSum b n ω) ^ 2) μ :=
  partialSum_sq_integrable_aux (h := h) b n

private lemma abs_mul_le_half_sq_add_sq (x y : ℝ) :
    |x * y| ≤ (x ^ 2 + y ^ 2) / 2 := by
  have hsq : (|x| - |y|) ^ 2 ≥ 0 := sq_nonneg _
  have hineq1 : 0 ≤ |x| ^ 2 - 2 * |x| * |y| + |y| ^ 2 := by
    have hh : (|x| - |y|) ^ 2 = |x| ^ 2 - 2 * |x| * |y| + |y| ^ 2 := by
      ring
    simpa [hh] using hsq
  have hx : |x| ^ 2 = x ^ 2 := by simpa [pow_two]
  have hy : |y| ^ 2 = y ^ 2 := by simpa [pow_two]
  have hineq2 : 0 ≤ x ^ 2 - 2 * |x| * |y| + y ^ 2 := by
    simpa [hx, hy] using hineq1
  have hineq0 : 0 ≤ x ^ 2 + y ^ 2 - 2 * |x * y| := by
    simpa [abs_mul, mul_comm, mul_left_comm, mul_assoc, sub_eq_add_neg, add_comm,
      add_left_comm, add_assoc]
      using hineq2
  have hineq' : 2 * |x * y| ≤ x ^ 2 + y ^ 2 :=
    sub_nonneg.mp hineq0
  have hmul :=
    (mul_le_mul_of_nonneg_right hineq' (by norm_num : 0 ≤ (1 / 2 : ℝ)) :
      (2 * |x * y|) * (1 / 2 : ℝ) ≤ (x ^ 2 + y ^ 2) * (1 / 2 : ℝ))
  exact
    (by
      simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
        using hmul)

private lemma partialSum_mul_diff_integrable (b : ℕ → ℝ) (n : ℕ) :
    Integrable (fun ω => h.partialSum b n ω * (b n * h.seq (n + 1) ω)) μ := by
  sorry

private lemma partialSum_cross_integral_zero (b : ℕ → ℝ) (n : ℕ) :
    ∫ ω, h.partialSum b n ω * (b n * h.seq (n + 1) ω) ∂ μ = 0 := by
  sorry

private lemma partialSum_sq_integral_eq_varianceTerm (b : ℕ → ℝ) :
    ∀ n, ∫ ω, (h.partialSum b n ω) ^ 2 ∂ μ = varianceTerm (h := h) (μ := μ) b n := by
  sorry
end MDSData

end

/-!
## D1 — MDS weighted-sum convergence (scaffolding)

This section provides a lightweight, non-committal statement for the
convergence of weighted sums of a martingale-difference sequence (MDS).
It is a placeholder theorems layer designed to be consumed by the
ODE/SA meta-theorem. The concrete proof (via L2-bounds and
Chebyshev/Borel–Cantelli, or via mathlib’s martingale convergence)
will be added later.
-/

namespace NOC
namespace Prob

/-- Hypotheses for 1D weighted MDS sums. The fields are intentionally
lightweight `Prop`s to keep this module independent of a specific
measure-theory API. Downstream instances (when available) can refine
these to mathlib statements. -/
structure MDSWeightedSumHypotheses where
  steps_sq_summable : Prop     -- ∑ b_n^2 < ∞
  mds_zero_mean     : Prop     -- E[ξ_{n+1} | 𝓕_n] = 0
  variance_bounded  : Prop     -- E[ξ_{n+1}^2 | 𝓕_n] ≤ σ^2

/-- Conclusion shape for the weighted MDS convergence. -/
structure MDSWeightedSumConclusion where
  L2_converges : Prop
  asexists_sum : Prop    -- almost sure existence of the infinite series

/-- D1 scaffold: weighted MDS convergence (statement-only layer).
Populate with a real proof once the probability layer lands. -/
def mds_weighted_sum_converges (H : MDSWeightedSumHypotheses)
    : MDSWeightedSumConclusion :=
  { L2_converges := True, asexists_sum := True }

end Prob
end NOC
