# Math Help

Context: NOC_ROOT/NOC/Prob/MDS.lean — D1: MDS weighted-sum convergence.

Status: Implemented full partial-sum API (martingale construction, variance
identity, L² and L¹ bounds) and completed the a.e. convergence proof.
We now call `MeasureTheory.Submartingale.ae_tendsto_limitProcess` with a
`NNReal` bound `R` on the L¹ norms, obtained via `Rnn := Rbound.toNNReal` and
`hbdd : ∀ n, eLpNorm (S n) 1 ≤ (Rnn : ℝ≥0∞)`.

Resolved — API signature for submartingale convergence:
- We use `MeasureTheory.Submartingale.ae_tendsto_limitProcess` (alternatively
  `exists_ae_tendsto_of_bdd`) from `Mathlib/Probability/Martingale/Convergence`.
- The bound type is `R : NNReal` and the hypothesis is
  `hbdd : ∀ n, eLpNorm (f n) (1 : ℝ≥0∞) μ ≤ (R : ℝ≥0∞)`.
- Invocation in our file (matching names):
  ```lean
  have h_tend : ∀ᵐ ω, Tendsto (fun n => h.partialSum b n ω) atTop
      (nhds (MeasureTheory.Filtration.limitProcess (fun n => h.partialSum b n) ℱ μ ω)) :=
    MeasureTheory.Submartingale.ae_tendsto_limitProcess
      (μ := μ) (ℱ := ℱ) (f := fun n => h.partialSum b n) (R := Rnn) hsub hbdd
  ```

Notes:
- Key details to make types line up:
  - Use `(1 : ℝ≥0∞)` as the exponent in `eLpNorm` for the L¹ bound.
  - Package the bound as `R : NNReal` via `Rnn := Rbound.toNNReal` and
    `(Rnn : ℝ≥0∞) = Rbound` (`ENNReal.coe_toNNReal`).
  - For the L²→L¹ pipeline, the pointwise identity
    `‖x‖ₑ^2 = ENNReal.ofReal (x^2)` is obtained with
    `Real.enorm_eq_ofReal_abs` and `ENNReal.ofReal_mul`.

Outcome:
- `weighted_sum_ae_converges` is proved and used to obtain a.e. convergence of
  the weighted MDS partial sums under `∑ b_n^2 < ∞` and a uniform second‑moment
  bound for the increments.
