# Math Help

## Blocker — D6 interior-hit small-tail step

**File / goal:** `NOC_ROOT/NOC/D/TTSA_Convergence.lean`, section after `d6_scalar_RS_summable`.

### Current status
- The expectation-level RS lemma `d6_scalar_RS_summable` is complete:
  the series `∑ₙ (2 ε₀) bₙ · E[(K - βₙ)\_+]` converges.
- Next goal in the interior-hit chain is the almost-sure statement
  `∀ᵐ ω, ∑ₙ bₙ (K - βₙ(ω))\_+ < ∞`.
- Existing lemmas give:
  * `(K - βₙ(ω))\_+ ∈ [0, K]` for all `n, ω`;
  * `φₙ(ω) := (K - βₙ(ω))\_+` is integrable (and square-integrable).

### Sticking point
Need a Lean-friendly theorem/lemma that upgrades the non-negative,
integrable series from an L¹ (expectation) bound to an almost-surely
summable pointwise series. Concretely, with

```
variables (μ : Measure Ω) [IsProbabilityMeasure μ]
variables {f : ℕ → Ω → ℝ}
  (hf_pos : ∀ n ω, 0 ≤ f n ω)
  (hf_int : ∀ n, Integrable (f n) μ)
  (hf_sum : Summable (fun n => ∫ ω, f n ω ∂ μ))
```

I need guidance/a reference to conclude
`∀ᵐ ω ∂ μ, Summable (fun n => f n ω)`.
The intuitive argument is via Tonelli or monotone convergence on
non-negative series, but I have not located a ready-made lemma in mathlib,
and I want to avoid re-deriving too much measure-theory infrastructure.

### Requested help
Please point me to (or sketch) a Lean proof pattern that bridges
the expectation-level summability to almost-sure summability for a
non-negative series. Once I have that tool, I can finish the D6
interior-hit lemmas.
# Math Help

## Blocker — D6 interior-hit small-tail step

**File / goal:** `NOC_ROOT/NOC/D/TTSA_Convergence.lean`, lemma `d6_weighted_gap_ae_summable`.

### Current status
- Expectation-level RS lemma finished: `Summable (fun n => (2 ε₀) bₙ ∫ (K−βₙ)_+)`.
- Need to upgrade `∑ bₙ (K−βₙ(ω))_+` from L¹ control to a.s. summability for the interior-hit argument. I attempted a direct Tonelli/monotone convergence proof but ran into complications massaging
  ```
    ∫⁻ ω, Σ' n ENNReal.ofReal (bₙ φₙ(ω)) = Σ' n ENNReal.ofReal (bₙ ∫ φₙ)
  ```
  into the desired a.e. finiteness statement; the `lintegral` algebra is proving thorny.
- Specifically, matching the shapes `∫⁻ ENNReal.ofReal (bₙ φₙ)` and `ENNReal.ofReal (bₙ ∫ φₙ)` after pulling constants through (`integral_const_mul`, `ofReal_integral_eq_lintegral_ofReal`) keeps failing because Lean normalises the products in different orders, and I’m burning time juggling `mul_comm`/`mul_assoc` rewrites.

### What I need
1. A short, reusable lemma (or pattern) that takes
   * `hf_nonneg : ∀ n ω, 0 ≤ fₙ(ω)`,
   * `hf_int : ∀ n, Integrable fₙ μ`,
   * `hf_sum : Summable (fun n => ∫ fₙ)`,
   and returns `∀ᵐ ω, Summable fun n => fₙ(ω)`. We only need it in the scalar case (`ℝ`, nonnegative).
2. Alternatively, a concrete walkthrough of the Tonelli/monotone convergence argument tailored to `fₙ := bₙ (K-βₙ)_+`, with Lean-level details on how to show the pointwise sum is finite a.e.

Once I have that piece, finishing `d6_weighted_gap_ae_summable` and the interior-hit step should be straightforward.
