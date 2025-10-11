Title: math help

Context
- Lean 4.23.0 + current mathlib in this repo.
- File in focus: NOC_ROOT/NOC/Prob/RobbinsSiegmund.lean.

Status snapshot
- Done/green:
  - MDS layer (NOC/Prob/MDS.lean), including weighted_sum_ae_converges.
  - RS v-sum partial bound and summability corollary (VSUM/VSUM_SUMMABLE).
  - RS L¹-uniform bound for the drifted normalized process (VSUM_L1BOUND), with NNReal packaging complete.
  - RS supermartingale wiring and convergence helper:
    • RSDrifted_supermartingale_of_RS (uses condExp_condExp_of_le + condExp_mono)
    • RSDrifted_ae_converges_of_RS (packages supermartingale + L¹ bound)

No further math help needed; prior API questions (tower property, monotonicity, base case, AE chaining) are resolved and implemented in the code.

Notes (already resolved; no help needed)
- L¹ constant packaging and ENNReal algebra are complete; RSDrifted_l1_uniform_bound_of_w_summable is green.
- Conditional-expectation algebra for the one-step RS bound is stable using a single constant C and condExp_add/condExp_const/condExp_smul.
- Weight algebra uses RSWeight_succ and mul_div_mul_right to obtain ((1+u n) * Y n ω) / W_{n+1} = (Y n ω) / W_n and rewrites back to *(1/W).

Pointers (file and lines)
- One-step CE block and assembly: NOC_ROOT/NOC/Prob/RobbinsSiegmund.lean:834–994.
- Supermartingale record + tower/mono induction: NOC_ROOT/NOC/Prob/RobbinsSiegmund.lean:997–1060.

Environment assumptions
- [IsFiniteMeasure μ], real-valued processes.
- Y adapted/integrable; u, v, w ≥ 0; RSWeight positivity available.

Implemented: hcond (tower+mono) and the supermartingale record for RSDrifted; the normalization convergence helper is live.
