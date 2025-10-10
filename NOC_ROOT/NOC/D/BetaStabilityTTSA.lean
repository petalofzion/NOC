import Mathlib
import NOC.B.Core
import NOC.B.Expectation

-- Silence common linter warnings for this file (place before declarations)
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unusedSectionVars false

/-!
Module: NOC.D.BetaStabilityTTSA
Status: scaffolding (with proof plan and tactic outline).

Implementation note (Tier‑2/Tier‑3): the file exposes both a property-based
projection interface (`ProjIccProps`) for SA/ODE style proofs and clamp wrappers
that simply reduce to those properties when `proj z = max 0 (min βmax z)`.
Prove the property lemmas once, then reuse them via the wrappers when working
with concrete clamp projections.

Refines Lemma D (β-stability) with a two-time-scale stochastic-approximation (TTSA)
framework suitable for an ODE method proof. This module encodes:

- TTSA schedules and martingale-noise hypotheses;
- a meta-regularizer with a bounded derivative on [0, β_max];
- a local positive-acceleration window (from Lemma B’s expectation layer);
- a projected recursion for the meta-parameter β_meta;
- the target drift inequality and a placeholder stability theorem.

Proof plan (high-level):
1) Model: β_{n+1} = Proj_[0,β_max](β_n + b_n·(E[Δ²U(θ_n)] − r'(β_n) + noise_slow_n)).
   The fast variable θ_n follows θ_{n+1} = θ_n + a_n·(h(θ_n, β_n) + noise_fast_n).
2) Assumptions: a_n,b_n satisfy SA conditions; b_n/a_n → 0 (two-time-scale separation);
   noise terms are MDS with bounded variances; θ-drift is locally Lipschitz and admits
   a compact attractor for fixed β in a neighborhood (standard TTSA hypotheses);
   from Lemma B (expectation layer), there is a region where E[Δ²U] ≥ ε > 0.
3) Deterministic ODE limits (Benaïm–Hofbauer–Sorins): the slow ODE is β' = ḡ(β) with
   ḡ(β) ≈ E_π[Δ²U(θ*(β))] − r'(β), where θ*(β) is an attracting set of the fast system
   at frozen β. Use compactness/invariance to ensure well-defined selection.
4) Drift positivity: for β in [0,β_max] within the acceleration window, ḡ(β) ≥ ε − sup|r'|.
   With an appropriate regularizer bound, this is strictly positive near β=0, yielding
   drift toward the interior (β increases).
5) Stability: use projected SA/TTSA theorems to show β_n remains in a compact subset of (0,β_max]
   and converges to an internally stable set where ḡ(β)=0 (a positive fixed point β⋆).

Tactic outline:
- Encode schedules/noise/regularity as `Prop` fields (done below) for gradual instantiation.
- State a drift inequality lemma: for β in Set.Icc(0,β_max) and θ in the invariant set,
  have g p θ β ≥ Window.ε. Package as `g_lower` plus `Reg.deriv_bound` once formalized.
- Apply standard SA/TTSA theorems (once available in mathlib or local library) to upgrade
  the stochastic recursion to ODE behaviour; then apply the projected stochastic-approximation
  stability lemma to conclude positive drift and compact invariance of β.
  In Lean: structure the proof into
    • measurability/adaptedness (opaque here),
    • Lyapunov/drift inequalities,
    • application of an SA meta-theorem.
Currently we keep a placeholder theorem to unblock downstream modules.
-/

namespace NOC
noncomputable section
open Classical

/-- Step-size schedules for TTSA: `θ` runs at the fast rate `a_n`, and
    the meta-parameter β runs at the slow rate `b_n`. -/
structure TTSASchedules where
  a : ℕ → ℝ
  b : ℕ → ℝ
  a_pos : ∀ n, 0 < a n
  b_pos : ∀ n, 0 < b n
  a_summable : Prop    -- ∑ a_n = ∞ and ∑ a_n^2 < ∞ (packed as Prop placeholders)
  a_square_summable : Prop
  b_summable : Prop
  b_square_summable : Prop
  scale_separation : Prop  -- b_n / a_n → 0

/-- Noise hypotheses: martingale-difference noise with bounded conditional variance,
    packed as Prop placeholders to be instantiated in a concrete model. -/
structure TTSANoise where
  mds_fast : Prop
  mds_slow : Prop
  var_bound_fast : Prop
  var_bound_slow : Prop

/-- Meta-regularizer with bounded derivative on [0, β_max]. -/
structure MetaReg where
  βmax : ℝ
  βmax_nonneg : 0 ≤ βmax
  r : ℝ → ℝ
  r' : ℝ → ℝ
  r0 : r 0 = 0
  deriv_bound : Prop   -- ∀β∈[0,βmax], |r'(β)| ≤ c_reg

/-- Positive-acceleration window: records that in a local region the expected
    Δ²U is bounded below by ε > 0, which drives the sign of the meta-gradient. -/
structure AccelWindow where
  ε : ℝ
  ε_pos : 0 < ε
  local_ok : Prop

/-- Projected TTSA recursion for the meta-parameter. -/
structure BetaTTSAContext where
  Schedules : TTSASchedules
  Noise : TTSANoise
  Reg : MetaReg
  Window : AccelWindow
  Params : Type
  -- fast variable θ and its drift (opaque here; provided by the model)
  θ : Type
  driftθ : Params → ℝ → θ → θ
  -- meta-gradient surrogate g(θ, β) that aligns with E[Δ²U] − r'(β)
  g : Params → θ → ℝ → ℝ
  g_lower : ∀ (p : Params) (θ : θ) (β : ℝ), β ∈ Set.Icc (0 : ℝ) Reg.βmax → g p θ β ≥ Window.ε
  -- projection of β to [0, βmax]
  proj : ℝ → ℝ := fun β => max 0 (min Reg.βmax β)
  proj_is_clamp : ∀ z, proj z = max 0 (min Reg.βmax z)

@[simp] lemma BetaTTSAContext.proj_eval (ctx : BetaTTSAContext) (z : ℝ) :
  ctx.proj z = max 0 (min ctx.Reg.βmax z) := ctx.proj_is_clamp z

/-! ### Skeleton: projected recursion and drift lemmas -/

/-- Projected slow update for β at step `n`. -/
def betaUpdate (ctx : BetaTTSAContext) (p : ctx.Params) (θ : ctx.θ) (β : ℝ) (n : ℕ) : ℝ :=
  ctx.proj (β + (ctx.Schedules.b n) * (ctx.g p θ β))

/-- On the positive-acceleration window and within the projection interval, the drift is
bounded below by a positive constant (to be tuned with the regularizer derivative bound). -/
lemma beta_drift_lower_on_window
  (ctx : BetaTTSAContext) (p : ctx.Params) (θ : ctx.θ) {β : ℝ}
  (hβ : β ∈ Set.Icc (0 : ℝ) ctx.Reg.βmax) :
  ctx.g p θ β ≥ ctx.Window.ε := by
  exact ctx.g_lower p θ β hβ

/-! ### Lemma D (TTSA form) — placeholder statement
Intended statement: under the TTSA and regularity hypotheses above, the projected
recursion for β drifts toward a positive fixed point β⋆ and remains in a compact subset
of (0, β_max]. The present lemma is a placeholder (`True`) to keep the code compiling;
replace with the nontrivial statement as the SA library is instantiated.
-/
theorem lemmaD_beta_stability_TTSA (ctx : BetaTTSAContext) : True := by
  trivial

/-- Deterministic one-dimensional lower-drift recursion: define a β-sequence by
`β_{n+1} = proj(β_n + b_n * g_n)` where `proj` clamps into `[0, βmax]` and `g_n ≥ ε > 0`
whenever `β_n ≤ β⋆`. If `∑ b_n` diverges and `β_0 ≤ β⋆ ≤ βmax`, then the sequence eventually
exceeds `β⋆`. This is the standard stepping-stone used in TTSA proofs before introducing ODE tools. -/
structure DriftHitThresholdContext where
  βmax : ℝ
  βstar : ℝ
  ε : ℝ
  b : ℕ → ℝ
  g : ℕ → ℝ
  β0 : ℝ
  proj : ℝ → ℝ := fun β => max 0 (min βmax β)
  proj_is_clamp : ∀ z, proj z = max 0 (min βmax z)
  βstar_within : 0 ≤ βstar ∧ βstar ≤ βmax
  ε_pos : 0 < ε
  b_nonneg : ∀ n, 0 ≤ b n
  g_lb : ∀ n, g n ≥ ε   -- use the robust case; variants can make it conditional on β_n ≤ β⋆
  β0_within : 0 ≤ β0 ∧ β0 ≤ βstar
  sum_b_diverges : Filter.Tendsto (fun N => (Finset.range N).sum b) Filter.atTop Filter.atTop

/-- Define the recursion `β_{n+1} = proj(β_n + b_n * g_n)`. -/
def DriftHitThresholdContext.betaSeq (C : DriftHitThresholdContext) : ℕ → ℝ
  | 0     => C.β0
  | n + 1 => C.proj (C.betaSeq n + C.b n * C.g n)

@[simp] lemma DriftHitThresholdContext.proj_eval (C : DriftHitThresholdContext) (z : ℝ) :
  C.proj z = max 0 (min C.βmax z) := C.proj_is_clamp z


/-! ### Canonical TTSA stepping lemmas (β-dependent drift) -/

namespace TTSA

/-! Projection properties (property-based interface).
These properties characterize a projection onto `[0, βmax]` without
requiring definitional equality with the clamp. -/

/-- Projection properties onto `[0, βmax]`. -/
structure ProjIccProps (βmax : ℝ) (proj : ℝ → ℝ) : Prop where
  range : ∀ z, 0 ≤ proj z ∧ proj z ≤ βmax
  fixed_on : ∀ {z}, 0 ≤ z ∧ z ≤ βmax → proj z = z
  monotone : Monotone proj

/-- Standard β-update (projected) with β-dependent drift `g`. -/
structure BetaUpdate where
  βmax : ℝ
  b    : ℕ → ℝ
  g    : ℝ → ℝ
  proj : ℝ → ℝ := fun z => max 0 (min βmax z)

/-- Canonical update step derived from the projection and drift. -/
def BetaUpdate.update (P : BetaUpdate) (β : ℝ) (n : ℕ) : ℝ :=
  P.proj (β + P.b n * P.g β)

@[simp] lemma BetaUpdate.update_eval (P : BetaUpdate) (β : ℝ) (n : ℕ) :
  BetaUpdate.update P β n = P.proj (β + P.b n * P.g β) := rfl

/-- Iterate the β-update starting from an initial value. -/
def iter (P : BetaUpdate) (β0 : ℝ) : ℕ → ℝ
| 0     => β0
| n + 1 => P.update (iter P β0 n) n

/-! Convenience: properties for the canonical clamp projection. -/

/-- The canonical clamp onto `[0, βmax]`. -/
def clamp (βmax : ℝ) (z : ℝ) : ℝ := max 0 (min βmax z)

/-- The clamp projection satisfies the standard projection properties. -/
lemma clamp_props (βmax : ℝ) (hβmax : 0 ≤ βmax) :
    ProjIccProps βmax (clamp βmax) := by
  refine ⟨?range, ?fixed, ?mono⟩
  · intro z
    refine ⟨?low, ?high⟩
    · exact le_max_left _ _
    ·
      have h0 : 0 ≤ βmax := hβmax
      have hmin : min βmax z ≤ βmax := min_le_left _ _
      exact (max_le_iff.mpr ⟨h0, hmin⟩)
  · intro z hz
    have hmin : min βmax z = z := min_eq_right hz.2
    have hmax : max 0 z = z := max_eq_right hz.1
    simpa [clamp, hmin, hmax]
  · intro x y hxy
    have hminβ : min βmax x ≤ βmax := min_le_left _ _
    have hminy : min βmax x ≤ y :=
      le_trans (min_le_right _ _) hxy
    have hmin : min βmax x ≤ min βmax y :=
      le_min hminβ hminy
    have h0 : 0 ≤ max 0 (min βmax y) := le_max_left _ _
    have hxle : min βmax x ≤ max 0 (min βmax y) :=
      le_trans hmin (le_max_right _ _)
    exact (max_le_iff.mpr ⟨h0, hxle⟩)

/-- If a projection equals the clamp pointwise, it inherits the interval properties. -/
lemma props_of_is_clamp
  {βmax : ℝ} {proj : ℝ → ℝ}
  (hβmax : 0 ≤ βmax)
  (hproj : ∀ z, proj z = clamp βmax z) :
  ProjIccProps βmax proj := by
  have hclamp : ProjIccProps βmax (clamp βmax) := clamp_props βmax hβmax
  refine ⟨?range, ?fixed, ?mono⟩
  · intro z
    simpa [clamp, hproj z] using (hclamp.range z)
  · intro z hz
    have hz' := hclamp.fixed_on (by simpa using hz)
    simpa [clamp, hproj z] using hz'
  · intro x y hxy
    have := hclamp.monotone hxy
    simpa [clamp, hproj x, hproj y] using this

/-- Canonical β-update using the clamp projection. -/
def BetaUpdate.clamped (βmax : ℝ) (b : ℕ → ℝ) (g : ℝ → ℝ) : BetaUpdate :=
  { βmax := βmax, b := b, g := g, proj := clamp βmax }

/-- Clamp-based update inherits the projection properties. -/
lemma BetaUpdate.clamped_props
  (βmax : ℝ) (hβmax : 0 ≤ βmax) (b : ℕ → ℝ) (g : ℝ → ℝ) :
  ProjIccProps βmax (BetaUpdate.clamped βmax b g).proj := by
  have hproj : ∀ z, (BetaUpdate.clamped βmax b g).proj z = clamp βmax z := by
    intro z; rfl
  exact props_of_is_clamp hβmax hproj

/-- Bounds invariance: the projected update stays in `[0, βmax]`. -/
lemma update_bounds
  (P : BetaUpdate) (props : ProjIccProps P.βmax P.proj)
  (β : ℝ) (n : ℕ) :
  0 ≤ P.update β n ∧ P.update β n ≤ P.βmax := by
  obtain ⟨hlo, hup⟩ := props.range (β + P.b n * P.g β)
  have hlo' : 0 ≤ P.update β n := by
    simpa [BetaUpdate.update_eval] using hlo
  have hup' : P.update β n ≤ P.βmax := by
    simpa [BetaUpdate.update_eval] using hup
  exact ⟨hlo', hup'⟩

/-- Iteration bounds: if β₀ is within `[0, βmax]`, every iterate stays inside. -/
lemma iter_bounds
  (P : BetaUpdate) (props : ProjIccProps P.βmax P.proj)
  (β0 : ℝ) (hβ0 : 0 ≤ β0 ∧ β0 ≤ P.βmax) :
  ∀ n, 0 ≤ iter P β0 n ∧ iter P β0 n ≤ P.βmax := by
  intro n
  induction n with
  | zero =>
      simpa [iter] using hβ0
  | succ n ih =>
      simpa [iter] using update_bounds P props (iter P β0 n) n

/-- Update monotonicity on a window: if `proj` and `g` are monotone, the update preserves order. -/
lemma update_monotone_on_window
  (βstar : ℝ) (P : BetaUpdate)
  (proj_mono : Monotone P.proj)
  (n : ℕ) (hb : 0 ≤ P.b n)
  (gmono : ∀ {β β'}, 0 ≤ β ∧ β ≤ βstar → 0 ≤ β' ∧ β' ≤ βstar → β ≤ β' → P.g β ≤ P.g β')
  {β β'}
  (hβ : 0 ≤ β ∧ β ≤ βstar)
  (hβ' : 0 ≤ β' ∧ β' ≤ βstar)
  (hle : β ≤ β') :
  P.update β n ≤ P.update β' n := by
  have hgle : P.g β ≤ P.g β' := gmono hβ hβ' hle
  have hmul : P.b n * P.g β ≤ P.b n * P.g β' :=
    mul_le_mul_of_nonneg_left hgle hb
  have hsum : β + P.b n * P.g β ≤ β' + P.b n * P.g β' :=
    add_le_add hle hmul
  have hproj := proj_mono hsum
  simpa [BetaUpdate.update] using hproj

/-- Drift lower bound ⇒ monotone growth under projection (arithmetic lemma). -/
theorem beta_drift_lower_bound_props
    (βstar ε : ℝ) (P : BetaUpdate)
    (hε : 0 ≤ ε)
    (hβstar : βstar ≤ P.βmax)
    (hb : ∀ n, 0 ≤ P.b n)
    (hg : ∀ β, 0 ≤ β ∧ β ≤ βstar → P.g β ≥ ε)
    (hproj : ProjIccProps P.βmax P.proj) :
    ∀ (β : ℝ) (n : ℕ), 0 ≤ β ∧ β ≤ βstar → P.update β n ≥ β := by
  intro β n hβ
  have hβ_le_max : β ≤ P.βmax := le_trans hβ.2 hβstar
  have hproj_id : P.proj β = β :=
    hproj.fixed_on ⟨hβ.1, hβ_le_max⟩
  have hg_ge : P.g β ≥ ε := hg β hβ
  have hg_nonneg : 0 ≤ P.g β := le_trans hε hg_ge
  have hmul_nonneg : 0 ≤ P.b n * P.g β := mul_nonneg (hb n) hg_nonneg
  have hsum : β ≤ β + P.b n * P.g β := le_add_of_nonneg_right hmul_nonneg
  have hmono := hproj.monotone hsum
  have hineq : β ≤ P.proj (β + P.b n * P.g β) := by
    simpa [hproj_id] using hmono
  simpa [BetaUpdate.update] using hineq

/-- Hitting a target level under infinite mass (∑ b_n = ∞) and positive drift. -/
theorem beta_hits_target_props
    (β0 βstar ε : ℝ) (P : BetaUpdate)
    (hβ : βstar < P.βmax) (hε : 0 < ε)
    (hβstar : βstar ≤ P.βmax)
    (hb : ∀ n, 0 ≤ P.b n)
    (hbSum : Filter.Tendsto (fun N => (Finset.range N).sum P.b) Filter.atTop Filter.atTop)
    (hg : ∀ β, 0 ≤ β ∧ β ≤ βstar → P.g β ≥ ε)
    (hproj : ProjIccProps P.βmax P.proj)
    (hβ0 : 0 ≤ β0 ∧ β0 ≤ βstar) :
    ∃ N, (iter P β0 N) ≥ βstar := by
  classical
  -- Assume no iterate reaches β⋆ and derive a contradiction.
  by_contra hno
  have hlt : ∀ n, iter P β0 n < βstar := by
    intro n
    have hn := (not_exists.mp hno) n
    exact lt_of_not_ge hn
  let S : ℕ → ℝ := fun N => (Finset.range N).sum P.b
  have hβmax_nonneg : 0 ≤ P.βmax :=
    le_trans hβ0.1 (le_trans hβ0.2 hβstar)
  -- Iterates stay within the projection bounds.
  have hβ0_le_max : β0 ≤ P.βmax := le_trans hβ0.2 hβstar
  have hbounds := iter_bounds P hproj β0 ⟨hβ0.1, hβ0_le_max⟩
  -- Lower bound iterates by accumulating the ε-weighted steps.
  have hlower : ∀ n, iter P β0 n ≥ β0 + ε * S n := by
    refine Nat.rec ?base ?step
    · simp [S, iter]
    · intro n ih
      set βn := iter P β0 n with hβn_def
      have hβn_lt : βn < βstar := by simpa [hβn_def] using hlt n
      have hβn_bounds := hbounds n
      obtain ⟨hβn_nonneg, hβn_le_max⟩ := hβn_bounds
      have hβn_le_star : βn ≤ βstar := le_of_lt hβn_lt
      have hg_ge : P.g βn ≥ ε := hg βn ⟨hβn_nonneg, hβn_le_star⟩
      have hg_nonneg : 0 ≤ P.g βn := le_trans hε.le hg_ge
      have hmul_nonneg : 0 ≤ P.b n * P.g βn := mul_nonneg (hb n) hg_nonneg
      have harg_nonneg : 0 ≤ βn + P.b n * P.g βn := add_nonneg hβn_nonneg hmul_nonneg
      have hproj_beta : P.proj P.βmax = P.βmax :=
        hproj.fixed_on ⟨hβmax_nonneg, le_rfl⟩
      have harg_le_max : βn + P.b n * P.g βn ≤ P.βmax := by
        by_contra hgt
        have hgt' : P.βmax < βn + P.b n * P.g βn := lt_of_not_ge hgt
        have hproj_ge : P.βmax ≤ P.proj (βn + P.b n * P.g βn) := by
          have hle : P.βmax ≤ βn + P.b n * P.g βn := le_of_lt hgt'
          have hmono := hproj.monotone hle
          simpa [hproj_beta] using hmono
        have hproj_le : P.proj (βn + P.b n * P.g βn) ≤ P.βmax := (hproj.range _).2
        have hproj_eq : P.proj (βn + P.b n * P.g βn) = P.βmax :=
          le_antisymm hproj_le hproj_ge
        have hnext_eq : iter P β0 (n + 1) = P.βmax := by
          simpa [iter, BetaUpdate.update, hβn_def, hproj_eq]
        have hnext_ge : βstar ≤ iter P β0 (n + 1) := by
          simpa [hnext_eq] using hβstar
        exact (not_lt.mpr hnext_ge) (hlt (n + 1))
      have hproj_arg : P.proj (βn + P.b n * P.g βn) = βn + P.b n * P.g βn :=
        hproj.fixed_on ⟨harg_nonneg, harg_le_max⟩
      have hiter_succ : iter P β0 (n + 1) = βn + P.b n * P.g βn := by
        simpa [iter, BetaUpdate.update, hproj_arg, hβn_def]
      have hmul_eps : ε * P.b n ≤ P.b n * P.g βn := by
        have := mul_le_mul_of_nonneg_left hg_ge (hb n)
        simpa [mul_comm] using this
      have hge_step : iter P β0 (n + 1) ≥ βn + ε * P.b n := by
        have := add_le_add_left hmul_eps βn
        simpa [hiter_succ, add_comm, add_left_comm, add_assoc, mul_comm] using this
      have hsum_le : β0 + ε * S n + ε * P.b n ≤ βn + ε * P.b n :=
        add_le_add_right ih (ε * P.b n)
      have hgoal : iter P β0 (n + 1) ≥ β0 + ε * S (n + 1) := by
        have htrans := le_trans hsum_le hge_step
        simpa [S, Finset.sum_range_succ, Nat.succ_eq_add_one, add_comm,
              add_left_comm, add_assoc, mul_add] using htrans
      exact hgoal
  -- Divergence of ∑ b_n ensures the accumulated drift exceeds β⋆ − β₀.
  have hEV := Filter.tendsto_atTop.1 hbSum ((βstar - β0) / ε)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hEV
  have hSN : (βstar - β0) / ε ≤ S N := hN N (le_rfl)
  have hdiff : βstar - β0 ≤ ε * S N := by
    have hεne : ε ≠ 0 := ne_of_gt hε
    have htmp := mul_le_mul_of_nonneg_left hSN hε.le
    have hlhs : ε * ((βstar - β0) / ε) = βstar - β0 := by
      field_simp [hεne, sub_eq_add_neg]
    simpa [S, hlhs, mul_comm, mul_left_comm, mul_assoc] using htmp
  have htarget : βstar ≤ β0 + ε * S N := by
    have := add_le_add_right hdiff β0
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc, mul_comm] using this
  have hiter_ge : βstar ≤ iter P β0 N :=
    le_trans htarget (hlower N)
  exact (not_lt.mpr hiter_ge) (hlt N)

/-- Clamp-based drift lemma: delegates to the property-based version via `props_of_is_clamp`. -/
theorem beta_drift_lower_bound
    (βstar ε : ℝ) (P : BetaUpdate)
    (hε : 0 ≤ ε)
    (hβstar : βstar ≤ P.βmax)
    (hb : ∀ n, 0 ≤ P.b n)
    (hg : ∀ β, 0 ≤ β ∧ β ≤ βstar → P.g β ≥ ε)
    (hproj : ∀ z, P.proj z = clamp P.βmax z) :
    ∀ (β : ℝ) (n : ℕ), 0 ≤ β ∧ β ≤ βstar → P.update β n ≥ β := by
  intro β n hβ
  have hβmax : 0 ≤ P.βmax :=
    le_trans hβ.1 (le_trans hβ.2 hβstar)
  have props : ProjIccProps P.βmax P.proj :=
    props_of_is_clamp hβmax hproj
  exact beta_drift_lower_bound_props βstar ε P hε hβstar hb hg props β n hβ

/-- Clamp-based hitting lemma: delegates to the property-based version via `props_of_is_clamp`. -/
theorem beta_hits_target
    (β0 βstar ε : ℝ) (P : BetaUpdate)
    (hβ : βstar < P.βmax) (hε : 0 < ε)
    (hβstar : βstar ≤ P.βmax)
    (hb : ∀ n, 0 ≤ P.b n)
    (hbSum : Filter.Tendsto (fun N => (Finset.range N).sum P.b) Filter.atTop Filter.atTop)
    (hg : ∀ β, 0 ≤ β ∧ β ≤ βstar → P.g β ≥ ε)
    (hproj : ∀ z, P.proj z = clamp P.βmax z)
    (hβ0 : 0 ≤ β0 ∧ β0 ≤ βstar) :
    ∃ N, (iter P β0 N) ≥ βstar := by
  have hβmax : 0 ≤ P.βmax :=
    le_trans hβ0.1 (le_trans hβ0.2 hβstar)
  have props : ProjIccProps P.βmax P.proj :=
    props_of_is_clamp hβmax hproj
  exact beta_hits_target_props β0 βstar ε P hβ hε hβstar hb hbSum hg props hβ0

end TTSA

/-- Property-based variant of the one-dimensional drift recursion used by TTSA. -/
structure DriftHitThresholdPropsContext where
  βmax : ℝ
  βstar : ℝ
  ε : ℝ
  b : ℕ → ℝ
  g : ℕ → ℝ
  β0 : ℝ
  proj : ℝ → ℝ
  props : TTSA.ProjIccProps βmax proj
  βstar_within : 0 ≤ βstar ∧ βstar ≤ βmax
  ε_pos : 0 < ε
  b_nonneg : ∀ n, 0 ≤ b n
  g_lb : ∀ n, g n ≥ ε
  β0_within : 0 ≤ β0 ∧ β0 ≤ βstar
  sum_b_diverges : Filter.Tendsto (fun N => (Finset.range N).sum b) Filter.atTop Filter.atTop

def DriftHitThresholdPropsContext.betaSeq (C : DriftHitThresholdPropsContext) : ℕ → ℝ
  | 0     => C.β0
  | n + 1 => C.proj (C.betaSeq n + C.b n * C.g n)

/-- Property-based hitting lemma (preferred Tier‑3 target). -/
theorem DriftHitThresholdPropsContext.hits_threshold_props
  (C : DriftHitThresholdPropsContext) :
  ∃ N, C.betaSeq N ≥ C.βstar := by
  classical
  by_contra hno
  have hlt : ∀ n, C.betaSeq n < C.βstar := by
    intro n
    have hn := (not_exists.mp hno) n
    exact lt_of_not_ge hn
  let S : ℕ → ℝ := fun N => (Finset.range N).sum C.b
  have hβmax_nonneg : 0 ≤ C.βmax :=
    le_trans C.β0_within.1 (le_trans C.β0_within.2 C.βstar_within.2)
  have hbounds : ∀ n, 0 ≤ C.betaSeq n ∧ C.betaSeq n ≤ C.βmax := by
    intro n
    induction n with
    | zero =>
        exact ⟨C.β0_within.1, le_trans C.β0_within.2 C.βstar_within.2⟩
    | succ n ih =>
        have h := C.props.range (C.betaSeq n + C.b n * C.g n)
        simpa [DriftHitThresholdPropsContext.betaSeq] using h
  have hβmax_proj : C.proj C.βmax = C.βmax :=
    C.props.fixed_on ⟨hβmax_nonneg, le_rfl⟩
  have hlower : ∀ n, C.betaSeq n ≥ C.β0 + C.ε * S n := by
    refine Nat.rec ?base ?step
    · have hsum_zero : S 0 = 0 := by
        unfold S
        simp
      have hbeta_zero : C.betaSeq 0 = C.β0 := rfl
      simpa [hbeta_zero, hsum_zero]
    · intro n ih
      set βn := C.betaSeq n with hβn_def
      have hβn_lt : βn < C.βstar := by simpa [hβn_def] using hlt n
      have hβn_bounds := hbounds n
      obtain ⟨hβn_nonneg, hβn_le_max⟩ := hβn_bounds
      have hmul_nonneg : 0 ≤ C.b n * C.g n :=
        mul_nonneg (C.b_nonneg n) (le_trans (le_of_lt C.ε_pos) (C.g_lb n))
      have harg_nonneg : 0 ≤ βn + C.b n * C.g n := add_nonneg hβn_nonneg hmul_nonneg
      have harg_le_max : βn + C.b n * C.g n ≤ C.βmax := by
        by_contra hgt
        have hgt' : C.βmax < βn + C.b n * C.g n := lt_of_not_ge hgt
        have hproj_ge : C.βmax ≤ C.proj (βn + C.b n * C.g n) := by
          have hle : C.βmax ≤ βn + C.b n * C.g n := le_of_lt hgt'
          have hmono := C.props.monotone hle
          simpa [hβmax_proj] using hmono
        have hproj_le : C.proj (βn + C.b n * C.g n) ≤ C.βmax := (C.props.range _).2
        have hproj_eq : C.proj (βn + C.b n * C.g n) = C.βmax :=
          le_antisymm hproj_le hproj_ge
        have hnext_eq : C.betaSeq (n + 1) = C.βmax := by
          simpa [DriftHitThresholdPropsContext.betaSeq, hβn_def, hproj_eq]
        have hnext_ge : C.βstar ≤ C.betaSeq (n + 1) := by
          simpa [hnext_eq] using C.βstar_within.2
        exact (not_lt.mpr hnext_ge) (hlt (n + 1))
      have hproj_arg : C.proj (βn + C.b n * C.g n) = βn + C.b n * C.g n :=
        C.props.fixed_on ⟨harg_nonneg, harg_le_max⟩
      have hnext_eq : C.betaSeq (n + 1) = βn + C.b n * C.g n := by
        simpa [DriftHitThresholdPropsContext.betaSeq, hβn_def, hproj_arg]
      have hmul_eps : C.ε * C.b n ≤ C.b n * C.g n := by
        have := mul_le_mul_of_nonneg_left (C.g_lb n) (C.b_nonneg n)
        simpa [mul_comm] using this
      have hge_step : βn + C.ε * C.b n ≤ C.betaSeq (n + 1) := by
        have := add_le_add_left hmul_eps βn
        simpa [hnext_eq, add_comm, add_left_comm, add_assoc, mul_comm] using this
      have hsum_le : C.β0 + C.ε * S n + C.ε * C.b n ≤ βn + C.ε * C.b n :=
        add_le_add_right ih (C.ε * C.b n)
      have hsum_succ : S (n + 1) = S n + C.b n := by
        unfold S
        simp [Finset.sum_range_succ, Nat.succ_eq_add_one]
      have htrans := le_trans hsum_le hge_step
      have : C.β0 + C.ε * S (n + 1) ≤ C.betaSeq (n + 1) := by
        simpa [hsum_succ, mul_add, add_comm, add_left_comm, add_assoc] using htrans
      exact this
  have hEV := Filter.tendsto_atTop.1 C.sum_b_diverges
      ((C.βstar - C.β0) / C.ε)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hEV
  have hSN : (C.βstar - C.β0) / C.ε ≤ S N := hN N le_rfl
  have hdiff : C.βstar - C.β0 ≤ C.ε * S N := by
    have hεne : C.ε ≠ 0 := ne_of_gt C.ε_pos
    have htmp := mul_le_mul_of_nonneg_left hSN (le_of_lt C.ε_pos)
    have hlhs : C.ε * ((C.βstar - C.β0) / C.ε) = C.βstar - C.β0 := by
      field_simp [hεne, sub_eq_add_neg]
    simpa [S, hlhs, mul_comm, mul_left_comm, mul_assoc] using htmp
  have htarget : C.βstar ≤ C.β0 + C.ε * S N := by
    have := add_le_add_right hdiff C.β0
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc, mul_comm] using this
  have hge := le_trans htarget (hlower N)
  exact (not_lt.mpr hge) (hlt N)

/-- Consolidated monotonicity on a drift window for the clamped update.
If `g(β) ≥ ε ≥ 0` for all `β ∈ [0, β⋆]` and `b n ≥ 0`, then every one‑step update
is non‑decreasing on that window (and clamped into `[0, βmax]`). This is a convenient
front‑door statement bundling `beta_drift_lower_bound_props` for callers. -/
theorem clamped_monotone_on_window
    (βstar ε : ℝ) (P : TTSA.BetaUpdate)
    (hε : 0 ≤ ε)
    (hβstar : βstar ≤ P.βmax)
    (hb : ∀ n, 0 ≤ P.b n)
    (hg : ∀ β, 0 ≤ β ∧ β ≤ βstar → P.g β ≥ ε)
    (hproj : TTSA.ProjIccProps P.βmax P.proj) :
    ∀ (β : ℝ) (n : ℕ), 0 ≤ β ∧ β ≤ βstar → P.update β n ≥ β :=
  TTSA.beta_drift_lower_bound_props βstar ε P hε hβstar hb hg hproj

/-- Consolidated hitting time under a positive‑drift window for the clamped update.
If `g(β) ≥ ε > 0` for `β ∈ [0, β⋆]`, `b n ≥ 0` with `∑ b(n) = ∞`, and `β0 ≤ β⋆ ≤ βmax`, then
the clamped recursion `β_{n+1} = proj(β_n + b_n g(β_n))` reaches `β⋆` in finite time. -/
theorem clamped_hitting_time_under_window
    (β0 βstar ε : ℝ) (P : TTSA.BetaUpdate)
    (hβ : βstar < P.βmax) (hε : 0 < ε)
    (hβstar : βstar ≤ P.βmax)
    (hb : ∀ n, 0 ≤ P.b n)
    (hbSum : Filter.Tendsto (fun N => (Finset.range N).sum P.b) Filter.atTop Filter.atTop)
    (hg : ∀ β, 0 ≤ β ∧ β ≤ βstar → P.g β ≥ ε)
    (hproj : TTSA.ProjIccProps P.βmax P.proj)
    (hβ0 : 0 ≤ β0 ∧ β0 ≤ βstar) :
    ∃ N, (TTSA.iter P β0 N) ≥ βstar :=
  TTSA.beta_hits_target_props β0 βstar ε P hβ hε hβstar hb hbSum hg hproj hβ0

/-- Clamp-based hitting lemma delegating to the property-based variant. -/
theorem DriftHitThresholdContext.hits_threshold
  (C : DriftHitThresholdContext) :
  ∃ N, C.betaSeq N ≥ C.βstar := by
  classical
  have hβ0_le : C.β0 ≤ C.βmax :=
    le_trans C.β0_within.2 C.βstar_within.2
  have hβmax : 0 ≤ C.βmax := le_trans C.β0_within.1 hβ0_le
  have props : TTSA.ProjIccProps C.βmax C.proj :=
    TTSA.props_of_is_clamp (βmax:=C.βmax) (proj:=C.proj)
      hβmax C.proj_is_clamp
  let Cp : DriftHitThresholdPropsContext :=
  { βmax := C.βmax, βstar := C.βstar, ε := C.ε,
    b := C.b, g := C.g, β0 := C.β0, proj := C.proj,
    props := props,
    βstar_within := C.βstar_within,
    ε_pos := C.ε_pos,
    b_nonneg := C.b_nonneg,
    g_lb := C.g_lb,
    β0_within := C.β0_within,
    sum_b_diverges := C.sum_b_diverges }
  have hβseq : ∀ n, Cp.betaSeq n = C.betaSeq n := by
    intro n; induction n with
    | zero => rfl
    | succ n ih =>
        have hproj := C.proj_is_clamp (C.betaSeq n + C.b n * C.g n)
        have hproj_fun : Cp.proj = C.proj := rfl
        have hb : Cp.b = C.b := rfl
        have hg : Cp.g = C.g := rfl
        simpa [DriftHitThresholdPropsContext.betaSeq, DriftHitThresholdContext.betaSeq, ih,
          hproj_fun, hb, hg] using hproj
  obtain ⟨N, hN⟩ := DriftHitThresholdPropsContext.hits_threshold_props Cp
  refine ⟨N, ?_⟩
  simpa [hβseq N] using hN

end
end NOC

/-! ## Lemma D — β-stability under a positive‑drift window (clamped, finitary)

This theorem packages the deterministic stepping results into a NOC‑flavored
statement: given a positive‑drift window and a divergent slow step‑size mass,
the clamped β‑update reaches any target level β⋆ below βmax in finite time.
This is the “front‑door” stability consequence needed by NOC; it does not yet
use SA/ODE machinery (noise/separation), and is axiom‑free.
-/

namespace NOC
open Classical

/-- Lemma D (β‑stability under a positive‑drift window, clamped update).
Context:
- `ctx` carries the β‑max clamp, per‑step slow step sizes `b`, and a surrogate
  meta‑gradient `g` that admits a uniform positive lower bound `ε` on a window.
- Fix any parameters `p` and fast state `θ`; define the clamped update with
  `βmax := ctx.Reg.βmax`, `b := ctx.Schedules.b`, and `g(β) := ctx.g p θ β`.

Claim:
- If `0 < ε := ctx.Window.ε`, `β0 ≤ β⋆ < βmax`, `β⋆ ≤ βmax`, `b n ≥ 0`, and the
  partial sums `∑_{n<N} b n` diverge to `+∞`, then there exists `N` such that
  the clamped recursion reaches the target: `β_N ≥ β⋆`.

This is a direct consequence of the consolidated hitting lemma
`clamped_hitting_time_under_window` specialized to the NOC context. -/
theorem lemmaD_beta_stability_TTSA_window
  (ctx : BetaTTSAContext) (p : ctx.Params) (θ : ctx.θ)
  (β0 βstar : ℝ)
  (hβ0 : 0 ≤ β0 ∧ β0 ≤ βstar)
  (hβstar : βstar ≤ ctx.Reg.βmax) (hβ : βstar < ctx.Reg.βmax)
  (hbSum : Filter.Tendsto (fun N => (Finset.range N).sum ctx.Schedules.b) Filter.atTop Filter.atTop)
  : ∃ N,
      (TTSA.iter (P := { βmax := ctx.Reg.βmax,
                         b := ctx.Schedules.b,
                         g := fun β => ctx.g p θ β,
                         proj := TTSA.clamp ctx.Reg.βmax }) β0 N) ≥ βstar := by
  classical
  -- Define the clamped update used for the stepping lemmas
  let P : TTSA.BetaUpdate := TTSA.BetaUpdate.clamped ctx.Reg.βmax ctx.Schedules.b (fun β => ctx.g p θ β)
  have hproj : TTSA.ProjIccProps P.βmax P.proj :=
    TTSA.BetaUpdate.clamped_props (βmax := ctx.Reg.βmax) (hβmax := ctx.Reg.βmax_nonneg)
      (b := ctx.Schedules.b) (g := fun β => ctx.g p θ β)
  -- Step sizes nonnegative from positivity
  have hb : ∀ n, 0 ≤ P.b n := by
    intro n; have := ctx.Schedules.b_pos n; exact (le_of_lt this)
  -- Uniform positive drift on [0, β⋆] from `g_lower` and `β⋆ ≤ βmax`.
  have hg : ∀ β, 0 ≤ β ∧ β ≤ βstar → P.g β ≥ ctx.Window.ε := by
    intro β hβ
    have hβ_in : β ∈ Set.Icc (0 : ℝ) ctx.Reg.βmax := by
      refine ⟨hβ.1, le_trans hβ.2 hβstar⟩
    simpa using (ctx.g_lower p θ β hβ_in)
  -- Apply the consolidated hitting lemma with ε := ctx.Window.ε
  have hε : 0 < ctx.Window.ε := ctx.Window.ε_pos
  have : ∃ N, (TTSA.iter P β0 N) ≥ βstar :=
    clamped_hitting_time_under_window
      (β0 := β0) (βstar := βstar) (ε := ctx.Window.ε) (P := P)
      (hβ := hβ) (hε := hε) (hβstar := hβstar)
      (hb := hb) (hbSum := hbSum) (hg := hg) (hproj := hproj) (hβ0 := hβ0)
  simpa using this

end NOC


/-! ## Lemma D — TTSA/ODE stability (full statement)

This section records the standard two‑time‑scale SA/ODE hypotheses as
explicit fields and states the final TTSA/ODE stability theorem that
Lemma D needs. The statement is axiom‑free: it does not assume any
global axioms; instead, all model‑specific obligations appear as
assumptions in the hypothesis bundle. The proof is left as a `sorry`
placeholder for the proof agent to discharge using a Borkar‑style ODE
method (fast attractor + slow ODE tracking under martingale noise).
-/

namespace NOC
noncomputable section
open Classical

/-- Bundle of TTSA–ODE tracking hypotheses for the β‑meta update.
It fixes an initial value, supplies an averaged slow drift `ḡ` with
continuity, records SA schedules and noise conditions, and adds the
standard positive‑drift window near 0 together with the existence of a
positive interior root `β⋆` in `(0, βmax]`. The fields are purely
assumptions to be instantiated in a concrete model; no axioms are used. -/
structure TTSATrackingHypotheses (ctx : BetaTTSAContext) where
  /- initial slow state -/
  β0 : ℝ
  β0_within : 0 ≤ β0 ∧ β0 ≤ ctx.Reg.βmax

  /- averaged slow drift (ODE right‑hand side) -/
  gbar : ℝ → ℝ
  gbar_cont : ContinuousOn gbar (Set.Icc (0 : ℝ) ctx.Reg.βmax)
  gbar_lipschitz : Prop   -- local Lipschitz on [0, βmax] (give concrete constant later)

  /- alignment of the stochastic recursion with the averaged drift.
     In a concrete instance, this asserts that the slow increment has the
     form gbar(β) plus a martingale difference plus a vanishing bias. -/
  aligns_with_gbar : Prop

  /- schedules and separation (standard SA conditions) -/
  a_summable        : ctx.Schedules.a_summable
  a_square_summable : ctx.Schedules.a_square_summable
  b_summable        : ctx.Schedules.b_summable
  b_square_summable : ctx.Schedules.b_square_summable
  scale_separation  : ctx.Schedules.scale_separation   -- b_n / a_n → 0

  /- martingale‑difference noise with bounded conditional variances -/
  noise_mds_fast  : ctx.Noise.mds_fast
  noise_mds_slow  : ctx.Noise.mds_slow
  noise_var_fast  : ctx.Noise.var_bound_fast
  noise_var_slow  : ctx.Noise.var_bound_slow

  /- positive drift window near 0 for the averaged drift -/
  pos_window : ∃ ε > 0, ∃ βpos > 0, βpos ≤ ctx.Reg.βmax ∧
               ∀ β, 0 ≤ β ∧ β ≤ βpos → gbar β ≥ ε

  /- interior root and (local) stability hypothesis for the ODE -/
  root_exists : ∃ β_star, 0 < β_star ∧ β_star ≤ ctx.Reg.βmax ∧ gbar β_star = 0
  root_stable : Prop   -- e.g., gbar' (β⋆) < 0 or Lyapunov condition on [0, βmax]

/-- Full TTSA/ODE stability theorem (statement only).
Given `ctx` and a hypothesis bundle `H`, the clamped slow recursion for β
remains in a compact positive subset of `[0, βmax]` after some finite
time and its limit set is contained in the zero set of the averaged
drift `ḡ`. Under uniqueness/local stability of the interior root, the
sequence converges to `β⋆ > 0`.

Notes for the proof agent:
- Use the property lemmas (`iter_bounds`, `clamped_monotone_on_window`,
  `clamped_hitting_time_under_window`) to obtain interior positivity.
- Invoke a two‑time‑scale ODE method (Borkar) with `aligns_with_gbar`,
  schedule and noise fields to identify the slow limit set with the
  ODE’s internally chain transitive set; then apply `root_stable`.
- Replace the placeholders in the conclusion with your concrete
  β‑sequence definition if you carry explicit noise terms; the clamp is
  `ctx.proj` with `proj_is_clamp` already registered in `ctx`. -/

/- Mathlib toolkit used by this TTSA/ODE scaffold (when the proof is filled):
  • D1 (MDS sums): conditional expectation API and martingale convergence
    (see `NOC.Prob.MDS` notes; files include
    `Probability/Martingale/Basic.lean`,
    `MeasureTheory/Function/ConditionalExpectation/Real.lean`, and
    optional `Probability/Martingale/Convergence.lean`).
  • D2 (Robbins–Siegmund): supermartingale construction and convergence
    helpers (see `NOC.Prob.RobbinsSiegmund`).
  • D3 (clamp nonexpansive): Lipschitz combinators
    `LipschitzWith.id.const_min`, `LipschitzWith.const_max`.
  • Deterministic stepping lemmas already provided in this file for the
    positive‑window route. No external axioms are required. -/
theorem lemmaD_beta_stability_TTSA_ode
  (ctx : BetaTTSAContext) (H : TTSATrackingHypotheses ctx) :
  ∃ K, 0 < K ∧ K ≤ ctx.Reg.βmax ∧
    /- eventual positivity and boundedness of the slow iterates -/
    (∃ β : ℕ → ℝ,
      β 0 = H.β0 ∧
      (∀ n, 0 ≤ β n ∧ β n ≤ ctx.Reg.βmax) ∧
      (∃ N0, ∀ n ≥ N0, K ≤ β n)) ∧
    /- limit set included in zeros of ḡ -/
    (∃ (Z : Set ℝ), (∀ z ∈ Z, z ∈ Set.Icc (0 : ℝ) ctx.Reg.βmax ∧ H.gbar z = 0) ∧ True) ∧
    /- convergence under uniqueness/local stability of the interior root -/
    (H.root_stable → ∃ β_star, 0 < β_star ∧ β_star ≤ ctx.Reg.βmax ∧ H.gbar β_star = 0 ∧ True) := by
  -- Skeleton: this theorem is a standard consequence of TTSA ODE tracking.
  -- Fill using SA/ODE tools once the concrete model discharges `aligns_with_gbar`.
  sorry

end
end NOC
-- Silence common linter warnings for this file
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySimpa false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unusedSectionVars false
