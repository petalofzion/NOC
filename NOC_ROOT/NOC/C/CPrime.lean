import Mathlib
import NOC.AHelpers
import NOC.B.Expectation

/-!
Module: NOC.CPrime
Summary: Sigma-law (improvement). Finitary expectation lemma parameterized by SDPI/Dobrushin constants.

This file proves an *average* lower bound from a split of the finite support `S`
into a “good” set `G` (where we have the pointwise C′ inequality) and its complement
(where we only have a floor). The proof is purely algebraic over `Finset` sums.

**Rename note.** To keep the statement agnostic to whether we are in the “improvement”
(C′, first-difference) or “acceleration” (C, second-difference) regime, we use
`dSigma` and `dU` for the per-sample quantities. In the acceleration lemma C,
`dU` will simply be plugged with `Δ²U`.
-/

namespace NOC
noncomputable section
open Classical
open scoped BigOperators

/-- Parameters for the Sigma-law (C′): `c1` from SDPI/Dobrushin, `lambdaXi` from deletion penalty. -/
structure SigmaLawParams where
  c1  : ℝ
  lambdaXi  : ℝ
  c1_nonneg : 0 ≤ c1
  lambdaXi_nonneg : 0 ≤ lambdaXi
/-- **Pointwise Σ‑law (C′ form, interface).**
`dSigma ≥ P.c1 * dU − P.lambdaXi * xiLoss`.  This is an interface lemma: to *use* it now,
pass the pointwise inequality you derive from your model premises; later we may prove such
an inequality from your HB/PL dynamics. -/
@[simp]
theorem lemmaCprime_pointwise
    {dSigma dU xiLoss : ℝ} (P : SigmaLawParams)
    (h : dSigma ≥ P.c1 * dU - P.lambdaXi * xiLoss) :
    dSigma ≥ P.c1 * dU - P.lambdaXi * xiLoss := h

/-- **Finitary expectation (C′).**
If on `G ⊆ S` we have `dSigma ≥ P.c1 * dU − P.lambdaXi * xiLoss`, and on the
complement `S \ G` we have `dSigma ≥ −MSigma`, then avg S dSigma ≥ (|G|/|S|) * (P.c1 * avg_G dU − P.lambdaXi * avg_G xiLoss)
+ ((|S| − |G|)/|S|) * (−MSigma).
-/
 theorem lemmaCprime_expectation_finitary
  {Ω : Type*} (S G : Finset Ω)
  (dSigma dU xiLoss : Ω → ℝ)
  (hGS : G ⊆ S) (hS : 0 < S.card)
  (P : SigmaLawParams)
  {MSigma : ℝ}
  (hGood : ∀ ω ∈ G, dSigma ω ≥ P.c1 * dU ω - P.lambdaXi * xiLoss ω)
  (hBad  : ∀ ω ∈ S \ G, dSigma ω ≥ -MSigma) :
  avg S dSigma ≥
    ((G.card : ℝ) / (S.card : ℝ)) * (P.c1 * avg G dU - P.lambdaXi * avg G xiLoss) +
    (((S.card - G.card : ℕ) : ℝ) / (S.card : ℝ)) * (-MSigma) := by
  classical
  -- Split S as G ∪ (S \ G)
  have hdisj : Disjoint G (S \ G) := by
    refine Finset.disjoint_left.mpr ?_
    intro ω hωG hωSdiff
    exact (Finset.mem_sdiff.mp hωSdiff).2 hωG
  have hunion : G ∪ (S \ G) = S := Finset.union_sdiff_of_subset hGS
  have hsplit :
      S.sum (fun ω => dSigma ω)
        = G.sum (fun ω => dSigma ω) + (S \ G).sum (fun ω => dSigma ω) := by
    simpa [hunion, add_comm, add_left_comm, add_assoc] using
      (Finset.sum_union hdisj)

  -- Lower bounds (sum over G, sum over complement)
  have hGsum_lb :
      G.sum (fun ω => P.c1 * dU ω - P.lambdaXi * xiLoss ω)
        ≤ G.sum (fun ω => dSigma ω) :=
    Finset.sum_le_sum (by intro ω hω; exact hGood ω hω)
  have hBsum_lb :
      (S \ G).sum (fun _ => (-MSigma))
        ≤ (S \ G).sum (fun ω => dSigma ω) :=
    Finset.sum_le_sum (by intro ω hω; exact hBad ω hω)

  -- Linearize the G‑sum and evaluate the constant sum on S\G
  have hsum_lin :
      G.sum (fun ω => P.c1 * dU ω - P.lambdaXi * xiLoss ω)
        = P.c1 * G.sum (fun ω => dU ω) - P.lambdaXi * G.sum (fun ω => xiLoss ω) := by
    simp [Finset.sum_sub_distrib, Finset.mul_sum]
  have hconst :
      (S \ G).sum (fun _ => (-MSigma)) = ((S \ G).card : ℝ) * (-MSigma) := by
    simp [Finset.sum_const, nsmul_eq_mul]

  -- Combine, then scale by 1/|S|
  have hsum_lb :
      P.c1 * G.sum (fun ω => dU ω)
      - P.lambdaXi * G.sum (fun ω => xiLoss ω)
      + ((S \ G).card : ℝ) * (-MSigma)
      ≤ S.sum (fun ω => dSigma ω) := by
    have := add_le_add hGsum_lb hBsum_lb
    simpa [hsplit, hsum_lin, hconst, add_comm, add_left_comm, add_assoc] using this

  have hSpos : 0 < (S.card : ℝ) := by exact_mod_cast hS
  have hscaled :
      (1 / (S.card : ℝ)) *
        (P.c1 * G.sum (fun ω => dU ω)
         - P.lambdaXi * G.sum (fun ω => xiLoss ω)
         + ((S \ G).card : ℝ) * (-MSigma))
      ≤ (1 / (S.card : ℝ)) * S.sum (fun ω => dSigma ω) :=
    mul_le_mul_of_nonneg_left hsum_lb (one_div_nonneg.mpr (le_of_lt hSpos))

  -- Helper: (1/|S|) * (∑_{ω∈G} f ω) = (|G|/|S|) * avg_G f
  have toAvg (f : Ω → ℝ) :
      (1 / (S.card : ℝ)) * G.sum (fun ω => f ω)
        = ((G.card : ℝ) / (S.card : ℝ)) * avg G f := by
    by_cases hG0 : G.card = 0
    · -- G empty
      have hGempty : G = (∅ : Finset Ω) := Finset.card_eq_zero.mp hG0
      simp [hGempty, avg, div_eq_mul_inv]
    · -- G nonempty
      have hGne : (G.card : ℝ) ≠ 0 := by exact_mod_cast (Nat.pos_of_ne_zero hG0).ne'
      calc
        (1 / (S.card : ℝ)) * G.sum (fun ω => f ω)
            = (G.sum (fun ω => f ω)) * (1 / (S.card : ℝ)) := by
                simp [mul_comm]
        _ = (G.sum (fun ω => f ω)) * (((G.card : ℝ) / (S.card : ℝ)) * (1 / (G.card : ℝ))) := by
                simp [div_eq_mul_inv, hGne, mul_comm]
        _ = ((G.card : ℝ) / (S.card : ℝ)) * ((G.sum (fun ω => f ω)) * (1 / (G.card : ℝ))) := by
                ring
        _ = ((G.card : ℝ) / (S.card : ℝ)) * ((G.sum (fun ω => f ω)) / (G.card : ℝ)) := by
                simp [div_eq_mul_inv, mul_comm]
        _ = ((G.card : ℝ) / (S.card : ℝ)) * avg G f := by
                simp [avg, div_eq_mul_inv, mul_comm]

  -- Convert each piece on the LHS of `hscaled`
  have hUterm :
      (1 / (S.card : ℝ)) * (P.c1 * G.sum (fun ω => dU ω))
        = ((G.card : ℝ) / (S.card : ℝ)) * (P.c1 * avg G dU) := by
    calc
      (1 / (S.card : ℝ)) * (P.c1 * G.sum (fun ω => dU ω))
          = P.c1 * ((1 / (S.card : ℝ)) * G.sum (fun ω => dU ω)) := by
              ring
      _ = P.c1 * (((G.card : ℝ) / (S.card : ℝ)) * avg G dU) := by
              simpa using congrArg (fun t => P.c1 * t) (toAvg (fun ω => dU ω))
      _ = ((G.card : ℝ) / (S.card : ℝ)) * (P.c1 * avg G dU) := by
              ring

  have hXterm :
      (1 / (S.card : ℝ)) * (P.lambdaXi * G.sum (fun ω => xiLoss ω))
        = ((G.card : ℝ) / (S.card : ℝ)) * (P.lambdaXi * avg G xiLoss) := by
    calc
      (1 / (S.card : ℝ)) * (P.lambdaXi * G.sum (fun ω => xiLoss ω))
          = P.lambdaXi * ((1 / (S.card : ℝ)) * G.sum (fun ω => xiLoss ω)) := by
              ring
      _ = P.lambdaXi * (((G.card : ℝ) / (S.card : ℝ)) * avg G xiLoss) := by
              simpa using congrArg (fun t => P.lambdaXi * t) (toAvg (fun ω => xiLoss ω))
      _ = ((G.card : ℝ) / (S.card : ℝ)) * (P.lambdaXi * avg G xiLoss) := by
              ring

  -- Complement term mass
  have hBterm :
      (1 / (S.card : ℝ)) * (((S \ G).card : ℝ) * (-MSigma))
        = (((S.card - G.card : ℕ) : ℝ) / (S.card : ℝ)) * (-MSigma) := by
    have hcard : ((S \ G).card : ℝ) = ((S.card - G.card : ℕ) : ℝ) := by
      simpa using (congrArg (fun n : ℕ => (n : ℝ)) (Finset.card_sdiff hGS))
    simp [div_eq_mul_inv, hcard, mul_comm, mul_left_comm]

  -- Distribute (1/|S|) across (A - B + C)
  have hdist :
      (1 / (S.card : ℝ)) *
        (P.c1 * G.sum (fun ω => dU ω)
          - P.lambdaXi * G.sum (fun ω => xiLoss ω)
          + ((S \ G).card : ℝ) * (-MSigma))
      =
      (1 / (S.card : ℝ)) * (P.c1 * G.sum (fun ω => dU ω))
        - (1 / (S.card : ℝ)) * (P.lambdaXi * G.sum (fun ω => xiLoss ω))
        + (1 / (S.card : ℝ)) * (((S \ G).card : ℝ) * (-MSigma)) := by
    ring

  -- Rewrite the LHS of `hscaled` into the target form
  have hLHS :
      (1 / (S.card : ℝ)) *
        (P.c1 * G.sum (fun ω => dU ω)
          - P.lambdaXi * G.sum (fun ω => xiLoss ω)
          + ((S \ G).card : ℝ) * (-MSigma))
      = ((G.card : ℝ) / (S.card : ℝ)) * (P.c1 * avg G dU - P.lambdaXi * avg G xiLoss)
        + (((S.card - G.card : ℕ) : ℝ) / (S.card : ℝ)) * (-MSigma) := by
    calc
      (1 / (S.card : ℝ)) *
        (P.c1 * G.sum (fun ω => dU ω)
          - P.lambdaXi * G.sum (fun ω => xiLoss ω)
          + ((S \ G).card : ℝ) * (-MSigma))
          = (1 / (S.card : ℝ)) * (P.c1 * G.sum (fun ω => dU ω))
            - (1 / (S.card : ℝ)) * (P.lambdaXi * G.sum (fun ω => xiLoss ω))
            + (1 / (S.card : ℝ)) * (((S \ G).card : ℝ) * (-MSigma)) := by
              simpa using hdist
      _ = ((G.card : ℝ) / (S.card : ℝ)) * (P.c1 * avg G dU)
            - ((G.card : ℝ) / (S.card : ℝ)) * (P.lambdaXi * avg G xiLoss)
            + (((S.card - G.card : ℕ) : ℝ) / (S.card : ℝ)) * (-MSigma) := by
              -- rewrite each piece explicitly
              rw [hUterm, hXterm, hBterm]
      _ = ((G.card : ℝ) / (S.card : ℝ)) * (P.c1 * avg G dU - P.lambdaXi * avg G xiLoss)
            + (((S.card - G.card : ℕ) : ℝ) / (S.card : ℝ)) * (-MSigma) := by
              ring

  -- Use the equality to rewrite the inequality from `hscaled`.
  -- `hscaled` has its LHS as `+ -((|S\G|)*MSigma)`. First align it with the `hLHS` shape
  -- that uses `((|S\G|) * (-MSigma))` via a tiny algebraic rewrite.
  have hflip :
      (1 / (S.card : ℝ)) *
        (P.c1 * G.sum (fun ω => dU ω)
          - P.lambdaXi * G.sum (fun ω => xiLoss ω)
          + -(((S \ G).card : ℝ) * MSigma))
      =
      (1 / (S.card : ℝ)) *
        (P.c1 * G.sum (fun ω => dU ω)
          - P.lambdaXi * G.sum (fun ω => xiLoss ω)
          + ((S \ G).card : ℝ) * (-MSigma)) := by
    -- Prove the small equality once: `-(a*b) = a*(-b)`.
    have hneg :
        -(((S \ G).card : ℝ) * MSigma)
          = ((S \ G).card : ℝ) * (-MSigma) := by
      simp [mul_neg]
    -- Lift it through the larger context via `congrArg`, avoiding global `simp`.
    exact
      congrArg
        (fun t =>
          (1 / (S.card : ℝ)) *
            (P.c1 * G.sum (fun ω => dU ω)
              - P.lambdaXi * G.sum (fun ω => xiLoss ω)
              + t))
        hneg

  have hscaled' :
      (1 / (S.card : ℝ)) *
        (P.c1 * G.sum (fun ω => dU ω)
          - P.lambdaXi * G.sum (fun ω => xiLoss ω)
          + ((S \ G).card : ℝ) * (-MSigma))
      ≤ (1 / (S.card : ℝ)) * S.sum (fun ω => dSigma ω) := by
    -- rewrite the LHS of `hscaled` via `hflip`
    simpa [hflip] using hscaled

  -- Now rewrite the LHS via `hLHS` to the target shape (no `simp` orientation).
  have htarget :
      ((G.card : ℝ) / (S.card : ℝ)) * (P.c1 * avg G dU - P.lambdaXi * avg G xiLoss)
      + (((S.card - G.card : ℕ) : ℝ) / (S.card : ℝ)) * (-MSigma)
      ≤ (1 / (S.card : ℝ)) * S.sum (fun ω => dSigma ω) := by
    -- `hLHS : oldLHS = newLHS`; we need `newLHS ≤ RHS` from `oldLHS ≤ RHS`.
    -- Use `le_of_eq_of_le (hLHS.symm)` to replace the left side.
    have hEq :
        ((G.card : ℝ) / (S.card : ℝ)) * (P.c1 * avg G dU - P.lambdaXi * avg G xiLoss)
        + (((S.card - G.card : ℕ) : ℝ) / (S.card : ℝ)) * (-MSigma)
        =
        (1 / (S.card : ℝ)) *
          (P.c1 * G.sum (fun ω => dU ω)
            - P.lambdaXi * G.sum (fun ω => xiLoss ω)
            + ((S \ G).card : ℝ) * (-MSigma)) := by
      simpa using hLHS.symm
    exact le_of_eq_of_le hEq hscaled'

  -- Right-hand side is exactly the average on S
  have hfinal :
      ((G.card : ℝ) / (S.card : ℝ)) * (P.c1 * avg G dU - P.lambdaXi * avg G xiLoss)
      + (((S.card - G.card : ℕ) : ℝ) / (S.card : ℝ)) * (-MSigma)
      ≤ avg S dSigma := by
    simpa [avg, div_eq_mul_inv, mul_comm] using htarget

  -- Reorient to match the statement (`≥` is just flipped `≤`)
  simpa [ge_iff_le] using hfinal

  /-- **C′ expectation with a mass lower bound `p0`.**
If on `G ⊆ S` we have the pointwise C′ inequality
`dSigma ≥ P.c1 * dU − P.lambdaXi * xiLoss`, and on `S \ G` we have `dSigma ≥ −MSigma`,
and if `p0 ≤ |G|/|S|` with nonnegative slope `(m0 + MSigma) ≥ 0` (where
`m0 := P.c1 * avg G dU - P.lambdaXi * avg G xiLoss`),
then
`avg S dSigma ≥ p0 * m0 - (1 - p0) * MSigma`.
-/
theorem lemmaCprime_expectation_with_fraction
  {Ω : Type*} (S G : Finset Ω)
  (dSigma dU xiLoss : Ω → ℝ)
  (hGS : G ⊆ S) (hS : 0 < S.card)
  (P : SigmaLawParams)
  {MSigma p0 : ℝ}
  (hGood : ∀ ω ∈ G, dSigma ω ≥ P.c1 * dU ω - P.lambdaXi * xiLoss ω)
  (hBad  : ∀ ω ∈ S \ G, dSigma ω ≥ -MSigma)
  (hSlope : 0 ≤ (P.c1 * avg G dU - P.lambdaXi * avg G xiLoss) + MSigma)
  (hp0  : p0 ≤ (G.card : ℝ) / (S.card : ℝ)) :
  avg S dSigma ≥
    p0 * (P.c1 * avg G dU - P.lambdaXi * avg G xiLoss) - (1 - p0) * MSigma := by
  classical
  -- Base bound with the exact fraction q := |G|/|S|
  have hbase :=
    lemmaCprime_expectation_finitary
      (S := S) (G := G) (dSigma := dSigma) (dU := dU) (xiLoss := xiLoss)
      (hGS := hGS) (hS := hS) (P := P) (MSigma := MSigma)
      (hGood := hGood) (hBad := hBad)
  -- Package the mass and the "slope" m0 + MSigma
  set q  : ℝ := (G.card : ℝ) / (S.card : ℝ)
  set m0 : ℝ := P.c1 * avg G dU - P.lambdaXi * avg G xiLoss
  -- hbase says: avg ≥ q*m0 + (1 - q)*(-MSigma) = φ(q)
  -- Re-express the complement fraction as `1 - q`.
  have hS_ne : (S.card : ℝ) ≠ 0 := by exact_mod_cast hS.ne'
  have hdisj : Disjoint G (S \ G) := by
    refine Finset.disjoint_left.mpr ?_
    intro ω hωG hωSdiff
    exact (Finset.mem_sdiff.mp hωSdiff).2 hωG
  have hunion : G ∪ (S \ G) = S := Finset.union_sdiff_of_subset hGS
  have hsum1 :
      S.sum (fun ω => (1 : ℝ))
        = G.sum (fun ω => (1 : ℝ)) + (S \ G).sum (fun ω => (1 : ℝ)) := by
    -- make the union version explicit to help typeclass inference
    have :
        (G ∪ (S \ G)).sum (fun _ => (1 : ℝ))
          = G.sum (fun _ => (1 : ℝ)) + (S \ G).sum (fun _ => (1 : ℝ)) :=
      Finset.sum_union hdisj
    simpa [hunion, add_comm, add_left_comm, add_assoc] using this
  have hcard_add :
      (S.card : ℝ) = (G.card : ℝ) + ((S \ G).card : ℝ) := by
    simpa [Finset.sum_const, nsmul_eq_mul] using hsum1
  have hcomp :
      ((S \ G).card : ℝ) = (S.card : ℝ) - (G.card : ℝ) := by
    exact (eq_sub_iff_add_eq).2 (by simpa [add_comm] using hcard_add.symm)
  have hmassSG :
      ((S \ G).card : ℝ) / (S.card : ℝ) = 1 - q := by
    calc
      ((S \ G).card : ℝ) / (S.card : ℝ)
          = ((S.card : ℝ) - (G.card : ℝ)) / (S.card : ℝ) := by simp [hcomp]
      _ = 1 - (G.card : ℝ) / (S.card : ℝ) := by
            simpa [div_self hS_ne] using
              (sub_div (S.card : ℝ) (G.card : ℝ) (S.card : ℝ))
  have hcast :
      ((S.card - G.card : ℕ) : ℝ) = ((S \ G).card : ℝ) := by
    simpa using (congrArg (fun n : ℕ => (n : ℝ)) (Finset.card_sdiff hGS)).symm
  have hmass :
      (((S.card - G.card : ℕ) : ℝ) / (S.card : ℝ)) = 1 - q := by
    simpa [hcast] using hmassSG

  let φ : ℝ → ℝ := fun p => p * m0 + (1 - p) * (-MSigma)
  have hφq_le_avg : φ q ≤ avg S dSigma := by
    -- rewrite `hbase` using `hmass` and flip to `≤` form
    have : avg S dSigma ≥ q * m0 + (1 - q) * (-MSigma) := by
      simpa [q, m0, hmass] using hbase
    simpa [φ, ge_iff_le] using this

  -- Monotonicity in p: φ(p) = p*(m0 + MSigma) - MSigma, slope ≥ 0 by hSlope
  have hmono : φ p0 ≤ φ q := by
    have hp0' : p0 * (m0 + MSigma) ≤ q * (m0 + MSigma) :=
      mul_le_mul_of_nonneg_right hp0 hSlope
    calc
      φ p0 = p0 * (m0 + MSigma) - MSigma := by ring
      _    ≤ q * (m0 + MSigma) - MSigma  := by
               simpa using (sub_le_sub_right hp0' MSigma)
      _    = φ q                         := by ring
  -- Chain them
  have hchain : φ p0 ≤ avg S dSigma := le_trans hmono hφq_le_avg
  -- Re-express φ(p0)
  simpa [φ, m0] using hchain

  /-- **C′ on all of `S`.**
If the pointwise C′ inequality holds on `S` (take the good set `G = S`), then
`avg S dSigma ≥ P.c1 * avg S dU - P.lambdaXi * avg S xiLoss`. -/
theorem lemmaCprime_expectation_allGood
  {Ω : Type*} (S : Finset Ω)
  (dSigma dU xiLoss : Ω → ℝ)
  (hS : 0 < S.card)
  (P : SigmaLawParams)
  (hGood : ∀ ω ∈ S, dSigma ω ≥ P.c1 * dU ω - P.lambdaXi * xiLoss ω) :
  avg S dSigma ≥ P.c1 * avg S dU - P.lambdaXi * avg S xiLoss := by
  classical
  -- sum the pointwise inequality over S, in ≤ orientation
  have hsum_lb :
      S.sum (fun ω => P.c1 * dU ω - P.lambdaXi * xiLoss ω)
        ≤ S.sum (fun ω => dSigma ω) :=
    Finset.sum_le_sum (by intro ω hω; exact hGood ω hω)
  -- linearize the RHS sum
  have hlin :
      S.sum (fun ω => P.c1 * dU ω - P.lambdaXi * xiLoss ω)
        = P.c1 * S.sum (fun ω => dU ω) - P.lambdaXi * S.sum (fun ω => xiLoss ω) := by
    simp [Finset.sum_sub_distrib, Finset.mul_sum]
  -- scale by (1/|S|) ≥ 0; first linearize the LHS to match shape
  have hpos : 0 < (S.card : ℝ) := by exact_mod_cast hS
  have hsum_lb_lin :
      P.c1 * S.sum (fun ω => dU ω) - P.lambdaXi * S.sum (fun ω => xiLoss ω)
        ≤ S.sum (fun ω => dSigma ω) := by
    simpa [hlin] using hsum_lb
  have hscaled :
      (1 / (S.card : ℝ)) *
            (P.c1 * S.sum (fun ω => dU ω) - P.lambdaXi * S.sum (fun ω => xiLoss ω))
        ≤ (1 / (S.card : ℝ)) * S.sum (fun ω => dSigma ω) :=
    mul_le_mul_of_nonneg_left hsum_lb_lin (one_div_nonneg.mpr (le_of_lt hpos))
  -- rewrite into averages; move the xi term to the RHS to match shapes
  let invS : ℝ := 1 / (S.card : ℝ)
  have hplus :
      invS * (P.c1 * S.sum (fun ω => dU ω))
        ≤ invS * S.sum (fun ω => dSigma ω)
          + invS * (P.lambdaXi * S.sum (fun ω => xiLoss ω)) := by
    -- add the same term to both sides, then simplify algebraically
    have := add_le_add_right hscaled (invS * (P.lambdaXi * S.sum (fun ω => xiLoss ω)))
    -- distribute and cancel the xi term on the LHS
    simpa [invS, mul_add, add_comm, add_left_comm, add_assoc,
           sub_eq_add_neg, mul_comm, mul_left_comm, mul_assoc] using this
  -- express in terms of averages and flip orientation to `≥`
  have :
      P.c1 * ((S.sum (fun ω => dU ω)) * invS)
        ≤ ((S.sum (fun ω => dSigma ω)) * invS)
          + P.lambdaXi * ((S.sum (fun ω => xiLoss ω)) * invS) := by
    -- reassociate factors to match the statement shape
    simpa [invS, mul_comm, mul_left_comm, mul_assoc] using hplus
  -- final `simpa`: P.c1 * avg dU ≤ avg dSigma + P.lambdaXi * avg xiLoss  ↔  avg dSigma ≥ P.c1 * avg dU - P.lambdaXi * avg xiLoss
  simpa [avg, div_eq_mul_inv, invS, ge_iff_le, sub_eq_add_neg,
         mul_comm, mul_left_comm, mul_assoc] using this


end
end NOC
