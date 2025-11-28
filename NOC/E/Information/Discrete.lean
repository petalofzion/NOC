/-
  NOC/E/Information/Discrete.lean
  
  Foundation for Target #2: Discrete Strong Data Processing Inequality (SDPI).
  
  Status: Scaffolding Phase (Definitions established, Proofs pending).
-/

import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

namespace NOC
namespace Information
noncomputable section
open Classical
open Real (log)
open scoped BigOperators

universe u

/-! ## 1. Basic Definitions: Entropy & KL -/

/-- Shannon Entropy of a PMF. H(p) = ∑ -p(x) log p(x). 
    We coerce PMF values (ENNReal) to Real using `toReal`.
-/
def entropy {α : Type u} [Fintype α] (p : PMF α) : ℝ :=
  ∑ x, Real.negMulLog (p x).toReal

/-- Kullback-Leibler Divergence D(p || q). 
    D(p || q) = ∑ p(x) log(p(x) / q(x)). 
    We use the form p * (log p - log q).
-/
def kl_divergence {α : Type u} [Fintype α] (p q : PMF α) : ℝ :=
  ∑ x, (p x).toReal * (log (p x).toReal - log (q x).toReal)

/-! ## 2. Joint and Conditional Definitions -/

/-- Joint Entropy H(X, Y). -/
def joint_entropy {α β : Type u} [Fintype α] [Fintype β] (p : PMF (α × β)) : ℝ :=
  entropy p

/-- Marginal Distribution of X from P(X,Y). -/
def marginal_fst {α β : Type u} [Fintype α] [Fintype β] (p : PMF (α × β)) : PMF α :=
  Prod.fst <$> p

/-- Marginal Distribution of Y from P(X,Y). -/
def marginal_snd {α β : Type u} [Fintype α] [Fintype β] (p : PMF (α × β)) : PMF β :=
  Prod.snd <$> p

/-- Mutual Information I(X; Y) = H(X) + H(Y) - H(X, Y). -/
def mutual_info {α β : Type u} [Fintype α] [Fintype β] (p : PMF (α × β)) : ℝ :=
  entropy (marginal_fst p) + entropy (marginal_snd p) - joint_entropy p

/-- Conditional Entropy H(Y | X) = H(X, Y) - H(X). -/
def cond_entropy {α β : Type u} [Fintype α] [Fintype β] (p : PMF (α × β)) : ℝ :=
  joint_entropy p - entropy (marginal_fst p)

/-! ## 3. Fundamental Inequalities (The Proof Targets) -/

/-- Gibbs' Inequality: D(p || q) ≥ 0. -/
theorem kl_nonneg {α : Type u} [Fintype α] (p q : PMF α) : 0 ≤ kl_divergence p q := by
  sorry

/-- Entropy is non-negative. 0 ≤ H(X). -/
theorem entropy_nonneg {α : Type u} [Fintype α] (p : PMF α) : 0 ≤ entropy p := by
  apply Finset.sum_nonneg
  intro x _
  apply Real.negMulLog_nonneg
  · apply ENNReal.toReal_nonneg
  · rw [← ENNReal.toReal_one]
    apply ENNReal.toReal_mono
    · exact ENNReal.one_ne_top
    · exact PMF.coe_le_one p x

/-- Entropy is bounded by log cardinality. H(X) ≤ log |X|. -/
theorem entropy_le_log_card {α : Type u} [Fintype α] (p : PMF α) : 
  entropy p ≤ log (Fintype.card α) := by
  sorry

/-- MI equals KL divergence from product of marginals. 
    I(X;Y) = D(P(X,Y) || P(X)P(Y)). -/
theorem mutual_info_eq_kl {α β : Type u} [Fintype α] [Fintype β] (p : PMF (α × β)) :
  mutual_info p = 
  kl_divergence p ((marginal_fst p) >>= (fun x => (marginal_snd p) >>= (fun y => pure (x, y)))) := by
  -- Note: We need to construct the product measure correctly.
  -- The product measure is P(X=x, Y=y) = P(X=x) * P(Y=y).
  -- Monadic bind: x <- pX; y <- pY; return (x, y)
  sorry

/-- Mutual Information is non-negative. I(X; Y) ≥ 0. -/
theorem mutual_info_nonneg {α β : Type u} [Fintype α] [Fintype β] (p : PMF (α × β)) : 
  0 ≤ mutual_info p := by
  sorry

/-- Chain Rule: H(X, Y) = H(X) + H(Y | X). -/
theorem chain_rule {α β : Type u} [Fintype α] [Fintype β] (p : PMF (α × β)) :
  joint_entropy p = entropy (marginal_fst p) + cond_entropy p := by
  -- This is definitional from `cond_entropy` definition, essentially.
  -- But we might want to prove the sum form: H(Y|X) = ∑ p(x) H(Y|X=x).
  sorry

/-- Data Processing Inequality (DPI).
    If X → Y → Z is a Markov Chain, then I(X; Z) ≤ I(X; Y). -/
theorem dpi {α β γ : Type u} [Fintype α] [Fintype β] [Fintype γ] 
  (p_xy : PMF (α × β)) (channel : β → PMF γ) :
  True := by -- Placeholder type until we define Markov Chains formally
  sorry

end -- End unnamed section
end Information
end NOC