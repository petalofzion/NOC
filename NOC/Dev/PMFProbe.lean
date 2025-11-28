import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.ProbabilityMassFunction.Monad

universe u
variable {α β : Type u}
variable (p : PMF (α × β))

#check Prod.fst <$> p