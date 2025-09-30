import Mathlib
open Classical

variable {Ω : Type*} [DecidableEq Ω]
variable (S G : Finset Ω)

#check (S \ G)         -- Finset Ω
#check ((S \ G).card)  -- Nat
