import Mathlib
import NOC.E.ConditionalDIDPI

/-!
Module: NOC.E.ConditionalDIDPI_Examples
Status: toy Massey–DI instantiation (no sorrys).

Purpose
- Demonstrate the `ConditionalDIDPI` aggregator by building `DI_before`/`DI_after` as sums
  of per-step reals and verifying both the non-strict and strict results.

Notes
- This is a number-level toy harness (no MI constructors). It mirrors an NCC configuration
  where each step contracts with factor ηₜ ≤ 1 and at least one step strictly contracts.
/-

namespace NOC

open scoped BigOperators

/- Finite process P: horizon T=3, finite alphabets (dummy types). -/
def ToyP : FiniteProcess :=
  { T := 3, State := Unit, Action := Unit, Observation := Unit }

/- Garbling predicate (placeholder): take η<1 as a witness we are in a contracting regime. -/
def ToyGarble : Garbling :=
  { η := 0.9, η_lt_one := by norm_num, witness := True }

/- Per-step arrays: perAfter ≤ perBefore termwise; strict at t=1. -/
@[simp] def perBefore (t : ℕ) : ℝ :=
  -- any nonnegative schedule; choose all ones for simplicity
  1

@[simp] def perAfter (t : ℕ) : ℝ :=
  -- contract at t=1, equality elsewhere
  if t = 1 then 0.8 else 1

lemma per_after_le_before : ∀ t ∈ Finset.range ToyP.T, perAfter t ≤ perBefore t := by
  intro t ht; by_cases h : t = 1 <;> simp [perAfter, perBefore, h]

lemma per_after_strict_exists : ∃ t ∈ Finset.range ToyP.T, perAfter t < perBefore t := by
  refine ⟨1, by decide, ?_⟩; simp [perAfter, perBefore]

/- Non-strict aggregator: DI_after ≤ DI_before. -/
lemma toy_di_dpi :
  let ctx : DIDPIContext :=
    { P := ToyP, garble := ToyGarble,
      DI_before := { value := (Finset.range ToyP.T).sum perBefore },
      DI_after  := { value := (Finset.range ToyP.T).sum perAfter } }
  ctx.DI_after.value ≤ ctx.DI_before.value := by
  intro ctx
  have h := per_after_le_before
  simpa using
    (conditional_DI_DPI (ctx := ctx)
      (perBefore := perBefore) (perAfter := perAfter)
      (hBefore := rfl) (hAfter := rfl) (hStep := h))

/- Strict aggregator: DI_after < DI_before. -/
lemma toy_di_dpi_strict :
  let ctx : DIDPIContext :=
    { P := ToyP, garble := ToyGarble,
      DI_before := { value := (Finset.range ToyP.T).sum perBefore },
      DI_after  := { value := (Finset.range ToyP.T).sum perAfter } }
  ctx.DI_after.value < ctx.DI_before.value := by
  intro ctx
  have h := per_after_le_before
  have hs := per_after_strict_exists
  simpa using
    (conditional_DI_DPI_massey_strict (ctx := ctx)
      (D := { perBefore := perBefore, perAfter := perAfter,
              chain_before := rfl, chain_after := rfl })
      (hStep := by intro t ht; exact h t ht)
      (hStrict := by rcases hs with ⟨t, ht, hlt⟩; exact ⟨t, ht, hlt⟩))

end NOC

