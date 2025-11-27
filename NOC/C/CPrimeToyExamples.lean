import Mathlib
import NOC.C.CPrime
import NOC.C.CPrimeToy

/-!
Module: NOC.C.CPrimeToyExamples
Status: concrete 2×2 C′ toy instantiation (no sorrys).

Purpose
- Provide a tiny, fully concrete instance (Ω = Fin 2) that demonstrates
  `lemmaCprime_expectation_finitary` with explicit `SigmaLawParams`.

Setup
- S = {0,1}, G = {0}. Define per-sample reals with `dSigma(0)=1`, `dU(0)=1`,
  and zero elsewhere; take `B ≡ 0`, `MSigma = 0`, and set `c1=1`, `lambdaXi=0`.
  The pointwise C′ inequality on G is immediate, and the floor on S\G is trivial.
-/

namespace NOC
noncomputable section
open Classical
open scoped BigOperators

@[simp] def S2 : Finset (Fin 2) := Finset.univ
@[simp] def G2 : Finset (Fin 2) := { (0 : Fin 2) }

lemma G2_subset_S2 : G2 ⊆ S2 := by
  intro i _; simp [S2]

lemma S2_pos : 0 < (S2 : Finset (Fin 2)).card := by
  simp [S2]

def E2 : CPrimeToy.TwoByTwo (Fin 2) :=
  { S := S2, G := G2, hGS := G2_subset_S2, hSpos := S2_pos }

/- Per-sample data: B≡0; dU(0)=1, dU(1)=0; dSigma(0)=1, dSigma(1)=0; MSigma=0. -/
def D2 : CPrimeToy.TwoByTwoData (E := E2) :=
  { A := fun _ => 0,
    B := fun _ => 0,
    dU := fun i => if (i : Fin 2) = 0 then 1 else 0,
    dSigma := fun i => if (i : Fin 2) = 0 then 1 else 0,
    MSigma := 0,
    good := by
      intro ω hω;
      have : ω = 0 := by simpa [G2] using (Finset.mem_singleton.mp hω)
      simp [this],
    bad := by
      intro ω hω;
      have hnot : ω ∉ G2 := (Finset.mem_sdiff.mp hω).2
      have hne : ω ≠ 0 := by simpa [G2, Finset.mem_singleton] using hnot
      simp [hne] }

/- Simple Sigma-law parameters: c1=1, lambdaXi=0. -/
def P2 : SigmaLawParams :=
  { c1 := 1, lambdaXi := 0, c1_nonneg := by norm_num, lambdaXi_nonneg := by norm_num }

/- Pointwise C′ on G2. -/
lemma hGood2 : ∀ ω ∈ E2.G, D2.dSigma ω ≥ P2.c1 * D2.dU ω - P2.lambdaXi * D2.B ω := by
  intro ω hω;
  have : ω = 0 := by simpa [G2] using (Finset.mem_singleton.mp hω)
  simp [D2, P2, this]

/- Concrete finitary bound: direct application of `lemmaCprime_expectation_finitary`. -/
theorem toy_Cprime_concrete_2x2 :
  avg E2.S D2.dSigma ≥
    ((E2.G.card : ℝ) / (E2.S.card : ℝ)) * (P2.c1 * avg E2.G D2.dU - P2.lambdaXi * avg E2.G D2.B)
    + (((E2.S.card - E2.G.card : ℕ) : ℝ) / (E2.S.card : ℝ)) * (-D2.MSigma) := by
  classical
  simpa using
    (lemmaCprime_expectation_finitary
      (S := E2.S) (G := E2.G)
      (dSigma := D2.dSigma) (dU := D2.dU) (xiLoss := D2.B)
      (hGS := E2.hGS) (hS := E2.hSpos) (P := P2)
      (MSigma := D2.MSigma) (hGood := hGood2) (hBad := D2.bad))

end
end NOC
