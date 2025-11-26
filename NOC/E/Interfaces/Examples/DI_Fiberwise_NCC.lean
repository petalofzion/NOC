import Mathlib
import NOC.E.Interfaces.DI
import NOC.E.Interfaces.DI_Averaging
import NOC.E.Interfaces.DI_Fiberwise
import NOC.E.Interfaces.DI_Toy

/-!
Module: NOC.E.Interfaces.Examples.DI_Fiberwise_NCC
Status: small fiberwise NCC example (no sorrys).

Purpose
- Demonstrate the fiberwise route (NCC) with a strict step and near‑identity elsewhere.
- This keeps SDPI uniform per step over fibers and shows both monotone and strict global results.

Model
- Types: `X = Unit`, `Y = Unit`.
- Fibers: `ι := Fin 2`, weights `w 0 = 0.6`, `w 1 = 0.4` (probabilities).
- pre_f t _ _ i := 1 for all (t,i) (nonnegative, positive everywhere).
- post_f t _ _ i := η t * pre_f t _ _ i, with `η 1 = 0.64 < 1` (strict), and `η t = 0.99` otherwise.

Notes
- We choose `η < 1` at all steps to match the `SDPI` class constraint. Conceptually, the non‑strict steps
  serve as near‑identity links (η ≈ 1), which is faithful to the aggregator plan without over‑assuming.
-/

namespace NOC
namespace DI

open scoped BigOperators

/- Fibers and weights -/
@[simp] def wEx (i : Fin 2) : ℝ := if i = 0 then (0.6 : ℝ) else (0.4 : ℝ)

lemma wEx_nonneg : ∀ i ∈ (Finset.univ : Finset (Fin 2)), 0 ≤ wEx i := by
  intro i hi; by_cases h : i = 0
  · subst h; simp [wEx]
  · have : i = 1 := by decide
    subst this; simp [wEx]

lemma wEx_sum_one : (Finset.univ : Finset (Fin 2)).sum (fun i => wEx i) = 1 := by
  classical
  have : (Finset.univ : Finset (Fin 2)) = {0,1}.toFinset := by decide
  simpa [this, wEx, Finset.sum_pair, Finset.mem_univ, if_pos rfl, if_neg (by decide)]

/- SDPI schedule: strict at t=1, near-identity elsewhere (still < 1 to satisfy class). -/
@[simp] def etaEx (t : Time) : ℝ := if t = 1 then (0.64 : ℝ) else (0.99 : ℝ)

lemma etaEx_range : ∀ t, 0 ≤ etaEx t ∧ etaEx t < 1 := by
  intro t; by_cases h : t = 1
  · subst h; norm_num
  · have : etaEx t = 0.99 := by simp [etaEx, h]
    simpa [this]

/- Per-fiber pre/post (abstract reals): pre=1; post=η·pre. -/
def pre_fEx (t : Time) (_x : Time → Unit) (_y : Time → Unit) (_i : Fin 2) : ℝ := 1
def post_fEx (t : Time) (_x : Time → Unit) (_y : Time → Unit) (_i : Fin 2) : ℝ := etaEx t

/- DirectedInfo perStep for this example — we align it with the aggregated `post` to make the link trivial. -/
instance : PerStepData Unit Unit where
  perStep := fun t _x _y => (Finset.univ : Finset (Fin 2)).sum (fun i => wEx i * post_fEx t (fun _ => ()) (fun _ => ()) i)

/- SDPI schedule as a class -/
instance : SDPIData Unit Unit where
  η := etaEx
  η_range := etaEx_range

instance : DirectedInfo Unit Unit := by infer_instance
instance : SDPI Unit Unit := by infer_instance

/- Monotone lemma via the fiberwise wrapper. -/
lemma fiberwise_monotone (n : Nat) :
  DirectedInfo.DI (X:=Unit) (Y:=Unit) n (fun _ => ()) (fun _ => ())
    ≤ (Finset.range (n+1)).sum (fun t => SDPI.η (X:=Unit) (Y:=Unit) t
                                    * aggPre (s:=Finset.univ) (w:=wEx) pre_fEx t (fun _ => ()) (fun _ => ())) := by
  classical
  -- h_per_le_post: perStep = aggregated post
  have h_per : ∀ t, DirectedInfo.perStep t (fun _ => ()) (fun _ => ())
      ≤ aggPost (s:=Finset.univ) (w:=wEx) post_fEx t (fun _ => ()) (fun _ => ()) := by
    intro t; simp [aggPost, post_fEx]
  -- uniform SDPI per step, fiberwise and averaged
  have hw_nonneg := wEx_nonneg
  have hpre_nonneg : ∀ t i, i ∈ (Finset.univ : Finset (Fin 2)) → 0 ≤ pre_fEx t (fun _ => ()) (fun _ => ()) i := by
    intro t i hi; simp [pre_fEx]
  have hsdpi : ∀ t i, i ∈ (Finset.univ : Finset (Fin 2)) →
      post_fEx t (fun _ => ()) (fun _ => ()) i ≤ SDPI.η (X:=Unit) (Y:=Unit) t * pre_fEx t (fun _ => ()) (fun _ => ()) i := by
    intro t i hi; simp [post_fEx, pre_fEx]
  -- Apply the fiberwise composition lemma
  simpa using
    (di_dpi_from_fibers (X:=Unit) (Y:=Unit) (ι:=Fin 2)
      (s:=Finset.univ) (w:=wEx) (pre_f:=pre_fEx) (post_f:=post_fEx)
      n (fun _ => ()) (fun _ => ())
      (h_per_le_post := by intro t; exact h_per t)
      (hw_nonneg := hw_nonneg) (hpre_nonneg := hpre_nonneg) (h_uniform_sdpi := hsdpi))

/- Strict lemma via positive‑mass strict fiber (any fiber works since pre=1 and weights > 0). -/
lemma fiberwise_strict :
  DirectedInfo.DI (X:=Unit) (Y:=Unit) 2 (fun _ => ()) (fun _ => ())
    < (Finset.range (2+1)).sum (fun t => aggPre (s:=Finset.univ) (w:=wEx) pre_fEx t (fun _ => ()) (fun _ => ())) := by
  classical
  -- perStep link: equality
  have h_per : ∀ t, DirectedInfo.perStep t (fun _ => ()) (fun _ => ())
      ≤ aggPost (s:=Finset.univ) (w:=wEx) post_fEx t (fun _ => ()) (fun _ => ()) := by
    intro t; simp [aggPost, post_fEx]
  have hw_nonneg := wEx_nonneg
  have hpre_nonneg : ∀ t i, i ∈ (Finset.univ : Finset (Fin 2)) → 0 ≤ pre_fEx t (fun _ => ()) (fun _ => ()) i := by
    intro t i hi; simp [pre_fEx]
  have hsdpi : ∀ t i, i ∈ (Finset.univ : Finset (Fin 2)) →
      post_fEx t (fun _ => ()) (fun _ => ()) i ≤ SDPI.η (X:=Unit) (Y:=Unit) t * pre_fEx t (fun _ => ()) (fun _ => ()) i := by
    intro t i hi; simp [post_fEx, pre_fEx]
  -- t0=1 is strict since η 1 = 0.64 < 1; pick fiber i0=0 with positive weight and pre=1>0
  have ht0 : 1 ∈ Finset.range (2+1) := by decide
  have hηlt : SDPI.η (X:=Unit) (Y:=Unit) 1 < 1 := by simp [etaEx]
  have hi0 : (0 : Fin 2) ∈ (Finset.univ : Finset (Fin 2)) := by simp
  have hwpos : 0 < wEx 0 := by simp [wEx]
  have hprepos : 0 < pre_fEx 1 (fun _ => ()) (fun _ => ()) 0 := by simp [pre_fEx]
  -- Apply fiberwise strict lemma
  simpa using
    (di_dpi_from_fibers_strict (X:=Unit) (Y:=Unit) (ι:=Fin 2)
      (s:=Finset.univ) (w:=wEx) (pre_f:=pre_fEx) (post_f:=post_fEx)
      2 (fun _ => ()) (fun _ => ())
      (h_per_le_post := by intro t; exact h_per t)
      (hw_nonneg := hw_nonneg) (hpre_nonneg := hpre_nonneg) (h_uniform_sdpi := hsdpi)
      (t0:=1) (ht0:=ht0) (hη_lt:=hηlt) (i0:=0) (hi0:=hi0) (hw_pos:=hwpos) (hpre_pos:=hprepos))

end DI
end NOC

