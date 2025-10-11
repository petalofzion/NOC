Title: math help

Context
- Lean 4.23.0 + current mathlib in this repo.
- Files in focus now: NOC_ROOT/NOC/D/TTSA_Convergence.lean (D6/D4) and NOC_ROOT/NOC/Prob/RobbinsSiegmund.lean.

Status snapshot (what’s green)
- MDS layer (NOC/Prob/MDS.lean), including weighted_sum_ae_converges (a.e.).
- RS layer: v-sum partial bound and summability corollary; L¹-uniform bound for the drifted normalized process; supermartingale wiring and a.e. convergence alias (`NOC.TTSA.RS_drifted_ae_converges_core`).

What I’m implementing next (Option 1)
- D6 (interior hit): show the clamped 1‑D recursion enters [K, βmax] in finite time a.s. under a positive drift window near 0, Robbins–Monro steps, MDS noise, and summable bias.
- D4 (convergence): with unique locally stable root β⋆ and mild regularity (continuity + local Lipschitz), prove β_n → β⋆ a.s., combining D6 + MDS sum convergence + Lyapunov drift.

Where I’m stuck mathematically (precise gaps to close)
1) RS inequality for Y_n := (K − β_n)_+^2 under projection
   - Need a robust per-step inequality of the form
     E[Y_{n+1} | 𝓕_n] ≤ (1 + u_n) Y_n − v_n + w_n,
     with u_n = O(b_n^2), v_n ≳ c·b_n·(K − β_n)_+, and
     w_n = O(b_n^2) + O(b_n·E[|δ_{n+1}| | 𝓕_n]).
   - This requires a clean algebraic bound for the clamp step:
     clamp_nonexpansive is available, but I need a standard inequality to control
     (max 0 (K − clamp(x + s)))^2 in terms of (max 0 (K − x))^2, linear term in s,
     and a quadratic O(s^2) remainder, usable under conditional expectation.

2) Choice of v_n and w_n compatible with RS_vsum_summable_of_w_summable
   - Target: pick u ≡ 0 to make RSWeight ≡ 1 (simplifies the telescope), set
     v_n := c·b_n·(K − β_n)_+, w_n := C1·b_n^2 + C2·b_n·E[|δ_{n+1}| | 𝓕_n].
   - Need confirmation that this fits the standard Robbins–Siegmund template in mathlib or a short custom proof (1‑D, real-valued) is acceptable here.

3) From ∑ v_n < ∞ to “eventual β_n ≥ K”
   - With v_n ≍ b_n·(K − β_n)_+, ∑ v_n < ∞ and ∑ b_n = ∞ do not alone imply
     eventual β_n ≥ K. The classical argument uses the positive drift window
     to show that when β_n ≤ K often, the potential decreases by a non-summable
     amount—contradicting ∑ v_n < ∞. I need a concise lemma formalizing this
     step in our setting (1‑D, clamp, positive drift). Pointers to a standard
     inequality or a reference would help fix constants cleanly.

4) Lyapunov one‑step bound for D4
   - For V(β) := ∫_{β⋆}^β ḡ(u) du, need
     E[V(β_{n+1}) | 𝓕_n] ≤ V(β_n) − c·b_n·ḡ(β_n)^2 + C(b_n^2 + b_n·E|δ_{n+1}|).
   - A crisp inequality usable with cond. exp. and projection (leveraging
     clamp_nonexpansive + local Lipschitz) will let me invoke RS to conclude
     ∑ b_n ḡ(β_n)^2 < ∞ and convergence of V(β_n).

Assumptions/preferences to confirm (so I can proceed deterministically)
- Bias: prefer the a.s. summable variant ∑ b_n |δ_{n+1}| < ∞ (robust and standard).
- Steps: Robbins–Monro (∑ b_n = ∞, ∑ b_n^2 < ∞), b_n deterministic/predictable.
- Noise: MDS with bounded conditional variance (L²‑integrable increments).
- Drift window: ∃ ε0, β° > 0 s.t. ḡ(β) ≥ ε0 on [0, β°].
- Regularity: ḡ continuous and locally Lipschitz on [0, βmax]; unique locally
  stable root β⋆ ∈ (0, βmax].

What I’m requesting
- A standard per‑step inequality (statement or reference) for the projected
  step that yields the RS form for Y_n := (K − β_n)_+^2 with the error terms
  as above; or approval to implement a short custom 1‑D derivation under the
  listed regularity, relying on |x + s − clamp(x + s)| ≤ |s| and clamp 1‑Lipschitz.
- A short lemma/template to go from ∑ b_n·(K − β_n)_+ < ∞ and the positive
  window to “eventually β_n ≥ K” under the recursion (clamped SA). A precise
  formulation will prevent brittle algebra in Lean.

Why this is needed
- These two ingredients let me turn the existing RS/MDS machinery into the
  full D6/D4 proofs. Without them, the AE‑chaining/cond‑exp pieces are in place,
  but the core drift inequalities remain the blocking step.

Pointers (for reviewers)
- RS step assembly and supermartingale wiring live at:
  NOC_ROOT/NOC/Prob/RobbinsSiegmund.lean:834–1066, 1073–1162.
- clamp_nonexpansive is defined at:
  NOC_ROOT/NOC/D/TTSA_Convergence.lean:36–46.

Once I have sign‑off or the requested lemmas, I will replace the D6/D4 wrappers
with full proofs and mark Option 1 as complete in docs/TODO.md.
