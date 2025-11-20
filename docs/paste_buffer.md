  1 -import Mathlib
       2 -import NOC.D.BetaStabilityTTSA
       3 -import NOC.Prob.MDS
       4 -import NOC.Prob.Alignment
       5 -import NOC.Prob.RobbinsSiegmund
       6 -
       7 -/-!
       8 -Module: NOC.D.TTSA_Convergence
       9 -Status: scaffolding (no axioms). Orga
          nizes the Option 1 (1‑D projected SA)
      10 -and Option 2 (full TTSA A/B) theorem
          targets with precise, named bundles
      11 -and conclusions. These statements are
           ready for the proof agent to fill.
      12 -
      13 -Design: conclusions are packaged as `
          Prop` fields in hypothesis bundles
      14 -so we avoid committing to a specific
          measure API in this file. Once the
      15 -probability layer lands (NOC.Prob.*),
           these fields can be realized.
      16 -
      17 -Mathlib toolkit referenced by this sc
          affold:
      18 -- D3 (clamp nonexpansive): `Lipschitz
          With.id.const_min`,
      19 -  `LipschitzWith.const_max` (Topology
          /MetricSpace/Holder.lean)
      20 -- D1 (MDS sums, used by Option 1): se
          e `NOC.Prob.MDS` notes — conditional
      21 -  expectation API, martingale constru
          ction, Chebyshev/BC and/or a.e.
      22 -  martingale convergence.
      23 -- D2 (Robbins–Siegmund, used by Optio
          n 1 + D6): see `NOC.Prob.RobbinsSiegm
          und`.
      24 -- Deterministic stepping lemmas (wind
          ow/hitting) already live in
      25 -  `NOC.D.BetaStabilityTTSA` and are i
          mported above.
      26 --/
      27 -
      28 -namespace NOC.TTSA
      29 -noncomputable section
      30 -open Classical
      31 -open Filter
      32 -open scoped BigOperators ENNReal
      33 -
      34 --- Silence common linter notification
          s in this file
      35 -set_option linter.unusedVariables fal
          se
      36 -set_option linter.unusedSimpArgs fals
          e
      37 -set_option linter.unnecessarySimpa fa
          lse
      38 -set_option linter.unreachableTactic f
          alse
      39 -set_option linter.unusedTactic false
      40 -set_option linter.unusedSectionVars f
          alse
      41 -set_option maxHeartbeats 10000000
      42 -
      43 -/-- Algebraic helper: (a + b + c)^2 ≤
           3 * (a^2 + b^2 + c^2). -/
      44 -private lemma sq_sum_le_three (a b c
          : ℝ) :
      45 -    (a + b + c)^2 ≤ 3 * (a^2 + b^2 +
          c^2) := by
      46 -  -- From 0 ≤ (a-b)^2 + (b-c)^2 + (c-
          a)^2 we derive ab+bc+ca ≤ a^2+b^2+c^2
      47 -  have H : 0 ≤ (a - b)^2 + (b - c)^2
          + (c - a)^2 := by
      48 -    have h1 : 0 ≤ (a - b)^2 := by exa
          ct sq_nonneg _
      49 -    have h2 : 0 ≤ (b - c)^2 := by exa
          ct sq_nonneg _
      50 -    have h3 : 0 ≤ (c - a)^2 := by exa
          ct sq_nonneg _
      51 -    simpa [add_assoc] using add_nonne
          g (add_nonneg h1 h2) h3
      52 -  have H' : 0 ≤ 2 * (a ^ 2 + b ^ 2 +
          c ^ 2) - 2 * (a * b + b * c + c * a)
          := by
      53 -    -- expand ((a-b)^2 + (b-c)^2 + (c
          -a)^2) = 2*(a^2+b^2+c^2) - 2*(ab+bc+c
          a)
      54 -    have : (a - b) ^ 2 + (b - c) ^ 2
          + (c - a) ^ 2
      55 -        = 2 * (a ^ 2 + b ^ 2 + c ^ 2)
           - 2 * (a * b + b * c + c * a) := by
      56 -      ring
      57 -    simpa [this]
      58 -      using H
      59 -  have habc : a * b + b * c + c * a ≤
           a ^ 2 + b ^ 2 + c ^ 2 := by
      60 -    -- Divide the previous inequality
           by 2 and rearrange
      61 -    have : 2 * (a ^ 2 + b ^ 2 + c ^ 2
          ) - 2 * (a * b + b * c + c * a) ≥ 0 :
          = H'
      62 -    -- linarith can rearrange this in
          equality
      63 -    nlinarith
      64 -  -- Now finish the target
      65 -  calc
      66 -    (a + b + c) ^ 2
      67 -        = a ^ 2 + b ^ 2 + c ^ 2 + 2 *
           (a * b + b * c + c * a) := by ring
      68 -    _ ≤ a ^ 2 + b ^ 2 + c ^ 2 + 2 * (
          a ^ 2 + b ^ 2 + c ^ 2) := by
      69 -      have := mul_le_mul_of_nonneg_le
          ft habc (by norm_num : 0 ≤ (2 : ℝ))
      70 -      linarith
      71 -    _ = 3 * (a ^ 2 + b ^ 2 + c ^ 2) :
          = by ring
      72 -
      73 -/-- Window product lower bound: for φ
          (x) = (K-x)_+ and g ≥ ε0 on [0,K],
      74 -we have φ(β) * g(β) ≥ ε0 * φ(β). This
           avoids case splits. -/
      75 -private lemma window_prod_lb
      76 -    {g : ℝ → ℝ} {β K : ℝ} (ε0 : ℝ)
      77 -    (β_nonneg : 0 ≤ β)
      78 -    (g_pos_on : ∀ x, 0 ≤ x → x ≤ K →
          g x ≥ ε0) :
      79 -    (max 0 (K - β)) * g β ≥ ε0 * (max
           0 (K - β)) := by
      80 -  by_cases hβ : β ≤ K
      81 -  · have hφ : max 0 (K - β) = K - β :
          = by
      82 -      have : 0 ≤ K - β := sub_nonneg.
          mpr hβ
      83 -      simpa [max_eq_left this]
      84 -    have hg : g β ≥ ε0 := g_pos_on β
          β_nonneg hβ
      85 -    have hnonneg : 0 ≤ K - β := sub_n
          onneg.mpr hβ
      86 -    simpa [hφ, mul_comm, mul_left_com
          m, mul_assoc] using
      87 -      (mul_le_mul_of_nonneg_left hg h
          nonneg)
      88 -  · have hφ : max 0 (K - β) = 0 := by
      89 -      have : K - β ≤ 0 := sub_nonpos.
          mpr (le_of_not_ge hβ)
      90 -      simpa [max_eq_left_iff, this] u
          sing (le_of_eq rfl : 0 ≤ max 0 (K - β
          ))
      91 -    simp [hφ]
      92 -
      93 -/-! ## Shared utilities -/
      94 -
      95 -/-- Non-expansiveness of the canonica
          l clamp projection on the interval
      96 -`[0, βmax]`.  We package it as a `Lip
          schitzWith` statement to make it easy
      97 -to reuse inside projected stochastic-
          approximation proofs. -/
      98 -lemma clamp_nonexpansive (βmax : ℝ) :
      99 -    LipschitzWith 1 (fun x : ℝ => max
           0 (min βmax x)) := by
     100 -  -- `min βmax` is 1-Lipschitz (compo
          sition with the identity), and compos
          ing
     101 -  -- with `max 0` preserves the const
          ant.
     102 -  have hmin : LipschitzWith 1 (fun x
          : ℝ => min βmax x) :=
     103 -    (LipschitzWith.id.const_min βmax)
     104 -  simpa using (LipschitzWith.const_ma
          x hmin 0)
     105 -
     106 -/-- Range control for the clamp map `
          x ↦ max 0 (min βmax x)`. -/
     107 -lemma clamp_in_range (βmax x : ℝ) (hβ
          max : 0 ≤ βmax) :
     108 -    0 ≤ max 0 (min βmax x)
     109 -      ∧ max 0 (min βmax x) ≤ βmax :=
          by
     110 -  refine ⟨?_, ?_⟩
     111 -  · exact le_max_left _ _
     112 -  ·
     113 -    have hmin : min βmax x ≤ βmax :=
          min_le_left _ _
     114 -    exact (max_le_iff).mpr ⟨hβmax, hm
          in⟩
     115 -
     116 -/-- Algebraic helper: `(a - c)_+^2 ≤
          a^2 - 2 c a + c^2` for all real `a,c`
          .
     117 -Here `x_+ := max 0 x`. This is immedi
          ate from `(max 0 t)^2 ≤ t^2` with `t
          = a - c`.
     118 --/
     119 -lemma pospart_sub_sq_le (a c : ℝ) :
     120 -    (max 0 (a - c))^2 ≤ a^2 - 2 * a *
           c + c^2 := by
     121 -  have hpoly : (a - c)^2 = a^2 - 2 *
          a * c + c^2 := by ring
     122 -  by_cases h : 0 ≤ a - c
     123 -  · simpa [max_eq_right h, hpoly]
     124 -  · have hlt : a - c < 0 := lt_of_not
          _ge h
     125 -    have hL : (max 0 (a - c))^2 = 0 :
          = by simpa [max_eq_left_of_lt hlt]
     126 -    have hR : 0 ≤ a^2 - 2 * a * c + c
          ^2 := by simpa [hpoly] using (sq_nonn
          eg (a - c))
     127 -    simpa [hL] using hR
     128 -
     129 -/-- Subadditivity for positive parts:
           `(a + r)_+ ≤ a_+ + r_+` for all real
           `a,r`. -/
     130 -lemma pospart_add_le_posparts (a r :
          ℝ) :
     131 -    max 0 (a + r) ≤ max 0 a + max 0 r
           := by
     132 -  have hsum : a + r ≤ max 0 a + max 0
           r :=
     133 -    add_le_add (le_max_of_le_right le
          _rfl) (le_max_of_le_right le_rfl)
     134 -  have hnonneg : 0 ≤ max 0 a + max 0
          r := add_nonneg (le_max_left _ _) (le
          _max_left _ _)
     135 -  have : max (a + r) 0 ≤ max 0 a + ma
          x 0 r := (max_le_iff.mpr ⟨hsum, hnonn
          eg⟩)
     136 -  simpa [max_comm] using this
     137 -
     138 -/-- Convenience corollary: `(a + r)_+
           ≤ a_+ + |r|`. -/
     139 -lemma pospart_add_le_pos_abs (a r : ℝ
          ) :
     140 -    max 0 (a + r) ≤ max 0 a + |r| :=
          by
     141 -  have h := pospart_add_le_posparts a
           r
     142 -  have hbound : max 0 r ≤ |r| := by
     143 -    by_cases hr : 0 ≤ r
     144 -    · simpa [hr, abs_of_nonneg hr]
     145 -    · have hr' : r ≤ 0 := le_of_lt (l
          t_of_not_ge hr)
     146 -      simp [hr', abs_nonneg]
     147 -  exact h.trans (add_le_add_left hbou
          nd _)
     148 -
     149 -/-- Quadratic bound: `(a + r)_+^2 ≤ 2
           (a_+^2 + r^2)` for all real `a,r`. -
          /
     150 -lemma add_sq_le_two_sq (x y : ℝ) : (x
           + y)^2 ≤ 2 * (x^2 + y^2) := by
     151 -  -- Standard inequality: follows fro
          m nonnegativity of `(x−y)^2` and `(x+
          y)^2`.
     152 -  have hx : (x - y)^2 ≥ 0 := sq_nonne
          g _
     153 -  have hy : (x + y)^2 ≥ 0 := sq_nonne
          g _
     154 -  nlinarith
     155 -
     156 -lemma pospart_add_sq_le_two (a r : ℝ)
           :
     157 -    (max 0 (a + r))^2 ≤ 2 * ((max 0 a
          )^2 + r^2) := by
     158 -  have hle : max 0 (a + r) ≤ max 0 a
          + |r| := pospart_add_le_pos_abs a r
     159 -  have hx : 0 ≤ max 0 (a + r) := le_m
          ax_left _ _
     160 -  have hy : 0 ≤ max 0 a + |r| := add_
          nonneg (le_max_left _ _) (abs_nonneg
          _)
     161 -  have hsq : (max 0 (a + r)) * (max 0
           (a + r)) ≤ (max 0 a + |r|) * (max 0
          a + |r|) :=
     162 -    mul_le_mul hle hle hx hy
     163 -  have habs_sq : (|r|)^2 = r^2 := by
          simpa [pow_two] using (abs_mul_self r
          )
     164 -  have hrhs : (max 0 a + |r|)^2 ≤ 2 *
           ((max 0 a)^2 + (|r|)^2) := add_sq_le
          _two_sq _ _
     165 -  have : (max 0 (a + r))^2 ≤ 2 * ((ma
          x 0 a)^2 + (|r|)^2) := by
     166 -    simpa [pow_two] using (le_trans (
          by simpa [pow_two] using hsq) hrhs)
     167 -  simpa [habs_sq] using this
     168 -
     169 -/-- Barrier inequality without projec
          tion: for all `K,x,s`,
     170 -`(K - (x + s))_+^2 ≤ (K - x)_+^2 - 2
          (K - x)_+ s + s^2`. -/
     171 -lemma pospart_sub_mono_left {y₁ y₂ s
          : ℝ} (h : y₁ ≤ y₂) :
     172 -    max 0 (y₁ - s) ≤ max 0 (y₂ - s) :
          = by
     173 -  have hle : y₁ - s ≤ y₂ - s := sub_l
          e_sub_right h _
     174 -  by_cases hy2 : y₂ - s ≤ 0
     175 -  · -- RHS is 0; then LHS is also 0 s
          ince y₁ - s ≤ y₂ - s ≤ 0
     176 -    have hy1 : y₁ - s ≤ 0 := le_trans
           hle hy2
     177 -    have hR : max 0 (y₂ - s) = 0 := b
          y simpa [hy2] using max_eq_left_of_lt
           (lt_of_le_of_ne hy2 (by intro H; cas
          es hy2; simpa [H]))
     178 -    have hL : max 0 (y₁ - s) = 0 := b
          y simpa [hy1] using max_eq_left_of_lt
           (lt_of_le_of_ne hy1 (by intro H; cas
          es hy1; simpa [H]))
     179 -    simpa [hL, hR]
     180 -  · -- RHS positive
     181 -    have hRpos : 0 < y₂ - s := lt_of_
          not_ge hy2
     182 -    have hR : max 0 (y₂ - s) = y₂ - s
           := by simpa [max_eq_right (le_of_lt
          hRpos)]
     183 -    by_cases hy1' : y₁ - s ≤ 0
     184 -    · have hL : max 0 (y₁ - s) = 0 :=
           by simpa [hy1'] using max_eq_left_of
          _lt (lt_of_le_of_ne hy1' (by intro H;
           cases hy1'; simpa [H]))
     185 -      simpa [hL, hR, le_of_lt hRpos]
     186 -    · have hLpos : 0 < y₁ - s := lt_o
          f_not_ge hy1'
     187 -      have hL : max 0 (y₁ - s) = y₁ -
           s := by simpa [max_eq_right (le_of_l
          t hLpos)]
     188 -      have : y₁ - s ≤ y₂ - s := hle
     189 -      simpa [hL, hR] using this
     190 -
     191 -lemma barrier_ineq_unprojected (K x s
           : ℝ) :
     192 -    (max 0 (K - (x + s)))^2 ≤ (max 0
          (K - x))^2 - 2 * (max 0 (K - x)) * s
          + s^2 := by
     193 -  -- Let t := K - x. We compare `(t -
           s)_+` with `((t)_+ - s)_+`.
     194 -  set t := K - x
     195 -  have ht_le : t ≤ max 0 t := by simp
          a [max_comm] using (le_max_left t 0)
     196 -  have hmono : max 0 (t - s) ≤ max 0
          (max 0 t - s) :=
     197 -    pospart_sub_mono_left (y₁ := t) (
          y₂ := max 0 t) (s := s) ht_le
     198 -  have hx : 0 ≤ max 0 (t - s) := le_m
          ax_left _ _
     199 -  have hy : 0 ≤ max 0 (max 0 t - s) :
          = le_max_left _ _
     200 -  have hsq : (max 0 (t - s))^2 ≤ (max
           0 (max 0 t - s))^2 := by
     201 -    simpa [pow_two] using mul_le_mul
          hmono hmono hx hy
     202 -  have hbase := pospart_sub_sq_le (a
          := max 0 t) (c := s)
     203 -  have : (max 0 (t - s))^2 ≤ (max 0 t
          )^2 - 2 * (max 0 t) * s + s^2 :=
     204 -    le_trans hsq hbase
     205 -  simpa [t, sub_eq_add_neg, add_comm,
           add_left_comm, add_assoc, mul_comm,
          mul_left_comm, mul_assoc]
     206 -    using this
     207 -
     208 -/-- Projection shrinks the positive g
          ap to `K ∈ [0, βmax]`:
     209 -`(K - clamp(x))_+ ≤ (K - x)_+`. Here
          `clamp(x) = max 0 (min βmax x)`. -/
     210 -lemma pospart_K_clamp_le (βmax K x :
          ℝ)
     211 -    (hK0 : 0 ≤ K) (hKmax : K ≤ βmax)
          :
     212 -    max 0 (K - (max 0 (min βmax x)))
          ≤ max 0 (K - x) := by
     213 -  classical
     214 -  by_cases hx0 : x ≤ 0
     215 -  · -- clamp(x) = 0
     216 -    have hmin_le : min βmax x ≤ 0 :=
          le_trans (min_le_right _ _) hx0
     217 -    have hclamp : max 0 (min βmax x)
          = 0 := (max_eq_left_iff.mpr hmin_le)
     218 -    have hxpos : 0 ≤ K - x := by
     219 -      have hxneg : 0 ≤ -x := by simpa
           using (neg_nonneg.mpr hx0)
     220 -      simpa [sub_eq_add_neg, add_comm
          , add_left_comm] using add_nonneg hK0
           hxneg
     221 -    have hRHS : max 0 (K - x) = K - x
           := max_eq_right hxpos
     222 -    have hk_le : K ≤ K - x := by
     223 -      have hxneg : 0 ≤ -x := by simpa
           using (neg_nonneg.mpr hx0)
     224 -      simpa [sub_eq_add_neg] using ad
          d_le_add_left hxneg K
     225 -    simpa [hclamp, max_eq_right hK0,
          hRHS] using hk_le
     226 -  · by_cases hxmax : βmax ≤ x
     227 -    · -- clamp(x) = βmax ≥ K, so left
           side is 0
     228 -      have hmin : min βmax x = βmax :
          = min_eq_left hxmax
     229 -      have hβ : 0 ≤ βmax := le_trans
          hK0 hKmax
     230 -      have hclamp : max 0 (min βmax x
          ) = βmax := by simpa [hmin, hβ]
     231 -      have hLHS : max 0 (K - (max 0 (
          min βmax x))) = 0 := by
     232 -        have : K - βmax ≤ 0 := sub_no
          npos.mpr hKmax
     233 -        simpa [hclamp, this] using (m
          ax_eq_left_iff.mpr this)
     234 -      have : 0 ≤ max 0 (K - x) := le_
          max_left _ _
     235 -      simpa [hLHS] using (le_of_lt (l
          t_of_le_of_ne this (by intro H; exact
           False.elim rfl)))
     236 -      -- The last line simply asserts
           0 ≤ RHS.
     237 -    · -- 0 < x < βmax, clamp(x) = x
     238 -      have hxpos : 0 < x := lt_of_not
          _ge hx0
     239 -      have hxmin : x < βmax := lt_of_
          not_ge hxmax
     240 -      have hclamp : max 0 (min βmax x
          ) = x := by
     241 -        have : min βmax x = x := min_
          eq_right (le_of_lt hxmin)
     242 -        have : max 0 x = x := max_eq_
          right (le_of_lt hxpos)
     243 -        simpa [this, *]
     244 -      simpa [hclamp]
     245 -
     246 -/-- Projected barrier inequality: com
          pare the squared positive gap to `K`
          after
     247 -adding a step `s` and then projecting
           (clamping to `[0,βmax]`). -/
     248 -lemma barrier_ineq_projected (βmax K
          x s : ℝ)
     249 -    (hK0 : 0 ≤ K) (hKmax : K ≤ βmax)
          :
     250 -    (max 0 (K - (max 0 (min βmax (x +
           s)))))^2
     251 -      ≤ (max 0 (K - x))^2 - 2 * (max
          0 (K - x)) * s + s^2 := by
     252 -  have hcl : max 0 (K - (max 0 (min β
          max (x + s))))
     253 -              ≤ max 0 (K - (x + s)) :
          =
     254 -    pospart_K_clamp_le (βmax := βmax)
           (K := K) (x := x + s) hK0 hKmax
     255 -  have hu : 0 ≤ max 0 (K - (max 0 (mi
          n βmax (x + s)))) := le_max_left _ _
     256 -  have hv : 0 ≤ max 0 (K - (x + s)) :
          = le_max_left _ _
     257 -  have hsq : (max 0 (K - (max 0 (min
          βmax (x + s)))))^2
     258 -                ≤ (max 0 (K - (x + s)
          ))^2 := by
     259 -    simpa [pow_two] using mul_le_mul
          hcl hcl hu hv
     260 -  have hbase := barrier_ineq_unprojec
          ted (K := K) (x := x) (s := s)
     261 -  exact hsq.trans hbase
     262 -
     263 -/-- Pointwise RS-style step for the c
          lamped recursion. -/
     264 -lemma rs_step_pointwise
     265 -    (βmax K : ℝ) (b : ℕ → ℝ)
     266 -    (β : ℕ → α → ℝ) (g : ℝ → ℝ) (ξ δ
          : ℕ → α → ℝ)
     267 -    (hK0 : 0 ≤ K) (hKmax : K ≤ βmax)
     268 -    (hrec : ∀ n (ω : α),
     269 -      β (n+1) ω
     270 -        = max 0 (min βmax (β n ω + b
          n * (g (β n ω) + ξ (n+1) ω + δ (n+1)
          ω)))) :
     271 -    ∀ n (ω : α),
     272 -      (max 0 (K - β (n+1) ω))^2
     273 -        ≤ (max 0 (K - β n ω))^2
     274 -            - 2 * (max 0 (K - β n ω))
           * (b n * (g (β n ω) + ξ (n+1) ω + δ
          (n+1) ω))
     275 -            + (b n * (g (β n ω) + ξ (
          n+1) ω + δ (n+1) ω))^2 := by
     276 -  intro n ω
     277 -  have := barrier_ineq_projected (βma
          x := βmax) (K := K)
     278 -    (x := β n ω) (s := b n * (g (β n
          ω) + ξ (n+1) ω + δ (n+1) ω)) hK0 hKma
          x
     279 -  -- rewrite β_{n+1} via the recursio
          n
     280 -  simpa [hrec n ω, sub_eq_add_neg, mu
          l_comm, mul_left_comm, mul_assoc] usi
          ng this
     281 -
     282 -/-! ## Option 1 — 1‑D projected SA me
          ta‑theorem -/
     283 -
     284 -/-- Hypotheses for the 1‑D projected
          SA convergence theorem. -/
     285 -structure OneDProjectedSAHypotheses w
          here
     286 -  βmax         : ℝ
     287 -  steps        : Prop   -- Robbins–Mo
          nro: ∑ b_n = ∞, ∑ b_n^2 < ∞
     288 -  noise        : Prop   -- MDS + boun
          ded conditional second moment
     289 -  bias         : Prop   -- ∑ b_n E|δ_
          {n+1}| < ∞ (or a.s. summable)
     290 -  drift        : Prop   -- ḡ continu
          ous, locally Lipschitz, sign window n
          ear 0
     291 -  root_unique  : Prop   -- unique int
          erior root β⋆ and local stability
     292 -  alignment    : Prop   -- β_{n+1} =
          clamp(β_n + b_n (ḡ + ξ + δ)) (adapte
          d)
     293 -  /-- Desired conclusion: a.s. interi
          or hit and convergence to β⋆. -/
     294 -  conclusion   : Prop
     295 -
     296 -/-- Projected SA convergence in 1‑D (
          Option 1).
     297 -Under the hypotheses above, the clamp
          ed recursion converges a.s. to the
     298 -unique, locally stable interior root
          of the averaged drift. -/
     299 -def projected_SA_converges_1D (H : On
          eDProjectedSAHypotheses) : Prop :=
     300 -  -- Target conclusion placeholder; t
          he proof agent will provide a term of
           this Prop.
     301 -  H.conclusion
     302 -
     303 -/-- D4 (alias): Projected SA converge
          nce in 1‑D.
     304 -This name matches the meta‑theorem re
          ferenced by downstream modules. -/
     305 -def projected_SA_converges (H : OneDP
          rojectedSAHypotheses) : Prop :=
     306 -  projected_SA_converges_1D H
     307 -
     308 -/-!
     309 -## D6 RS Wiring — Hypothesis bundle (
          skeleton)
     310 -
     311 -To keep the TTSA layer model‑agnostic
           while enabling the RS pipeline, we e
          xpose
     312 -an interface bundle that callers can
          instantiate. The proof is provided in
           the
     313 -probability layer; here we only organ
          ize the data in a stable shape.
     314 --/
     315 -
     316 -section D6_RS
     317 -
     318 -variable {Ω : Type*} {m0 : Measurable
          Space Ω}
     319 -
     320 -/-- Minimal hypothesis bundle to driv
          e the D6 RS inequality wiring.
     321 -
     322 -This bundle is intentionally model‑ag
          nostic. It collects:
     323 -- a recursion `β` updated by a clampe
          d step with `b`, `g`, `ξ`, `δ`;
     324 -- a positive window level `K` with `0
           ≤ K ≤ βmax`;
     325 -- a monotone `g`-window lower bound `
          ε0` on `[0,K]`;
     326 -- deterministic bounds needed to form
           a summable `w` budget.
     327 -
     328 -It does not fix a measure or filtrati
          on; those are supplied at the probabi
          lity
     329 -layer, which will prove the expectati
          on‑level RS step and summability.
     330 --/
     331 -structure D6RSData where
     332 -  βmax  : ℝ
     333 -  K     : ℝ
     334 -  b     : ℕ → ℝ
     335 -  g     : ℝ → ℝ
     336 -  ξ     : ℕ → Ω → ℝ
     337 -  δ     : ℕ → Ω → ℝ
     338 -  β     : ℕ → Ω → ℝ
     339 -  ε0    : ℝ
     340 -  K_nonneg : 0 ≤ K
     341 -  K_le_βmax : K ≤ βmax
     342 -  g_window  : ∀ x, 0 ≤ x → x ≤ K → g
          x ≥ ε0
     343 -  /-- Clamped recursion (pointwise, m
          odel‑agnostic). -/
     344 -  step : ∀ n ω,
     345 -    β (n+1) ω = max 0 (min βmax (β n
          ω + b n * (g (β n ω) + ξ (n+1) ω + δ
          (n+1) ω)))
     346 -
     347 -/-- The RS field to be formed from `D
          6RSData`. Exposes `Y,u,v,w` in the TT
          SA layer. -/
     348 -structure D6RSField (D : D6RSData) wh
          ere
     349 -  Y : ℕ → Ω → ℝ := fun n ω => (max 0
          (D.K - D.β n ω))^2
     350 -  u : ℕ → ℝ := fun _ => 0
     351 -  v : ℕ → Ω → ℝ := fun n ω => 2 * D.ε
          0 * D.b n * max 0 (D.K - D.β n ω)
     352 -  w_model : ℕ → Ω → ℝ    -- caller su
          pplies a nonnegative model‑specific b
          udget
     353 -
     354 -end D6_RS
     355 -
     356 --- (D6 wrappers added later, after th
          e main expectation-level lemma.)
     357 -
     358 -/-!
     359 -## D6 RS — Expectation-level inequali
          ty (Prop skeleton)
     360 -
     361 -This section records the expectation-
          level RS inequality and summability g
          oals
     362 -as `Prop` statements parameterized by
           a measure and filtration. The proofs
           live
     363 -in the probability layer. Keeping the
          m as `Prop` here lets TTSA remain
     364 -model-agnostic while exposing stable
          names for downstream code.
     365 --/
     366 -
     367 -section D6_RS_Expectations
     368 -
     369 -variable {Ω : Type*} {m0 : Measurable
          Space Ω}
     370 -variable (μ : MeasureTheory.Measure Ω
          ) (ℱ : MeasureTheory.Filtration ℕ m0)
     371 -
     372 -variable (D : D6RSData (Ω := Ω))
     373 -
     374 -/-- The RS components derived from `D
          6RSData` (names only). -/
     375 -def D6RS_Y : ℕ → Ω → ℝ := fun n ω =>
          (max 0 (D.K - D.β n ω))^2
     376 -def D6RS_u : ℕ → ℝ := fun _ => 0
     377 -def D6RS_v : ℕ → Ω → ℝ := fun n ω =>
          2 * D.ε0 * D.b n * max 0 (D.K - D.β n
           ω)
     378 -def D6RS_w (C : ℝ) (d : ℕ → ℝ) : ℕ →
          Ω → ℝ :=
     379 -  fun n _ => C * (D.b n) ^ 2 + 2 * D.
          K * D.b n * d n
     380 -
     381 -/-- RS conditional-expectation inequa
          lity (Prop):
     382 -`μ[ Y(n+1) | ℱ n ] ≤ (1+u n) Y n − v
          n + w n` with `u ≡ 0`. -/
     383 -def D6_RS_condExp_ineq
     384 -  (μ : MeasureTheory.Measure Ω)
     385 -  (ℱ : MeasureTheory.Filtration ℕ m0)
     386 -  (D : D6RSData (Ω := Ω))
     387 -  (C : ℝ) (d : ℕ → ℝ) : Prop := True
     388 -
     389 -/-- Deterministic summability budget
          (Prop): `∑(C b_n^2 + 2 K b_n d_n) < ∞
          `. -/
     390 -def D6_RS_w_summable (C : ℝ) (d : ℕ →
           ℝ) : Prop :=
     391 -  Summable (fun n => C * (D.b n) ^ 2
          + 2 * D.K * D.b n * d n)
     392 -
     393 -/-- Interior-hit goal (Prop): eventua
          lly `β n ≥ K` almost surely. -/
     394 -def D6_RS_interior_hit_goal
     395 -  (μ : MeasureTheory.Measure Ω)
     396 -  (D : D6RSData (Ω := Ω)) : Prop :=
     397 -  ∀ᵐ ω ∂ μ, ∃ N, ∀ n ≥ N, D.β n ω ≥ D
          .K
     398 -
     399 -/-- RS-to-interior-hit wrapper (Prop)
          : under the RS inequality and budget,
           the
     400 -interior-hit property holds. The proo
          f is supplied in the probability laye
          r. -/
     401 -def D6_RS_interior_hit_from_RS (C : ℝ
          ) (d : ℕ → ℝ) : Prop :=
     402 -  (D6_RS_condExp_ineq μ ℱ D C d ∧ D6_
          RS_w_summable (D := D) C d) →
     403 -  D6_RS_interior_hit_goal μ D
     404 -
     405 -end D6_RS_Expectations
     406 -
     407 -/-! ## D6 — Scalar RS u≡0 summability
           helper (TTSA alias)
     408 -
     409 -This helper wraps the RS scalar summa
          bility result with `u ≡ 0`, suitable
          for
     410 -consuming a scalar RS step `S (n+1) ≤
           S n − v n + w n` with summable `w`.
     411 --/
     412 -
     413 -section D6_RS_Scalar
     414 -
     415 -open NOC NOC.TTSA NOC.Prob MeasureThe
          ory
     416 -
     417 -variable {Ω : Type*} {m0 : Measurable
          Space Ω}
     418 -variable (μ : MeasureTheory.Measure Ω
          ) (ℱ : MeasureTheory.Filtration ℕ m0)
     419 -
     420 -theorem D6_scalar_RS_u0_summable
     421 -  [MeasureTheory.IsProbabilityMeasure
           μ]
     422 -  (ℱ : MeasureTheory.Filtration ℕ m0)
     423 -  (S v w : ℕ → ℝ)
     424 -  (hS_nonneg : ∀ n, 0 ≤ S n)
     425 -  (hv : ∀ k, 0 ≤ v k)
     426 -  (hw : ∀ k, 0 ≤ w k)
     427 -  (hstep : ∀ n, S (n+1) ≤ S n - v n +
           w n)
     428 -  (hwsum : Summable w) :
     429 -  Summable v := by
     430 -  classical
     431 -  -- Instantiate the RS u≡0 helper on
           the constant-in-ω process
     432 -  let Y : ℕ → Ω → ℝ := fun n _ => S n
     433 -  have hInt : ∀ n, MeasureTheory.Inte
          grable (Y n) μ := by
     434 -    intro n; simpa [Y] using MeasureT
          heory.integrable_const (S n)
     435 -  have hY_nonneg : ∀ n, 0 ≤ᵐ[μ] fun ω
           => Y n ω := by
     436 -    intro n
     437 -    have : ∀ᵐ ω ∂ μ, 0 ≤ S n := Measu
          reTheory.ae_of_all μ (fun _ => hS_non
          neg n)
     438 -    exact this.mono (by intro _ h; si
          mpa [Y] using h)
     439 -  have hRS : ∀ n,
     440 -      μ[ Y (n+1) | ℱ n ] ≤ᵐ[μ]
     441 -        (fun ω => (1 + (0 : ℝ)) * Y n
           ω - v n + w n) := by
     442 -    intro n
     443 -    have hL : μ[ Y (n+1) | ℱ n ] = fu
          n _ => S (n+1) := by
     444 -      simpa [Y] using
     445 -        (MeasureTheory.condExp_const
          (μ := μ) (m := ℱ n) (hm := ℱ.le n) (c
           := S (n+1)))
     446 -    have hR : (fun ω => (1 + (0 : ℝ))
           * Y n ω - v n + w n) = fun _ => S n
          - v n + w n := by
     447 -      funext ω; simp [Y]
     448 -    have : (fun _ => S (n+1)) ≤ᵐ[μ] (
          fun _ => S n - v n + w n) :=
     449 -      (MeasureTheory.ae_of_all μ (fun
           _ => hstep n))
     450 -    simpa [hL, hR] using this
     451 -  -- u ≡ 0; apply RS alias
     452 -  exact NOC.TTSA.RS_summable_u_zero_c
          ore (μ := μ) (ℱ := ℱ)
     453 -    (Y := Y) (v := v) (w := w) hv hw
          hY_nonneg hInt hRS hwsum
     454 -
     455 -end D6_RS_Scalar
     456 -
     457 -/-! ## D6 — RS scalar context (packag
          ed) -/
     458 -
     459 -section D6_RS_ScalarContext
     460 -
     461 -variable {Ω : Type*} {m0 : Measurable
          Space Ω}
     462 -variable (μ : MeasureTheory.Measure Ω
          ) (ℱ : MeasureTheory.Filtration ℕ m0)
     463 -
     464 -structure D6ScalarRSContext (S v w :
          ℕ → ℝ) : Prop where
     465 -  hS_nonneg   : ∀ n, 0 ≤ S n
     466 -  hv_nonneg   : ∀ n, 0 ≤ v n
     467 -  hw_nonneg   : ∀ n, 0 ≤ w n
     468 -  step        : ∀ n, S (n+1) ≤ S n -
          v n + w n
     469 -  w_summable  : Summable w
     470 -
     471 -/-- From a scalar RS inequality with
          `u ≡ 0` and summable `w`, conclude `∑
           v` converges. -/
     472 -theorem d6_vsum_summable_from_scalar
     473 -  [MeasureTheory.IsProbabilityMeasure
           μ]
     474 -  (ℱ : MeasureTheory.Filtration ℕ m0)
     475 -  {S v w : ℕ → ℝ}
     476 -  (ctx : D6ScalarRSContext S v w)
     477 -  : Summable v :=
     478 -  D6_scalar_RS_u0_summable (μ := μ) (
          ℱ := ℱ)
     479 -    S v w ctx.hS_nonneg ctx.hv_nonneg
           ctx.hw_nonneg ctx.step ctx.w_summabl
          e
     480 -
     481 -end D6_RS_ScalarContext
     482 -
     483 -/-! ## D6 — Helper defs to shape scal
          ar RS from β -/
     484 -
     485 -section D6_RS_Scalars
     486 -
     487 -open MeasureTheory
     488 -
     489 -variable {Ω : Type*} {m0 : Measurable
          Space Ω}
     490 -variable (μ : MeasureTheory.Measure Ω
          )
     491 -
     492 -variable (D : D6RSData (Ω := Ω))
     493 -
     494 -/-- Scalar potential Sₙ from β: S n =
           ∫ (K − βₙ)_+^2 dμ. -/
     495 -def D6_S (n : ℕ) : ℝ := ∫ ω, (max 0 (
          D.K - D.β n ω))^2 ∂ μ
     496 -
     497 -/-- Scalar useful decrease vₙ from β
          with coefficient `c ≥ 0`:
     498 -v n = c · bₙ · ∫ (K − βₙ)_+ dμ. -/
     499 -def D6_v (c : ℝ) (n : ℕ) : ℝ := c * D
          .b n * (∫ ω, max 0 (D.K - D.β n ω) ∂
          μ)
     500 -
     501 -/-- Nonnegativity of `D6_S`. -/
     502 -lemma D6_S_nonneg (n : ℕ) : 0 ≤ D6_S
          (μ := μ) (D := D) n := by
     503 -  have hpos : 0 ≤ᵐ[μ] fun ω => (max 0
           (D.K - D.β n ω))^2 :=
     504 -    Filter.Eventually.of_forall (by i
          ntro ω; exact sq_nonneg _)
     505 -  simpa [D6_S] using (integral_nonneg
          _of_ae hpos)
     506 -
     507 -/-- Nonnegativity of `D6_v` when `c ≥
           0` and `bₙ ≥ 0`. -/
     508 -lemma D6_v_nonneg (c : ℝ) (hc : 0 ≤ c
          )
     509 -    (hb : ∀ n, 0 ≤ D.b n) (n : ℕ) :
     510 -    0 ≤ D6_v (μ := μ) (D := D) c n :=
           by
     511 -  have hint_nonneg : 0 ≤ ∫ ω, max 0 (
          D.K - D.β n ω) ∂ μ := by
     512 -    have hpos : 0 ≤ᵐ[μ] fun ω => max
          0 (D.K - D.β n ω) :=
     513 -      Filter.Eventually.of_forall (by
           intro ω; exact le_max_left _ _)
     514 -    simpa using (integral_nonneg_of_a
          e hpos)
     515 -  have : 0 ≤ c * D.b n := mul_nonneg
          hc (hb n)
     516 -  exact mul_nonneg this hint_nonneg
     517 -
     518 -end D6_RS_Scalars
     519 -
     520 -/-! ## D6 — Scalar step derived from
          D6RSData (packaged) -/
     521 -
     522 -/-
     523 -section D6_RS_From_Data
     524 -
     525 -open MeasureTheory
     526 -
     527 -variable {Ω : Type*} {m0 : Measurable
          Space Ω}
     528 -variable (μ : MeasureTheory.Measure Ω
          ) (ℱ : MeasureTheory.Filtration ℕ m0)
     529 -
     530 -variable (D : D6RSData (Ω := Ω))
     531 -
     532 -/-- Package a scalar RS step derived
          from `D6RSData` against a measure/fil
          tration. -/
     533 -structure D6ScalarFromData where
     534 -  S v w       : ℕ → ℝ
     535 -  hS_nonneg   : ∀ n, 0 ≤ S n
     536 -  hv_nonneg   : ∀ n, 0 ≤ v n
     537 -  hw_nonneg   : ∀ n, 0 ≤ w n
     538 -  step        : ∀ n, S (n+1) ≤ S n -
          v n + w n
     539 -  w_summable  : Summable w
     540 -
     541 -/-- From the packaged scalar step, co
          nclude the v-sum is summable (u ≡ 0).
           -/
     542 -theorem d6_vsum_summable_from_data
     543 -  [MeasureTheory.IsProbabilityMeasure
           μ]
     544 -  (ctx : D6ScalarFromData (D := D)) :
     545 -  Summable ctx.v := by
     546 -  -- Apply the scalar RS context theo
          rem
     547 -  refine d6_vsum_summable_from_scalar
           (μ := μ) (ℱ := ℱ)
     548 -      (ctx := {
     549 -        hS_nonneg := ctx.hS_nonneg,
     550 -        hv_nonneg := ctx.hv_nonneg,
     551 -        hw_nonneg := ctx.hw_nonneg,
     552 -        step := ctx.step,
     553 -        w_summable := ctx.w_summable
     554 -      } : D6ScalarRSContext ctx.S ctx
          .v ctx.w)
     555 -
     556 -end D6_RS_From_Data
     557 --/
     558 -
     559 -/-!
     560 -## D6 — Expectation-level RS step (L²
          -bias variant)
     561 -
     562 -We derive a scalar RS inequality for
          the clamped recursion under standard
     563 -stochastic assumptions, and conclude
          a summability statement for the usefu
          l
     564 -decrease terms. This prepares the int
          erior-hit argument.
     565 --/
     566 -
     567 ---
     568 -section D6_RS_ExpectationProof
     569 -
     570 -open MeasureTheory
     571 -
     572 -variable {Ω : Type*} {m0 : Measurable
          Space Ω}
     573 -variable (μ : Measure Ω) (ℱ : Measure
          Theory.Filtration ℕ m0)
     574 -variable [IsProbabilityMeasure μ]
     575 -
     576 -variable (D : D6RSData (Ω := Ω))
     577 -
     578 -/-- Assumptions needed to form the ex
          pectation-level RS step (L²-bias). -/
     579 -structure D6ProbAssumptions where
     580 -  adaptedβ   : Adapted ℱ D.β
     581 -  zeroMeanξ  : ∀ n, μ[ D.ξ (n+1) | ℱ
          n ] =ᵐ[μ] 0
     582 -  varBoundξ  : ℝ
     583 -  varBoundξ_nonneg : 0 ≤ varBoundξ
     584 -  secondMomξ : ∀ n, ∫ ω, (D.ξ (n+1) ω
          ) ^ 2 ∂ μ ≤ varBoundξ
     585 -  gBound     : ℝ    -- bound on g ove
          r [0,βmax]
     586 -  gBound_ge0 : 0 ≤ gBound
     587 -  gBound_ok  : ∀ x, 0 ≤ x → x ≤ D.βma
          x → |D.g x| ≤ gBound
     588 -  g_measurable : Measurable D.g
     589 -  ε0_nonneg : 0 ≤ D.ε0
     590 -  ε0_pos    : 0 < D.ε0
     591 -  bias2Bound : ℝ    -- uniform L² bou
          nd on δ
     592 -  bias2_nonneg : 0 ≤ bias2Bound
     593 -  secondMomδ : ∀ n, ∫ ω, (D.δ (n+1) ω
          ) ^ 2 ∂ μ ≤ bias2Bound
     594 -  steps_sq   : Summable (fun n => (D.
          b n) ^ 2)
     595 -  beta0_mem  : ∀ ω, 0 ≤ D.β 0 ω ∧ D.β
           0 ω ≤ D.βmax
     596 -  steps_nonneg : ∀ n, 0 ≤ D.b n
     597 -  biasAbs      : ℕ → ℝ
     598 -  biasAbs_nonneg : ∀ n, 0 ≤ biasAbs n
     599 -  biasAbs_dom :
     600 -    ∀ n, ∫ ω, |D.δ (n+1) ω| ∂ μ ≤ bia
          sAbs n
     601 -  biasAbs_summable :
     602 -    Summable (fun n => D.b n * biasAb
          s n)
     603 -  steps_sum_diverges :
     604 -    Tendsto (fun N => (Finset.range N
          ).sum fun k => D.b k) atTop atTop
     605 -  measξ  : ∀ n, AEStronglyMeasurable
          (fun ω => D.ξ (n+1) ω) μ
     606 -  measδ  : ∀ n, AEStronglyMeasurable
          (fun ω => D.δ (n+1) ω) μ
     607 -  xi_sq_integrable : ∀ n, Integrable
          (fun ω => (D.ξ (n+1) ω) ^ 2) μ
     608 -  delta_sq_integrable : ∀ n, Integrab
          le (fun ω => (D.δ (n+1) ω) ^ 2) μ
     609 -
     610 -/-- The clamped recursion keeps every
           iterate inside `[0, βmax]`. -/
     611 -lemma D6ProbAssumptions.beta_range
     612 -    (H : D6ProbAssumptions (μ := μ) (
          ℱ := ℱ) (D := D)) :
     613 -    ∀ n ω, 0 ≤ D.β n ω ∧ D.β n ω ≤ D.
          βmax := by
     614 -  classical
     615 -  have hβmax_nonneg : 0 ≤ D.βmax :=
     616 -    le_trans D.K_nonneg D.K_le_βmax
     617 -  refine Nat.rec ?base ?step
     618 -  · exact H.beta0_mem
     619 -  · intro n _ ω
     620 -    have hclamp :
     621 -        0 ≤ max 0
     622 -              (min D.βmax
     623 -                (D.β n ω
     624 -                  + D.b n *
     625 -                      (D.g (D.β n ω)
          + D.ξ (n + 1) ω + D.δ (n + 1) ω)))
     626 -          ∧
     627 -          max 0
     628 -              (min D.βmax
     629 -                (D.β n ω
     630 -                  + D.b n *
     631 -                      (D.g (D.β n ω)
          + D.ξ (n + 1) ω + D.δ (n + 1) ω)))
     632 -            ≤ D.βmax :=
     633 -      clamp_in_range (βmax := D.βmax)
     634 -        (x :=
     635 -          D.β n ω
     636 -            + D.b n *
     637 -                (D.g (D.β n ω) + D.ξ
          (n + 1) ω + D.δ (n + 1) ω))
     638 -        hβmax_nonneg
     639 -    rcases hclamp with ⟨hlo, hup⟩
     640 -    exact ⟨by simpa [D.step n ω] usin
          g hlo, by simpa [D.step n ω] using hu
          p⟩
     641 -
     642 -/-!  ### D6 helper functions  -/
     643 -
     644 -/-- Positive part gap `φₙ(ω) = (K − β
          ₙ(ω))_+`. -/
     645 -def d6_phi (D : D6RSData (Ω := Ω)) (n
           : ℕ) (ω : Ω) : ℝ :=
     646 -  max 0 (D.K - D.β n ω)
     647 -
     648 -/-- Noise/drift aggregate `χₙ = g(βₙ)
           + ξ_{n+1} + δ_{n+1}`. -/
     649 -def d6_chi (D : D6RSData (Ω := Ω)) (n
           : ℕ) (ω : Ω) : ℝ :=
     650 -  D.g (D.β n ω) + D.ξ (n+1) ω + D.δ (
          n+1) ω
     651 -
     652 -/-- Scaled aggregate `ψₙ = bₙ · χₙ`.
          -/
     653 -def d6_psi (D : D6RSData (Ω := Ω)) (n
           : ℕ) (ω : Ω) : ℝ :=
     654 -  D.b n * d6_chi (D := D) n ω
     655 -
     656 --- Basic arithmetic helper: |x| ≤ x²
          + 1, useful to pass from L² to L¹ on
          a finite measure.
     657 -private lemma abs_le_sq_add_one (x :
          ℝ) : |x| ≤ x ^ 2 + 1 := by
     658 -  have hrewrite : (|x| - 1 / 2) ^ 2 +
           3 / 4 = |x| ^ 2 - |x| + 1 := by ring
     659 -  have hident :
     660 -      x ^ 2 + 1 - |x| = (|x| - 1 / 2)
           ^ 2 + 3 / 4 := by
     661 -    have hx2' :
     662 -        x ^ 2 - |x| + 1 = |x| ^ 2 - |
          x| + 1 := by
     663 -      have := (abs_sq x).symm
     664 -      simpa [pow_two, sub_eq_add_neg]
           using congrArg (fun t => t - |x| + 1
          ) this
     665 -    calc
     666 -      x ^ 2 + 1 - |x| = x ^ 2 - |x| +
           1 := by ring
     667 -      _ = |x| ^ 2 - |x| + 1 := hx2'
     668 -      _ = (|x| - 1 / 2) ^ 2 + 3 / 4 :
          = by simpa [hrewrite] using hrewrite.
          symm
     669 -  have hpos : 0 ≤ (|x| - 1 / 2) ^ 2 +
           3 / 4 :=
     670 -    add_nonneg (sq_nonneg _) (by norm
          _num)
     671 -  have : 0 ≤ x ^ 2 + 1 - |x| := by
     672 -    simpa [hident] using hpos
     673 -  exact sub_nonneg.mp this
     674 -
     675 --- On any finite measure space, L² co
          ntrol implies L¹ control for real-val
          ued maps.
     676 -private lemma integrable_abs_of_sq
     677 -    (f : Ω → ℝ) (hf : AEStronglyMeasu
          rable f μ)
     678 -    [IsFiniteMeasure μ]
     679 -    (hL2 : Integrable (fun ω => (f ω)
           ^ 2) μ) :
     680 -    Integrable (fun ω => |f ω|) μ :=
          by
     681 -  have hdom :
     682 -      ∀ᵐ ω ∂ μ, ‖|f ω|‖ ≤ (f ω) ^ 2 +
           1 :=
     683 -    Filter.Eventually.of_forall (fun
          ω => by
     684 -      simpa [Real.norm_eq_abs, abs_of
          _nonneg (abs_nonneg _)]
     685 -        using abs_le_sq_add_one (f ω)
          )
     686 -  have hf_abs : AEStronglyMeasurable
          (fun ω => |f ω|) μ := by
     687 -    simpa [Real.norm_eq_abs] using hf
          .norm
     688 -  refine Integrable.mono'
     689 -      (hL2.add (integrable_const (μ :
          = μ) (1 : ℝ)))
     690 -      hf_abs
     691 -      hdom
     692 -
     693 -/-- If `φ` is ℱₙ-measurable and integ
          rable, and `ξ` has zero conditional
     694 -expectation with respect to ℱₙ, then
          the cross integral vanishes. -/
     695 -lemma integral_phi_mul_condexp_zero
     696 -    (μ : Measure Ω) (ℱ : Filtration ℕ
           m0) [IsProbabilityMeasure μ]
     697 -    {n : ℕ} {φ ξ : Ω → ℝ}
     698 -    (hφ_meas : AEStronglyMeasurable[ℱ
           n] φ μ)
     699 -    (hφξ_int : Integrable (fun ω => φ
           ω * ξ ω) μ)
     700 -    (hξ_int : Integrable ξ μ)
     701 -    (hzero : μ[ξ | ℱ n] =ᵐ[μ] 0) :
     702 -    ∫ ω, φ ω * ξ ω ∂ μ = 0 := by
     703 -  classical
     704 -  have hce :=
     705 -    condExp_mul_of_aestronglyMeasurab
          le_left
     706 -      (μ := μ) (m := ℱ n)
     707 -      (hf := hφ_meas) (hg := hξ_int)
          (hfg := hφξ_int)
     708 -  have hmono : ℱ n ≤ m0 := ℱ.le _
     709 -  have hint :=
     710 -    (integral_condExp (μ := μ) (m :=
          ℱ n)
     711 -      (f := fun ω => φ ω * ξ ω) hmono
          ).symm
     712 -  have hzero' :
     713 -      ∫ ω,
     714 -          (μ[
     715 -            fun ω => φ ω * ξ ω
     716 -            | ℱ n]) ω ∂ μ = 0 := by
     717 -    have hpull :
     718 -        (μ[
     719 -          fun ω => φ ω * ξ ω
     720 -          | ℱ n]) =ᵐ[μ]
     721 -            (fun ω => φ ω * μ[ξ | ℱ n
          ] ω) := hce
     722 -    have hconst :
     723 -        (fun ω => φ ω * μ[ξ | ℱ n] ω)
           =ᵐ[μ] 0 := by
     724 -      filter_upwards [hzero] with ω h
          ω
     725 -      simp [hω]
     726 -    have := integral_congr_ae (μ := μ
          ) (hpull.trans hconst)
     727 -    simpa using this
     728 -  exact hint.trans hzero'
     729 -
     730 -/-- Integrate a window lower bound: i
          f `φ·h ≥ ε₀·φ` a.e. and both sides ar
          e
     731 -integrable, then the integral inequal
          ity holds. -/
     732 -lemma integral_window_lb
     733 -    (μ : Measure Ω) {φ h : Ω → ℝ} {ε0
           : ℝ}
     734 -    (hφh_int : Integrable (fun ω => φ
           ω * h ω) μ)
     735 -    (hφ_int : Integrable φ μ)
     736 -    (hineq : ∀ᵐ ω ∂ μ, ε0 * φ ω ≤ φ ω
           * h ω) :
     737 -    ε0 * ∫ ω, φ ω ∂ μ ≤ ∫ ω, φ ω * h
          ω ∂ μ := by
     738 -  have hright :
     739 -      Integrable (fun ω => ε0 * φ ω)
          μ :=
     740 -    hφ_int.smul ε0
     741 -  have hmono :=
     742 -    integral_mono_ae (hf := hright) (
          hg := hφh_int) (μ := μ) hineq
     743 -  have hconst :
     744 -      ∫ ω, ε0 * φ ω ∂ μ = ε0 * ∫ ω, φ
           ω ∂ μ :=
     745 -    integral_const_mul (μ := μ) (r :=
           ε0) (f := φ)
     746 -  simpa [Pi.smul_apply, smul_eq_mul,
          mul_comm, mul_left_comm, mul_assoc, h
          const]
     747 -    using hmono
     748 -
     749 -lemma d6_phi_nonneg
     750 -    (H : D6ProbAssumptions (μ := μ) (
          ℱ := ℱ) (D := D))
     751 -    (n : ℕ) (ω : Ω) :
     752 -    0 ≤ d6_phi D n ω := by
     753 -  unfold d6_phi
     754 -  exact le_max_left _ _
     755 -
     756 -lemma d6_phi_le_K
     757 -    (H : D6ProbAssumptions (μ := μ) (
          ℱ := ℱ) (D := D))
     758 -    (n : ℕ) (ω : Ω) :
     759 -    d6_phi D n ω ≤ D.K := by
     760 -  unfold d6_phi
     761 -  have hβ_nonneg : 0 ≤ D.β n ω := (H.
          beta_range (n := n) (ω := ω)).1
     762 -  have hdiff : D.K - D.β n ω ≤ D.K :=
           by
     763 -    have : - D.β n ω ≤ 0 := neg_nonpo
          s.mpr hβ_nonneg
     764 -    simpa [sub_eq_add_neg, add_comm,
          add_left_comm] using add_le_add_left
          this D.K
     765 -  exact (max_le_iff).mpr ⟨D.K_nonneg,
           hdiff⟩
     766 -
     767 -lemma d6_phi_aestronglyMeasurable
     768 -    (H : D6ProbAssumptions (μ := μ) (
          ℱ := ℱ) (D := D))
     769 -    (n : ℕ) :
     770 -    AEStronglyMeasurable[ℱ n] (fun ω
          => d6_phi D n ω) μ :=
     771 -  by
     772 -    unfold d6_phi
     773 -    have hβ :
     774 -        Measurable[ℱ n] (fun ω => D.β
           n ω) :=
     775 -      (H.adaptedβ n).measurable
     776 -    have hsub :
     777 -        Measurable[ℱ n] (fun ω => D.K
           - D.β n ω) :=
     778 -      measurable_const.sub hβ
     779 -    have hmax :
     780 -        Measurable[ℱ n] (fun ω => max
           (0 : ℝ) (D.K - D.β n ω)) :=
     781 -      measurable_const.max hsub
     782 -    exact hmax.aestronglyMeasurable
     783 -
     784 -lemma d6_phi_integrable
     785 -    (H : D6ProbAssumptions (μ := μ) (
          ℱ := ℱ) (D := D))
     786 -    (n : ℕ) :
     787 -    Integrable (fun ω => d6_phi D n ω
          ) μ := by
     788 -  have hsm :=
     789 -    (d6_phi_aestronglyMeasurable (μ :
          = μ) (ℱ := ℱ) (D := D) H n).mono (ℱ.l
          e n)
     790 -  have hbound :
     791 -      ∀ᵐ ω ∂ μ, ‖d6_phi D n ω‖ ≤ D.K
          := by
     792 -    refine Filter.Eventually.of_foral
          l ?_
     793 -    intro ω
     794 -    have hnonneg :
     795 -        0 ≤ d6_phi D n ω :=
     796 -      d6_phi_nonneg (μ := μ) (ℱ := ℱ)
           (D := D) H n ω
     797 -    have hφ_le :
     798 -        d6_phi D n ω ≤ D.K :=
     799 -      d6_phi_le_K (μ := μ) (ℱ := ℱ) (
          D := D) H n ω
     800 -    simpa [Real.norm_eq_abs, abs_of_n
          onneg hnonneg] using hφ_le
     801 -  refine Integrable.mono'
     802 -      (integrable_const (μ := μ) D.K)
     803 -      hsm
     804 -      hbound
     805 -
     806 -lemma d6_chi_aestronglyMeasurable
     807 -    (H : D6ProbAssumptions (μ := μ) (
          ℱ := ℱ) (D := D))
     808 -    (n : ℕ) :
     809 -    AEStronglyMeasurable (fun ω => d6
          _chi D n ω) μ := by
     810 -  unfold d6_chi
     811 -  have hβ :
     812 -      StronglyMeasurable (fun ω => D.
          β n ω) :=
     813 -    (H.adaptedβ n).mono (ℱ.le n)
     814 -  have h_gβ :
     815 -      AEStronglyMeasurable (fun ω =>
          D.g (D.β n ω)) μ :=
     816 -    (H.g_measurable.comp hβ.measurabl
          e).aestronglyMeasurable
     817 -  exact (h_gβ.add (H.measξ n)).add (H
          .measδ n)
     818 -
     819 -lemma d6_g_sq_integrable
     820 -    (H : D6ProbAssumptions (μ := μ) (
          ℱ := ℱ) (D := D))
     821 -    (n : ℕ) :
     822 -    Integrable (fun ω => (D.g (D.β n
          ω))^2) μ := by
     823 -  have hg_meas :
     824 -      AEStronglyMeasurable (fun ω =>
          D.g (D.β n ω)) μ := by
     825 -    have hβ : StronglyMeasurable (fun
           ω => D.β n ω) :=
     826 -      (H.adaptedβ n).mono (ℱ.le n)
     827 -    exact (H.g_measurable.comp hβ.mea
          surable).aestronglyMeasurable
     828 -  have hbound :
     829 -      ∀ᵐ ω ∂ μ, ‖(D.g (D.β n ω))^2‖ ≤
           H.gBound ^ 2 := by
     830 -    refine Filter.Eventually.of_foral
          l ?_
     831 -    intro ω
     832 -    have hβrng := H.beta_range (n :=
          n) (ω := ω)
     833 -    have hgabs : |D.g (D.β n ω)| ≤ H.
          gBound :=
     834 -      H.gBound_ok (D.β n ω) hβrng.1 h
          βrng.2
     835 -    have hsq :
     836 -        (D.g (D.β n ω))^2 ≤ H.gBound
          ^ 2 := by
     837 -      have hgabs' : |D.g (D.β n ω)| ≤
           |H.gBound| := by
     838 -        simpa [abs_of_nonneg H.gBound
          _ge0] using hgabs
     839 -      exact (sq_le_sq).mpr hgabs'
     840 -    have hnonneg : 0 ≤ (D.g (D.β n ω)
          )^2 := sq_nonneg _
     841 -    have hnorm :
     842 -        ‖(D.g (D.β n ω))^2‖ = (D.g (D
          .β n ω))^2 := by
     843 -      simpa [Real.norm_eq_abs, abs_of
          _nonneg hnonneg]
     844 -    simpa [hnorm] using hsq
     845 -  refine
     846 -    Integrable.mono'
     847 -      (integrable_const (μ := μ) (H.g
          Bound ^ 2))
     848 -      (hg_meas.pow 2)
     849 -      hbound
     850 -
     851 -lemma d6_g_abs_integrable
     852 -    (H : D6ProbAssumptions (μ := μ) (
          ℱ := ℱ) (D := D))
     853 -    (n : ℕ) :
     854 -    Integrable (fun ω => |D.g (D.β n
          ω)|) μ := by
     855 -  have hg_sq := d6_g_sq_integrable (μ
           := μ) (ℱ := ℱ) (D := D) H n
     856 -  have hg_meas :
     857 -      AEStronglyMeasurable (fun ω =>
          D.g (D.β n ω)) μ := by
     858 -    have hβ : StronglyMeasurable (fun
           ω => D.β n ω) :=
     859 -      (H.adaptedβ n).mono (ℱ.le n)
     860 -    exact (H.g_measurable.comp hβ.mea
          surable).aestronglyMeasurable
     861 -  exact integrable_abs_of_sq (μ := μ)
     862 -    (f := fun ω => D.g (D.β n ω)) hg_
          meas hg_sq
     863 -
     864 -lemma d6_phi_mul_g_integrable
     865 -    (H : D6ProbAssumptions (μ := μ) (
          ℱ := ℱ) (D := D))
     866 -    (n : ℕ) :
     867 -    Integrable (fun ω => d6_phi D n ω
           * D.g (D.β n ω)) μ := by
     868 -  have hφ_int := d6_phi_integrable (μ
           := μ) (ℱ := ℱ) (D := D) H n
     869 -  have hg_int :
     870 -      Integrable (fun ω => |D.g (D.β
          n ω)|) μ :=
     871 -    d6_g_abs_integrable (μ := μ) (ℱ :
          = ℱ) (D := D) H n
     872 -  have hg_meas :
     873 -      AEStronglyMeasurable (fun ω =>
          D.g (D.β n ω)) μ := by
     874 -    have hβ : StronglyMeasurable (fun
           ω => D.β n ω) :=
     875 -      (H.adaptedβ n).mono (ℱ.le n)
     876 -    exact (H.g_measurable.comp hβ.mea
          surable).aestronglyMeasurable
     877 -  have hbound :
     878 -      ∀ᵐ ω ∂ μ,
     879 -        ‖d6_phi D n ω * D.g (D.β n ω)
          ‖
     880 -          ≤ D.K * |D.g (D.β n ω)| :=
          by
     881 -    refine Filter.Eventually.of_foral
          l ?_
     882 -    intro ω
     883 -    have hφ_nonneg :
     884 -        0 ≤ d6_phi D n ω :=
     885 -      d6_phi_nonneg (μ := μ) (ℱ := ℱ)
           (D := D) H n ω
     886 -    have hφ_le :
     887 -        d6_phi D n ω ≤ D.K :=
     888 -      d6_phi_le_K (μ := μ) (ℱ := ℱ) (
          D := D) H n ω
     889 -    have hnorm :
     890 -        ‖d6_phi D n ω * D.g (D.β n ω)
          ‖
     891 -          = d6_phi D n ω * |D.g (D.β
          n ω)| := by
     892 -      have := abs_mul (d6_phi D n ω)
          (D.g (D.β n ω))
     893 -      have hφ_abs : |d6_phi D n ω| =
          d6_phi D n ω := by
     894 -        simpa [abs_of_nonneg hφ_nonne
          g]
     895 -      simpa [Real.norm_eq_abs, hφ_abs
          ] using this
     896 -    have hbnd :=
     897 -      mul_le_mul_of_nonneg_right hφ_l
          e (abs_nonneg (D.g (D.β n ω)))
     898 -    simpa [hnorm, abs_of_nonneg D.K_n
          onneg, mul_comm, mul_left_comm, mul_a
          ssoc]
     899 -      using hbnd
     900 -  have hint :
     901 -      Integrable (fun ω => D.K * |D.g
           (D.β n ω)|) μ :=
     902 -    (hg_int.smul D.K)
     903 -  refine Integrable.mono'
     904 -      hint
     905 -      (((d6_phi_aestronglyMeasurable
          (μ := μ) (ℱ := ℱ) (D := D) H n).mono
          (ℱ.le n)).mul
     906 -        hg_meas)
     907 -      hbound
     908 -
     909 -lemma d6_phi_sq_integrable
     910 -    (H : D6ProbAssumptions (μ := μ) (
          ℱ := ℱ) (D := D))
     911 -    (n : ℕ) :
     912 -    Integrable (fun ω => (d6_phi D n
          ω) ^ 2) μ := by
     913 -  have hsm :=
     914 -    (d6_phi_aestronglyMeasurable (μ :
          = μ) (ℱ := ℱ) (D := D) H n).mono (ℱ.l
          e n)
     915 -  have hbound :
     916 -      ∀ᵐ ω ∂ μ, ‖(d6_phi D n ω) ^ 2‖
          ≤ D.K ^ 2 := by
     917 -    refine Filter.Eventually.of_foral
          l ?_
     918 -    intro ω
     919 -    have hnonneg : 0 ≤ (d6_phi D n ω)
           ^ 2 := sq_nonneg _
     920 -    have hnorm :
     921 -        ‖(d6_phi D n ω) ^ 2‖
     922 -          = (d6_phi D n ω) ^ 2 := by
     923 -      simpa [Real.norm_eq_abs, abs_of
          _nonneg hnonneg]
     924 -    have hφ_le : d6_phi D n ω ≤ D.K :
          =
     925 -      d6_phi_le_K (μ := μ) (ℱ := ℱ) (
          D := D) H n ω
     926 -    have hφ_nonneg :
     927 -        0 ≤ d6_phi D n ω :=
     928 -      d6_phi_nonneg (μ := μ) (ℱ := ℱ)
           (D := D) H n ω
     929 -    have hsq :
     930 -        (d6_phi D n ω) ^ 2 ≤ D.K ^ 2
          := by
     931 -      simpa [pow_two, mul_comm, mul_l
          eft_comm] using
     932 -        (mul_le_mul hφ_le hφ_le hφ_no
          nneg D.K_nonneg)
     933 -    simpa [hnorm] using hsq
     934 -  refine
     935 -    Integrable.mono'
     936 -      (integrable_const (μ := μ) (D.K
           ^ 2))
     937 -      (hsm.pow 2)
     938 -      hbound
     939 -
     940 -lemma d6_chi_sq_integrable
     941 -    (H : D6ProbAssumptions (μ := μ) (
          ℱ := ℱ) (D := D))
     942 -    (n : ℕ) :
     943 -    Integrable (fun ω => (d6_chi D n
          ω) ^ 2) μ := by
     944 -  have hg_sq := d6_g_sq_integrable (μ
           := μ) (ℱ := ℱ) (D := D) H n
     945 -  have hξ_sq := H.xi_sq_integrable n
     946 -  have hδ_sq := H.delta_sq_integrable
           n
     947 -  have hsm := d6_chi_aestronglyMeasur
          able (μ := μ) (ℱ := ℱ) (D := D) H n
     948 -  have hbound :
     949 -      ∀ᵐ ω ∂ μ,
     950 -        ‖(d6_chi D n ω) ^ 2‖ ≤
     951 -          3 * (H.gBound ^ 2
     952 -              + (D.ξ (n+1) ω) ^ 2 + (
          D.δ (n+1) ω) ^ 2) := by
     953 -    refine Filter.Eventually.of_foral
          l ?_
     954 -    intro ω
     955 -    have hβrange : 0 ≤ D.β n ω ∧ D.β
          n ω ≤ D.βmax :=
     956 -      H.beta_range (n := n) (ω := ω)
     957 -    have hgabs :
     958 -        |D.g (D.β n ω)| ≤ H.gBound :=
     959 -      H.gBound_ok (D.β n ω) hβrange.1
           hβrange.2
     960 -    have hgbound :
     961 -        (D.g (D.β n ω))^2 ≤ H.gBound
          ^ 2 := by
     962 -      have hgabs' : |D.g (D.β n ω)| ≤
           |H.gBound| := by
     963 -        simpa [abs_of_nonneg H.gBound
          _ge0] using hgabs
     964 -      exact (sq_le_sq).mpr hgabs'
     965 -    have hineq :=
     966 -      sq_sum_le_three (D.g (D.β n ω))
           (D.ξ (n+1) ω) (D.δ (n+1) ω)
     967 -    have hnonneg : 0 ≤ (d6_chi D n ω)
           ^ 2 := sq_nonneg _
     968 -    have hnorm :
     969 -        ‖(d6_chi D n ω) ^ 2‖
     970 -          = (d6_chi D n ω) ^ 2 := by
     971 -      simpa [Real.norm_eq_abs, abs_of
          _nonneg hnonneg]
     972 -    have hrewrite :
     973 -        (d6_chi D n ω) =
     974 -          D.g (D.β n ω) + D.ξ (n+1) ω
           + D.δ (n+1) ω := rfl
     975 -    have hineq' :
     976 -        (d6_chi D n ω) ^ 2
     977 -          ≤ 3 * ((D.g (D.β n ω))^2
     978 -                + (D.ξ (n+1) ω)^2 + (
          D.δ (n+1) ω)^2) := by
     979 -      simpa [hrewrite, add_comm, add_
          left_comm, add_assoc] using hineq
     980 -    have hsum_le :
     981 -        (D.g (D.β n ω))^2
     982 -            + (D.ξ (n+1) ω)^2 + (D.δ
          (n+1) ω)^2
     983 -          ≤ H.gBound ^ 2
     984 -              + (D.ξ (n+1) ω)^2 + (D.
          δ (n+1) ω)^2 :=
     985 -      add_le_add_right (add_le_add hg
          bound (le_of_eq rfl)) _
     986 -    have hconst_nonneg : 0 ≤ (3 : ℝ)
          := by norm_num
     987 -    have hineq'' :
     988 -        (d6_chi D n ω) ^ 2
     989 -          ≤ 3 * (H.gBound ^ 2
     990 -                + (D.ξ (n+1) ω)^2 + (
          D.δ (n+1) ω)^2) :=
     991 -      le_trans hineq'
     992 -        (mul_le_mul_of_nonneg_left hs
          um_le hconst_nonneg)
     993 -    simpa [hnorm] using hineq''
     994 -  have hdom :
     995 -      Integrable
     996 -        (fun ω =>
     997 -          3 * (H.gBound ^ 2
     998 -              + (D.ξ (n+1) ω) ^ 2 + (
          D.δ (n+1) ω) ^ 2)) μ := by
     999 -    have hconst := integrable_const (
          μ := μ) (3 * H.gBound ^ 2)
    1000 -    have hξ := hξ_sq.smul (3 : ℝ)
    1001 -    have hδ := hδ_sq.smul (3 : ℝ)
    1002 -    have hsum := hξ.add hδ
    1003 -    have hdom' := hconst.add hsum
    1004 -    simpa [Pi.smul_apply, smul_eq_mul
          , mul_add, add_comm, add_left_comm,
    1005 -      add_assoc] using hdom'
    1006 -  refine Integrable.mono' hdom (hsm.p
          ow 2) ?_
    1007 -  refine hbound.mono ?_
    1008 -  intro ω hω
    1009 -  exact hω
    1010 -
    1011 -lemma d6_psi_aestronglyMeasurable
    1012 -    (H : D6ProbAssumptions (μ := μ) (
          ℱ := ℱ) (D := D))
    1013 -    (n : ℕ) :
    1014 -    AEStronglyMeasurable (fun ω => d6
          _psi D n ω) μ := by
    1015 -  unfold d6_psi
    1016 -  have hconst :
    1017 -      AEStronglyMeasurable (fun _ : Ω
           => D.b n) μ :=
    1018 -    measurable_const.aestronglyMeasur
          able
    1019 -  exact hconst.mul (d6_chi_aestrongly
          Measurable (μ := μ) (ℱ := ℱ) (D := D)
           H n)
    1020 -lemma d6_psi_sq_integrable
    1021 -    (H : D6ProbAssumptions (μ := μ) (
          ℱ := ℱ) (D := D))
    1022 -    (n : ℕ) :
    1023 -    Integrable (fun ω => (d6_psi D n
          ω) ^ 2) μ := by
    1024 -  have hχ := d6_chi_sq_integrable (μ
          := μ) (ℱ := ℱ) (D := D) H n
    1025 -  have h := hχ.smul ((D.b n) ^ 2)
    1026 -  have hconv :
    1027 -      (fun ω => ((D.b n) ^ 2) * (d6_c
          hi D n ω) ^ 2)
    1028 -        =ᵐ[μ] fun ω => (d6_psi D n ω)
           ^ 2 := by
    1029 -    refine Filter.Eventually.of_foral
          l ?_
    1030 -    intro ω
    1031 -    simp [Pi.smul_apply, smul_eq_mul,
           d6_psi, d6_chi, pow_two,
    1032 -      mul_comm, mul_left_comm, mul_as
          soc]
    1033 -  exact h.congr hconv
    1034 -
    1035 -lemma d6_phi_mul_psi_integrable
    1036 -    (H : D6ProbAssumptions (μ := μ) (
          ℱ := ℱ) (D := D))
    1037 -    (n : ℕ) :
    1038 -    Integrable (fun ω => d6_phi D n ω
           * d6_psi D n ω) μ := by
    1039 -  have hψ_sq := d6_psi_sq_integrable
          (μ := μ) (ℱ := ℱ) (D := D) H n
    1040 -  have hψ_sm := d6_psi_aestronglyMeas
          urable (μ := μ) (ℱ := ℱ) (D := D) H n
    1041 -  have hintAbsψ :
    1042 -      Integrable (fun ω => |d6_psi D
          n ω|) μ :=
    1043 -    integrable_abs_of_sq (μ := μ)
    1044 -      (f := fun ω => d6_psi D n ω) hψ
          _sm hψ_sq
    1045 -  have hbound :
    1046 -      ∀ᵐ ω ∂ μ,
    1047 -        ‖d6_phi D n ω * d6_psi D n ω‖
    1048 -          ≤ D.K * |d6_psi D n ω| := b
          y
    1049 -    refine Filter.Eventually.of_foral
          l ?_
    1050 -    intro ω
    1051 -    have hφ_nonneg :
    1052 -        0 ≤ d6_phi D n ω :=
    1053 -      d6_phi_nonneg (μ := μ) (ℱ := ℱ)
           (D := D) H n ω
    1054 -    have hφ_le : d6_phi D n ω ≤ D.K :
          =
    1055 -      d6_phi_le_K (μ := μ) (ℱ := ℱ) (
          D := D) H n ω
    1056 -    have hnorm :
    1057 -        ‖d6_phi D n ω * d6_psi D n ω‖
    1058 -          = d6_phi D n ω * |d6_psi D
          n ω| := by
    1059 -      have := abs_mul (d6_phi D n ω)
          (d6_psi D n ω)
    1060 -      have hφ_abs : |d6_phi D n ω| =
          d6_phi D n ω := by
    1061 -        simpa [abs_of_nonneg hφ_nonne
          g]
    1062 -      simpa [Real.norm_eq_abs, hφ_abs
          ] using this
    1063 -    have hbnd :=
    1064 -      mul_le_mul_of_nonneg_right hφ_l
          e (abs_nonneg (d6_psi D n ω))
    1065 -    simpa [hnorm, abs_of_nonneg D.K_n
          onneg, mul_comm, mul_left_comm, mul_a
          ssoc]
    1066 -      using hbnd
    1067 -  have hintKψ :
    1068 -      Integrable (fun ω => D.K * |d6_
          psi D n ω|) μ :=
    1069 -    (hintAbsψ.smul D.K)
    1070 -  refine Integrable.mono'
    1071 -      hintKψ
    1072 -      (((d6_phi_aestronglyMeasurable
          (μ := μ) (ℱ := ℱ) (D := D) H n).mono
          (ℱ.le n)).mul
    1073 -        (d6_psi_aestronglyMeasurable
          (μ := μ) (ℱ := ℱ) (D := D) H n))
    1074 -      hbound
    1075 -
    1076 -lemma d6_xi_abs_integrable
    1077 -    (H : D6ProbAssumptions (μ := μ) (
          ℱ := ℱ) (D := D))
    1078 -    (n : ℕ) :
    1079 -    Integrable (fun ω => |D.ξ (n+1) ω
          |) μ :=
    1080 -  integrable_abs_of_sq (μ := μ)
    1081 -    (f := fun ω => D.ξ (n+1) ω) (hf :
          = H.measξ n)
    1082 -    (hL2 := H.xi_sq_integrable n)
    1083 -
    1084 -lemma d6_phi_mul_xi_integrable
    1085 -    (H : D6ProbAssumptions (μ := μ) (
          ℱ := ℱ) (D := D))
    1086 -    (n : ℕ) :
    1087 -    Integrable (fun ω => d6_phi D n ω
           * D.ξ (n+1) ω) μ := by
    1088 -  have hξ_abs := d6_xi_abs_integrable
           (μ := μ) (ℱ := ℱ) (D := D) H n
    1089 -  have hbound :
    1090 -      ∀ᵐ ω ∂ μ,
    1091 -        ‖d6_phi D n ω * D.ξ (n+1) ω‖
    1092 -          ≤ D.K * |D.ξ (n+1) ω| := by
    1093 -    refine Filter.Eventually.of_foral
          l ?_
    1094 -    intro ω
    1095 -    have hφ_nonneg :
    1096 -        0 ≤ d6_phi D n ω :=
    1097 -      d6_phi_nonneg (μ := μ) (ℱ := ℱ)
           (D := D) H n ω
    1098 -    have hφ_le :
    1099 -        d6_phi D n ω ≤ D.K :=
    1100 -      d6_phi_le_K (μ := μ) (ℱ := ℱ) (
          D := D) H n ω
    1101 -    have hφ_abs : |d6_phi D n ω| = d6
          _phi D n ω := by
    1102 -      simpa [abs_of_nonneg hφ_nonneg]
    1103 -    have :=
    1104 -      mul_le_mul_of_nonneg_right hφ_l
          e (abs_nonneg (D.ξ (n+1) ω))
    1105 -    simpa [Real.norm_eq_abs, abs_mul,
           hφ_abs, abs_of_nonneg D.K_nonneg,
    1106 -      mul_comm, mul_left_comm, mul_as
          soc]
    1107 -      using this
    1108 -  have hintK :
    1109 -      Integrable (fun ω => D.K * |D.ξ
           (n+1) ω|) μ :=
    1110 -    (hξ_abs.smul D.K)
    1111 -  refine Integrable.mono'
    1112 -      hintK
    1113 -      (((d6_phi_aestronglyMeasurable
          (μ := μ) (ℱ := ℱ) (D := D) H n).mono
          (ℱ.le n)).mul
    1114 -        (H.measξ n))
    1115 -      hbound
    1116 -
    1117 -lemma d6_delta_abs_integrable
    1118 -    (H : D6ProbAssumptions (μ := μ) (
          ℱ := ℱ) (D := D))
    1119 -    (n : ℕ) :
    1120 -    Integrable (fun ω => |D.δ (n+1) ω
          |) μ :=
    1121 -  integrable_abs_of_sq (μ := μ)
    1122 -    (f := fun ω => D.δ (n+1) ω) (hf :
          = H.measδ n)
    1123 -    (hL2 := H.delta_sq_integrable n)
    1124 -
    1125 -lemma d6_phi_mul_delta_integrable
    1126 -    (H : D6ProbAssumptions (μ := μ) (
          ℱ := ℱ) (D := D))
    1127 -    (n : ℕ) :
    1128 -    Integrable (fun ω => d6_phi D n ω
           * D.δ (n+1) ω) μ := by
    1129 -  have hδ_abs := d6_delta_abs_integra
          ble (μ := μ) (ℱ := ℱ) (D := D) H n
    1130 -  have hbound :
    1131 -      ∀ᵐ ω ∂ μ,
    1132 -        ‖d6_phi D n ω * D.δ (n+1) ω‖
    1133 -          ≤ D.K * |D.δ (n+1) ω| := by
    1134 -    refine Filter.Eventually.of_foral
          l ?_
    1135 -    intro ω
    1136 -    have hφ_nonneg :
    1137 -        0 ≤ d6_phi D n ω :=
    1138 -      d6_phi_nonneg (μ := μ) (ℱ := ℱ)
           (D := D) H n ω
    1139 -    have hφ_le :
    1140 -        d6_phi D n ω ≤ D.K :=
    1141 -      d6_phi_le_K (μ := μ) (ℱ := ℱ) (
          D := D) H n ω
    1142 -    have hφ_abs : |d6_phi D n ω| = d6
          _phi D n ω := by
    1143 -      simpa [abs_of_nonneg hφ_nonneg]
    1144 -    have :=
    1145 -      mul_le_mul_of_nonneg_right hφ_l
          e (abs_nonneg (D.δ (n+1) ω))
    1146 -    simpa [Real.norm_eq_abs, abs_mul,
           hφ_abs, abs_of_nonneg D.K_nonneg,
    1147 -      mul_comm, mul_left_comm, mul_as
          soc]
    1148 -      using this
    1149 -  have hintK :
    1150 -      Integrable (fun ω => D.K * |D.δ
           (n+1) ω|) μ :=
    1151 -    (hδ_abs.smul D.K)
    1152 -  refine Integrable.mono'
    1153 -      hintK
    1154 -      (((d6_phi_aestronglyMeasurable
          (μ := μ) (ℱ := ℱ) (D := D) H n).mono
          (ℱ.le n)).mul
    1155 -        (H.measδ n))
    1156 -      hbound
    1157 -
    1158 -lemma d6_phi_delta_smul_bound
    1159 -    (H : D6ProbAssumptions (μ := μ) (
          ℱ := ℱ) (D := D))
    1160 -    (n : ℕ) :
    1161 -    |∫ ω, d6_phi D n ω * (D.b n * D.δ
           (n+1) ω) ∂ μ|
    1162 -      ≤ D.b n * D.K * H.biasAbs n :=
          by
    1163 -  have hφ_nonneg :
    1164 -      ∀ ω, 0 ≤ d6_phi D n ω :=
    1165 -    d6_phi_nonneg (μ := μ) (ℱ := ℱ) (
          D := D) H n
    1166 -  have hφ_le : ∀ ω, d6_phi D n ω ≤ D.
          K :=
    1167 -    d6_phi_le_K (μ := μ) (ℱ := ℱ) (D
          := D) H n
    1168 -  have habs :
    1169 -      ∀ ω,
    1170 -        |d6_phi D n ω * (D.b n * D.δ
          (n+1) ω)|
    1171 -          ≤ D.b n * D.K * |D.δ (n+1)
          ω| := by
    1172 -    intro ω
    1173 -    have hφ_abs : |d6_phi D n ω| = d6
          _phi D n ω := by
    1174 -      simpa [abs_of_nonneg (hφ_nonneg
           ω)]
    1175 -    have :=
    1176 -      mul_le_mul_of_nonneg_right
    1177 -        (hφ_le ω)
    1178 -        (abs_nonneg (D.b n * D.δ (n+1
          ) ω))
    1179 -    simpa [abs_mul, hφ_abs, abs_of_no
          nneg D.K_nonneg,
    1180 -      abs_of_nonneg (H.steps_nonneg n
          ), mul_comm, mul_left_comm, mul_assoc
          ]
    1181 -      using this
    1182 -  have hδ_abs :
    1183 -      Integrable (fun ω => |D.δ (n+1)
           ω|) μ :=
    1184 -    d6_delta_abs_integrable (μ := μ)
          (ℱ := ℱ) (D := D) H n
    1185 -  have hint_prod_base :=
    1186 -    d6_phi_mul_delta_integrable (μ :=
           μ) (ℱ := ℱ) (D := D) H n
    1187 -  have hprod :
    1188 -      Integrable
    1189 -        (fun ω => d6_phi D n ω * (D.b
           n * D.δ (n+1) ω)) μ := by
    1190 -    have hsmul := hint_prod_base.smul
           (D.b n)
    1191 -    have hconv :
    1192 -        (fun ω => D.b n * (d6_phi D n
           ω * D.δ (n+1) ω))
    1193 -          =ᵐ[μ] fun ω =>
    1194 -              d6_phi D n ω * (D.b n *
           D.δ (n+1) ω) := by
    1195 -      refine Filter.Eventually.of_for
          all ?_
    1196 -      intro ω
    1197 -      ring_nf
    1198 -    exact hsmul.congr hconv
    1199 -  have hint_absprod_norm := hprod.nor
          m
    1200 -  have hint_absprod :
    1201 -      Integrable
    1202 -        (fun ω => |d6_phi D n ω * (D.
          b n * D.δ (n+1) ω)|) μ := by
    1203 -    refine hint_absprod_norm.congr ?_
    1204 -    exact Filter.Eventually.of_forall
           (fun ω => by
    1205 -      simp only [Real.norm_eq_abs])
    1206 -  have hint_absδ :
    1207 -      Integrable (fun ω => D.b n * D.
          K * |D.δ (n+1) ω|) μ :=
    1208 -    (hδ_abs.smul (D.b n * D.K))
    1209 -  have hscale :
    1210 -      ∫ ω, |d6_phi D n ω * (D.b n * D
          .δ (n+1) ω)| ∂ μ
    1211 -        ≤ ∫ ω, D.b n * D.K * |D.δ (n+
          1) ω| ∂ μ := by
    1212 -    refine
    1213 -      integral_mono_ae
    1214 -        (hf := hint_absprod)
    1215 -        (hg := hint_absδ)
    1216 -        ?_
    1217 -    exact Filter.Eventually.of_forall
           habs
    1218 -  have hconst_mul :
    1219 -      ∫ ω, D.b n * D.K * |D.δ (n+1) ω
          | ∂ μ
    1220 -        = D.b n * D.K * ∫ ω, |D.δ (n+
          1) ω| ∂ μ := by
    1221 -    simpa [mul_comm, mul_left_comm, m
          ul_assoc] using
    1222 -      integral_const_mul (μ := μ)
    1223 -        (r := D.b n * D.K)
    1224 -        (f := fun ω => |D.δ (n+1) ω|)
    1225 -  have htriangle :=
    1226 -    abs_integral_le_integral_abs
    1227 -      (f := fun ω =>
    1228 -        d6_phi D n ω * (D.b n * D.δ (
          n+1) ω))
    1229 -      (μ := μ)
    1230 -  have hconst_nonneg : 0 ≤ D.b n * D.
          K :=
    1231 -    mul_nonneg (H.steps_nonneg n) D.K
          _nonneg
    1232 -  have hscaled :=
    1233 -    mul_le_mul_of_nonneg_left (H.bias
          Abs_dom n) hconst_nonneg
    1234 -  refine htriangle.trans ?_
    1235 -  calc
    1236 -    ∫ ω, |d6_phi D n ω * (D.b n * D.δ
           (n+1) ω)| ∂ μ
    1237 -        ≤ ∫ ω, D.b n * D.K * |D.δ (n+
          1) ω| ∂ μ := hscale
    1238 -    _ = D.b n * D.K * ∫ ω, |D.δ (n+1)
           ω| ∂ μ := hconst_mul
    1239 -    _ ≤ D.b n * D.K * H.biasAbs n :=
          by
    1240 -      simpa [mul_comm, mul_left_comm,
           mul_assoc] using hscaled
    1241 -
    1242 -lemma d6_phi_mul_chi_integrable
    1243 -    (H : D6ProbAssumptions (μ := μ) (
          ℱ := ℱ) (D := D))
    1244 -    (n : ℕ) :
    1245 -    Integrable (fun ω => d6_phi D n ω
           * d6_chi D n ω) μ := by
    1246 -  classical
    1247 -  set fg := fun ω => d6_phi D n ω * D
          .g (D.β n ω)
    1248 -  set fξ := fun ω => d6_phi D n ω * D
          .ξ (n+1) ω
    1249 -  set fδ := fun ω => d6_phi D n ω * D
          .δ (n+1) ω
    1250 -  have hfg := d6_phi_mul_g_integrable
           (μ := μ) (ℱ := ℱ) (D := D) H n
    1251 -  have hfξ := d6_phi_mul_xi_integrabl
          e (μ := μ) (ℱ := ℱ) (D := D) H n
    1252 -  have hfδ := d6_phi_mul_delta_integr
          able (μ := μ) (ℱ := ℱ) (D := D) H n
    1253 -  have hsum := hfg.add (hfξ.add hfδ)
    1254 -  have hsame :
    1255 -      (fun ω => d6_phi D n ω * d6_chi
           D n ω) =ᵐ[μ]
    1256 -        fun ω => fg ω + (fξ ω + fδ ω)
           := by
    1257 -    refine Filter.Eventually.of_foral
          l ?_
    1258 -    intro ω
    1259 -    simp [fg, fξ, fδ, d6_chi, mul_add
          , add_comm, add_left_comm, add_assoc,
    1260 -      mul_comm, mul_left_comm, mul_as
          soc]
    1261 -  exact hsum.congr hsame.symm
    1262 -
    1263 -lemma d6_chi_sq_integral_bound
    1264 -    (H : D6ProbAssumptions (μ := μ) (
          ℱ := ℱ) (D := D))
    1265 -    (n : ℕ) :
    1266 -    ∫ ω, (d6_chi D n ω) ^ 2 ∂ μ
    1267 -      ≤ 3 * (H.gBound ^ 2 + H.varBoun
          dξ + H.bias2Bound) := by
    1268 -  set χ := fun ω => d6_chi D n ω
    1269 -  have hineq_point :
    1270 -      ∀ ω,
    1271 -        χ ω ^ 2
    1272 -          ≤ 3 * (H.gBound ^ 2
    1273 -                + (D.ξ (n+1) ω) ^ 2 +
           (D.δ (n+1) ω) ^ 2) := by
    1274 -    intro ω
    1275 -    have hbase :
    1276 -        (χ ω) ^ 2
    1277 -          ≤ 3 * ((D.g (D.β n ω)) ^ 2
    1278 -                + (D.ξ (n+1) ω) ^ 2 +
           (D.δ (n+1) ω) ^ 2) := by
    1279 -      simpa [χ, d6_chi, add_comm, add
          _left_comm, add_assoc]
    1280 -        using
    1281 -          sq_sum_le_three (D.g (D.β n
           ω)) (D.ξ (n+1) ω) (D.δ (n+1) ω)
    1282 -    have hβ := H.beta_range (n := n)
          (ω := ω)
    1283 -    have hgabs :
    1284 -        |D.g (D.β n ω)| ≤ H.gBound :=
    1285 -      H.gBound_ok (D.β n ω) hβ.1 hβ.2
    1286 -    have hgbound :
    1287 -        (D.g (D.β n ω)) ^ 2 ≤ H.gBoun
          d ^ 2 := by
    1288 -      have hgabs' : |D.g (D.β n ω)| ≤
           |H.gBound| := by
    1289 -        simpa [abs_of_nonneg H.gBound
          _ge0] using hgabs
    1290 -      exact (sq_le_sq).mpr hgabs'
    1291 -    have hsum :
    1292 -        (D.g (D.β n ω)) ^ 2
    1293 -            + (D.ξ (n+1) ω) ^ 2 + (D.
          δ (n+1) ω) ^ 2
    1294 -          ≤ H.gBound ^ 2
    1295 -              + (D.ξ (n+1) ω) ^ 2 + (
          D.δ (n+1) ω) ^ 2 :=
    1296 -      add_le_add_right (add_le_add hg
          bound (le_of_eq rfl)) _
    1297 -    have hconst_nonneg : 0 ≤ (3 : ℝ)
          := by norm_num
    1298 -    exact hbase.trans
    1299 -      (mul_le_mul_of_nonneg_left hsum
           hconst_nonneg)
    1300 -  have hineq_ae :
    1301 -      (fun ω => χ ω ^ 2)
    1302 -        ≤ᶠ[ae μ]
    1303 -          fun ω =>
    1304 -            3 * (H.gBound ^ 2
    1305 -              + (D.ξ (n+1) ω) ^ 2 + (
          D.δ (n+1) ω) ^ 2) :=
    1306 -    Filter.Eventually.of_forall hineq
          _point
    1307 -  have hconst :
    1308 -      Integrable (fun _ : Ω => 3 * H.
          gBound ^ 2) μ := by
    1309 -    classical
    1310 -    refine ⟨measurable_const.aestrong
          lyMeasurable, ?_⟩
    1311 -    simpa using
    1312 -      (hasFiniteIntegral_const (μ :=
          μ) ((3 : ℝ) * H.gBound ^ 2))
    1313 -  have hxi :
    1314 -      Integrable (fun ω => 3 * (D.ξ (
          n+1) ω) ^ 2) μ := by
    1315 -    simpa [Pi.smul_apply, smul_eq_mul
          ] using
    1316 -      (H.xi_sq_integrable n).smul (3
          : ℝ)
    1317 -  have hδ :
    1318 -      Integrable (fun ω => 3 * (D.δ (
          n+1) ω) ^ 2) μ := by
    1319 -    simpa [Pi.smul_apply, smul_eq_mul
          ] using
    1320 -      (H.delta_sq_integrable n).smul
          (3 : ℝ)
    1321 -  have hdom' :
    1322 -      Integrable
    1323 -        (fun ω =>
    1324 -          3 * H.gBound ^ 2
    1325 -            + (3 * (D.ξ (n+1) ω) ^ 2
          + 3 * (D.δ (n+1) ω) ^ 2)) μ :=
    1326 -    hconst.add (hxi.add hδ)
    1327 -  have hdom :
    1328 -      Integrable
    1329 -        (fun ω =>
    1330 -          3 * (H.gBound ^ 2
    1331 -              + (D.ξ (n+1) ω) ^ 2 + (
          D.δ (n+1) ω) ^ 2)) μ := by
    1332 -    have hrewrite :
    1333 -        (fun ω =>
    1334 -          3 * (H.gBound ^ 2
    1335 -              + (D.ξ (n+1) ω) ^ 2 + (
          D.δ (n+1) ω) ^ 2))
    1336 -          =
    1337 -            fun ω =>
    1338 -              3 * H.gBound ^ 2
    1339 -                + (3 * (D.ξ (n+1) ω)
          ^ 2 + 3 * (D.δ (n+1) ω) ^ 2) := by
    1340 -      funext ω
    1341 -      simp [mul_add, add_comm, add_le
          ft_comm, add_assoc]
    1342 -    simpa [hrewrite] using hdom'
    1343 -  have hineq :=
    1344 -    integral_mono_ae
    1345 -      (hf := d6_chi_sq_integrable (μ
          := μ) (ℱ := ℱ) (D := D) H n)
    1346 -      (hg := hdom)
    1347 -      (μ := μ) hineq_ae
    1348 -  have hsum_split₁ :
    1349 -      ∫ ω,
    1350 -          3 * H.gBound ^ 2
    1351 -            + (3 * (D.ξ (n+1) ω) ^ 2
          + 3 * (D.δ (n+1) ω) ^ 2) ∂ μ
    1352 -        = ∫ ω, 3 * H.gBound ^ 2 ∂ μ
    1353 -            + ∫ ω,
    1354 -                (3 * (D.ξ (n+1) ω) ^
          2 + 3 * (D.δ (n+1) ω) ^ 2) ∂ μ :=
    1355 -    integral_add hconst (hxi.add hδ)
    1356 -  have hsum_split₂ :
    1357 -      ∫ ω,
    1358 -          (3 * (D.ξ (n+1) ω) ^ 2 + 3
          * (D.δ (n+1) ω) ^ 2) ∂ μ
    1359 -        = ∫ ω, 3 * (D.ξ (n+1) ω) ^ 2
          ∂ μ
    1360 -            + ∫ ω, 3 * (D.δ (n+1) ω)
          ^ 2 ∂ μ :=
    1361 -    integral_add hxi hδ
    1362 -  have hconst_eval :
    1363 -      ∫ ω, 3 * H.gBound ^ 2 ∂ μ = 3 *
           H.gBound ^ 2 := by
    1364 -    simpa using integral_const (μ :=
          μ) (3 * H.gBound ^ 2)
    1365 -  have hxi_eval :
    1366 -      ∫ ω, 3 * (D.ξ (n+1) ω) ^ 2 ∂ μ
    1367 -        = 3 * ∫ ω, (D.ξ (n+1) ω) ^ 2
          ∂ μ := by
    1368 -    simpa [mul_comm, mul_left_comm, m
          ul_assoc] using
    1369 -      integral_const_mul (μ := μ) (r
          := (3 : ℝ))
    1370 -        (f := fun ω => (D.ξ (n+1) ω)
          ^ 2)
    1371 -  have hδ_eval :
    1372 -      ∫ ω, 3 * (D.δ (n+1) ω) ^ 2 ∂ μ
    1373 -        = 3 * ∫ ω, (D.δ (n+1) ω) ^ 2
          ∂ μ := by
    1374 -    simpa [mul_comm, mul_left_comm, m
          ul_assoc] using
    1375 -      integral_const_mul (μ := μ) (r
          := (3 : ℝ))
    1376 -        (f := fun ω => (D.δ (n+1) ω)
          ^ 2)
    1377 -  have htotal :
    1378 -      (∫ ω,
    1379 -          3 * (H.gBound ^ 2
    1380 -              + (D.ξ (n+1) ω) ^ 2 + (
          D.δ (n+1) ω) ^ 2) ∂ μ)
    1381 -        ≤ 3 * (H.gBound ^ 2 + H.varBo
          undξ + H.bias2Bound) := by
    1382 -    have hle_xi : 3 * ∫ ω, (D.ξ (n+1)
           ω) ^ 2 ∂ μ ≤ 3 * H.varBoundξ :=
    1383 -      mul_le_mul_of_nonneg_left (H.se
          condMomξ n) (by norm_num)
    1384 -    have hle_delta : 3 * ∫ ω, (D.δ (n
          +1) ω) ^ 2 ∂ μ ≤ 3 * H.bias2Bound :=
    1385 -      mul_le_mul_of_nonneg_left (H.se
          condMomδ n) (by norm_num)
    1386 -    have hcalc :
    1387 -        ∫ ω,
    1388 -            3 * (H.gBound ^ 2
    1389 -                + (D.ξ (n+1) ω) ^ 2 +
           (D.δ (n+1) ω) ^ 2) ∂ μ
    1390 -          = 3 * H.gBound ^ 2
    1391 -              + (3 * ∫ ω, (D.ξ (n+1)
          ω) ^ 2 ∂ μ
    1392 -                  + 3 * ∫ ω, (D.δ (n+
          1) ω) ^ 2 ∂ μ) := by
    1393 -      calc
    1394 -        ∫ ω,
    1395 -            3 * (H.gBound ^ 2
    1396 -                + (D.ξ (n+1) ω) ^ 2 +
           (D.δ (n+1) ω) ^ 2) ∂ μ
    1397 -            = ∫ ω,
    1398 -                3 * H.gBound ^ 2
    1399 -                  + (3 * (D.ξ (n+1) ω
          ) ^ 2 + 3 * (D.δ (n+1) ω) ^ 2) ∂ μ :=
           by
    1400 -              simp [mul_add, add_comm
          , add_left_comm, add_assoc]
    1401 -        _ = 3 * H.gBound ^ 2
    1402 -              + ∫ ω,
    1403 -                  (3 * (D.ξ (n+1) ω)
          ^ 2 + 3 * (D.δ (n+1) ω) ^ 2) ∂ μ := b
          y
    1404 -              simpa [hconst_eval] usi
          ng hsum_split₁
    1405 -        _ = 3 * H.gBound ^ 2
    1406 -              + (∫ ω, 3 * (D.ξ (n+1)
          ω) ^ 2 ∂ μ
    1407 -                  + ∫ ω, 3 * (D.δ (n+
          1) ω) ^ 2 ∂ μ) := by
    1408 -              simpa [add_comm, add_le
          ft_comm, add_assoc] using hsum_split₂
    1409 -        _ = 3 * H.gBound ^ 2
    1410 -              + (3 * ∫ ω, (D.ξ (n+1)
          ω) ^ 2 ∂ μ
    1411 -                  + 3 * ∫ ω, (D.δ (n+
          1) ω) ^ 2 ∂ μ) := by
    1412 -              simp [hxi_eval, hδ_eval
          , add_comm, add_left_comm, add_assoc]
    1413 -    have hsum_le :
    1414 -        3 * H.gBound ^ 2
    1415 -            + (3 * ∫ ω, (D.ξ (n+1) ω)
           ^ 2 ∂ μ
    1416 -                + 3 * ∫ ω, (D.δ (n+1)
           ω) ^ 2 ∂ μ)
    1417 -          ≤ 3 * H.gBound ^ 2 + 3 * H.
          varBoundξ + 3 * H.bias2Bound := by
    1418 -      have hcore := add_le_add hle_xi
           hle_delta
    1419 -      have := add_le_add_left hcore (
          3 * H.gBound ^ 2)
    1420 -      simpa [add_comm, add_left_comm,
           add_assoc] using this
    1421 -    have hC :
    1422 -        3 * H.gBound ^ 2 + 3 * H.varB
          oundξ + 3 * H.bias2Bound
    1423 -          = 3 * (H.gBound ^ 2 + H.var
          Boundξ + H.bias2Bound) := by
    1424 -      ring
    1425 -    calc
    1426 -      (∫ ω,
    1427 -          3 * (H.gBound ^ 2
    1428 -              + (D.ξ (n+1) ω) ^ 2 + (
          D.δ (n+1) ω) ^ 2) ∂ μ)
    1429 -          = 3 * H.gBound ^ 2
    1430 -              + (3 * ∫ ω, (D.ξ (n+1)
          ω) ^ 2 ∂ μ
    1431 -                  + 3 * ∫ ω, (D.δ (n+
          1) ω) ^ 2 ∂ μ) := hcalc
    1432 -      _ ≤ 3 * H.gBound ^ 2 + 3 * H.va
          rBoundξ + 3 * H.bias2Bound := hsum_le
    1433 -      _ = 3 * (H.gBound ^ 2 + H.varBo
          undξ + H.bias2Bound) := by
    1434 -        simpa [hC]
    1435 -  exact hineq.trans htotal
    1436 -
    1437 -lemma d6_window_lower_bound
    1438 -    (H : D6ProbAssumptions (μ := μ) (
          ℱ := ℱ) (D := D))
    1439 -    (n : ℕ) (ω : Ω) :
    1440 -    d6_phi D n ω * D.g (D.β n ω) ≥ D.
          ε0 * d6_phi D n ω := by
    1441 -  have hβ := H.beta_range (n := n) (ω
           := ω)
    1442 -  simpa [d6_phi] using
    1443 -    window_prod_lb (β := D.β n ω) (K
          := D.K) (ε0 := D.ε0)
    1444 -      hβ.1
    1445 -      (fun x hx0 hxK => D.g_window x
          hx0 hxK)
    1446 -
    1447 -/-!
    1448 -Summary checklist for the L² D6 step
          (for future agents):
    1449 -* `S n` is the square-gap potential `
          ∫ (K − βₙ)_+²`, uniformly bounded by
          `K²`.
    1450 -* The “useful decrease” is `v n = 2 ε
          ₀ bₙ ∫ (K − βₙ)_+`.
    1451 -* The quadratic budget is always pack
          aged as `C · bₙ²` with
    1452 -  `C := 3 (gBound² + varBoundξ + bias
          2Bound)` via the Cauchy–Schwarz bound
    1453 -  `(a + b + c)² ≤ 3 (a² + b² + c²)` a
          nd the integral scaling lemmas.
    1454 - * All integrability goals use Route 
          A (certify each side is integrable,
    1455 -  then apply `integral_mono_ae`). In
          practice we rely on:
    1456 -   - bounded/nonnegative functions ⇒
          `Integrable` via `integrable_const` +
    1457 -     `Integrable.mono'`;
    1458 -   - `HasFiniteIntegral.mono` / `HasF
          initeIntegral.mono'` from
    1459 -     `Mathlib/MeasureTheory/Function/
          L1Space/HasFiniteIntegral.lean` to tu
          rn the
    1460 -     L² bounds `∫ ξ² ≤ varBoundξ`, `∫
           δ² ≤ bias2Bound` into reusable
    1461 -     `Integrable (ξ²)` / `Integrable
          (|ξ|)` statements; see the usage arou
          nd
    1462 -     `hIntRHS`.
    1463 -* Window positivity is discharged by
          `window_prod_lb`, so the `g ≥ ε₀`
    1464 -  hypothesis on `[0, K]` enters only
          through that lemma.
    1465 -* Local helpers `abs_le_sq_add_one`,
          `integrable_abs_of_sq` (defined above
          )
    1466 -  encode the `L² ⇒ L¹` upgrade used f
          or the δ-cross term.
    1467 -* Lemmas `integral_phi_mul_condexp_ze
          ro` and `integral_window_lb`
    1468 -  package the conditional-expectation
           cancellation and the window integral
    1469 -  bound so future agents do not need
          to rediscover the measure-theoretic s
          teps.
    1470 -* The deterministic bias budget `bias
          Abs` records envelopes
    1471 -  `∫ |δ_{n+1}| ≤ biasAbs n` with `∑ b
          ₙ biasAbs n < ∞`, so the linear bias
          term
    1472 -  folds cleanly into the RS budget `w
          `.
    1473 -These facts are fully self-contained
          in this file; no external search requ
          ired.
    1474 --/
    1475 -
    1476 -/-- Scalar RS summability from the cl
          amped recursion (L²-bias). -/
    1477 -theorem d6_scalar_RS_summable
    1478 -  (H : D6ProbAssumptions (μ := μ) (ℱ
          := ℱ) (D := D)) :
    1479 -  Summable (fun n => (2 * D.ε0) * D.b
           n * (∫ ω, max 0 (D.K - D.β n ω) ∂ μ)
          ) := by
    1480 -  set_option maxHeartbeats 10000000 i
          n
    1481 -  classical
    1482 -  let S : ℕ → ℝ := fun n => ∫ ω, (d6_
          phi D n ω) ^ 2 ∂ μ
    1483 -  let v : ℕ → ℝ :=
    1484 -    fun n => (2 * D.ε0) * D.b n * ∫ ω
          , d6_phi D n ω ∂ μ
    1485 -  let C : ℝ := 3 * (H.gBound ^ 2 + H.
          varBoundξ + H.bias2Bound)
    1486 -  let w : ℕ → ℝ :=
    1487 -    fun n => C * (D.b n) ^ 2 + 2 * D.
          K * D.b n * H.biasAbs n
    1488 -  suffices hvsum : Summable v by
    1489 -    simpa [v] using hvsum
    1490 -  have hβ_range := H.beta_range (μ :=
           μ) (ℱ := ℱ) (D := D)
    1491 -  have C_nonneg : 0 ≤ C := by
    1492 -    have hsum : 0 ≤ H.gBound ^ 2 + H.
          varBoundξ + H.bias2Bound := by
    1493 -      have hg : 0 ≤ H.gBound ^ 2 := s
          q_nonneg _
    1494 -      have hrest : 0 ≤ H.varBoundξ +
          H.bias2Bound :=
    1495 -        add_nonneg H.varBoundξ_nonneg
           H.bias2_nonneg
    1496 -      simpa [add_assoc] using add_non
          neg hg hrest
    1497 -    have hconst : 0 ≤ (3 : ℝ) := by n
          orm_num
    1498 -    simpa [C] using mul_nonneg hconst
           hsum
    1499 -  have hw_nonneg : ∀ n, 0 ≤ w n := by
    1500 -    intro n
    1501 -    have hb_sq : 0 ≤ (D.b n) ^ 2 := s
          q_nonneg _
    1502 -    have h1 : 0 ≤ C * (D.b n) ^ 2 :=
          mul_nonneg C_nonneg hb_sq
    1503 -    have hconst : 0 ≤ 2 * D.K := mul_
          nonneg (by norm_num) D.K_nonneg
    1504 -    have h2 :
    1505 -        0 ≤ 2 * D.K * D.b n * H.biasA
          bs n :=
    1506 -      mul_nonneg (mul_nonneg hconst (
          H.steps_nonneg n)) (H.biasAbs_nonneg
          n)
    1507 -    exact add_nonneg h1 h2
    1508 -  have hv_nonneg : ∀ n, 0 ≤ v n := by
    1509 -    intro n
    1510 -    have hφ_nonneg :
    1511 -        0 ≤ ∫ ω, d6_phi D n ω ∂ μ :=
    1512 -      integral_nonneg (by intro ω; ex
          act d6_phi_nonneg (μ := μ) (ℱ := ℱ) (
          D := D) H n ω)
    1513 -    have hcoeff : 0 ≤ (2 * D.ε0) * D.
          b n :=
    1514 -      mul_nonneg (mul_nonneg (by norm
          _num) H.ε0_nonneg) (H.steps_nonneg n)
    1515 -    exact mul_nonneg hcoeff hφ_nonneg
    1516 -  have hS_nonneg : ∀ n, 0 ≤ S n := by
    1517 -    intro n
    1518 -    have :=
    1519 -      integral_nonneg (μ := μ)
    1520 -        (f := fun ω => (d6_phi D n ω)
           ^ 2)
    1521 -        (by intro ω; exact sq_nonneg
          _)
    1522 -    simpa [S] using this
    1523 -  have hRS_step : ∀ n, S (n+1) ≤ S n
          - v n + w n := by
    1524 -    intro n
    1525 -    classical
    1526 -    set φNext := d6_phi D (n+1)
    1527 -    set φ := d6_phi D n
    1528 -    set χ := d6_chi D n
    1529 -    set f_rhs :=
    1530 -      fun ω =>
    1531 -        ((φ ω) ^ 2 + (-2 * D.b n * (φ
           ω * χ ω))) + (D.b n) ^ 2 * (χ ω) ^ 2
    1532 -    have hpt :=
    1533 -      rs_step_pointwise (βmax := D.βm
          ax) (K := D.K) (b := D.b)
    1534 -        (β := D.β) (g := D.g) (ξ := D
          .ξ) (δ := D.δ)
    1535 -        D.K_nonneg D.K_le_βmax D.step
           n
    1536 -    have hineq_ae :
    1537 -        (fun ω => (φNext ω) ^ 2) ≤ᶠ[a
          e μ]
    1538 -          f_rhs := by
    1539 -      refine Filter.Eventually.of_for
          all ?_
    1540 -      intro ω
    1541 -      have := hpt ω
    1542 -      convert this using 1 <;>
    1543 -        simp [φNext, φ, χ, f_rhs, d6_
          phi, d6_chi, pow_two, sub_eq_add_neg,
    1544 -          mul_comm, mul_left_comm, mu
          l_assoc, add_comm, add_left_comm,
    1545 -          add_assoc]
    1546 -    have hint_LHS : Integrable (fun ω
           => (φNext ω) ^ 2) μ :=
    1547 -      d6_phi_sq_integrable (μ := μ) (
          ℱ := ℱ) (D := D) H (n+1)
    1548 -    have hint_phi_sq : Integrable (fu
          n ω => (φ ω) ^ 2) μ :=
    1549 -      d6_phi_sq_integrable (μ := μ) (
          ℱ := ℱ) (D := D) H n
    1550 -    have hint_phichi :
    1551 -        Integrable (fun ω => φ ω * χ
          ω) μ :=
    1552 -      d6_phi_mul_chi_integrable (μ :=
           μ) (ℱ := ℱ) (D := D) H n
    1553 -    have hint_cross :
    1554 -        Integrable (fun ω => -2 * D.b
           n * (φ ω * χ ω)) μ := by
    1555 -      refine
    1556 -        (hint_phichi.smul (-2 * D.b n
          )).congr
    1557 -          (Filter.Eventually.of_foral
          l ?_)
    1558 -      intro ω
    1559 -      simp [Pi.smul_apply, smul_eq_mu
          l, mul_comm, mul_left_comm, mul_assoc
          ,
    1560 -        mul_add, add_comm, add_left_c
          omm, add_assoc]
    1561 -    have hint_partial :
    1562 -        Integrable
    1563 -          (fun ω => (φ ω) ^ 2 + (-2 *
           D.b n * (φ ω * χ ω))) μ := by
    1564 -      simpa [add_comm, add_left_comm,
           add_assoc] using
    1565 -        hint_phi_sq.add hint_cross
    1566 -    have hint_chi_sq : Integrable (fu
          n ω => (χ ω) ^ 2) μ :=
    1567 -      d6_chi_sq_integrable (μ := μ) (
          ℱ := ℱ) (D := D) H n
    1568 -    have hint_square :
    1569 -        Integrable (fun ω => (D.b n)
          ^ 2 * (χ ω) ^ 2) μ := by
    1570 -      refine
    1571 -        (hint_chi_sq.smul ((D.b n) ^
          2)).congr
    1572 -          (Filter.Eventually.of_foral
          l ?_)
    1573 -      intro ω
    1574 -      simp [Pi.smul_apply, smul_eq_mu
          l, mul_comm, mul_left_comm, mul_assoc
          ]
    1575 -    have hint_RHS : Integrable f_rhs
          μ := by
    1576 -      simpa [f_rhs] using hint_partia
          l.add hint_square
    1577 -    have hineq := integral_mono_ae (h
          f := hint_LHS) (hg := hint_RHS) (μ :=
           μ) hineq_ae
    1578 -    have hsplit₁ :
    1579 -        ∫ ω, f_rhs ω ∂ μ =
    1580 -          ∫ ω, (φ ω) ^ 2 + (-2 * D.b
          n * (φ ω * χ ω)) ∂ μ +
    1581 -            ∫ ω, (D.b n) ^ 2 * (χ ω)
          ^ 2 ∂ μ := by
    1582 -      simpa [f_rhs, add_comm, add_lef
          t_comm, add_assoc]
    1583 -        using integral_add hint_parti
          al hint_square
    1584 -    have hsplit₂ :
    1585 -        ∫ ω, (φ ω) ^ 2 + (-(2 * D.b n
           * (φ ω * χ ω))) ∂ μ =
    1586 -          ∫ ω, (φ ω) ^ 2 ∂ μ + ∫ ω, -
          (2 * D.b n * (φ ω * χ ω)) ∂ μ := by
    1587 -      convert
    1588 -        (integral_add hint_phi_sq hin
          t_cross) using 1 <;>
    1589 -        simp [mul_comm, mul_left_comm
          , mul_assoc, add_comm, add_left_comm,
    1590 -          add_assoc]
    1591 -    have hconst_cross :
    1592 -        ∫ ω, -(2 * D.b n * (φ ω * χ ω
          )) ∂ μ =
    1593 -          -(2 * D.b n) * ∫ ω, φ ω * χ
           ω ∂ μ := by
    1594 -      have := integral_const_mul (μ :
          = μ) (r := -(2 * D.b n))
    1595 -          (f := fun ω => φ ω * χ ω)
    1596 -      simpa [Pi.smul_apply, smul_eq_m
          ul, mul_comm, mul_left_comm, mul_asso
          c]
    1597 -        using this
    1598 -    have hconst_sq :
    1599 -        ∫ ω, (D.b n) ^ 2 * (χ ω) ^ 2
          ∂ μ =
    1600 -          (D.b n) ^ 2 * ∫ ω, (χ ω) ^
          2 ∂ μ := by
    1601 -      have := integral_const_mul (μ :
          = μ) (r := (D.b n) ^ 2)
    1602 -          (f := fun ω => (χ ω) ^ 2)
    1603 -      simpa [Pi.smul_apply, smul_eq_m
          ul, mul_comm, mul_left_comm, mul_asso
          c]
    1604 -        using this
    1605 -    have hRHS_eval :
    1606 -        ∫ ω, f_rhs ω ∂ μ =
    1607 -          S n + (-2 * D.b n * ∫ ω, φ
          ω * χ ω ∂ μ +
    1608 -            (D.b n) ^ 2 * ∫ ω, (χ ω)
          ^ 2 ∂ μ) := by
    1609 -      have hsplit :=
    1610 -        calc
    1611 -          ∫ ω, f_rhs ω ∂ μ
    1612 -              = ∫ ω, (φ ω) ^ 2 + (-2
          * D.b n * (φ ω * χ ω)) ∂ μ +
    1613 -                  ∫ ω, (D.b n) ^ 2 *
          (χ ω) ^ 2 ∂ μ := hsplit₁
    1614 -          _ = (∫ ω, (φ ω) ^ 2 ∂ μ + ∫
           ω, -2 * D.b n * (φ ω * χ ω) ∂ μ) +
    1615 -                  ∫ ω, (D.b n) ^ 2 *
          (χ ω) ^ 2 ∂ μ := by
    1616 -                simpa [hsplit₂, add_c
          omm, add_left_comm, add_assoc]
    1617 -          _ = S n + (-2 * D.b n * ∫ ω
          , φ ω * χ ω ∂ μ) +
    1618 -                (D.b n) ^ 2 * ∫ ω, (χ
           ω) ^ 2 ∂ μ := by
    1619 -                simp [S, φ, hconst_cr
          oss, hconst_sq, add_comm, add_left_co
          mm,
    1620 -                  add_assoc, sub_eq_a
          dd_neg]
    1621 -      simpa [add_comm, add_left_comm,
           add_assoc] using hsplit
    1622 -    have hineq_eval' :
    1623 -        S (n+1) ≤
    1624 -          S n + (-2 * D.b n * ∫ ω, φ
          ω * χ ω ∂ μ +
    1625 -            (D.b n) ^ 2 * ∫ ω, (χ ω)
          ^ 2 ∂ μ) := by
    1626 -      simpa [S, φ, φNext, hRHS_eval,
          add_comm, add_left_comm,
    1627 -        add_assoc] using hineq
    1628 -    have hineq_eval :
    1629 -        S (n+1) ≤
    1630 -          S n - 2 * D.b n * ∫ ω, φ ω
          * χ ω ∂ μ +
    1631 -            (D.b n) ^ 2 * ∫ ω, (χ ω)
          ^ 2 ∂ μ := by
    1632 -      simpa [sub_eq_add_neg, add_comm
          , add_left_comm, add_assoc]
    1633 -        using hineq_eval'
    1634 -    have hφχ_split :
    1635 -        ∫ ω, φ ω * χ ω ∂ μ =
    1636 -          ∫ ω, φ ω * D.g (D.β n ω) ∂
          μ
    1637 -            + ∫ ω, φ ω * D.ξ (n+1) ω
          ∂ μ
    1638 -            + ∫ ω, φ ω * D.δ (n+1) ω
          ∂ μ := by
    1639 -      have hint_g := d6_phi_mul_g_int
          egrable (μ := μ) (ℱ := ℱ) (D := D) H
          n
    1640 -      have hint_ξ := d6_phi_mul_xi_in
          tegrable (μ := μ) (ℱ := ℱ) (D := D) H
           n
    1641 -      have hint_δ := d6_phi_mul_delta
          _integrable (μ := μ) (ℱ := ℱ) (D := D
          ) H n
    1642 -      have hdecomp :
    1643 -          (fun ω => φ ω * χ ω) =
    1644 -            fun ω => (φ ω * D.g (D.β
          n ω)) +
    1645 -              ((φ ω * D.ξ (n+1) ω) +
          (φ ω * D.δ (n+1) ω)) := by
    1646 -        funext ω
    1647 -        simp [χ, d6_chi, mul_add, add
          _comm, add_left_comm, add_assoc, mul_
          comm,
    1648 -          mul_left_comm, mul_assoc]
    1649 -      have hsum₁ :
    1650 -          ∫ ω, (φ ω * D.ξ (n+1) ω) +
          (φ ω * D.δ (n+1) ω) ∂ μ =
    1651 -            ∫ ω, φ ω * D.ξ (n+1) ω ∂
          μ + ∫ ω, φ ω * D.δ (n+1) ω ∂ μ :=
    1652 -        integral_add hint_ξ hint_δ
    1653 -      have hsum₂ :
    1654 -          ∫ ω, (φ ω * D.g (D.β n ω))
          +
    1655 -              ((φ ω * D.ξ (n+1) ω) +
          (φ ω * D.δ (n+1) ω)) ∂ μ =
    1656 -            ∫ ω, φ ω * D.g (D.β n ω)
          ∂ μ +
    1657 -              ∫ ω, (φ ω * D.ξ (n+1) ω
          ) + (φ ω * D.δ (n+1) ω) ∂ μ :=
    1658 -        integral_add hint_g (hint_ξ.a
          dd hint_δ)
    1659 -      calc
    1660 -        ∫ ω, φ ω * χ ω ∂ μ
    1661 -            = ∫ ω, (φ ω * D.g (D.β n
          ω)) +
    1662 -                ((φ ω * D.ξ (n+1) ω)
          + (φ ω * D.δ (n+1) ω)) ∂ μ := by
    1663 -                simpa [hdecomp]
    1664 -        _ = ∫ ω, φ ω * D.g (D.β n ω)
          ∂ μ +
    1665 -              ∫ ω, (φ ω * D.ξ (n+1) ω
          ) + (φ ω * D.δ (n+1) ω) ∂ μ := by
    1666 -                simpa using hsum₂
    1667 -        _ = ∫ ω, φ ω * D.g (D.β n ω)
          ∂ μ +
    1668 -              (∫ ω, φ ω * D.ξ (n+1) ω
           ∂ μ + ∫ ω, φ ω * D.δ (n+1) ω ∂ μ) :=
           by
    1669 -                simpa using hsum₁
    1670 -        _ = ∫ ω, φ ω * D.g (D.β n ω)
          ∂ μ
    1671 -              + ∫ ω, φ ω * D.ξ (n+1)
          ω ∂ μ
    1672 -              + ∫ ω, φ ω * D.δ (n+1)
          ω ∂ μ := by
    1673 -                simpa [add_comm, add_
          left_comm, add_assoc]
    1674 -    have hξ_zero : ∫ ω, φ ω * D.ξ (n+
          1) ω ∂ μ = 0 := by
    1675 -      have hφ_meas :
    1676 -          AEStronglyMeasurable[ℱ n] φ
           μ := by
    1677 -        simpa [φ] using
    1678 -          d6_phi_aestronglyMeasurable
           (μ := μ) (ℱ := ℱ) (D := D) H n
    1679 -      have hint_prod := d6_phi_mul_xi
          _integrable (μ := μ) (ℱ := ℱ) (D := D
          ) H n
    1680 -      have hξ_int : Integrable (fun ω
           => D.ξ (n+1) ω) μ := by
    1681 -        have hnorm :
    1682 -            Integrable (fun ω => ‖D.ξ
           (n+1) ω‖) μ := by
    1683 -          simpa [Real.norm_eq_abs]
    1684 -            using d6_xi_abs_integrabl
          e (μ := μ) (ℱ := ℱ) (D := D) H n
    1685 -        exact
    1686 -          (integrable_norm_iff (μ :=
          μ)
    1687 -              (f := fun ω => D.ξ (n+1
          ) ω)
    1688 -              (hf := H.measξ n)).mp h
          norm
    1689 -      simpa [φ] using
    1690 -        integral_phi_mul_condexp_zero
           (μ := μ) (ℱ := ℱ) (n := n)
    1691 -          (φ := φ) (ξ := fun ω => D.ξ
           (n+1) ω) hφ_meas hint_prod hξ_int (H
          .zeroMeanξ n)
    1692 -    have hwindow :
    1693 -        D.ε0 * ∫ ω, φ ω ∂ μ ≤ ∫ ω, φ
          ω * D.g (D.β n ω) ∂ μ := by
    1694 -      refine integral_window_lb (μ :=
           μ) (φ := φ) (h := fun ω => D.g (D.β
          n ω))
    1695 -        (ε0 := D.ε0)
    1696 -        (d6_phi_mul_g_integrable (μ :
          = μ) (ℱ := ℱ) (D := D) H n)
    1697 -        (d6_phi_integrable (μ := μ) (
          ℱ := ℱ) (D := D) H n)
    1698 -        (Filter.Eventually.of_forall
    1699 -          (d6_window_lower_bound (μ :
          = μ) (ℱ := ℱ) (D := D) H n))
    1700 -    have hdelta_bound :
    1701 -        |∫ ω, φ ω * (D.b n * D.δ (n+1
          ) ω) ∂ μ| ≤ D.b n * D.K * H.biasAbs n
           :=
    1702 -      d6_phi_delta_smul_bound (μ := μ
          ) (ℱ := ℱ) (D := D) H n
    1703 -    have hchi_int :
    1704 -        (D.b n) ^ 2 * ∫ ω, (χ ω) ^ 2
          ∂ μ ≤ C * (D.b n) ^ 2 := by
    1705 -      have hχ_sq := d6_chi_sq_integra
          l_bound (μ := μ) (ℱ := ℱ) (D := D) H
          n
    1706 -      have hb_sq : 0 ≤ (D.b n) ^ 2 :=
           sq_nonneg _
    1707 -      have := mul_le_mul_of_nonneg_le
          ft hχ_sq hb_sq
    1708 -      simpa [C, mul_comm, mul_left_co
          mm, mul_assoc] using this
    1709 -    set Ig : ℝ := ∫ ω, φ ω * D.g (D.β
           n ω) ∂ μ
    1710 -    set Iδ : ℝ := ∫ ω, φ ω * D.δ (n+1
          ) ω ∂ μ
    1711 -    have hφχ_decomp :
    1712 -        ∫ ω, φ ω * χ ω ∂ μ = Ig + Iδ
          := by
    1713 -      simpa [hφχ_split, hξ_zero, Ig,
          Iδ, add_comm, add_left_comm, add_asso
          c]
    1714 -    have hcore :
    1715 -        S (n+1) ≤ S n - 2 * D.b n * (
          Ig + Iδ)
    1716 -              + (D.b n) ^ 2 * ∫ ω, (χ
           ω) ^ 2 ∂ μ := by
    1717 -      simpa [hφχ_decomp, mul_add, Ig,
           Iδ, add_comm, add_left_comm, add_ass
          oc]
    1718 -        using hineq_eval
    1719 -    have hg_term :
    1720 -        - 2 * D.b n * Ig
    1721 -          ≤ -(2 * D.ε0) * D.b n * ∫ ω
          , φ ω ∂ μ := by
    1722 -      have hpos : 0 ≤ 2 * D.b n := by
           nlinarith [H.steps_nonneg n]
    1723 -      have := mul_le_mul_of_nonneg_le
          ft hwindow hpos
    1724 -      have := neg_le_neg this
    1725 -      simpa [Ig, mul_comm, mul_left_c
          omm, mul_assoc] using this
    1726 -    have hδ_term :
    1727 -        - 2 * D.b n * Iδ
    1728 -          ≤ 2 * D.K * D.b n * H.biasA
          bs n := by
    1729 -      have hint :=
    1730 -        integral_const_mul (μ := μ) (
          r := D.b n)
    1731 -          (f := fun ω => φ ω * D.δ (n
          +1) ω)
    1732 -      have hrewrite :
    1733 -          D.b n * Iδ =
    1734 -            ∫ ω, φ ω * (D.b n * D.δ (
          n+1) ω) ∂ μ := by
    1735 -        simpa [Iδ, φ, mul_comm, mul_l
          eft_comm, mul_assoc] using hint.symm
    1736 -      have habs :
    1737 -          |D.b n * Iδ|
    1738 -            ≤ D.b n * D.K * H.biasAbs
           n := by
    1739 -        simpa [hrewrite] using hdelta
          _bound
    1740 -      have hcoeff :
    1741 -          |2 * D.b n * Iδ|
    1742 -            ≤ 2 * D.K * D.b n * H.bia
          sAbs n := by
    1743 -        have hscale := mul_le_mul_of_
          nonneg_left habs (by norm_num : (0 :
          ℝ) ≤ 2)
    1744 -        have hbabs : |D.b n| = D.b n
          := abs_of_nonneg (H.steps_nonneg n)
    1745 -        have htwo : |(2 : ℝ)| = (2 :
          ℝ) := by norm_num
    1746 -        simpa [abs_mul, Iδ, htwo, hba
          bs, mul_comm, mul_left_comm, mul_asso
          c]
    1747 -          using hscale
    1748 -      have hneg :=
    1749 -        (neg_le_abs (2 * D.b n * Iδ))
    1750 -      have hgoal :=
    1751 -        hneg.trans hcoeff
    1752 -      simpa [Iδ, mul_comm, mul_left_c
          omm, mul_assoc] using hgoal
    1753 -    have hineq_final : S (n+1) ≤ S n
          - v n + w n := by
    1754 -      have hsplit :
    1755 -          - 2 * D.b n * (Ig + Iδ)
    1756 -            = - 2 * D.b n * Ig + (- 2
           * D.b n * Iδ) := by ring
    1757 -      have hbound :
    1758 -          S (n+1) ≤
    1759 -            S n + (-(2 * D.ε0) * D.b
          n * ∫ ω, φ ω ∂ μ)
    1760 -              + (2 * D.K * D.b n * H.
          biasAbs n) + C * (D.b n) ^ 2 :=
    1761 -        calc
    1762 -          S (n+1) ≤
    1763 -              S n + (- 2 * D.b n * Ig
          )
    1764 -                + (- 2 * D.b n * Iδ)
    1765 -                + (D.b n) ^ 2 * ∫ ω,
          (χ ω) ^ 2 ∂ μ := by
    1766 -            simpa [hsplit, add_comm,
          add_left_comm, add_assoc,
    1767 -              sub_eq_add_neg, mul_add
          ,
    1768 -              Ig, Iδ, mul_comm, mul_l
          eft_comm, mul_assoc] using hcore
    1769 -          _ ≤ S n + (-(2 * D.ε0) * D.
          b n * ∫ ω, φ ω ∂ μ)
    1770 -              + (2 * D.K * D.b n * H.
          biasAbs n) + C * (D.b n) ^ 2 := by
    1771 -            have hsum := add_le_add h
          g_term hδ_term
    1772 -            have hsum' := add_le_add_
          left hsum (S n)
    1773 -            have hsum'' := add_le_add
           hsum' hchi_int
    1774 -            simpa [add_comm, add_left
          _comm, add_assoc,
    1775 -              Ig, Iδ, mul_comm, mul_l
          eft_comm, mul_assoc] using hsum''
    1776 -      have hw_eq :
    1777 -          S n + (-(2 * D.ε0) * D.b n
          * ∫ ω, φ ω ∂ μ)
    1778 -              + (2 * D.K * D.b n * H.
          biasAbs n) + C * (D.b n) ^ 2
    1779 -            = S n + (-(2 * D.ε0) * D.
          b n * ∫ ω, φ ω ∂ μ) + w n := by
    1780 -        simp [w, add_comm, add_left_c
          omm, add_assoc]
    1781 -      have hv :
    1782 -          -(2 * D.ε0) * D.b n * ∫ ω,
          φ ω ∂ μ = -v n := by
    1783 -        have hv_def : v n = (2 * D.ε0
          ) * D.b n * ∫ ω, φ ω ∂ μ := rfl
    1784 -        have hassoc :
    1785 -            -(2 * D.ε0) * D.b n * ∫ ω
          , φ ω ∂ μ
    1786 -              = -((2 * D.ε0) * D.b n
          * ∫ ω, φ ω ∂ μ) := by
    1787 -          ring
    1788 -        simpa [hv_def] using hassoc
    1789 -      have hrewrite_v :
    1790 -          S n + (-(2 * D.ε0) * D.b n
          * ∫ ω, φ ω ∂ μ) + w n
    1791 -            = S n + (-v n) + w n := b
          y
    1792 -        simpa [add_comm, add_left_com
          m, add_assoc] using
    1793 -          congrArg (fun t => S n + t
          + w n) hv
    1794 -      have hrewrite :
    1795 -          S n + (-(2 * D.ε0) * D.b n
          * ∫ ω, φ ω ∂ μ) + w n
    1796 -            = S n - v n + w n := by
    1797 -        simpa [sub_eq_add_neg, add_co
          mm, add_left_comm, add_assoc]
    1798 -          using hrewrite_v
    1799 -      exact hrewrite ▸ (hw_eq ▸ hboun
          d)
    1800 -    exact hineq_final
    1801 -  have hw_sum : Summable w := by
    1802 -    have hsteps : Summable (fun n =>
          C * (D.b n) ^ 2) :=
    1803 -      (H.steps_sq.mul_left C)
    1804 -    have hbias : Summable (fun n => 2
           * D.K * D.b n * H.biasAbs n) := by
    1805 -      have hbias0 :
    1806 -          Summable (fun n => (2 * D.K
          ) * (D.b n * H.biasAbs n)) :=
    1807 -        H.biasAbs_summable.mul_left (
          2 * D.K)
    1808 -      simpa [mul_comm, mul_left_comm,
           mul_assoc] using hbias0
    1809 -    exact hsteps.add hbias
    1810 -  classical
    1811 -  -- Define combined potential `T n :
          = S n + ∑_{k<n} v k`.
    1812 -  let T : ℕ → ℝ :=
    1813 -    fun n => S n + (Finset.range n).s
          um (fun k => v k)
    1814 -  -- Show `T n ≤ S₀ + ∑_{k<n} w k` by
           induction.
    1815 -  have hT :
    1816 -      ∀ n, T n ≤ S 0 + (Finset.range
          n).sum (fun k => w k) := by
    1817 -    intro n
    1818 -    induction' n with n ih
    1819 -    · simp [T]
    1820 -    · have hstep := hRS_step n
    1821 -      have hsum_v :
    1822 -          (Finset.range (n+1)).sum (f
          un k => v k)
    1823 -            = (Finset.range n).sum (f
          un k => v k) + v n := by
    1824 -        simp [Finset.sum_range_succ,
          add_comm, add_left_comm, add_assoc]
    1825 -      have hsum_w :
    1826 -          (Finset.range (n+1)).sum (f
          un k => w k)
    1827 -            = (Finset.range n).sum (f
          un k => w k) + w n := by
    1828 -        simp [Finset.sum_range_succ,
          add_comm, add_left_comm, add_assoc]
    1829 -      have hineq :
    1830 -          T (n+1) ≤ T n + w n := by
    1831 -        have :=
    1832 -          add_le_add_right
    1833 -            (add_le_add_right
    1834 -              (add_le_add_left hstep
          ((Finset.range n).sum fun k => v k))
    1835 -              (v n))
    1836 -            (0 : ℝ)
    1837 -        simpa [T, hsum_v, add_comm, a
          dd_left_comm, add_assoc, sub_eq_add_n
          eg]
    1838 -          using this
    1839 -      -- combine with the induction h
          ypothesis
    1840 -      calc
    1841 -        T (n+1) ≤ T n + w n := hineq
    1842 -        _ ≤ S 0 + (Finset.range n).su
          m (fun k => w k) + w n :=
    1843 -          add_le_add_right ih (w n)
    1844 -        _ = S 0 + (Finset.range (n+1)
          ).sum (fun k => w k) := by
    1845 -          simpa [T, hsum_w, add_comm,
           add_left_comm, add_assoc]
    1846 -  -- Extract the desired inequality f
          or the partial sums of `v`.
    1847 -  have hv_partial :
    1848 -      ∀ N,
    1849 -        (Finset.range N).sum (fun k =
          > v k)
    1850 -          ≤ S 0 + (Finset.range N).su
          m (fun k => w k) := by
    1851 -    intro N
    1852 -    have h := hT N
    1853 -    have hnonneg := hS_nonneg N
    1854 -    -- subtract `S N` from both sides
           and use `S N ≥ 0`
    1855 -    have htemp :
    1856 -        (Finset.range N).sum (fun k =
          > v k)
    1857 -          ≤ S 0 + (Finset.range N).su
          m (fun k => w k) - S N := by
    1858 -      have := add_le_add_right h (-(S
           N))
    1859 -      simpa [T, add_comm, add_left_co
          mm, add_assoc, sub_eq_add_neg] using
          this
    1860 -    have hzero :
    1861 -        S 0 + (Finset.range N).sum (f
          un k => w k) - S N
    1862 -          ≤ S 0 + (Finset.range N).su
          m (fun k => w k) := by
    1863 -      have : -S N ≤ (0 : ℝ) := by sim
          pa using (neg_nonpos.mpr hnonneg)
    1864 -      have := add_le_add_left this (S
           0 + (Finset.range N).sum fun k => w
          k)
    1865 -      simpa [sub_eq_add_neg, add_comm
          , add_left_comm, add_assoc] using thi
          s
    1866 -    exact htemp.trans hzero
    1867 -  -- Bound the partial sums of `v` by
           the total sum of `w`.
    1868 -  have hv_bound :
    1869 -      ∀ N,
    1870 -        (Finset.range N).sum (fun k =
          > v k)
    1871 -          ≤ S 0 + ∑' k, w k := by
    1872 -    intro N
    1873 -    have hw_bound :
    1874 -        (Finset.range N).sum (fun k =
          > w k) ≤ ∑' k, w k :=
    1875 -      hw_sum.sum_le_tsum (s := Finset
          .range N)
    1876 -        (by
    1877 -          intro k _
    1878 -          exact hw_nonneg k)
    1879 -    have hconst := add_le_add_left hw
          _bound (S 0)
    1880 -    exact (hv_partial N).trans hconst
    1881 -  -- Summability of `v` follows from
          nonnegativity and the uniform bound o
          n partial sums.
    1882 -  have hvsum : Summable v := by
    1883 -    have hv_bound' :
    1884 -        ∀ N, ∑ k ∈ Finset.range N, v
          k ≤ S 0 + ∑' k, w k := by
    1885 -      intro N
    1886 -      simpa using hv_bound N
    1887 -    exact
    1888 -      summable_of_sum_range_le (f :=
          fun n => v n)
    1889 -        (c := S 0 + ∑' k, w k) hv_non
          neg hv_bound'
    1890 -  exact hvsum
    1891 -
    1892 -/-- Upgrade summability of expectatio
          ns of a nonnegative sequence of funct
          ions to
    1893 -almost-sure pointwise summability. We
           work over a finite measure space so
          that
    1894 -`lintegral` finiteness implies a.e. f
          initeness. This lemma packages the
    1895 -Tonelli/monotone-convergence step nee
          ded repeatedly in D6. -/
    1896 -lemma ae_summable_of_summable_integra
          l_nonneg
    1897 -    (μ : Measure Ω) [IsFiniteMeasure
          μ]
    1898 -    {f : ℕ → Ω → ℝ}
    1899 -    (hf_meas : ∀ n, AEMeasurable (f n
          ) μ)
    1900 -    (hf_nonneg : ∀ n ω, 0 ≤ f n ω)
    1901 -    (hf_int : ∀ n, Integrable (f n) μ
          )
    1902 -    (h_sum : Summable fun n => ∫ ω, f
           n ω ∂ μ) :
    1903 -    ∀ᵐ ω ∂ μ, Summable fun n => f n ω
           := by
    1904 -  classical
    1905 -  -- Each `lintegral` matches the rea
          l expectation because `f n ≥ 0`.
    1906 -  have h_term :
    1907 -      ∀ n,
    1908 -        ∫⁻ ω, ENNReal.ofReal (f n ω)
          ∂ μ =
    1909 -          ENNReal.ofReal (∫ ω, f n ω
          ∂ μ) := by
    1910 -    intro n
    1911 -    have hnn : 0 ≤ᵐ[μ] fun ω => f n ω
           :=
    1912 -      Filter.Eventually.of_forall (hf
          _nonneg n)
    1913 -    simpa using
    1914 -      (MeasureTheory.ofReal_integral_
          eq_lintegral_ofReal
    1915 -        (μ := μ) (f := f n)
    1916 -        (hfi := hf_int n) (f_nn := hn
          n)).symm
    1917 -  -- Tonelli: integrate the series te
          rm-wise in `ℝ≥0∞`.
    1918 -  have h_meas :
    1919 -      ∀ n, AEMeasurable (fun ω => ENN
          Real.ofReal (f n ω)) μ := by
    1920 -    intro n
    1921 -    exact
    1922 -      (ENNReal.measurable_ofReal.comp
          _aemeasurable (hf_meas n))
    1923 -  have h_lintegral :
    1924 -      ∫⁻ ω, (∑' n, ENNReal.ofReal (f
          n ω)) ∂ μ
    1925 -        = ∑' n, ENNReal.ofReal (∫ ω,
          f n ω ∂ μ) := by
    1926 -    have :=
    1927 -      MeasureTheory.lintegral_tsum (μ
           := μ)
    1928 -        (f := fun n ω => ENNReal.ofRe
          al (f n ω))
    1929 -        (hf := h_meas)
    1930 -    simpa [h_term] using this
    1931 -  -- The RHS is finite thanks to the
          assumed real summability.
    1932 -  have h_nonneg_int :
    1933 -      ∀ n, 0 ≤ ∫ ω, f n ω ∂ μ := fun
          n =>
    1934 -        integral_nonneg (by intro ω;
          exact hf_nonneg n ω)
    1935 -  have h_sum_lt_top :
    1936 -      (∑' n, ENNReal.ofReal (∫ ω, f n
           ω ∂ μ)) < (⊤ : ℝ≥0∞) := by
    1937 -    have hval :
    1938 -        ∑' n, ENNReal.ofReal (∫ ω, f
          n ω ∂ μ)
    1939 -          = ENNReal.ofReal (∑' n, ∫ ω
          , f n ω ∂ μ) := by
    1940 -      simpa using
    1941 -        (ENNReal.ofReal_tsum_of_nonne
          g h_nonneg_int h_sum).symm
    1942 -    simpa [hval] using
    1943 -      ENNReal.ofReal_lt_top (∑' n, ∫
          ω, f n ω ∂ μ)
    1944 -  -- Hence the pointwise series has f
          inite `lintegral`, so it is finite a.
          e.
    1945 -  have h_ae_fin :
    1946 -      ∀ᵐ ω ∂ μ,
    1947 -        (∑' n, ENNReal.ofReal (f n ω)
          ) < ∞ := by
    1948 -    have hneq :
    1949 -        ∫⁻ ω, (∑' n, ENNReal.ofReal (
          f n ω)) ∂ μ ≠ ∞ := by
    1950 -      exact ne_of_lt <| by simpa [h_l
          integral] using h_sum_lt_top
    1951 -    have hmeas_sum :
    1952 -        AEMeasurable (fun ω => ∑' n,
          ENNReal.ofReal (f n ω)) μ :=
    1953 -      AEMeasurable.ennreal_tsum (fun
          n => h_meas n)
    1954 -    exact ae_lt_top' hmeas_sum hneq
    1955 -  -- Convert the `ℝ≥0∞` finiteness in
          to real-valued summability.
    1956 -  refine h_ae_fin.mono ?_
    1957 -  intro ω hω
    1958 -  have hnot_top :
    1959 -      (∑' n, ENNReal.ofReal (f n ω))
          ≠ ∞ := ne_of_lt hω
    1960 -  have h_bound :
    1961 -      ∀ n, ∑ k ∈ Finset.range n, f k
          ω
    1962 -          ≤ (∑' m, ENNReal.ofReal (f
          m ω)).toReal := by
    1963 -    intro n
    1964 -    classical
    1965 -    have hpartial :
    1966 -        ∑ m ∈ Finset.range n, ENNReal
          .ofReal (f m ω)
    1967 -          ≤ ∑' m, ENNReal.ofReal (f m
           ω) := by
    1968 -      simpa using
    1969 -        (ENNReal.sum_le_tsum
    1970 -          (f := fun m => ENNReal.ofRe
          al (f m ω))
    1971 -          (s := Finset.range n))
    1972 -    have h_ofReal :
    1973 -        ENNReal.ofReal (∑ k ∈ Finset.
          range n, f k ω)
    1974 -          = ∑ m ∈ Finset.range n, ENN
          Real.ofReal (f m ω) := by
    1975 -      induction n with
    1976 -      | zero =>
    1977 -          simp
    1978 -      | succ n ih =>
    1979 -          have hpos : 0 ≤ f n ω := hf
          _nonneg n ω
    1980 -          have hsum_nonneg :
    1981 -              0 ≤ ∑ k ∈ Finset.range
          n, f k ω :=
    1982 -            Finset.sum_nonneg (fun k
          hk => hf_nonneg k ω)
    1983 -          have hpartial_n :
    1984 -              ∑ m ∈ Finset.range n, E
          NNReal.ofReal (f m ω)
    1985 -                ≤ ∑' m, ENNReal.ofRea
          l (f m ω) := by
    1986 -            simpa using
    1987 -              (ENNReal.sum_le_tsum
    1988 -                (f := fun m => ENNRea
          l.ofReal (f m ω))
    1989 -                (s := Finset.range n)
          )
    1990 -          have hcalc :
    1991 -              ENNReal.ofReal (∑ k ∈ F
          inset.range (n + 1), f k ω)
    1992 -                = ENNReal.ofReal (f n
           ω) + ∑ m ∈ Finset.range n, ENNReal.o
          fReal (f m ω) := by
    1993 -            calc
    1994 -            ENNReal.ofReal (∑ k ∈ Fin
          set.range (n + 1), f k ω)
    1995 -                = ENNReal.ofReal (f n
           ω + ∑ k ∈ Finset.range n, f k ω) :=
          by
    1996 -                    simp [Finset.rang
          e_succ, hpos, add_comm, add_left_comm
          , add_assoc]
    1997 -            _ = ENNReal.ofReal (f n ω
          ) + ENNReal.ofReal (∑ k ∈ Finset.rang
          e n, f k ω) := by
    1998 -                    simpa [hsum_nonne
          g, hpos, add_comm, add_left_comm, add
          _assoc]
    1999 -                      using ENNReal.o
          fReal_add hpos hsum_nonneg
    2000 -            _ = ENNReal.ofReal (f n ω
          ) + ∑ m ∈ Finset.range n, ENNReal.ofR
          eal (f m ω) := by
    2001 -                    simpa [ih hpartia
          l_n]
    2002 -          have hsum_exp :
    2003 -              ∑ m ∈ Finset.range (n +
           1), ENNReal.ofReal (f m ω)
    2004 -                = ENNReal.ofReal (f n
           ω) + ∑ m ∈ Finset.range n, ENNReal.o
          fReal (f m ω) := by
    2005 -            simp [Finset.range_succ,
          hpos, add_comm, add_left_comm, add_as
          soc]
    2006 -          exact hcalc.trans hsum_exp.
          symm
    2007 -    have hpartial' :
    2008 -        ENNReal.ofReal (∑ k ∈ Finset.
          range n, f k ω)
    2009 -          ≤ ∑' m, ENNReal.ofReal (f m
           ω) := by
    2010 -      simpa [h_ofReal] using hpartial
    2011 -    exact
    2012 -      (ENNReal.ofReal_le_iff_le_toRea
          l hnot_top).1 hpartial'
    2013 -  have hpos :
    2014 -      ∀ n, 0 ≤ f n ω := fun n => hf_n
          onneg n ω
    2015 -  have hsum :=
    2016 -    summable_of_sum_range_le hpos h_b
          ound
    2017 -  simpa using hsum
    2018 -
    2019 -lemma d6_weighted_gap_ae_summable
    2020 -  (H : D6ProbAssumptions (μ := μ) (ℱ
          := ℱ) (D := D)) :
    2021 -  ∀ᵐ ω ∂ μ, Summable fun n => D.b n *
           d6_phi D n ω := by
    2022 -  classical
    2023 -  -- Summability of `∫ bₙ φₙ` follows
           from the RS inequality.
    2024 -  have h_series :
    2025 -      Summable fun n => D.b n * ∫ ω,
          d6_phi D n ω ∂ μ := by
    2026 -    have hvsum := d6_scalar_RS_summab
          le (μ := μ) (ℱ := ℱ) (D := D) H
    2027 -    have hscaled :
    2028 -        Summable fun n =>
    2029 -          (2 * D.ε0) * (D.b n * ∫ ω,
          d6_phi D n ω ∂ μ) := by
    2030 -      convert hvsum using 1 with n
    2031 -      simp [d6_phi, mul_comm, mul_lef
          t_comm, mul_assoc]
    2032 -    have hcoeff : (2 * D.ε0) ≠ (0 : ℝ
          ) := by
    2033 -      apply mul_ne_zero (by norm_num)
    2034 -      exact ne_of_gt H.ε0_pos
    2035 -    exact
    2036 -      (summable_mul_left_iff
    2037 -          (a := 2 * D.ε0)
    2038 -          (f := fun n => D.b n * ∫ ω,
           d6_phi D n ω ∂ μ) hcoeff).1 hscaled
    2039 -  -- Package the sequence `f n := bₙ
          · φₙ` to apply the general lemma.
    2040 -  have hf_meas :
    2041 -      ∀ n, AEMeasurable (fun ω => D.b
           n * d6_phi D n ω) μ := by
    2042 -    intro n
    2043 -    have hconst : AEMeasurable (fun _
           : Ω => D.b n) μ := aemeasurable_cons
          t
    2044 -    have hphi :
    2045 -        AEMeasurable (fun ω => d6_phi
           D n ω) μ :=
    2046 -      ((d6_phi_aestronglyMeasurable (
          μ := μ) (ℱ := ℱ) (D := D) H n).mono
    2047 -        (ℱ.le n)).aemeasurable
    2048 -    simpa [mul_comm, mul_left_comm, m
          ul_assoc] using hconst.mul hphi
    2049 -  have hf_nonneg :
    2050 -      ∀ n ω, 0 ≤ D.b n * d6_phi D n ω
           := by
    2051 -    intro n ω
    2052 -    exact mul_nonneg (H.steps_nonneg
          n)
    2053 -      (d6_phi_nonneg (μ := μ) (ℱ := ℱ
          ) (D := D) H n ω)
    2054 -  have hf_int :
    2055 -      ∀ n, Integrable (fun ω => D.b n
           * d6_phi D n ω) μ := by
    2056 -    intro n
    2057 -    have hsmul :=
    2058 -      (d6_phi_integrable (μ := μ) (ℱ
          := ℱ) (D := D) H n).smul (D.b n)
    2059 -    have hfun :
    2060 -        (fun ω => D.b n * d6_phi D n
          ω)
    2061 -          = fun ω => D.b n • d6_phi D
           n ω := by
    2062 -      funext ω
    2063 -      simp [smul_eq_mul, mul_comm, mu
          l_left_comm, mul_assoc]
    2064 -    simpa [hfun] using hsmul
    2065 -  have h_integral :
    2066 -      ∀ n, ∫ ω, D.b n * d6_phi D n ω
          ∂ μ
    2067 -          = D.b n * ∫ ω, d6_phi D n ω
           ∂ μ := by
    2068 -    intro n
    2069 -    simpa [mul_comm, mul_left_comm, m
          ul_assoc] using
    2070 -      MeasureTheory.integral_mul_cons
          t
    2071 -        (μ := μ)
    2072 -        (f := fun ω => d6_phi D n ω)
    2073 -        (r := D.b n)
    2074 -  have h_series' :
    2075 -      Summable fun n => ∫ ω, D.b n *
          d6_phi D n ω ∂ μ := by
    2076 -    refine h_series.congr ?_
    2077 -    intro n
    2078 -    simpa [h_integral n]
    2079 -  -- Apply the monotone-convergence u
          pgrade lemma.
    2080 -  have h_ae :=
    2081 -    ae_summable_of_summable_integral_
          nonneg (μ := μ)
    2082 -      (f := fun n ω => D.b n * d6_phi
           D n ω)
    2083 -      hf_meas hf_nonneg hf_int h_seri
          es'
    2084 -  -- Reorder the product to match the
           target statement.
    2085 -  refine h_ae.mono ?_
    2086 -  intro ω hω
    2087 -  simpa [mul_comm] using hω
    2088 -
    2089 -/-- If `(bₙ)` is nonnegative with div
          ergent partial sums and `(tₙ)` is non
          negative with
    2090 -`∑ bₙ tₙ < ∞`, then `tₙ` cannot stay
          eventually bounded below by a positiv
          e constant. -/
    2091 -lemma not_eventually_ge_of_weighted_s
          ummable
    2092 -    {b t : ℕ → ℝ} {ε : ℝ}
    2093 -    (hb_nonneg : ∀ n, 0 ≤ b n)
    2094 -    (hb_div : Tendsto (fun N => (Fins
          et.range N).sum fun k => b k) atTop a
          tTop)
    2095 -    (ht_nonneg : ∀ n, 0 ≤ t n)
    2096 -    (hs : Summable fun n => b n * t n
          )
    2097 -    (hε : 0 < ε) :
    2098 -    ¬ (∀ᶠ n in Filter.atTop, ε ≤ t n)
           := by
    2099 -  classical
    2100 -  set S : ℕ → ℝ := fun N => (Finset.r
          ange N).sum fun k => b k * t k
    2101 -  set B : ℕ → ℝ := fun N => (Finset.r
          ange N).sum fun k => b k
    2102 -  have hb_prod_nonneg : ∀ n, 0 ≤ b n
          * t n := by
    2103 -    intro n
    2104 -    exact mul_nonneg (hb_nonneg n) (h
          t_nonneg n)
    2105 -  have hS_nonneg : ∀ N, 0 ≤ S N := by
    2106 -    intro N
    2107 -    have :=
    2108 -      Finset.sum_nonneg (by intro k _
          ; exact hb_prod_nonneg k)
    2109 -    simpa [S]
    2110 -  obtain ⟨s, hs_has⟩ := hs.hasSum
    2111 -  have hS_tendsto : Tendsto S atTop (
          𝓝 s) := hs_has.tendsto_sum_nat
    2112 -  by_contra hE
    2113 -  obtain ⟨N0, hN0⟩ := Filter.eventual
          ly_atTop.1 hE
    2114 -  have h_tail :
    2115 -      ∀ m : ℕ, ε * (B (N0 + m) - B N0
          ) ≤ S (N0 + m) := by
    2116 -    refine Nat.rec ?base ?step
    2117 -    · have hzero : B (N0 + 0) - B N0
          = 0 := by simp [B]
    2118 -      simpa [hzero, S, B, mul_zero] u
          sing hS_nonneg N0
    2119 -    · intro m hm
    2120 -      have ht_ge : ε ≤ t (N0 + m) :=
          hN0 _ (Nat.le_add_left _ _)
    2121 -      have hb_ge : 0 ≤ b (N0 + m) :=
          hb_nonneg _
    2122 -      have hSsucc :
    2123 -          S (N0 + (m + 1)) = S (N0 +
          m) + b (N0 + m) * t (N0 + m) := by
    2124 -        simp [S, Nat.add_comm, Nat.ad
          d_left_comm, Nat.add_assoc,
    2125 -              Finset.sum_range_succ,
          add_comm, add_left_comm, add_assoc]
    2126 -      have hBsucc :
    2127 -          B (N0 + (m + 1)) = B (N0 +
          m) + b (N0 + m) := by
    2128 -        simp [B, Nat.add_comm, Nat.ad
          d_left_comm, Nat.add_assoc,
    2129 -              Finset.sum_range_succ,
          add_comm, add_left_comm, add_assoc]
    2130 -      have hmul :
    2131 -          ε * b (N0 + m) ≤ b (N0 + m)
           * t (N0 + m) := by
    2132 -        simpa [mul_comm, mul_left_com
          m, mul_assoc] using
    2133 -          mul_le_mul_of_nonneg_right
          ht_ge hb_ge
    2134 -      have hsum :
    2135 -          ε * (B (N0 + m) - B N0) + ε
           * b (N0 + m)
    2136 -            ≤ S (N0 + m) + b (N0 + m)
           * t (N0 + m) :=
    2137 -        add_le_add hm hmul
    2138 -      have hgoal :
    2139 -          ε * (B (N0 + (m + 1)) - B N
          0)
    2140 -            = ε * (B (N0 + m) - B N0)
           + ε * b (N0 + m) := by
    2141 -        simp [hBsucc, add_comm, add_l
          eft_comm, add_assoc,
    2142 -              sub_eq_add_neg, mul_add
          , add_comm, add_left_comm, add_assoc]
    2143 -      simpa [hSsucc, hgoal, add_comm,
           add_left_comm, add_assoc] using hsum
    2144 -  have hS_bound :
    2145 -      ∀ᶠ n in Filter.atTop, |S n - s|
           < 1 :=
    2146 -    hS_tendsto (Metric.ball_mem_nhds
          _ (by norm_num))
    2147 -  obtain ⟨N1, hN1⟩ := Filter.eventual
          ly_atTop.1 hS_bound
    2148 -  have hS_le :
    2149 -      ∀ n ≥ N1, S n ≤ s + 1 := by
    2150 -    intro n hn
    2151 -    have habs := abs_lt.1 (hN1 n hn)
    2152 -    have : S n < s + 1 := by
    2153 -      have := habs.2
    2154 -      exact (sub_lt_iff_lt_add').1 th
          is
    2155 -    exact this.le
    2156 -  have hB_event :
    2157 -      ∀ᶠ n in Filter.atTop,
    2158 -        (s + 2) / ε + B N0 + 1 ≤ B n
          :=
    2159 -    (Filter.tendsto_atTop.1 hb_div) _
    2160 -  obtain ⟨N2, hN2⟩ := Filter.eventual
          ly_atTop.1 hB_event
    2161 -  let n := max N2 (max N1 N0)
    2162 -  have hn_ge_N0 : N0 ≤ n := by
    2163 -    have : N0 ≤ max N1 N0 := le_max_r
          ight _ _
    2164 -    exact le_trans this (le_max_right
           _ _)
    2165 -  have hn_ge_N1 : N1 ≤ n := by
    2166 -    have : N1 ≤ max N1 N0 := le_max_l
          eft _ _
    2167 -    exact le_trans this (le_max_right
           _ _)
    2168 -  have hn_ge_N2 : N2 ≤ n := le_max_le
          ft _ _
    2169 -  have hB_large :
    2170 -      (s + 2) / ε + B N0 + 1 ≤ B n :=
           hN2 n hn_ge_N2
    2171 -  have hdiff :
    2172 -      (s + 2) / ε + 1 ≤ B n - B N0 :=
           by
    2173 -    simpa [sub_eq_add_neg, add_comm,
          add_left_comm, add_assoc] using
    2174 -      sub_le_sub_right hB_large (B N0
          )
    2175 -  have hmult :
    2176 -      s + 2 + ε ≤ ε * (B n - B N0) :=
           by
    2177 -    have := mul_le_mul_of_nonneg_left
           hdiff hε.le
    2178 -    simpa [add_comm, add_left_comm, a
          dd_assoc, mul_add, mul_comm,
    2179 -      mul_left_comm, mul_assoc, hε.ne
          '] using this
    2180 -  have hm_index :
    2181 -      ε * (B n - B N0) ≤ S n := by
    2182 -    have : S n = S (N0 + (n - N0)) :=
           by
    2183 -      have := Nat.add_sub_of_le hn_ge
          _N0
    2184 -      simpa [S, Nat.add_comm, Nat.add
          _left_comm, Nat.add_assoc, this]
    2185 -    have htail_eval :=
    2186 -      h_tail (n - N0)
    2187 -    have hB_eq :
    2188 -        B (N0 + (n - N0)) = B n := by
    2189 -      have := Nat.add_sub_of_le hn_ge
          _N0
    2190 -      simpa [B, Nat.add_comm, Nat.add
          _left_comm, Nat.add_assoc, this]
    2191 -    have hS_eq := this
    2192 -    have hB_diff :
    2193 -        B (N0 + (n - N0)) - B N0 = B
          n - B N0 := by
    2194 -      simp [hB_eq]
    2195 -    simpa [hB_diff, hS_eq] using htai
          l_eval
    2196 -  have hcontr :
    2197 -      s + 2 + ε ≤ S n := le_trans hmu
          lt hm_index
    2198 -  have hS_upper : S n ≤ s + 1 := hS_l
          e n hn_ge_N1
    2199 -  have : s + 2 + ε ≤ s + 1 := le_tran
          s hcontr hS_upper
    2200 -  have : ε ≤ -1 := by linarith
    2201 -  exact (not_lt_of_ge this hε)
    2202 -end D6_RS_ExpectationProof
    2203 --- end of D6 RS expectation-level pro
          of
    2204 -
    2205 -/-! ## D6 — Interior positivity (brid
          ge lemma)
    2206 -
    2207 -This is the 1‑D “interior hit” statem
          ent used to pass from a positive
    2208 -drift window near 0 to eventual posit
          ivity of the clamped recursion. We
    2209 -keep it as a Prop‑level target here;
          downstream files can instantiate it
    2210 -with Robbins–Siegmund once the probab
          ility layer is finalized. -/
    2211 -
    2212 -/-- Hypotheses for the 1‑D interior h
          it under stochasticity. -/
    2213 -structure OneDInteriorHitHypotheses w
          here
    2214 -  βmax        : ℝ
    2215 -  steps       : Prop   -- ∑ b_n^2 < ∞
           and b_n → 0 (Robbins–Monro)
    2216 -  noise       : Prop   -- MDS noise w
          ith bounded conditional variance
    2217 -  bias        : Prop   -- ∑ b_n E|δ_{
          n+1}| < ∞ (or a.s.)
    2218 -  pos_window  : Prop   -- ḡ(β) ≥ ε o
          n [0, K]
    2219 -  alignment   : Prop   -- β_{n+1} = c
          lamp(β_n + b_n (ḡ(β_n)+ξ_{n+1}+δ_{n+
          1}))
    2220 -  conclusion  : Prop   -- ∃ K>0, τ_K
          < ∞ a.s. and β_n ≥ K for n ≥ τ_K
    2221 -
    2222 -/-- D6: interior positivity (stochast
          ic window → a.s. hit). -/
    2223 -def projected_SA_interior_hit (H : On
          eDInteriorHitHypotheses) : Prop :=
    2224 -  H.conclusion
    2225 -
    2226 -/-!
    2227 -Auxiliary D6/D4 wrappers with explici
          t names. These provide stable entry p
          oints
    2228 -for the proof layer while we keep the
           high‑level hypothesis packaging mode
          l‑agnostic.
    2229 -The implementations here are placehol
          ders that return the bundled conclusi
          ons;
    2230 -they should be replaced by the full p
          roofs using the RS and MDS machinery.
    2231 -
    2232 -Why add these now?
    2233 -- Downstream modules and docs referen
          ce these names. Providing them as wra
          ppers
    2234 -  lets us wire call sites without com
          mitting to a specific proof shape her
          e.
    2235 -- RS/MDS files already contain the he
          avy lifting (supermartingale normaliz
          ation
    2236 -  and a.e. convergence); the TTSA lay
          er will consume them in the eventual
          proof.
    2237 --/
    2238 -
    2239 -/-- D6 (named): Interior hit for the
          1‑D clamped recursion via RS.
    2240 -This wrapper exposes the intended the
          orem name; it currently reduces to th
          e
    2241 -bundled `projected_SA_interior_hit H`
           and will later be replaced by the fu
          ll
    2242 -proof via Robbins–Siegmund and clamp
          nonexpansiveness. -/
    2243 -theorem ttsa_interior_hit_via_RS
    2244 -  (H : OneDInteriorHitHypotheses) : p
          rojected_SA_interior_hit H = projecte
          d_SA_interior_hit H :=
    2245 -  rfl
    2246 -
    2247 -/-- D4 (named): Projected 1‑D SA conv
          ergence under Option 1 hypotheses.
    2248 -This wrapper exposes the intended the
          orem name; it currently reduces to th
          e
    2249 -bundled `projected_SA_converges_1D H`
           and will later be replaced by the fu
          ll
    2250 -proof combining RS, MDS weighted sums
          , and a Lyapunov drift. -/
    2251 -theorem projected_SA_converges_1D_ful
          l
    2252 -  (H : OneDProjectedSAHypotheses) : p
          rojected_SA_converges_1D H = projecte
          d_SA_converges_1D H :=
    2253 -  rfl
    2254 -
    2255 -/-!
    2256 -## D4 RS — Lyapunov Wiring (Prop skel
          etons)
    2257 -
    2258 -Analogous to D6, we collect Lyapunov-
          based RS inequalities and the converg
          ence
    2259 -goal for Option 1 in a model-agnostic
           way. Proofs live in the probability
          layer.
    2260 --/
    2261 -
    2262 -section D4_RS_Expectations
    2263 -
    2264 -variable {Ω : Type*} {m0 : Measurable
          Space Ω}
    2265 -
    2266 -/-- Minimal Lyapunov data for D4: rec
          ursion, drift `h`, and a Lyapunov `V`
          . -/
    2267 -structure D4RSData where
    2268 -  βmax  : ℝ
    2269 -  b     : ℕ → ℝ
    2270 -  h     : ℝ → ℝ
    2271 -  ξ     : ℕ → Ω → ℝ
    2272 -  δ     : ℕ → Ω → ℝ
    2273 -  beta  : ℕ → Ω → ℝ
    2274 -  betaStar : ℝ
    2275 -  V     : ℝ → ℝ
    2276 -  /-- Clamped recursion (pointwise, m
          odel‑agnostic). -/
    2277 -  step : ∀ n ω,
    2278 -    beta (n+1) ω = max 0 (min βmax (b
          eta n ω - b n * (h (beta n ω) - (ξ (n
          +1) ω + δ (n+1) ω))))
    2279 -
    2280 -variable (μ : MeasureTheory.Measure Ω
          ) (ℱ : MeasureTheory.Filtration ℕ m0)
    2281 -
    2282 -variable (D4 : D4RSData (Ω := Ω))
    2283 -
    2284 -/-- Lyapunov process. -/
    2285 -def D4RS_Y : ℕ → Ω → ℝ := fun n ω =>
          D4.V (D4.beta n ω)
    2286 -
    2287 -/-- D4 RS conditional expectation ine
          quality (Prop placeholder). -/
    2288 -def D4_RS_condExp_ineq (C : ℝ) (d : ℕ
           → ℝ) : Prop := True
    2289 -
    2290 -/-- D4 deterministic summability budg
          et (Prop): `∑(C b_n^2 + b_n d_n) < ∞`
          . -/
    2291 -def D4_RS_w_summable (C : ℝ) (d : ℕ →
           ℝ) : Prop :=
    2292 -  Summable (fun n => C * (D4.b n) ^ 2
           + (D4.b n) * d n)
    2293 -
    2294 -/-- D4 convergence goal (Prop): almos
          t sure convergence to β⋆. -/
    2295 -def D4_RS_converges_goal : Prop :=
    2296 -  ∀ᵐ ω ∂ μ, Filter.Tendsto (fun n =>
          D4.beta n ω) Filter.atTop (nhds D4.be
          taStar)
    2297 -
    2298 -/-- D4 RS to convergence wrapper (Pro
          p). -/
    2299 -def D4_RS_converges_from_RS (C : ℝ) (
          d : ℕ → ℝ) : Prop :=
    2300 -  (D4_RS_condExp_ineq C d ∧ D4_RS_w_s
          ummable (D4 := D4) C d)
    2301 -  → D4_RS_converges_goal (μ := μ) (D4
           := D4)
    2302 -
    2303 -end D4_RS_Expectations
    2304 -
    2305 -/-! ## Option 2A — Full TTSA with uni
          que fast equilibrium (vector) -/
    2306 -
    2307 -/-- Hypothesis bundle for TTSA with a
           unique globally stable fast equilibr
          ium.
    2308 -Spaces and projections are abstracted
          ; Lipschitz, separation, and noise
    2309 -conditions are summarized as `Prop` f
          ields to be instantiated later. -/
    2310 -structure TTSAUniqueEqHypotheses wher
          e
    2311 -  spaces        : Prop   -- Y,B compa
          ct convex sets (abstracted)
    2312 -  projections   : Prop   -- non-expan
          sive projections (Euclidean)
    2313 -  schedules     : Prop   -- ∑ a_n = ∞
          , ∑ a_n^2 < ∞; ∑ b_n = ∞, ∑ b_n^2 < ∞
          ; b_n/a_n → 0
    2314 -  drifts        : Prop   -- H,G Lipsc
          hitz
    2315 -  fast_unique   : Prop   -- ∀β, uniqu
          e globally stable y*(β), continuous i
          n β
    2316 -  slow_avg      : Prop   -- define Ḡ
          (β) = G(y*(β), β), continuous
    2317 -  slow_proj_ode : Prop   -- projected
           ODE well-posed (tangent-cone form)
    2318 -  noise         : Prop   -- two MDS w
          ith bounded conditional second moment
          s
    2319 -  stable_root   : Prop   -- unique lo
          cally stable equilibrium β⋆ in int(B)
    2320 -  conclusion    : Prop   -- tracking
          + APT + convergence
    2321 -
    2322 -/-- TTSA meta-theorem (Option 2A, pro
          jected): unique fast equilibrium. -/
    2323 -def TTSA_projected_unique_equilibrium
           (H : TTSAUniqueEqHypotheses) : Prop
          :=
    2324 -  -- Conclusion placeholder: tracking
           + APT + convergence (to be proved).
    2325 -  H.conclusion
    2326 -
    2327 -/-! ## Option 2B — Full TTSA with erg
          odic fast dynamics (vector) -/
    2328 -
    2329 -/-- Hypothesis bundle for TTSA with e
          rgodic fast dynamics and averaging. -
          /
    2330 -structure TTSAErgodicHypotheses where
    2331 -  spaces        : Prop   -- Y,B compa
          ct convex sets (abstracted)
    2332 -  projections   : Prop   -- non-expan
          sive projections (Euclidean)
    2333 -  schedules     : Prop   -- ∑ a_n = ∞
          , ∑ a_n^2 < ∞; ∑ b_n = ∞, ∑ b_n^2 < ∞
          ; b_n/a_n → 0
    2334 -  drifts        : Prop   -- H,G Lipsc
          hitz; fast Markov dynamics well-defin
          ed
    2335 -  ergodic_fast  : Prop   -- ∀β, invar
          iant μ_β; mixing adequate for averagi
          ng
    2336 -  slow_avg      : Prop   -- Ḡ(β) = ∫
           G(y,β) dμ_β(y), continuous
    2337 -  slow_proj_ode : Prop   -- projected
           ODE well-posed (tangent-cone form)
    2338 -  noise         : Prop   -- two MDS w
          ith bounded conditional second moment
          s
    2339 -  stable_root   : Prop   -- unique lo
          cally stable equilibrium β⋆ in int(B)
    2340 -  conclusion    : Prop   -- averaging
           + APT + convergence
    2341 -
    2342 -/-- TTSA meta-theorem (Option 2B, pro
          jected): ergodic fast dynamics. -/
    2343 -def TTSA_projected_ergodic (H : TTSAE
          rgodicHypotheses) : Prop :=
    2344 -  -- Conclusion placeholder: averagin
          g + APT + convergence (to be proved).
    2345 -  H.conclusion
    2346 -
    2347 -end
    2348 -end NOC.TTSA
    2349 -
    2350 -/-! ## D6 — Wrappers tying data to su
          mmability (after proofs) -/
    2351 -
    2352 -namespace NOC.TTSA
    2353 -
    2354 -open MeasureTheory
    2355 -
    2356 -/- Convenience wrapper: from probabil
          istic assumptions on the clamped recu
          rsion,
    2357 -obtain the scalar RS summability `∑ (
          2 ε0) bₙ ∫ (K − βₙ)_+ < ∞` directly.
    2358 -
    2359 -Note: this is an alias of `d6_scalar_
          RS_summable`; keep here for TTSA-faci
          ng API.
    2360 -- Implementation routed to `d6_scalar
          _RS_summable` above. -/
    2361 -/-
    2362 -theorem d6_scalar_rs_from_data_summab
          le
    2363 -  {Ω : Type*} {m0 : MeasurableSpace Ω
          }
    2364 -  (μ : MeasureTheory.Measure Ω) (ℱ :
          MeasureTheory.Filtration ℕ m0)
    2365 -  [MeasureTheory.IsProbabilityMeasure
           μ]
    2366 -  (D : D6RSData (Ω := Ω))
    2367 -  (H : D6ProbAssumptions) :
    2368 -  Summable (fun n => (2 * D.ε0) * D.b
           n * (∫ ω, max 0 (D.K - D.β n ω) ∂ μ)
          ) :=
    2369 -  by
    2370 -  exact NOC.TTSA.d6_scalar_RS_summabl
          e (μ := μ) (ℱ := ℱ) (D := D) H
    2371 --/
    2372 -
    2373 -end NOC.TTSA
    2374 -
    2375 --- (RS wiring aliases are provided di
          rectly in `NOC.Prob.RobbinsSiegmund`.
          )
    2376 -
    2377 -/-!
    2378 -## Usage note: wiring RS convergence
          in TTSA (doc stub)
    2379 -
    2380 -Example (sketch): To use the RS utili
          ties for a β-recursion, define
    2381 -
    2382 -  Y n ω := nonnegative potential at t
          ime n (measurable, integrable)
    2383 -  u n, v n, w n ≥ 0 with the RS step
    2384 -       μ[ Y (n+1) | ℱ n ] ≤ (1 + u n)
           * Y n − v n + w n
    2385 -  and summable ∑ w n / RSWeight u (n+
          1).
    2386 -
    2387 -Then call
    2388 -
    2389 -  NOC.Prob.RSDrifted_ae_converges_of_
          RS
    2390 -
    2391 -with the adaptedness/integrability/no
          nnegativity proofs and the RS inequal
          ity
    2392 -to obtain a.e. convergence of the dri
          fted normalized process
    2393 -
    2394 -  G n ω = (RSWeight u n)⁻¹ * Y n ω +
          ∑_{k<n} v k / RSWeight u (k+1)
    2395 -           − ∑_{k<n} w k / RSWeight u
           (k+1).
    2396 -
    2397 -This plugs into TTSA by instantiating
           Y,u,v,w from the β-layer residual yo
          u
    2398 -track, after you verify the RS hypoth
          eses and the w/W summability budget.
    2399 --/
