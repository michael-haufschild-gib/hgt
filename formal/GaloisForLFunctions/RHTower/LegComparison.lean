/-
# LegComparison — a genuine attack on the OPEN (L1) inequality (task #138/#142; docs 28/30)

Doc 28 §5b states (L1) — `dW/dθ < 0` for `θ < 1/2` on the constant-δ lattice — only "[PROVED
HERE, outline]", i.e. NOT rigorously. This module makes the load-bearing structural step exact
and supplies the analytic brick the outline was missing.

Register: this is research, not transcription. The *reduction* (`l1_reduction`,
`l1_neg_of_head_gt_tail`) and the *cubic upper bound* (`rphi_le_cubic`) are proved here; the
constant head-vs-tail estimate that closes (L1) in the small-δ regime is assembled from them
(see the module docstring reasoning). The full (L1) across all `(M,N,δ,θ<1/2)` — in particular
the near-crossing regime `θ ↑ 1/2` where the head gain vanishes — remains open.

Writing `φ = rphi = csch²·coth = cosh/sinh³` (the Calogero kernel) and, on the constant-δ
lattice, `dW/dθ = (δ/4)·D` with
`D = Σ_{k<N} φ((1−θ+k)δ/2) − Σ_{k<M} φ((θ+k)δ/2)`, `a_k=(θ+k)δ/2 < b_k=(1−θ+k)δ/2`:

* `self_le_sinh` — `s ≤ sinh s` for `s ≥ 0` (needed for the cubic bound; `sinh−id` monotone).
* `rphi_le_cubic` — **the missing brick**: `φ(s) ≤ cosh 1 / s³` for `0 < s ≤ 1` (`cosh s ≤ cosh 1`,
  `sinh s ≥ s`). `CothInfra` had only the *lower* bound `rphi_ge_cubic`.
* `l1_reduction` — **the exact structural step**: `D = tail − headGain` where
  `headGain = Σ_{k<M}[φ(a_k)−φ(b_k)]`, `tail = Σ_{M≤k<N} φ(b_k)`. No approximation — the doc's
  "termwise domination plus surplus" made precise.
* `l1_neg_of_head_gt_tail` — hence **`headGain > tail ⟹ D < 0`** (`dW/dθ < 0`): the crossing
  criterion reduced to one head-vs-tail inequality.

Closing (L1) in the small-δ regime (reasoning, from these bricks): `headGain ≥ φ(θδ/2) −
φ((1−θ)δ/2) ≥ 2/(θδ)³ − 128/δ³` (via `rphi_ge_cubic` on the head, `rphi_le_cubic` on the
subtrahend with `1−θ ≥ ½`); for `θ ≤ 1/8` this is `≥ 896/δ³`, while the tail is `≤ 32/δ³` by the
same cubic upper bound — so head beats tail for every `M ≥ 1`, giving `dW/dθ < 0`. The `θ`-window
`(1/8, 1/2)` (head shrinks toward the crossing) is the honest open remainder.
-/
import GaloisForLFunctions.RHTower.CothInfra

noncomputable section

namespace RHTower

open Finset

/-- `s ≤ sinh s` for `s ≥ 0`: `sinh − id` has derivative `cosh − 1 ≥ 0` and vanishes at `0`. -/
theorem self_le_sinh {s : ℝ} (hs : 0 ≤ s) : s ≤ Real.sinh s := by
  have hmono : MonotoneOn (fun t => Real.sinh t - t) (Set.Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0) (by fun_prop) (by fun_prop)
    intro t ht
    rw [interior_Ici, Set.mem_Ioi] at ht
    have hd : HasDerivAt (fun t => Real.sinh t - t) (Real.cosh t - 1) t :=
      (Real.hasDerivAt_sinh t).sub (hasDerivAt_id t)
    rw [hd.deriv]
    linarith [Real.one_le_cosh t]
  have hkey := hmono (Set.self_mem_Ici) (Set.mem_Ici.mpr hs) hs
  simpa using hkey

/-- **The missing cubic upper bound** (the brick doc 28 §5b's outline needed for the tail):
`φ(s) = cosh s/sinh³ s ≤ cosh 1 / s³` for `0 < s ≤ 1`. From `cosh s ≤ cosh 1` and
`sinh s ≥ s > 0`. Together with `CothInfra.rphi_ge_cubic` this brackets the Calogero kernel
`1/(4s³) ≤ φ(s) ≤ cosh 1/s³ (< 2/s³)` on `(0,1]`. -/
theorem rphi_le_cubic {s : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1) : rphi s ≤ Real.cosh 1 / s ^ 3 := by
  have hs : 0 < Real.sinh s := sinh_pos_of_pos hs0
  have hself : s ≤ Real.sinh s := self_le_sinh hs0.le
  have hrphi : rphi s = Real.cosh s / (Real.sinh s) ^ 3 := by
    simp only [rphi, rcsch, rcoth]; field_simp
  rw [hrphi]
  have hcosh : Real.cosh s ≤ Real.cosh 1 := by
    rw [Real.cosh_le_cosh, abs_of_pos hs0, abs_of_pos (by norm_num : (0:ℝ) < 1)]; exact hs1
  have hsinh3 : s ^ 3 ≤ (Real.sinh s) ^ 3 := pow_le_pow_left₀ hs0.le hself 3
  exact div_le_div₀ (Real.cosh_pos 1).le hcosh (by positivity) hsinh3

/-- **Head-gain lower bound with explicit constants** — the estimate the outline asserted but
never bounded. The `k=0` head gain `φ(x) − φ(y)` (here `x = θδ/2`, `y = (1−θ)δ/2 > x`) is at
least `1/(4x³) − cosh 1/y³`: the cubic blow-up of `φ` at the small ahead-distance `x`. For
`θδ` small this is `≈ 2/(θδ)³`, dwarfing the far-behind tail — the mechanism of (L1). Combines
`CothInfra.rphi_ge_cubic` (head) and `rphi_le_cubic` (subtrahend). -/
theorem headGain_lower {x y : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) (hy0 : 0 < y) (hy1 : y ≤ 1) :
    1 / (4 * x ^ 3) - Real.cosh 1 / y ^ 3 ≤ rphi x - rphi y := by
  have h1 := rphi_ge_cubic hx0 hx1
  have h2 := rphi_le_cubic hy0 hy1
  linarith

/-- **The exact structural reduction of (L1)** (doc 28 §5b, made rigorous). With
`fa k = φ(a_k)`, `fb k = φ(b_k)` and `M ≤ N`, the derivative datum
`D = Σ_{k<N} fb − Σ_{k<M} fa` decomposes *exactly* as `tail − headGain`:
`Σ_{M≤k<N} fb − Σ_{k<M}(fa − fb)`. No termwise approximation. -/
theorem l1_reduction {M N : ℕ} (hMN : M ≤ N) (fa fb : ℕ → ℝ) :
    (∑ k ∈ range N, fb k) - (∑ k ∈ range M, fa k)
      = (∑ k ∈ Ico M N, fb k) - (∑ k ∈ range M, (fa k - fb k)) := by
  rw [← Finset.sum_range_add_sum_Ico fb hMN, Finset.sum_sub_distrib]
  ring

/-- **The crossing criterion** `headGain > tail ⟹ D < 0` (`dW/dθ < 0`). With `φ` decreasing on
the lattice arguments (`fb k ≤ fa k`), if the head gain `Σ_{k<M}(fa − fb)` exceeds the far
tail `Σ_{M≤k<N} fb`, the ahead sum wins: `Σ_{k<N} fb < Σ_{k<M} fa`. This is the whole content
of (L1) reduced to one inequality — the piece the doc's outline left implicit. -/
theorem l1_neg_of_head_gt_tail {M N : ℕ} (hMN : M ≤ N) (fa fb : ℕ → ℝ)
    (hhead : (∑ k ∈ Ico M N, fb k) < ∑ k ∈ range M, (fa k - fb k)) :
    (∑ k ∈ range N, fb k) < ∑ k ∈ range M, fa k := by
  have hD := l1_reduction hMN fa fb
  linarith [hD, hhead]

/-- **The far-behind tail bound** (the piece §5b never wrote as a lemma). The unpaired behind
charges `k ∈ [M, N)` contribute `Σ φ((1−θ+k)δ/2) ≤ 64 e^{−(1−θ+M)δ}/(1−e^{−δ})` once the nearest
far charge is at hyperbolic distance `≥ 1` (`(1−θ+M)δ/2 ≥ 1`). Reindex `Ico M N → range (N−M)`,
then the banked geometric-tail bound `rphi_geom_tail_le`. -/
theorem tail_geom_bound {θ δ : ℝ} {M N : ℕ} (hδ : 0 < δ)
    (ha : 1 ≤ (1 - θ + M) * (δ / 2)) :
    ∑ k ∈ Ico M N, rphi ((1 - θ + k) * (δ / 2))
      ≤ 64 * Real.exp (-2 * ((1 - θ + M) * (δ / 2))) / (1 - Real.exp (-2 * (δ / 2))) := by
  rw [Finset.sum_Ico_eq_sum_range]
  have hstep : ∀ n : ℕ, (1 - θ + (↑(M + n) : ℝ)) * (δ / 2)
      = (1 - θ + M) * (δ / 2) + (n : ℝ) * (δ / 2) := by
    intro n; push_cast; ring
  simp_rw [hstep]
  exact rphi_geom_tail_le ha (by positivity) (N - M)

/-- **(L1), CLOSED in the small-θ regime** — the complete, end-to-end theorem (no reasoning-only
step). On the constant-δ lattice with `M ≥ 1` ahead charges and `N ≥ M` behind, if `θ ≤ 1/2`,
the head/subtrahend arguments lie in the cubic window (`θδ/2 ≤ 1`, `(1−θ)δ/2 ≤ 1`), the nearest
far charge is at distance `≥ 1`, and the explicit head-beats-tail inequality `hbeat` holds, then
`Σ_{k<N} φ(b_k) < Σ_{k<M} φ(a_k)`, i.e. **`dW/dθ < 0`**. Assembles `tail_geom_bound` (tail),
`headGain_lower` (head, `k=0`), `rphi_strictAntiOn_pos` (paired `k≥1` terms `≥ 0`), and
`l1_neg_of_head_gt_tail` (the reduction). For `δ = 2, θ ≤ 1/8, M ≥ 1` the head `≥ 125` beats the
tail `≤ 1.8`, so `hbeat` holds unconditionally there — a genuine closed instance of (L1). -/
theorem dW_dtheta_neg {θ δ : ℝ} {M N : ℕ} (hMN : M ≤ N) (hM1 : 1 ≤ M)
    (hθ0 : 0 < θ) (hθhalf : θ ≤ 1 / 2) (hδ : 0 < δ)
    (hx1 : θ * δ / 2 ≤ 1) (hy1 : (1 - θ) * δ / 2 ≤ 1)
    (ha : 1 ≤ (1 - θ + M) * (δ / 2))
    (hbeat : 64 * Real.exp (-2 * ((1 - θ + M) * (δ / 2))) / (1 - Real.exp (-2 * (δ / 2)))
      < 1 / (4 * (θ * δ / 2) ^ 3) - Real.cosh 1 / ((1 - θ) * δ / 2) ^ 3) :
    (∑ k ∈ range N, rphi ((1 - θ + k) * (δ / 2)))
      < ∑ k ∈ range M, rphi ((θ + k) * (δ / 2)) := by
  set fa : ℕ → ℝ := fun k => rphi ((θ + k) * (δ / 2)) with hfa
  set fb : ℕ → ℝ := fun k => rphi ((1 - θ + k) * (δ / 2)) with hfb
  have hxpos : 0 < θ * δ / 2 := by positivity
  have hypos : 0 < (1 - θ) * δ / 2 := by
    have : (0 : ℝ) < 1 - θ := by linarith
    positivity
  -- head (k = 0) lower bound
  have hhead0 : 1 / (4 * (θ * δ / 2) ^ 3) - Real.cosh 1 / ((1 - θ) * δ / 2) ^ 3
      ≤ fa 0 - fb 0 := by
    simp only [hfa, hfb, Nat.cast_zero, add_zero]
    rw [show θ * (δ / 2) = θ * δ / 2 from by ring,
      show (1 - θ) * (δ / 2) = (1 - θ) * δ / 2 from by ring]
    exact headGain_lower hxpos hx1 hypos hy1
  -- every paired term ≥ 0
  have hnonneg : ∀ k ∈ range M, 0 ≤ fa k - fb k := by
    intro k _
    simp only [hfa, hfb]
    have h1 : (0 : ℝ) < (θ + k) * (δ / 2) := by positivity
    have h2 : (θ + k) * (δ / 2) ≤ (1 - θ + k) * (δ / 2) := by
      have hδ2 : (0 : ℝ) < δ / 2 := by positivity
      nlinarith [hθhalf, hδ2]
    have hanti := rphi_strictAntiOn_pos.antitoneOn (Set.mem_Ioi.mpr h1)
      (Set.mem_Ioi.mpr (lt_of_lt_of_le h1 h2)) h2
    linarith
  have hheadsum : fa 0 - fb 0 ≤ ∑ k ∈ range M, (fa k - fb k) :=
    Finset.single_le_sum hnonneg (Finset.mem_range.mpr (by omega))
  -- tail upper bound
  have htail : (∑ k ∈ Ico M N, fb k)
      ≤ 64 * Real.exp (-2 * ((1 - θ + M) * (δ / 2))) / (1 - Real.exp (-2 * (δ / 2))) := by
    simp only [hfb]
    exact tail_geom_bound hδ ha
  refine l1_neg_of_head_gt_tail hMN fa fb ?_
  calc (∑ k ∈ Ico M N, fb k)
      ≤ _ := htail
    _ < 1 / (4 * (θ * δ / 2) ^ 3) - Real.cosh 1 / ((1 - θ) * δ / 2) ^ 3 := hbeat
    _ ≤ fa 0 - fb 0 := hhead0
    _ ≤ ∑ k ∈ range M, (fa k - fb k) := hheadsum

/-- **(L1), an UNCONDITIONAL closed instance** at `δ = 2, θ = 1/8`. For every `M ≥ 1` ahead and
`N ≥ M` behind charges, `dW/dθ < 0` — the head gain (`≥ 125`) beats the far-behind tail (`≤ 8`),
with the head-vs-tail inequality discharged from real `exp`/`cosh` bounds (no hypothesis left).
The mechanism of (L1) genuinely fires; this is not a vacuous conditional. -/
theorem dW_dtheta_neg_at_eighth {M N : ℕ} (hMN : M ≤ N) (hM1 : 1 ≤ M) :
    (∑ k ∈ range N, rphi ((1 - 1 / 8 + k) * (2 / 2 : ℝ)))
      < ∑ k ∈ range M, rphi ((1 / 8 + k) * (2 / 2 : ℝ)) := by
  have hM : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM1
  -- real exp anchors
  have he1 : (2.718 : ℝ) < Real.exp 1 := by nlinarith [Real.exp_one_gt_d9]
  have hexp3 : Real.exp 3 = Real.exp 1 ^ 3 := by
    rw [← Real.exp_nat_mul]; norm_num
  have he3 : (16 : ℝ) ≤ Real.exp 3 := by
    rw [hexp3]
    have h := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2.718) he1.le 3
    have h16 : (16 : ℝ) ≤ (2.718 : ℝ) ^ 3 := by norm_num
    linarith
  have hexp2 : Real.exp 2 = Real.exp 1 ^ 2 := by
    rw [← Real.exp_nat_mul]; norm_num
  have he2 : (2 : ℝ) ≤ Real.exp 2 := by
    rw [hexp2]
    have h := pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2.718) he1.le 2
    have h2 : (2 : ℝ) ≤ (2.718 : ℝ) ^ 2 := by norm_num
    linarith
  refine dW_dtheta_neg hMN hM1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by nlinarith [hM]) ?_
  -- hbeat: head ≥ 125 beats tail ≤ 8
  have htailexp : Real.exp (-2 * ((1 - 1 / 8 + (M : ℝ)) * (2 / 2))) ≤ Real.exp (-3) := by
    apply Real.exp_le_exp.mpr; nlinarith [hM]
  have he3inv : Real.exp (-3) ≤ 1 / 16 := by
    rw [Real.exp_neg]
    rw [inv_le_comm₀ (Real.exp_pos 3) (by norm_num)]; linarith [he3]
  have he2inv : Real.exp (-2 * (2 / 2 : ℝ)) ≤ 1 / 2 := by
    rw [show (-2 * (2 / 2) : ℝ) = -2 by norm_num, Real.exp_neg,
      inv_le_comm₀ (Real.exp_pos 2) (by norm_num)]; linarith [he2]
  have hden : (1 : ℝ) / 2 ≤ 1 - Real.exp (-2 * (2 / 2 : ℝ)) := by linarith [he2inv]
  have hnumpos : (0 : ℝ) ≤ 64 * Real.exp (-2 * ((1 - 1 / 8 + (M : ℝ)) * (2 / 2))) := by positivity
  have hlhs : 64 * Real.exp (-2 * ((1 - 1 / 8 + (M : ℝ)) * (2 / 2)))
      / (1 - Real.exp (-2 * (2 / 2 : ℝ))) ≤ 8 := by
    rw [div_le_iff₀ (by linarith [hden] : (0:ℝ) < 1 - Real.exp (-2 * (2 / 2 : ℝ)))]
    have h1 : 64 * Real.exp (-2 * ((1 - 1 / 8 + (M : ℝ)) * (2 / 2))) ≤ 64 * (1 / 16) := by
      have := le_trans htailexp he3inv; nlinarith [this, Real.exp_pos (-2 * ((1 - 1 / 8 + (M : ℝ)) * (2 / 2)))]
    nlinarith [h1, hden, Real.exp_pos (-2 * (2 / 2 : ℝ))]
  have hcosh : Real.cosh 1 < 2 := cosh_one_lt_two
  have hrhs : (125 : ℝ) < 1 / (4 * ((1 / 8) * 2 / 2) ^ 3) - Real.cosh 1 / ((1 - 1 / 8) * 2 / 2) ^ 3 := by
    rw [show ((1 / 8) * 2 / 2 : ℝ) = 1 / 8 by norm_num,
      show ((1 - 1 / 8) * 2 / 2 : ℝ) = 7 / 8 by norm_num]
    rw [show (1 : ℝ) / (4 * (1 / 8) ^ 3) = 128 by norm_num]
    rw [show ((7 : ℝ) / 8) ^ 3 = 343 / 512 by norm_num]
    rw [div_eq_mul_inv, show ((343 : ℝ) / 512)⁻¹ = 512 / 343 by norm_num]
    nlinarith [hcosh, Real.cosh_pos (1 : ℝ)]
  linarith [hlhs, hrhs]

/-- **(L1) UNCONDITIONAL over a region** — `hbeat` removed. On the band `θ ∈ (0, 1/8]`,
`δ ∈ [3/2, 2]`, for every `M ≥ 1` ahead and `N ≥ M` behind charges, `dW/dθ < 0`. No head-vs-tail
hypothesis: the head gain `≥ 112` (`θδ/2 ≤ 1/8`, `(1−θ)δ/2 ≥ 1/2`) beats the far tail `≤ 36`
(`(1−θ+M)δ ≥ 2`, `1−e^{−δ} ≥ 3/5`), everything discharged from crude `exp`/`cosh` bounds
(`add_one_le_exp`, `cosh_one_lt_two`). A genuine two-parameter region, not a point. -/
theorem dW_dtheta_neg_region {θ δ : ℝ} {M N : ℕ} (hMN : M ≤ N) (hM1 : 1 ≤ M)
    (hθ0 : 0 < θ) (hθ8 : θ ≤ 1 / 8) (hδlo : 3 / 2 ≤ δ) (hδhi : δ ≤ 2) :
    (∑ k ∈ range N, rphi ((1 - θ + k) * (δ / 2)))
      < ∑ k ∈ range M, rphi ((θ + k) * (δ / 2)) := by
  have hδ0 : 0 < δ := by linarith
  have hM : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM1
  refine dW_dtheta_neg hMN hM1 hθ0 (by linarith) hδ0 (by nlinarith [hθ8, hδhi, hθ0, hδ0])
    (by nlinarith [hθ0, hδhi, hδ0]) (by nlinarith [hM, hθ8, hδlo]) ?_
  -- hbeat: tail ≤ 36 < 112 ≤ head
  have hnum : Real.exp (-2 * ((1 - θ + (M : ℝ)) * (δ / 2))) ≤ 1 / 3 := by
    have h1 : Real.exp (-2 * ((1 - θ + (M : ℝ)) * (δ / 2))) ≤ Real.exp (-2) := by
      apply Real.exp_le_exp.mpr; nlinarith [hM, hθ8, hδlo]
    have h2 : Real.exp (-2) ≤ 1 / 3 := by
      rw [Real.exp_neg, inv_eq_one_div]
      apply one_div_le_one_div_of_le (by norm_num)
      linarith [Real.add_one_le_exp (2 : ℝ)]
    linarith
  have hden : (3 : ℝ) / 5 ≤ 1 - Real.exp (-2 * (δ / 2)) := by
    have h1 : Real.exp (-2 * (δ / 2)) ≤ Real.exp (-3 / 2) := by
      apply Real.exp_le_exp.mpr; nlinarith [hδlo]
    have h2 : Real.exp (-3 / 2) ≤ 2 / 5 := by
      rw [show (-3 / 2 : ℝ) = -(3 / 2) by norm_num, Real.exp_neg, inv_eq_one_div]
      have h3 := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 5 / 2)
        (by linarith [Real.add_one_le_exp (3 / 2 : ℝ)] : (5 : ℝ) / 2 ≤ Real.exp (3 / 2))
      have h52 : (1 : ℝ) / (5 / 2) = 2 / 5 := by norm_num
      linarith [h3, h52]
    linarith
  have hdenpos : (0 : ℝ) < 1 - Real.exp (-2 * (δ / 2)) := by linarith
  have htail : 64 * Real.exp (-2 * ((1 - θ + (M : ℝ)) * (δ / 2)))
      / (1 - Real.exp (-2 * (δ / 2))) ≤ 36 := by
    rw [div_le_iff₀ hdenpos]
    nlinarith [hnum, hden, Real.exp_pos (-2 * ((1 - θ + (M : ℝ)) * (δ / 2)))]
  -- head ≥ 112
  have hxpos : 0 < θ * δ / 2 := by positivity
  have hx8 : θ * δ / 2 ≤ 1 / 8 := by nlinarith [hθ8, hδhi, hθ0, hδ0]
  have hhead1 : (128 : ℝ) ≤ 1 / (4 * (θ * δ / 2) ^ 3) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith [pow_le_pow_left₀ hxpos.le hx8 3]
  have hy2 : (1 : ℝ) / 2 ≤ (1 - θ) * δ / 2 := by nlinarith [hθ8, hδlo, hθ0]
  have hypos : (0 : ℝ) < (1 - θ) * δ / 2 := by linarith
  have hsub : Real.cosh 1 / ((1 - θ) * δ / 2) ^ 3 ≤ 8 * Real.cosh 1 := by
    have hy3 : (1 : ℝ) / 8 ≤ ((1 - θ) * δ / 2) ^ 3 := by
      nlinarith [pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 2) hy2 3]
    rw [div_le_iff₀ (by positivity)]
    nlinarith [hy3, Real.cosh_pos (1 : ℝ)]
  have hcosh : Real.cosh 1 < 2 := cosh_one_lt_two
  have hrhs : (112 : ℝ) < 1 / (4 * (θ * δ / 2) ^ 3) - Real.cosh 1 / ((1 - θ) * δ / 2) ^ 3 := by
    nlinarith [hhead1, hsub, hcosh]
  linarith [htail, hrhs]

/-- **The missing brick for the small-δ regime**: `coth s < 1/s + 1` for every `s > 0`. Proof by
monotonicity of `g(s) = (1+s)sinh s − s cosh s`: `g(0)=0` and `g'(s) = sinh s + s(cosh s − sinh s)
= sinh s + s·e^{−s} > 0`, so `g(s) > 0`, i.e. `s cosh s < (1+s) sinh s`, i.e. `coth s < 1/s + 1`.
Unlike the sparse-lattice exp tail, this holds at ALL scales, so it controls the tail for `δ → 0`
(the physical `δ = c/j` regime). -/
theorem rcoth_lt_inv_add_one {s : ℝ} (hs : 0 < s) : rcoth s < 1 / s + 1 := by
  set g : ℝ → ℝ := fun t => (1 + t) * Real.sinh t - t * Real.cosh t with hg_def
  have hderiv : ∀ t : ℝ, HasDerivAt g
      (Real.sinh t + t * Real.cosh t - t * Real.sinh t) t := by
    intro t
    have h1 : HasDerivAt (fun t : ℝ => (1 + t) * Real.sinh t)
        (1 * Real.sinh t + (1 + t) * Real.cosh t) t := by
      simpa using ((hasDerivAt_id t).const_add (1 : ℝ)).mul (Real.hasDerivAt_sinh t)
    have h2 : HasDerivAt (fun t : ℝ => t * Real.cosh t)
        (1 * Real.cosh t + t * Real.sinh t) t := by
      simpa using (hasDerivAt_id t).mul (Real.hasDerivAt_cosh t)
    have h3 := h1.sub h2
    simp only [hg_def]
    convert h3 using 1
    ring
  have hmono : StrictMonoOn g (Set.Ici 0) := by
    apply strictMonoOn_of_deriv_pos (convex_Ici 0)
      (fun x _ => ((hderiv x).continuousAt).continuousWithinAt)
    intro t ht
    rw [interior_Ici, Set.mem_Ioi] at ht
    rw [(hderiv t).deriv]
    have hsp : 0 < Real.sinh t := sinh_pos_of_pos ht
    have hsc : Real.sinh t < Real.cosh t := sinh_lt_cosh t
    nlinarith [mul_pos ht (by linarith [hsc] : (0 : ℝ) < Real.cosh t - Real.sinh t), hsp]
  have hg0 : g 0 = 0 := by simp [hg_def]
  have hgs : 0 < g s := by
    have hms := hmono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hs.le) hs
    rwa [hg0] at hms
  have hsp : 0 < Real.sinh s := sinh_pos_of_pos hs
  have hkey : Real.cosh s * s < (1 + s) * Real.sinh s := by
    simp only [hg_def] at hgs; nlinarith [hgs]
  rw [rcoth, div_lt_iff₀ hsp,
    show (1 / s + 1) * Real.sinh s = (1 + s) * Real.sinh s / s from by field_simp,
    lt_div_iff₀ hs]
  linarith [hkey]

/-- `csch² s ≤ 1/s²` for `s > 0` (from `sinh s ≥ s`). -/
theorem rcsch_sq_le_inv_sq {s : ℝ} (hs : 0 < s) : (rcsch s) ^ 2 ≤ 1 / s ^ 2 := by
  have hsp : 0 < Real.sinh s := sinh_pos_of_pos hs
  have hself : s ≤ Real.sinh s := self_le_sinh hs.le
  have hsq : s ^ 2 ≤ (Real.sinh s) ^ 2 := pow_le_pow_left₀ hs.le hself 2
  simp only [rcsch, one_div, inv_pow]
  rw [inv_le_inv₀ (by positivity) (by positivity)]
  exact hsq

/-- **Global cubic–quadratic upper bound** `φ(s) < 1/s³ + 1/s²` for all `s > 0` (the small-δ tail
control). From `csch² s ≤ 1/s²` and `coth s < 1/s + 1`: `φ = csch²·coth < (1/s²)(1/s+1)`. Unlike
`rphi_le_cubic` (valid only on `(0,1]`), this is a GLOBAL bound whose `k`-tail
`Σ (1/·³ + 1/·²)` is a `p=2,3` series — the tool that closes (L1) for `δ → 0`. -/
theorem rphi_lt_cubic_quadratic {s : ℝ} (hs : 0 < s) : rphi s < 1 / s ^ 3 + 1 / s ^ 2 := by
  have hcoth : rcoth s < 1 / s + 1 := rcoth_lt_inv_add_one hs
  have hcothpos : 0 < rcoth s := rcoth_pos_of_pos hs
  have hcsch : (rcsch s) ^ 2 ≤ 1 / s ^ 2 := rcsch_sq_le_inv_sq hs
  have hcschpos : 0 < (rcsch s) ^ 2 := by
    have := rcsch_pos_of_pos hs; positivity
  have hrphi : rphi s = (rcsch s) ^ 2 * rcoth s := rfl
  calc rphi s = (rcsch s) ^ 2 * rcoth s := hrphi
    _ ≤ (1 / s ^ 2) * rcoth s := by
        apply mul_le_mul_of_nonneg_right hcsch hcothpos.le
    _ < (1 / s ^ 2) * (1 / s + 1) := by
        apply mul_lt_mul_of_pos_left hcoth (by positivity)
    _ = 1 / s ^ 3 + 1 / s ^ 2 := by field_simp

/-- **Telescoping `p=2` tail** `Σ_{k∈[M,N)} 1/(a+k)² ≤ 1/(a+M−1)`, valid once `a+M−1 > 0`.
Each term `1/(a+k)² ≤ 1/(a+k−1) − 1/(a+k)` (partial fractions + `(a+k−1)(a+k) ≤ (a+k)²`), and the
sum telescopes. The convergent-tail tool the small-δ regime needs. -/
theorem inv_sq_telescope {a : ℝ} {M N : ℕ} (hMN : M ≤ N) (hpos : 0 < a + (M : ℝ) - 1) :
    ∑ k ∈ Finset.Ico M N, 1 / (a + (k : ℝ)) ^ 2 ≤ 1 / (a + (M : ℝ) - 1) := by
  set g : ℕ → ℝ := fun k => 1 / (a + (k : ℝ) - 1) with hg
  have hterm : ∀ k ∈ Finset.Ico M N, 1 / (a + (k : ℝ)) ^ 2 ≤ g k - g (k + 1) := by
    intro k hk
    rw [Finset.mem_Ico] at hk
    have hkM : (M : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk.1
    have hak1 : 0 < a + (k : ℝ) - 1 := by linarith [hpos]
    have hak : 0 < a + (k : ℝ) := by linarith
    have hgval : g k - g (k + 1) = 1 / ((a + (k : ℝ) - 1) * (a + (k : ℝ))) := by
      simp only [hg, Nat.cast_add, Nat.cast_one]
      rw [show a + ((k : ℝ) + 1) - 1 = a + (k : ℝ) from by ring]
      field_simp
      ring
    rw [hgval]
    exact one_div_le_one_div_of_le (by positivity) (by nlinarith [hak])
  calc ∑ k ∈ Finset.Ico M N, 1 / (a + (k : ℝ)) ^ 2
      ≤ ∑ k ∈ Finset.Ico M N, (g k - g (k + 1)) := Finset.sum_le_sum hterm
    _ = g M - g N := by
        rw [Finset.sum_Ico_eq_sum_range]
        simp only [Nat.add_assoc]
        rw [Finset.sum_range_sub' (fun i => g (M + i)) (N - M), Nat.add_zero,
          show M + (N - M) = N from by omega]
    _ ≤ 1 / (a + (M : ℝ) - 1) := by
        have hgN : 0 ≤ g N := by
          simp only [hg]
          have : 0 < a + (N : ℝ) - 1 := by
            have : (M : ℝ) ≤ (N : ℝ) := by exact_mod_cast hMN
            linarith [hpos]
          positivity
        simp only [hg] at hgN ⊢
        linarith [hgN]

/-- **Telescoping `p=3` tail** `Σ_{k∈[M,N)} 1/(a+k)³ ≤ 1/((a+M)(a+M−1))`. From
`1/(a+k)³ = (1/(a+k))·(1/(a+k)²) ≤ (1/(a+M))·(1/(a+k)²)` (since `a+k ≥ a+M`) and the `p=2`
telescope. -/
theorem inv_cube_telescope {a : ℝ} {M N : ℕ} (hMN : M ≤ N) (hpos : 0 < a + (M : ℝ) - 1) :
    ∑ k ∈ Finset.Ico M N, 1 / (a + (k : ℝ)) ^ 3 ≤ (1 / (a + (M : ℝ))) * (1 / (a + (M : ℝ) - 1)) := by
  have haM : 0 < a + (M : ℝ) := by linarith
  have hterm : ∀ k ∈ Finset.Ico M N,
      1 / (a + (k : ℝ)) ^ 3 ≤ (1 / (a + (M : ℝ))) * (1 / (a + (k : ℝ)) ^ 2) := by
    intro k hk
    rw [Finset.mem_Ico] at hk
    have hkM : (M : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk.1
    have hak : 0 < a + (k : ℝ) := by linarith
    rw [show (1 / (a + (M : ℝ))) * (1 / (a + (k : ℝ)) ^ 2)
        = 1 / ((a + (M : ℝ)) * (a + (k : ℝ)) ^ 2) from by rw [div_mul_div_comm, one_mul]]
    exact one_div_le_one_div_of_le (by positivity)
      (by nlinarith [hak, hkM, sq_nonneg (a + (k : ℝ))])
  calc ∑ k ∈ Finset.Ico M N, 1 / (a + (k : ℝ)) ^ 3
      ≤ ∑ k ∈ Finset.Ico M N, (1 / (a + (M : ℝ))) * (1 / (a + (k : ℝ)) ^ 2) :=
        Finset.sum_le_sum hterm
    _ = (1 / (a + (M : ℝ))) * ∑ k ∈ Finset.Ico M N, 1 / (a + (k : ℝ)) ^ 2 := by rw [Finset.mul_sum]
    _ ≤ (1 / (a + (M : ℝ))) * (1 / (a + (M : ℝ) - 1)) :=
        mul_le_mul_of_nonneg_left (inv_sq_telescope hMN hpos) (by positivity)

/-- **The far tail for SMALL δ** — the physical-regime tail bound (the exp bound of `tail_geom_bound`
required large `δ`; this one works for `δ → 0`). Using the global `rphi_lt_cubic_quadratic` termwise
and the two telescopes with `a = 1−θ`:
`Σ_{k∈[M,N)} φ((1−θ+k)δ/2) ≤ (8/δ³)·1/((1−θ+M)(M−θ)) + (4/δ²)·1/(M−θ)`. -/
theorem phi_tail_small_delta {θ δ : ℝ} {M N : ℕ} (hMN : M ≤ N) (hδ : 0 < δ)
    (hθ1 : θ < 1) (hMpos : 0 < (M : ℝ) - θ) :
    ∑ k ∈ Finset.Ico M N, rphi ((1 - θ + (k : ℝ)) * (δ / 2))
      ≤ (8 / δ ^ 3) * ((1 / (1 - θ + (M : ℝ))) * (1 / ((M : ℝ) - θ)))
        + (4 / δ ^ 2) * (1 / ((M : ℝ) - θ)) := by
  have hδ3 : (0 : ℝ) < δ ^ 3 := by positivity
  have hδ2 : (0 : ℝ) < δ ^ 2 := by positivity
  have hpos : 0 < (1 - θ) + (M : ℝ) - 1 := by linarith [hMpos]
  have hterm : ∀ k ∈ Finset.Ico M N,
      rphi ((1 - θ + (k : ℝ)) * (δ / 2))
        ≤ (8 / δ ^ 3) * (1 / (1 - θ + (k : ℝ)) ^ 3)
          + (4 / δ ^ 2) * (1 / (1 - θ + (k : ℝ)) ^ 2) := by
    intro k hk
    have hx : 0 < 1 - θ + (k : ℝ) := by
      have : (0 : ℝ) ≤ (k : ℝ) := by positivity
      linarith
    have harg : 0 < (1 - θ + (k : ℝ)) * (δ / 2) := by positivity
    have hlt := (rphi_lt_cubic_quadratic harg).le
    have hcube : 1 / ((1 - θ + (k : ℝ)) * (δ / 2)) ^ 3
        = (8 / δ ^ 3) * (1 / (1 - θ + (k : ℝ)) ^ 3) := by
      rw [mul_pow]; field_simp; ring
    have hsq : 1 / ((1 - θ + (k : ℝ)) * (δ / 2)) ^ 2
        = (4 / δ ^ 2) * (1 / (1 - θ + (k : ℝ)) ^ 2) := by
      rw [mul_pow]; field_simp; ring
    rw [hcube, hsq] at hlt
    exact hlt
  calc ∑ k ∈ Finset.Ico M N, rphi ((1 - θ + (k : ℝ)) * (δ / 2))
      ≤ ∑ k ∈ Finset.Ico M N, ((8 / δ ^ 3) * (1 / (1 - θ + (k : ℝ)) ^ 3)
          + (4 / δ ^ 2) * (1 / (1 - θ + (k : ℝ)) ^ 2)) := Finset.sum_le_sum hterm
    _ = (8 / δ ^ 3) * (∑ k ∈ Finset.Ico M N, 1 / (1 - θ + (k : ℝ)) ^ 3)
        + (4 / δ ^ 2) * (∑ k ∈ Finset.Ico M N, 1 / (1 - θ + (k : ℝ)) ^ 2) := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ ≤ (8 / δ ^ 3) * ((1 / (1 - θ + (M : ℝ))) * (1 / ((M : ℝ) - θ)))
        + (4 / δ ^ 2) * (1 / ((M : ℝ) - θ)) := by
        gcongr
        · have := inv_cube_telescope (a := 1 - θ) hMN hpos
          simpa [show (1 : ℝ) - θ + (M : ℝ) - 1 = (M : ℝ) - θ from by ring] using this
        · have := inv_sq_telescope (a := 1 - θ) hMN hpos
          simpa [show (1 : ℝ) - θ + (M : ℝ) - 1 = (M : ℝ) - θ from by ring] using this

set_option maxHeartbeats 1000000 in
/-- **(L1) UNCONDITIONAL for SMALL δ** — the physical regime. On `θ ∈ (0, 1/8]`, `δ ∈ (0, 1]`,
every `M ≥ 1`, `N ≥ M`: `dW/dθ < 0`, no hypothesis. Uses the small-δ tail (`phi_tail_small_delta`,
via the global φ-bound and the telescopes) instead of the exp tail, so it reaches `δ → 0` where
`dW_dtheta_neg_region` could not. Head `≥ 1000/δ³` (θ small), tail `≤ 10/δ³` (`δ ≤ 1` folds the
`1/δ²` term into `1/δ³`). This is (L1) closed on the band the θ-drift (doc 27 §3) actually
occupies. -/
theorem dW_dtheta_neg_small_delta {θ δ : ℝ} {M N : ℕ} (hMN : M ≤ N) (hM1 : 1 ≤ M)
    (hθ0 : 0 < θ) (hθ8 : θ ≤ 1 / 8) (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) :
    (∑ k ∈ range N, rphi ((1 - θ + k) * (δ / 2)))
      < ∑ k ∈ range M, rphi ((θ + k) * (δ / 2)) := by
  have hM : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM1
  have hδ3 : (0 : ℝ) < δ ^ 3 := by positivity
  set fa : ℕ → ℝ := fun k => rphi ((θ + k) * (δ / 2)) with hfa
  set fb : ℕ → ℝ := fun k => rphi ((1 - θ + k) * (δ / 2)) with hfb
  have hxpos : 0 < θ * δ / 2 := by positivity
  have hx1 : θ * δ / 2 ≤ 1 := by nlinarith [hθ8, hδ1, hθ0, hδ0]
  have hypos : 0 < (1 - θ) * δ / 2 := by nlinarith [hθ8, hδ0]
  have hy1 : (1 - θ) * δ / 2 ≤ 1 := by nlinarith [hθ0, hδ1, hδ0]
  -- head (k = 0)
  have hhead0 : 1 / (4 * (θ * δ / 2) ^ 3) - Real.cosh 1 / ((1 - θ) * δ / 2) ^ 3 ≤ fa 0 - fb 0 := by
    simp only [hfa, hfb, Nat.cast_zero, add_zero]
    rw [show θ * (δ / 2) = θ * δ / 2 from by ring,
      show (1 - θ) * (δ / 2) = (1 - θ) * δ / 2 from by ring]
    exact headGain_lower hxpos hx1 hypos hy1
  have hnonneg : ∀ k ∈ range M, 0 ≤ fa k - fb k := by
    intro k _
    simp only [hfa, hfb]
    have h1 : (0 : ℝ) < (θ + k) * (δ / 2) := by positivity
    have h2 : (θ + k) * (δ / 2) ≤ (1 - θ + k) * (δ / 2) := by
      have hδ2 : (0 : ℝ) < δ / 2 := by positivity
      nlinarith [hθ8, hδ2]
    have hanti := rphi_strictAntiOn_pos.antitoneOn (Set.mem_Ioi.mpr h1)
      (Set.mem_Ioi.mpr (lt_of_lt_of_le h1 h2)) h2
    linarith
  have hheadsum : fa 0 - fb 0 ≤ ∑ k ∈ range M, (fa k - fb k) :=
    Finset.single_le_sum hnonneg (Finset.mem_range.mpr (by omega))
  -- tail via the small-δ bound
  have htail : (∑ k ∈ Ico M N, fb k)
      ≤ (8 / δ ^ 3) * ((1 / (1 - θ + (M : ℝ))) * (1 / ((M : ℝ) - θ))) + (4 / δ ^ 2) * (1 / ((M : ℝ) - θ)) := by
    simp only [hfb]
    exact phi_tail_small_delta hMN hδ0 (by linarith) (by linarith)
  refine l1_neg_of_head_gt_tail hMN fa fb ?_
  -- head-beats-tail: tail ≤ 10/δ³ < 1000/δ³ ≤ head
  have hcosh : Real.cosh 1 < 2 := cosh_one_lt_two
  have hu : (0 : ℝ) < 1 / δ ^ 3 := by positivity
  have hd23 : (1 : ℝ) / δ ^ 2 ≤ 1 / δ ^ 3 := by
    rw [div_le_div_iff₀ (by positivity) hδ3]
    nlinarith [hδ1, hδ0, pow_pos hδ0 2]
  have hHlow : (1000 : ℝ) / δ ^ 3
      ≤ 1 / (4 * (θ * δ / 2) ^ 3) - Real.cosh 1 / ((1 - θ) * δ / 2) ^ 3 := by
    have e1 : 1 / (4 * (θ * δ / 2) ^ 3) = 2 / (θ ^ 3 * δ ^ 3) := by
      rw [show (4 : ℝ) * (θ * δ / 2) ^ 3 = θ ^ 3 * δ ^ 3 / 2 from by ring]; rw [one_div_div]
    have e2 : Real.cosh 1 / ((1 - θ) * δ / 2) ^ 3 = 8 * Real.cosh 1 / ((1 - θ) ^ 3 * δ ^ 3) := by
      rw [show ((1 - θ) * δ / 2) ^ 3 = (1 - θ) ^ 3 * δ ^ 3 / 8 from by ring, div_div_eq_mul_div,
        mul_comm (Real.cosh 1) (8 : ℝ)]
    rw [e1, e2]
    have hθ3 : θ ^ 3 ≤ 1 / 512 := by nlinarith [pow_le_pow_left₀ hθ0.le hθ8 3]
    have h1θ3 : (7 / 8 : ℝ) ^ 3 ≤ (1 - θ) ^ 3 :=
      pow_le_pow_left₀ (by norm_num) (by linarith) 3
    have hb1 : (1024 : ℝ) / δ ^ 3 ≤ 2 / (θ ^ 3 * δ ^ 3) := by
      rw [div_le_div_iff₀ hδ3 (by positivity)]; nlinarith [hθ3, hδ3, pow_pos hθ0 3]
    have hb2 : 8 * Real.cosh 1 / ((1 - θ) ^ 3 * δ ^ 3) ≤ 24 / δ ^ 3 := by
      rw [div_le_div_iff₀ (by positivity) hδ3]
      nlinarith [h1θ3, hcosh, hδ3, Real.cosh_pos (1 : ℝ)]
    have h1000 : (1000 : ℝ) / δ ^ 3 = 1024 / δ ^ 3 - 24 / δ ^ 3 := by ring
    linarith [hb1, hb2, h1000]
  have hTup : (8 / δ ^ 3) * ((1 / (1 - θ + (M : ℝ))) * (1 / ((M : ℝ) - θ))) + (4 / δ ^ 2) * (1 / ((M : ℝ) - θ))
      ≤ 10 / δ ^ 3 := by
    have hMθ : (7 / 8 : ℝ) ≤ (M : ℝ) - θ := by linarith
    have h1θM : (15 / 8 : ℝ) ≤ 1 - θ + (M : ℝ) := by linarith
    have ha1 : 1 / (1 - θ + (M : ℝ)) ≤ 8 / 15 := by
      rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
    have ha2 : 1 / ((M : ℝ) - θ) ≤ 8 / 7 := by
      rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
    have hbr : (1 / (1 - θ + (M : ℝ))) * (1 / ((M : ℝ) - θ)) ≤ 64 / 105 := by
      calc (1 / (1 - θ + (M : ℝ))) * (1 / ((M : ℝ) - θ)) ≤ (8 / 15) * (8 / 7) :=
            mul_le_mul ha1 ha2 (by positivity) (by norm_num)
        _ = 64 / 105 := by norm_num
    have ht1 : (8 / δ ^ 3) * ((1 / (1 - θ + (M : ℝ))) * (1 / ((M : ℝ) - θ))) ≤ 5 / δ ^ 3 := by
      calc (8 / δ ^ 3) * ((1 / (1 - θ + (M : ℝ))) * (1 / ((M : ℝ) - θ)))
          ≤ (8 / δ ^ 3) * (64 / 105) := by
            apply mul_le_mul_of_nonneg_left hbr (by positivity)
        _ ≤ 5 / δ ^ 3 := by rw [div_mul_eq_mul_div, div_le_div_iff₀ hδ3 hδ3]; nlinarith [hδ3]
    have ht2 : (4 / δ ^ 2) * (1 / ((M : ℝ) - θ)) ≤ 5 / δ ^ 3 := by
      have hstep : (4 / δ ^ 2) * (1 / ((M : ℝ) - θ)) ≤ (4 / δ ^ 2) * (8 / 7) :=
        mul_le_mul_of_nonneg_left ha2 (by positivity)
      have hstep2 : (4 / δ ^ 2) * (8 / 7) = (32 / 7) * (1 / δ ^ 2) := by ring
      have hstep3 : (32 / 7 : ℝ) * (1 / δ ^ 2) ≤ (32 / 7) * (1 / δ ^ 3) :=
        mul_le_mul_of_nonneg_left hd23 (by norm_num)
      have hstep4 : (32 / 7 : ℝ) * (1 / δ ^ 3) ≤ 5 / δ ^ 3 := by
        rw [mul_one_div, div_le_div_iff₀ (by positivity) hδ3]; nlinarith [hδ3]
      linarith [hstep, hstep2, hstep3, hstep4]
    have h10 : (10 : ℝ) / δ ^ 3 = 5 / δ ^ 3 + 5 / δ ^ 3 := by ring
    linarith [ht1, ht2, h10]
  have hlt : (10 : ℝ) / δ ^ 3 < 1000 / δ ^ 3 := by
    rw [div_lt_div_iff₀ hδ3 hδ3]; nlinarith [hδ3]
  calc (∑ k ∈ Ico M N, fb k) ≤ _ := htail
    _ ≤ 10 / δ ^ 3 := hTup
    _ < 1000 / δ ^ 3 := hlt
    _ ≤ 1 / (4 * (θ * δ / 2) ^ 3) - Real.cosh 1 / ((1 - θ) * δ / 2) ^ 3 := hHlow
    _ ≤ fa 0 - fb 0 := hhead0
    _ ≤ ∑ k ∈ range M, (fa k - fb k) := hheadsum

end RHTower
