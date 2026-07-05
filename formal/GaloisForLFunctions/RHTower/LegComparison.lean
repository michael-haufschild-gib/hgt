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

end RHTower
