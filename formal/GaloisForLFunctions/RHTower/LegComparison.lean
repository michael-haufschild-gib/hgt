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

end RHTower
