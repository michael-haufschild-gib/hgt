import GaloisForLFunctions.RHTower.MobiusReciprocalMarkerBlockCount
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The growing marker schedule

Two bookkeeping facts control every retained block of the growing reciprocal-marker construction.

* **Cofactor windows stay long.**  Cutting the block index at `K` with
  `K + 4 ≤ (log h - w)/log 2` forces `h / 2^{k+2} ≥ 4 e^w` for every retained `k`.  The subtraction
  of `w` is exactly what keeps the window length above `e^w`; without it the last blocks would have
  windows of bounded length and no distribution theorem could be applied to them.
* **Cofactor starts stay large.**  With `X = N²` and a marker `p ≤ 2^{k+1} N`, the start `⌊X/p⌋` is
  at least `N / 2^{k+1}`.  So the start scale falls only by the block factor, which is what the
  reciprocal-fibre charge is measured against.

Both are exact: the first is a real inequality with no error term, the second holds in natural
division.
-/

noncomputable section

namespace RHTower

open Finset

/-- **Retained blocks have long cofactor windows.**  Cutting at `K` with
`K + 4 ≤ (log h - w)/log 2` keeps every window above `4 e^w`. -/
theorem markerBlock_window_length_ge {h w : ℝ} (hh : 0 < h) {K : ℕ}
    (hK : (K : ℝ) + 4 ≤ (Real.log h - w) / Real.log 2) {k : ℕ} (hk : k ≤ K) :
    4 * Real.exp w ≤ h / 2 ^ (k + 2) := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hkK : (k : ℝ) ≤ (K : ℝ) := by exact_mod_cast hk
  have hexp : ((k : ℝ) + 2) * Real.log 2 ≤ Real.log h - w - 2 * Real.log 2 := by
    have hstep : (k : ℝ) + 4 ≤ (Real.log h - w) / Real.log 2 := by linarith
    rw [le_div_iff₀ hlog2] at hstep
    linarith
  have hpow : (2 : ℝ) ^ (k + 2) = Real.exp (((k : ℝ) + 2) * Real.log 2) := by
    rw [← Real.rpow_natCast (2 : ℝ) (k + 2), Real.rpow_def_of_pos (by norm_num)]
    push_cast
    ring_nf
  have h4 : Real.exp (2 * Real.log 2) = 4 := by
    have hsplit : (2 : ℝ) * Real.log 2 = Real.log 2 + Real.log 2 := by ring
    rw [hsplit, Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    norm_num
  have hval : Real.exp (Real.log h - w - 2 * Real.log 2) = h * Real.exp (-w) / 4 := by
    rw [Real.exp_sub, Real.exp_sub, Real.exp_log hh, h4, Real.exp_neg]
    have hne : Real.exp w ≠ 0 := Real.exp_ne_zero w
    field_simp
  have hle : (2 : ℝ) ^ (k + 2) ≤ h * Real.exp (-w) / 4 := by
    rw [hpow, ← hval]
    exact Real.exp_le_exp.2 hexp
  have hpowpos : (0 : ℝ) < (2 : ℝ) ^ (k + 2) := by positivity
  have hfinal : h / (h * Real.exp (-w) / 4) = 4 * Real.exp w := by
    rw [Real.exp_neg]
    have hne : Real.exp w ≠ 0 := Real.exp_ne_zero w
    field_simp
  calc 4 * Real.exp w = h / (h * Real.exp (-w) / 4) := hfinal.symm
    _ ≤ h / (2 : ℝ) ^ (k + 2) := div_le_div_of_nonneg_left hh.le hpowpos hle

/-- **Retained blocks have large cofactor starts.**  With `X = N²`, a marker at most `2^{k+1} N`
has reciprocal start at least `N / 2^{k+1}`. -/
theorem markerBlock_start_ge {N X p k : ℕ} (hX : X = N * N) (hp : 0 < p)
    (hple : p ≤ 2 ^ (k + 1) * N) (hN : 1 ≤ N) :
    N / 2 ^ (k + 1) ≤ X / p := by
  have hstep : X / (2 ^ (k + 1) * N) ≤ X / p := Nat.div_le_div_left hple hp
  have hcalc : X / (2 ^ (k + 1) * N) = N / 2 ^ (k + 1) := by
    rw [hX]
    exact Nat.mul_div_mul_right (m := N) N (2 ^ (k + 1)) (by omega)
  omega

end RHTower
