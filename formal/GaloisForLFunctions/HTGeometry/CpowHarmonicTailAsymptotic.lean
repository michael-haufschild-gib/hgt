import GaloisForLFunctions.HTGeometry.RpowHarmonicTailAsymptotic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# The sharp tail of an oscillatory power series

For a complex exponent `s` with `Re s < 1` the tail `∑_{m > N} m^s w_m`, with the harmonic
increment `w_m = 1/m - 1/(m+1)`, is asymptotically `N^{s-1}/(1-s)`.  Real monotonicity is
unavailable, so the comparison is made by a derivative bound on each unit window: the primitive
`t^{s-1}/(s-1)` has derivative `t^{s-2}`, and the second derivative bound `|s-2|t^{Re s-3}` turns
the telescoping increment into the term with an error that sums to `O(N^{Re s-2})`.  Multiplying
by `N^{1-s}` kills the error and leaves `((N+1)/N)^{s-1}/(1-s) → 1/(1-s)`.

The oscillation therefore only rotates the constant: the real decay exponent is unchanged.
-/

open Filter Topology Complex

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-! ## The unit-window derivative bounds -/

/-- The unit-window increment bound for a complex power with nonpositive real exponent. -/
theorem norm_ofReal_cpow_sub_le {w : ℂ} (hw : w ≠ 0) (hwre : w.re ≤ 1) {m t : ℝ} (hm : 0 < m)
    (ht : t ∈ Set.Icc m (m + 1)) :
    ‖((t : ℝ) : ℂ) ^ w - ((m : ℝ) : ℂ) ^ w‖ ≤ ‖w‖ * m ^ (w.re - 1) := by
  have hderiv : ∀ x ∈ Set.Icc m (m + 1),
      HasDerivWithinAt (fun y : ℝ => ((y : ℝ) : ℂ) ^ w) (w * ((x : ℝ) : ℂ) ^ (w - 1))
        (Set.Icc m (m + 1)) x := by
    intro x hx
    have hx0 : x ≠ 0 := ne_of_gt (lt_of_lt_of_le hm hx.1)
    exact (hasDerivAt_ofReal_cpow_const hx0 hw).hasDerivWithinAt
  have hbound : ∀ x ∈ Set.Icc m (m + 1),
      ‖w * ((x : ℝ) : ℂ) ^ (w - 1)‖ ≤ ‖w‖ * m ^ (w.re - 1) := by
    intro x hx
    have hx0 : 0 < x := lt_of_lt_of_le hm hx.1
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx0]
    have hre : (w - 1).re = w.re - 1 := by simp
    rw [hre]
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos hm hx.1 (by linarith)) (norm_nonneg w)
  have hmem : m ∈ Set.Icc m (m + 1) := Set.left_mem_Icc.2 (by linarith)
  have hmain := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hderiv hbound
    (convex_Icc m (m + 1)) hmem ht
  refine hmain.trans ?_
  have hdist : ‖t - m‖ ≤ 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (by linarith [ht.1])]
    linarith [ht.2]
  have hC : (0 : ℝ) ≤ ‖w‖ * m ^ (w.re - 1) := by positivity
  calc ‖w‖ * m ^ (w.re - 1) * ‖t - m‖ ≤ ‖w‖ * m ^ (w.re - 1) * 1 :=
        mul_le_mul_of_nonneg_left hdist hC
    _ = ‖w‖ * m ^ (w.re - 1) := by ring

/-- **The unit-window comparison of the telescoping increment with the term.** -/
theorem norm_cpow_increment_sub_term_le {s : ℂ} (hs : s.re < 1) {m : ℝ} (hm : 0 < m) :
    ‖(((m + 1 : ℝ) : ℂ) ^ (s - 1) / (s - 1) - ((m : ℝ) : ℂ) ^ (s - 1) / (s - 1))
        - ((m : ℝ) : ℂ) ^ (s - 2)‖
      ≤ ‖s - 2‖ * m ^ (s.re - 3) := by
  have hs2 : s - 2 ≠ 0 := by
    intro h
    have : s = 2 := by linear_combination h
    rw [this] at hs
    norm_num at hs
  have hs1 : s - 1 ≠ 0 := by
    intro h
    have : s = 1 := by linear_combination h
    rw [this] at hs
    norm_num at hs
  have hrw : s - 2 + 1 = s - 1 := by ring
  set G : ℝ → ℂ := fun t => ((t : ℝ) : ℂ) ^ (s - 1) / (s - 1)
    - ((m : ℝ) : ℂ) ^ (s - 2) * ((t : ℝ) : ℂ) with hG
  have hderiv : ∀ x ∈ Set.Icc m (m + 1),
      HasDerivWithinAt G (((x : ℝ) : ℂ) ^ (s - 2) - ((m : ℝ) : ℂ) ^ (s - 2))
        (Set.Icc m (m + 1)) x := by
    intro x hx
    have hx0 : x ≠ 0 := ne_of_gt (lt_of_lt_of_le hm hx.1)
    have hprim : HasDerivAt (fun y : ℝ => ((y : ℝ) : ℂ) ^ (s - 1) / (s - 1))
        (((x : ℝ) : ℂ) ^ (s - 2)) x := by
      have h := hasDerivAt_ofReal_cpow_const' (x := x) hx0 (r := s - 2)
        (by intro h; apply hs1; linear_combination h)
      rwa [hrw] at h
    have hlin : HasDerivAt (fun y : ℝ => ((m : ℝ) : ℂ) ^ (s - 2) * ((y : ℝ) : ℂ))
        (((m : ℝ) : ℂ) ^ (s - 2)) x := by
      have h : HasDerivAt (fun y : ℝ => ((y : ℝ) : ℂ)) 1 x := Complex.ofRealCLM.hasDerivAt
      simpa using h.const_mul (((m : ℝ) : ℂ) ^ (s - 2))
    exact (hprim.sub hlin).hasDerivWithinAt
  have hbound : ∀ x ∈ Set.Icc m (m + 1),
      ‖((x : ℝ) : ℂ) ^ (s - 2) - ((m : ℝ) : ℂ) ^ (s - 2)‖ ≤ ‖s - 2‖ * m ^ (s.re - 3) := by
    intro x hx
    have hre : (s - 2).re - 1 = s.re - 3 := by simp; ring
    have := norm_ofReal_cpow_sub_le (w := s - 2) hs2 (by simp; linarith) hm hx
    rwa [hre] at this
  have hmem : m ∈ Set.Icc m (m + 1) := Set.left_mem_Icc.2 (by linarith)
  have hmem2 : m + 1 ∈ Set.Icc m (m + 1) := Set.right_mem_Icc.2 (by linarith)
  have hmain := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hderiv hbound
    (convex_Icc m (m + 1)) hmem hmem2
  have hval : G (m + 1) - G m
      = (((m + 1 : ℝ) : ℂ) ^ (s - 1) / (s - 1) - ((m : ℝ) : ℂ) ^ (s - 1) / (s - 1))
        - ((m : ℝ) : ℂ) ^ (s - 2) := by
    rw [hG]
    push_cast
    ring
  rw [hval] at hmain
  refine hmain.trans (le_of_eq ?_)
  have hdist : ‖(m + 1 : ℝ) - m‖ = 1 := by
    rw [show (m + 1 : ℝ) - m = 1 by ring, Real.norm_eq_abs, abs_one]
  rw [hdist, mul_one]

/-! ## The shifted tail -/

/-- The tail of the second-difference terms. -/
def cpowShiftTail (s : ℂ) (N : ℕ) : ℂ :=
  ∑' k : ℕ, (((N : ℝ) + 1 + (k : ℝ) : ℝ) : ℂ) ^ (s - 2)

/-- The tail of the harmonic-weighted oscillatory source. -/
def cpowHarmonicTail (s : ℂ) (N : ℕ) : ℂ :=
  ∑' k : ℕ, (((N : ℝ) + 1 + (k : ℝ) : ℝ) : ℂ) ^ s
    * ((1 / ((N : ℝ) + 1 + (k : ℝ)) - 1 / ((N : ℝ) + 1 + (k : ℝ) + 1) : ℝ) : ℂ)

theorem summable_cpowShift {s : ℂ} (hs : s.re < 1) (N : ℕ) :
    Summable fun k : ℕ => (((N : ℝ) + 1 + (k : ℝ) : ℝ) : ℂ) ^ (s - 2) := by
  refine Summable.of_norm ?_
  have hq : s.re - 1 < 0 := by linarith
  refine (summable_shift_rpow hq N).congr fun k => ?_
  have hN0 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  have hx : (0 : ℝ) < (N : ℝ) + 1 + (k : ℝ) := by linarith
  rw [Complex.norm_cpow_eq_rpow_re_of_pos hx]
  congr 1
  simp
  ring

theorem summable_cpowIncrementError {s : ℂ} (hs : s.re < 1) (N : ℕ) :
    Summable fun k : ℕ => ‖s - 2‖ * ((N : ℝ) + 1 + (k : ℝ)) ^ (s.re - 3) := by
  have hq : s.re - 2 < 0 := by linarith
  refine ((summable_shift_rpow hq N).congr fun k => ?_).mul_left _
  congr 1
  ring

/-! ## The tail estimate -/

/-- **The shifted tail is `(N+1)^{s-1}/(1-s)` up to `O(N^{Re s - 2})`.** -/
theorem norm_cpowShiftTail_sub_le {s : ℂ} (hs : s.re < 1) {N : ℕ} (hN : 1 ≤ N) :
    ‖cpowShiftTail s N - (((N : ℝ) + 1 : ℝ) : ℂ) ^ (s - 1) / (1 - s)‖
      ≤ ‖s - 2‖ / (2 - s.re) * (N : ℝ) ^ (s.re - 2) := by
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hs1 : s - 1 ≠ 0 := by
    intro h
    have hval : s = 1 := by linear_combination h
    rw [hval] at hs
    norm_num at hs
  set g : ℕ → ℂ := fun k => (((N : ℝ) + 1 + (k : ℝ) : ℝ) : ℂ) ^ (s - 1) / (s - 1) with hgdef
  set a : ℕ → ℂ := fun k => (((N : ℝ) + 1 + (k : ℝ) : ℝ) : ℂ) ^ (s - 2) with hadef
  have hx : ∀ k : ℕ, (0 : ℝ) < (N : ℝ) + 1 + (k : ℝ) := by
    intro k
    have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith
  have herr : ∀ k : ℕ, ‖(g (k + 1) - g k) - a k‖
      ≤ ‖s - 2‖ * ((N : ℝ) + 1 + (k : ℝ)) ^ (s.re - 3) := by
    intro k
    have hcast : ((N : ℝ) + 1 + ((k + 1 : ℕ) : ℝ)) = ((N : ℝ) + 1 + (k : ℝ)) + 1 := by
      push_cast
      ring
    have h := norm_cpow_increment_sub_term_le (s := s) hs (m := (N : ℝ) + 1 + (k : ℝ)) (hx k)
    rw [hgdef, hadef]
    simp only
    rw [hcast]
    exact h
  have hmajerr : Summable fun k : ℕ => ‖s - 2‖ * ((N : ℝ) + 1 + (k : ℝ)) ^ (s.re - 3) :=
    summable_cpowIncrementError hs N
  have hdiffsum : Summable fun k : ℕ => (g (k + 1) - g k) - a k :=
    Summable.of_norm (Summable.of_nonneg_of_le (fun k => norm_nonneg _) herr hmajerr)
  have hasum : Summable a := summable_cpowShift hs N
  have hbsum : Summable fun k : ℕ => g (k + 1) - g k := by
    refine (hdiffsum.add hasum).congr fun k => ?_
    ring
  have hgto : Tendsto g atTop (𝓝 0) := by
    have hq : (0 : ℝ) < 1 - s.re := by linarith
    have hbase : Tendsto (fun M : ℕ => (N : ℝ) + 1 + (M : ℝ)) atTop atTop :=
      tendsto_atTop_add_const_left _ _ tendsto_natCast_atTop_atTop
    have hpow : Tendsto (fun M : ℕ => ((N : ℝ) + 1 + (M : ℝ)) ^ (s.re - 1)) atTop (𝓝 0) := by
      have := (tendsto_rpow_neg_atTop (y := 1 - s.re) hq).comp hbase
      have hre : -(1 - s.re) = s.re - 1 := by ring
      simpa [Function.comp_def, hre] using this
    have hmaj : Tendsto (fun M : ℕ => (1 / ‖s - 1‖) * ((N : ℝ) + 1 + (M : ℝ)) ^ (s.re - 1))
        atTop (𝓝 0) := by
      have := hpow.const_mul (1 / ‖s - 1‖)
      simpa using this
    refine squeeze_zero_norm' ?_ hmaj
    filter_upwards with M
    rw [hgdef]
    simp only
    rw [norm_div, Complex.norm_cpow_eq_rpow_re_of_pos (hx M)]
    have hre : (s - 1).re = s.re - 1 := by simp
    rw [hre, div_eq_mul_inv, one_div]
    exact le_of_eq (by ring)
  have htel : ∀ M : ℕ, ∑ k ∈ Finset.range M, (g (k + 1) - g k) = g M - g 0 :=
    fun M => Finset.sum_range_sub g M
  have htsum_b : ∑' k : ℕ, (g (k + 1) - g k) = -g 0 := by
    have hlim := hbsum.hasSum.tendsto_sum_nat
    have hlim2 : Tendsto (fun M : ℕ => g M - g 0) atTop (𝓝 (0 - g 0)) :=
      hgto.sub tendsto_const_nhds
    rw [zero_sub] at hlim2
    exact tendsto_nhds_unique (hlim.congr htel) hlim2
  have hg0 : g 0 = (((N : ℝ) + 1 : ℝ) : ℂ) ^ (s - 1) / (s - 1) := by
    rw [hgdef]
    norm_num
  have hAeq : cpowShiftTail s N = ∑' k : ℕ, a k := rfl
  have hsubtsum : ∑' k : ℕ, ((g (k + 1) - g k) - a k)
      = (∑' k : ℕ, (g (k + 1) - g k)) - ∑' k : ℕ, a k := hbsum.tsum_sub hasum
  have hsub : cpowShiftTail s N - (((N : ℝ) + 1 : ℝ) : ℂ) ^ (s - 1) / (1 - s)
      = -(∑' k : ℕ, ((g (k + 1) - g k) - a k)) := by
    rw [hsubtsum, htsum_b, hg0, hAeq]
    have hneg : (((N : ℝ) + 1 : ℝ) : ℂ) ^ (s - 1) / (1 - s)
        = -((((N : ℝ) + 1 : ℝ) : ℂ) ^ (s - 1) / (s - 1)) := by
      rw [show (1 : ℂ) - s = -(s - 1) by ring, div_neg]
    rw [hneg]
    ring
  rw [hsub, norm_neg]
  refine (norm_tsum_le_tsum_norm ?_).trans ?_
  · exact Summable.of_nonneg_of_le (fun k => norm_nonneg _) herr hmajerr
  · refine (Summable.tsum_le_tsum herr
      (Summable.of_nonneg_of_le (fun k => norm_nonneg _) herr hmajerr) hmajerr).trans ?_
    rw [tsum_mul_left]
    have hq : s.re - 2 < 0 := by linarith
    have hmaj : ∑' k : ℕ, ((N : ℝ) + 1 + (k : ℝ)) ^ (s.re - 3)
        ≤ (N : ℝ) ^ (s.re - 2) / (2 - s.re) := by
      have h := tsum_shift_rpow_le (q := s.re - 2) hq hN
      have hexp : s.re - 2 - 1 = s.re - 3 := by ring
      rw [hexp] at h
      have hneg : -(s.re - 2) = 2 - s.re := by ring
      rwa [hneg] at h
    calc ‖s - 2‖ * ∑' k : ℕ, ((N : ℝ) + 1 + (k : ℝ)) ^ (s.re - 3)
        ≤ ‖s - 2‖ * ((N : ℝ) ^ (s.re - 2) / (2 - s.re)) :=
          mul_le_mul_of_nonneg_left hmaj (norm_nonneg _)
      _ = ‖s - 2‖ / (2 - s.re) * (N : ℝ) ^ (s.re - 2) := by ring

/-- The termwise comparison of the harmonic weight with the second-difference weight. -/
theorem norm_cpow_harmonic_term_sub_le {s : ℂ} {x : ℝ} (hx : 0 < x) :
    ‖((x : ℝ) : ℂ) ^ s * ((1 / x - 1 / (x + 1) : ℝ) : ℂ) - ((x : ℝ) : ℂ) ^ (s - 2)‖
      ≤ x ^ (s.re - 3) := by
  have hxne : ((x : ℝ) : ℂ) ≠ 0 := by
    simpa using ne_of_gt hx
  have hsq : ((x : ℝ) : ℂ) ^ (2 : ℂ) = ((x : ℝ) : ℂ) * ((x : ℝ) : ℂ) := by
    rw [show (2 : ℂ) = ((2 : ℕ) : ℂ) by norm_num, Complex.cpow_natCast]
    ring
  have hpow : ((x : ℝ) : ℂ) ^ (s - 2) = ((x : ℝ) : ℂ) ^ s / (((x : ℝ) : ℂ) * ((x : ℝ) : ℂ)) := by
    rw [Complex.cpow_sub _ _ hxne, hsq]
  have hval : ((x : ℝ) : ℂ) ^ s * ((1 / x - 1 / (x + 1) : ℝ) : ℂ) - ((x : ℝ) : ℂ) ^ (s - 2)
      = -(((x : ℝ) : ℂ) ^ s * ((1 / (x ^ 2 * (x + 1)) : ℝ) : ℂ)) := by
    rw [hpow]
    have hx1 : ((x : ℝ) : ℂ) + 1 ≠ 0 := by
      have hc : ((x : ℝ) : ℂ) + 1 = ((x + 1 : ℝ) : ℂ) := by push_cast; ring
      rw [hc]
      exact Complex.ofReal_ne_zero.2 (ne_of_gt (by linarith : (0 : ℝ) < x + 1))
    push_cast
    field_simp
    ring
  rw [hval, norm_neg, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (by positivity)]
  have hpos : (0 : ℝ) < x ^ s.re := Real.rpow_pos_of_pos hx _
  have hx3 : x ^ (3 : ℝ) = x ^ (3 : ℕ) := by
    rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [Real.rpow_sub hx, hx3, div_eq_mul_inv]
  refine mul_le_mul_of_nonneg_left ?_ hpos.le
  rw [one_mul, inv_le_inv₀ (by positivity) (by positivity)]
  nlinarith [hx]

theorem summable_cpowHarmonic {s : ℂ} (hs : s.re < 1) (N : ℕ) :
    Summable fun k : ℕ => (((N : ℝ) + 1 + (k : ℝ) : ℝ) : ℂ) ^ s
      * ((1 / ((N : ℝ) + 1 + (k : ℝ)) - 1 / ((N : ℝ) + 1 + (k : ℝ) + 1) : ℝ) : ℂ) := by
  have hq : s.re - 2 < 0 := by linarith
  have hx : ∀ k : ℕ, (0 : ℝ) < (N : ℝ) + 1 + (k : ℝ) := by
    intro k
    have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    have hN0 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
    linarith
  have hmaj : Summable fun k : ℕ => ((N : ℝ) + 1 + (k : ℝ)) ^ (s.re - 3) := by
    refine (summable_shift_rpow hq N).congr fun k => ?_
    congr 1
    ring
  have hdiff : Summable fun k : ℕ => (((N : ℝ) + 1 + (k : ℝ) : ℝ) : ℂ) ^ s
      * ((1 / ((N : ℝ) + 1 + (k : ℝ)) - 1 / ((N : ℝ) + 1 + (k : ℝ) + 1) : ℝ) : ℂ)
      - (((N : ℝ) + 1 + (k : ℝ) : ℝ) : ℂ) ^ (s - 2) :=
    Summable.of_norm (Summable.of_nonneg_of_le (fun k => norm_nonneg _)
      (fun k => norm_cpow_harmonic_term_sub_le (hx k)) hmaj)
  refine ((hdiff.add (summable_cpowShift hs N)).congr fun k => ?_)
  ring

/-- **The harmonic weight and the second-difference weight differ by `O(N^{Re s - 2})`.** -/
theorem norm_cpowHarmonicTail_sub_shift_le {s : ℂ} (hs : s.re < 1) {N : ℕ} (hN : 1 ≤ N) :
    ‖cpowHarmonicTail s N - cpowShiftTail s N‖ ≤ (N : ℝ) ^ (s.re - 2) / (2 - s.re) := by
  have hq : s.re - 2 < 0 := by linarith
  have hx : ∀ k : ℕ, (0 : ℝ) < (N : ℝ) + 1 + (k : ℝ) := by
    intro k
    have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    have hN0 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
    linarith
  have hmaj : Summable fun k : ℕ => ((N : ℝ) + 1 + (k : ℝ)) ^ (s.re - 3) := by
    refine (summable_shift_rpow hq N).congr fun k => ?_
    congr 1
    ring
  have hnorm : ∀ k : ℕ, ‖(((N : ℝ) + 1 + (k : ℝ) : ℝ) : ℂ) ^ s
      * ((1 / ((N : ℝ) + 1 + (k : ℝ)) - 1 / ((N : ℝ) + 1 + (k : ℝ) + 1) : ℝ) : ℂ)
      - (((N : ℝ) + 1 + (k : ℝ) : ℝ) : ℂ) ^ (s - 2)‖
      ≤ ((N : ℝ) + 1 + (k : ℝ)) ^ (s.re - 3) := fun k => norm_cpow_harmonic_term_sub_le (hx k)
  have hnormsum : Summable fun k : ℕ => ‖(((N : ℝ) + 1 + (k : ℝ) : ℝ) : ℂ) ^ s
      * ((1 / ((N : ℝ) + 1 + (k : ℝ)) - 1 / ((N : ℝ) + 1 + (k : ℝ) + 1) : ℝ) : ℂ)
      - (((N : ℝ) + 1 + (k : ℝ) : ℝ) : ℂ) ^ (s - 2)‖ :=
    Summable.of_nonneg_of_le (fun k => norm_nonneg _) hnorm hmaj
  rw [cpowHarmonicTail, cpowShiftTail,
    ← (summable_cpowHarmonic hs N).tsum_sub (summable_cpowShift hs N)]
  refine (norm_tsum_le_tsum_norm hnormsum).trans ?_
  refine (Summable.tsum_le_tsum hnorm hnormsum hmaj).trans ?_
  have h := tsum_shift_rpow_le (q := s.re - 2) hq hN
  have hexp : s.re - 2 - 1 = s.re - 3 := by ring
  rw [hexp] at h
  have hneg : -(s.re - 2) = 2 - s.re := by ring
  rwa [hneg] at h

/-! ## The asymptotic -/

/-- **(24.84) The sharp oscillatory tail asymptotic.**  For `Re s < 1`,
`N^{1-s}·∑_{m > N} m^s w_m → 1/(1-s)`: the oscillation rotates the constant but leaves the real
decay exponent unchanged. -/
theorem tendsto_cpowHarmonicTail {s : ℂ} (hs : s.re < 1) :
    Tendsto (fun N : ℕ => ((N : ℝ) : ℂ) ^ (1 - s) * cpowHarmonicTail s N) atTop
      (𝓝 (1 / (1 - s))) := by
  have hs1 : (1 : ℂ) - s ≠ 0 := by
    intro h
    have hval : s = 1 := by linear_combination -h
    rw [hval] at hs
    norm_num at hs
  have hmain : Tendsto (fun N : ℕ => ((N : ℝ) : ℂ) ^ (1 - s)
      * ((((N : ℝ) + 1 : ℝ) : ℂ) ^ (s - 1) / (1 - s))) atTop (𝓝 (1 / (1 - s))) := by
    have hratio : Tendsto (fun N : ℕ => (((((N : ℝ) + 1) / (N : ℝ)) : ℝ) : ℂ) ^ (s - 1)) atTop
        (𝓝 1) := by
      have hbase : Tendsto (fun N : ℕ => ((N : ℝ) + 1) / (N : ℝ)) atTop (𝓝 1) := by
        have h : Tendsto (fun N : ℕ => 1 + 1 / (N : ℝ)) atTop (𝓝 (1 + 0)) :=
          tendsto_const_nhds.add tendsto_one_div_atTop_nhds_zero_nat
        rw [add_zero] at h
        refine h.congr' ?_
        filter_upwards [eventually_ge_atTop 1] with N hN
        have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
        field_simp
      have hcont : ContinuousAt (fun y : ℝ => ((y : ℝ) : ℂ) ^ (s - 1)) 1 :=
        Complex.continuousAt_ofReal_cpow_const 1 (s - 1) (Or.inr one_ne_zero)
      have := hcont.tendsto.comp hbase
      simpa [Function.comp_def, Complex.one_cpow] using this
    have hdiv := hratio.div_const (1 - s)
    refine hdiv.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    have hNne : ((N : ℝ) : ℂ) ≠ 0 := by
      simpa using ne_of_gt hN0
    have hfact : (((N : ℝ) + 1 : ℝ) : ℂ) = ((N : ℝ) : ℂ) * ((((N : ℝ) + 1) / (N : ℝ) : ℝ) : ℂ) := by
      rw [Complex.ofReal_div]
      field_simp
    have hcancel : ((N : ℝ) : ℂ) ^ (1 - s) * ((N : ℝ) : ℂ) ^ (s - 1) = 1 := by
      rw [← Complex.cpow_add _ _ hNne, show (1 - s) + (s - 1) = 0 by ring, Complex.cpow_zero]
    rw [hfact, mul_cpow_ofReal_nonneg hN0.le (by positivity)]
    rw [show ((N : ℝ) : ℂ) ^ (1 - s)
        * (((N : ℝ) : ℂ) ^ (s - 1) * ((((N : ℝ) + 1) / (N : ℝ) : ℝ) : ℂ) ^ (s - 1) / (1 - s))
        = (((N : ℝ) : ℂ) ^ (1 - s) * ((N : ℝ) : ℂ) ^ (s - 1))
          * ((((N : ℝ) + 1) / (N : ℝ) : ℝ) : ℂ) ^ (s - 1) / (1 - s) by ring,
      hcancel, one_mul]
  have herr : Tendsto (fun N : ℕ => ((N : ℝ) : ℂ) ^ (1 - s)
      * (cpowHarmonicTail s N - (((N : ℝ) + 1 : ℝ) : ℂ) ^ (s - 1) / (1 - s))) atTop (𝓝 0) := by
    have hconst : Tendsto (fun N : ℕ => (1 + ‖s - 2‖) / (2 - s.re) * (1 / (N : ℝ))) atTop
        (𝓝 0) := by
      have := tendsto_one_div_atTop_nhds_zero_nat.const_mul ((1 + ‖s - 2‖) / (2 - s.re))
      simpa using this
    refine squeeze_zero_norm' ?_ hconst
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
    have hnormpow : ‖((N : ℝ) : ℂ) ^ (1 - s)‖ = (N : ℝ) ^ (1 - s.re) := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hN0]
      congr 1
    have hsplit : ‖cpowHarmonicTail s N - (((N : ℝ) + 1 : ℝ) : ℂ) ^ (s - 1) / (1 - s)‖
        ≤ (1 + ‖s - 2‖) / (2 - s.re) * (N : ℝ) ^ (s.re - 2) := by
      have h1 := norm_cpowHarmonicTail_sub_shift_le hs hN
      have h2 := norm_cpowShiftTail_sub_le hs hN
      have htri : ‖cpowHarmonicTail s N - (((N : ℝ) + 1 : ℝ) : ℂ) ^ (s - 1) / (1 - s)‖
          ≤ ‖cpowHarmonicTail s N - cpowShiftTail s N‖
            + ‖cpowShiftTail s N - (((N : ℝ) + 1 : ℝ) : ℂ) ^ (s - 1) / (1 - s)‖ := by
        have := norm_add_le (cpowHarmonicTail s N - cpowShiftTail s N)
          (cpowShiftTail s N - (((N : ℝ) + 1 : ℝ) : ℂ) ^ (s - 1) / (1 - s))
        simpa using this
      refine htri.trans ?_
      have hval : (N : ℝ) ^ (s.re - 2) / (2 - s.re)
          + ‖s - 2‖ / (2 - s.re) * (N : ℝ) ^ (s.re - 2)
          = (1 + ‖s - 2‖) / (2 - s.re) * (N : ℝ) ^ (s.re - 2) := by
        field_simp
      rw [← hval]
      exact add_le_add h1 h2
    rw [norm_mul, hnormpow]
    have hcalc : (N : ℝ) ^ (1 - s.re) * ((1 + ‖s - 2‖) / (2 - s.re) * (N : ℝ) ^ (s.re - 2))
        = (1 + ‖s - 2‖) / (2 - s.re) * (1 / (N : ℝ)) := by
      rw [show (1 + ‖s - 2‖) / (2 - s.re) * (N : ℝ) ^ (s.re - 2)
          = (N : ℝ) ^ (s.re - 2) * ((1 + ‖s - 2‖) / (2 - s.re)) by ring]
      rw [← mul_assoc, ← Real.rpow_add hN0]
      rw [show (1 - s.re) + (s.re - 2) = -1 by ring]
      rw [Real.rpow_neg_one]
      rw [one_div]
      ring
    calc (N : ℝ) ^ (1 - s.re)
          * ‖cpowHarmonicTail s N - (((N : ℝ) + 1 : ℝ) : ℂ) ^ (s - 1) / (1 - s)‖
        ≤ (N : ℝ) ^ (1 - s.re) * ((1 + ‖s - 2‖) / (2 - s.re) * (N : ℝ) ^ (s.re - 2)) :=
          mul_le_mul_of_nonneg_left hsplit (Real.rpow_nonneg hN0.le _)
      _ = (1 + ‖s - 2‖) / (2 - s.re) * (1 / (N : ℝ)) := hcalc
  have hsum := hmain.add herr
  rw [add_zero] at hsum
  refine hsum.congr fun N => ?_
  ring


end

end GaloisForLFunctions.HTGeometry
