import Mathlib

/-!
# Sine transforms of decreasing functions

If `f` is continuous, integrable on `(0, ∞)` and strictly decreasing on `[0, ∞)`, then
`∫₀^∞ f(t) sin(yt) dt > 0` for every `y > 0`.  Over each period `[kP, (k+1)P]`, `P = 2π/y`, the
second half-period is the first shifted by `P/2` with the sign of the sine reversed, so the period
integral is `∫_{kP}^{kP+P/2} (f(t) - f(t + P/2)) sin(yt) dt ≥ 0`, strictly positive for `k = 0`;
the partial sums increase to the improper integral.
-/

open Set MeasureTheory Filter Topology

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- Over a full period the sine transform folds onto the first half-period:
`∫_a^{a+2π/y} f(t) sin(yt) dt = ∫_a^{a+π/y} (f(t) - f(t + π/y)) sin(yt) dt`. -/
theorem integral_period_mul_sin_eq {f : ℝ → ℝ} (hf : Continuous f) {y : ℝ} (hy : 0 < y)
    (a : ℝ) :
    ∫ t in a..a + 2 * Real.pi / y, f t * Real.sin (y * t) =
      ∫ t in a..a + Real.pi / y, (f t - f (t + Real.pi / y)) * Real.sin (y * t) := by
  set h := Real.pi / y with hh
  have hcont : Continuous fun t => f t * Real.sin (y * t) := by fun_prop
  have e : ∀ t, f (t + h) * Real.sin (y * (t + h)) = -(f (t + h) * Real.sin (y * t)) := by
    intro t
    rw [show y * (t + h) = y * t + Real.pi by rw [hh]; field_simp, Real.sin_add_pi]
    ring
  rw [show a + 2 * Real.pi / y = a + h + h by rw [hh]; ring,
    ← intervalIntegral.integral_add_adjacent_intervals (b := a + h)
      (hcont.intervalIntegrable _ _) (hcont.intervalIntegrable _ _),
    ← intervalIntegral.integral_comp_add_right (a := a) (b := a + h)
      (fun t => f t * Real.sin (y * t)) h]
  simp only [e, intervalIntegral.integral_neg]
  rw [← sub_eq_add_neg, ← intervalIntegral.integral_sub (hcont.intervalIntegrable _ _)
    ((by fun_prop : Continuous fun t => f (t + h) * Real.sin (y * t)).intervalIntegrable _ _)]
  refine intervalIntegral.integral_congr fun t _ => ?_
  ring

/-- **Positivity of sine transforms of decreasing functions.** If `f` is continuous, integrable on
`(0, ∞)` and strictly decreasing on `[0, ∞)`, then `∫₀^∞ f(t) sin(yt) dt > 0` for `y > 0`. -/
theorem integral_mul_sin_pos_of_strictAntiOn {f : ℝ → ℝ} (hf : Continuous f)
    (hanti : StrictAntiOn f (Ici 0)) (hint : IntegrableOn f (Ioi 0)) {y : ℝ} (hy : 0 < y) :
    0 < ∫ t in Ioi 0, f t * Real.sin (y * t) := by
  set P := 2 * Real.pi / y with hPdef
  set h := Real.pi / y with hhdef
  have hP : 0 < P := by positivity
  have hh : 0 < h := by positivity
  have hcont : Continuous fun t => f t * Real.sin (y * t) := by fun_prop
  have hint' : IntegrableOn (fun t => f t * Real.sin (y * t)) (Ioi 0) := by
    refine hint.norm.mono' hcont.aestronglyMeasurable (Eventually.of_forall fun t => ?_)
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_sin_le_one _)
  set I : ℕ → ℝ := fun k => ∫ t in (k * P)..((k + 1) * P), f t * Real.sin (y * t)
  have hdrop : ∀ t, 0 ≤ t → 0 < f t - f (t + h) := fun t ht =>
    sub_pos.mpr (hanti (mem_Ici.mpr ht) (mem_Ici.mpr (by linarith)) (by linarith))
  have hIk : ∀ k, 0 ≤ I k := by
    intro k
    simp only [I]
    rw [show ((k : ℝ) + 1) * P = k * P + 2 * Real.pi / y by rw [hPdef]; ring,
      integral_period_mul_sin_eq hf hy]
    refine intervalIntegral.integral_nonneg (by linarith) fun t ht => mul_nonneg
      (hdrop t (le_trans (by positivity) ht.1)).le ?_
    rw [← Real.sin_sub_nat_mul_two_pi (y * t) k]
    have h1 : (k : ℝ) * P ≤ t := ht.1
    have h2 : t ≤ k * P + h := ht.2
    have hyP : y * P = 2 * Real.pi := by rw [hPdef]; field_simp
    have hyh : y * h = Real.pi := by rw [hhdef]; field_simp
    apply Real.sin_nonneg_of_nonneg_of_le_pi
    · have := mul_le_mul_of_nonneg_left h1 hy.le
      nlinarith
    · have := mul_le_mul_of_nonneg_left h2 hy.le
      nlinarith
  have hI0 : 0 < I 0 := by
    simp only [I, Nat.cast_zero, zero_mul, zero_add, one_mul]
    rw [show P = 0 + 2 * Real.pi / y by rw [hPdef]; ring, integral_period_mul_sin_eq hf hy,
      zero_add]
    refine intervalIntegral.intervalIntegral_pos_of_pos_on
      ((by fun_prop : Continuous fun t => (f t - f (t + Real.pi / y)) *
        Real.sin (y * t)).intervalIntegrable _ _) (fun t ht => mul_pos (hdrop t ht.1.le)
          (Real.sin_pos_of_pos_of_lt_pi (mul_pos hy ht.1) ?_)) hh
    have := mul_lt_mul_of_pos_left ht.2 hy
    rwa [mul_div_cancel₀ _ hy.ne'] at this
  have hsum : ∀ n : ℕ, ∫ t in (0 : ℝ)..(n * P), f t * Real.sin (y * t) =
      ∑ k ∈ Finset.range n, I k := by
    intro n
    have := intervalIntegral.sum_integral_adjacent_intervals (μ := volume)
      (a := fun k : ℕ => (k : ℝ) * P) (n := n) (fun k _ => hcont.intervalIntegrable _ _)
    simp only [Nat.cast_zero, zero_mul, Nat.cast_succ] at this
    exact this.symm
  have hlim := intervalIntegral_tendsto_integral_Ioi 0 hint'
    (tendsto_natCast_atTop_atTop.atTop_mul_const hP)
  refine lt_of_lt_of_le hI0 (ge_of_tendsto hlim ?_)
  filter_upwards [eventually_ge_atTop 1] with n hn
  rw [hsum n]
  calc I 0 = ∑ k ∈ Finset.range 1, I k := by simp
    _ ≤ ∑ k ∈ Finset.range n, I k :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hn) fun k _ _ => hIk k

end GaloisForLFunctions.HTGeometry
