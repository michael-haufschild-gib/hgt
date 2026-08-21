import GaloisForLFunctions.RHTower.ConnesArchPeriodization
import GaloisForLFunctions.RHTower.ConnesLatticeRapidDecay

/-!
# Rapid decay of the punctured periodization

Appendix I Lemma 2 of

  A. Connes, *Trace formula in noncommutative geometry and the zeros of the Riemann zeta
  function*, arXiv:math/9811068:

  `|E(f)(g)| ≤ c e^{-n |log |g||}` for every `n`.

At the archimedean place the two ends are handled separately and by the same estimate: for
`|g| → ∞` the punctured lattice sum of a Schwartz function decays faster than every power
(App I (46)), and for `|g| → 0` the reflection `E(f)(g) = E(f̂)(1/g)` of (38) transports that
statement to the other end.  Together they are the two-sided rapid decay of Lemma 2.
-/

open MeasureTheory Filter Topology
open scoped SchwartzMap FourierTransform

namespace GaloisForLFunctions.RHTower

noncomputable section

theorem norm_connesArchPunctured_le (f : SchwartzMap ℝ ℂ) {a : ℝ} (ha : a ≠ 0) :
    ‖connesArchPunctured f a‖ ≤ connesLatticeSum f a := by
  rw [connesArchPunctured, connesLatticeSum]
  refine le_trans (norm_tsum_le_tsum_norm ?_) (le_of_eq ?_)
  · refine (connes_latticeSum_summable f ha).congr fun n => ?_
    by_cases h : n = 0 <;> simp [h]
  · refine tsum_congr fun n => ?_
    by_cases h : n = 0 <;> simp [h]

/-- **Appendix I Lemma 2, the large end.**  The punctured periodization decays faster than every
power of the module. -/
theorem connes_archPeriodization_rapidDecay (f : SchwartzMap ℝ ℂ) (k : ℕ) :
    Tendsto (fun a : ℝ => a ^ k * ‖connesArchPeriodization f a‖) atTop (𝓝 0) := by
  have hmaj : Tendsto (fun a : ℝ => a ^ (k + 1) * connesLatticeSum f a) atTop (𝓝 0) := by
    have h := connes_latticeSum_rapidDecay f (c := (1 : ℝ)) one_pos (k + 1)
    simpa using h
  refine squeeze_zero' ?_ ?_ hmaj
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with a ha
    positivity
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with a ha
    have ha0 : (0 : ℝ) < a := lt_of_lt_of_le zero_lt_one ha
    have hane : a ≠ 0 := ne_of_gt ha0
    have hsqrt : Real.sqrt a ≤ a := by
      have h1 : Real.sqrt a ≤ Real.sqrt (a * a) := Real.sqrt_le_sqrt (by nlinarith)
      rwa [Real.sqrt_mul_self ha0.le] at h1
    have hnorm : ‖connesArchPeriodization f a‖
        = Real.sqrt a * ‖connesArchPunctured f a‖ := by
      rw [connesArchPeriodization, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.sqrt_nonneg a)]
    have hpunc : ‖connesArchPunctured f a‖ ≤ connesLatticeSum f a :=
      norm_connesArchPunctured_le f hane
    have hL0 : 0 ≤ connesLatticeSum f a := connes_latticeSum_nonneg f a
    calc a ^ k * ‖connesArchPeriodization f a‖
        = a ^ k * (Real.sqrt a * ‖connesArchPunctured f a‖) := by rw [hnorm]
      _ ≤ a ^ k * (a * connesLatticeSum f a) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact mul_le_mul hsqrt hpunc (norm_nonneg _) ha0.le
      _ = a ^ (k + 1) * connesLatticeSum f a := by ring

/-- **Appendix I Lemma 2, the small end.**  On `𝒮(ℝ)_0` the reflection (38) transports the rapid
decay to `|g| → 0`. -/
theorem connes_archPeriodization_rapidDecay_zero (f : SchwartzMap ℝ ℂ) (h0 : f 0 = 0)
    (hint : (∫ x : ℝ, f x) = 0) (k : ℕ) :
    Tendsto (fun b : ℝ => b ^ k * ‖connesArchPeriodization f b⁻¹‖) atTop (𝓝 0) := by
  have hmain := connes_archPeriodization_rapidDecay (𝓕 f) k
  refine hmain.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with b hb
  have hbinv : (0 : ℝ) < b⁻¹ := inv_pos.mpr hb
  have hrefl := connes_archPeriodization_reflect f h0 hint hbinv
  rw [inv_inv] at hrefl
  rw [← hrefl]

end

end GaloisForLFunctions.RHTower
