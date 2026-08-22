import GaloisForLFunctions.HTGeometry.TruncatedPowerFourierBound
import GaloisForLFunctions.HTGeometry.PowerFourierGamma

/-!
# The limit of the conjugated Fourier transform of a truncated power

Burnol's kernel is `C_a(u, s) = ∫_a^∞ e^{2πiut} t^{-s} dt`, the `T → ∞` limit of the conjugate of
`𝓕(1_{(a,T)} t^{-s̄})(u)`.  Splitting `∫_a^∞ = ∫_0^∞ − ∫_0^a` and using the Fourier–Mellin
evaluation of a power identifies it as

`C_a(u,s) = Γ(1-s)(-2πui)^{s-1} − ∫_0^a e^{2πiut} t^{-s} dt`,

whose first term carries the whole `χ`-factor and whose second term is entire in `s` on `Re s < 1`.

## Main results

* `conj_fourierIntegral_truncPower`
* `tendsto_conj_fourierIntegral_truncPower`
-/

namespace GaloisForLFunctions.HTGeometry

open Complex MeasureTheory Set Filter Topology intervalIntegral FourierTransform

noncomputable section

/-- The oscillating power is interval integrable on any interval in `[0, ∞)`, since `Re s < 1`. -/
theorem intervalIntegrable_powerOsc {b c : ℝ} (hb : 0 ≤ b) (hbc : b ≤ c) {s : ℂ} (hs1 : s.re < 1)
    (L : ℝ) :
    IntervalIntegrable (fun t : ℝ => (t : ℂ) ^ (-s) * Complex.exp ((t * L : ℝ) * Complex.I))
      volume b c := by
  have hIoc : Set.uIoc b c = Set.Ioc b c := Set.uIoc_of_le hbc
  have hdom : IntervalIntegrable (fun t : ℝ => t ^ (-s.re)) volume b c := by
    refine intervalIntegral.intervalIntegrable_rpow' ?_
    linarith
  refine hdom.mono_fun ?_ ?_
  · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_uIoc
    rw [hIoc]
    refine ContinuousOn.mul ?_ (by fun_prop)
    intro t ht
    refine ContinuousAt.continuousWithinAt ?_
    exact Complex.continuousAt_ofReal_cpow_const t (-s)
      (Or.inr (lt_of_le_of_lt hb ht.1).ne')
  · filter_upwards [ae_restrict_mem measurableSet_uIoc] with t ht
    rw [hIoc] at ht
    have htpos : 0 < t := lt_of_le_of_lt hb ht.1
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos htpos, Complex.neg_re, Complex.norm_exp]
    have hphase : (((t * L : ℝ) : ℂ) * Complex.I).re = 0 := by simp
    rw [hphase, Real.exp_zero, mul_one, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg htpos.le _)]

/-- The conjugate of the Fourier transform of a truncated power reverses the oscillation. -/
theorem conj_fourierIntegral_truncPower {a T : ℝ} (ha : 0 ≤ a) (haT : a ≤ T) (s : ℂ) (u : ℝ) :
    (starRingEnd ℂ) (𝓕 (truncPower a T ((starRingEnd ℂ) s)) u)
      = ∫ t in a..T, (t : ℂ) ^ (-s) * Complex.exp ((t * (2 * Real.pi * u) : ℝ) * Complex.I) := by
  rw [fourierIntegral_truncPower haT ((starRingEnd ℂ) s) u, oscPowerIntegral,
    intervalIntegral.integral_of_le haT, intervalIntegral.integral_of_le haT,
    ← _root_.integral_conj]
  refine setIntegral_congr_fun measurableSet_Ioc fun t ht => ?_
  have htpos : 0 < t := lt_of_le_of_lt ha ht.1
  rw [map_mul, conj_cpow_ofReal_base htpos, ← Complex.exp_conj, map_mul, Complex.conj_ofReal,
    Complex.conj_I]
  rw [mul_comm]
  congr 2
  · simp
  · push_cast
    ring

/-- **The limit that defines Burnol's kernel.** -/
theorem tendsto_conj_fourierIntegral_truncPower {a : ℝ} (ha : 0 < a) {s : ℂ}
    (hs0 : 0 < s.re) (hs1 : s.re < 1) {u : ℝ} (hu : u ≠ 0) :
    Tendsto (fun T : ℝ =>
        ∫ t in a..T, (t : ℂ) ^ (-s) * Complex.exp ((t * (2 * Real.pi * u) : ℝ) * Complex.I))
      atTop
      (𝓝 (Complex.Gamma (1 - s) * (-((((2 * Real.pi * u : ℝ)) : ℂ) * Complex.I)) ^ (s - 1)
            - ∫ t in (0 : ℝ)..a,
                (t : ℂ) ^ (-s) * Complex.exp ((t * (2 * Real.pi * u) : ℝ) * Complex.I))) := by
  have hL : (2 * Real.pi * u) ≠ 0 := by
    have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
    exact mul_ne_zero hpi.ne' hu
  have hbase := tendsto_integral_powerOsc_ne hs0 hs1 hL
  have hsub := hbase.sub (tendsto_const_nhds
    (x := ∫ t in (0 : ℝ)..a, (t : ℂ) ^ (-s) * Complex.exp ((t * (2 * Real.pi * u) : ℝ) * Complex.I))
    (f := (atTop : Filter ℝ)))
  refine hsub.congr' ?_
  filter_upwards [eventually_ge_atTop a] with T hT
  have h0a := intervalIntegrable_powerOsc (le_refl (0:ℝ)) ha.le hs1 (2 * Real.pi * u)
  have haT := intervalIntegrable_powerOsc ha.le hT hs1 (2 * Real.pi * u)
  have hadd := intervalIntegral.integral_add_adjacent_intervals h0a haT
  rw [← hadd]
  ring

end

end GaloisForLFunctions.HTGeometry
