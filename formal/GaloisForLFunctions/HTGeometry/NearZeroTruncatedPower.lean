import GaloisForLFunctions.HTGeometry.TruncatedPowerFourierLimit
import Mathlib.MeasureTheory.Function.L2Space

/-!
# The truncated power down to the origin

`1_{(0,a)} t^{-s}` is square integrable exactly when `Re s < 1/2` and integrable when `Re s < 1`.
This is the near-origin companion of `TruncatedPowerFourierBound`, and it is what makes Burnol's
correction kernel `E_a(u,s) = ∫_0^a e^{2πiut}t^{-s}dt` the Fourier transform of an honest `L²`
function supported in the band (arXiv:math/0203120).

## Main results

* `memLp_two_truncPower_zero`
* `integrable_truncPower_zero`
-/

namespace GaloisForLFunctions.HTGeometry

open Complex MeasureTheory Set Real

noncomputable section

theorem integrableOn_rpow_Ioo_zero {a r : ℝ} (hr : -1 < r) :
    IntegrableOn (fun t : ℝ => t ^ r) (Set.Ioo (0 : ℝ) a) volume := by
  have h := intervalIntegral.intervalIntegrable_rpow' (a := (0 : ℝ)) (b := a) hr
  rcases le_total (0 : ℝ) a with hle | hle
  · rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hle] at h
    exact h.mono_set Set.Ioo_subset_Ioc_self
  · rw [Set.Ioo_eq_empty (not_lt.2 hle)]
    exact integrableOn_empty

theorem memLp_two_truncPower_zero {a : ℝ} {s : ℂ} (hs : s.re < 1 / 2) :
    MemLp (truncPower 0 a s) 2 volume := by
  rw [truncPower, memLp_indicator_iff_restrict measurableSet_Ioo]
  have hmeas : AEStronglyMeasurable (fun t : ℝ => (t : ℂ) ^ (-s))
      ((volume : Measure ℝ).restrict (Set.Ioo (0 : ℝ) a)) := by
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioo
    intro t ht
    exact (Complex.continuousAt_ofReal_cpow_const t (-s) (Or.inr ht.1.ne')).continuousWithinAt
  rw [memLp_two_iff_integrable_sq_norm hmeas]
  have hbase : IntegrableOn (fun t : ℝ => t ^ (-(2 * s.re))) (Set.Ioo (0 : ℝ) a) volume := by
    refine integrableOn_rpow_Ioo_zero ?_
    linarith
  refine hbase.congr_fun ?_ measurableSet_Ioo
  intro t ht
  have htpos : 0 < t := ht.1
  show t ^ (-(2 * s.re)) = ‖((t : ℝ) : ℂ) ^ (-s)‖ ^ 2
  rw [Complex.norm_cpow_eq_rpow_re_of_pos htpos, Complex.neg_re, ← Real.rpow_natCast _ 2,
    ← Real.rpow_mul htpos.le]
  congr 1
  push_cast
  ring

theorem integrable_truncPower_zero {a : ℝ} (ha : 0 ≤ a) {s : ℂ} (hs : s.re < 1) :
    Integrable (truncPower 0 a s) volume := by
  rw [truncPower, integrable_indicator_iff measurableSet_Ioo]
  have h := intervalIntegrable_powerOsc (le_refl (0 : ℝ)) ha hs 0
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le ha] at h
  have h' : IntegrableOn (fun t : ℝ => (t : ℂ) ^ (-s)) (Set.Ioc (0 : ℝ) a) volume := by
    refine h.congr_fun ?_ measurableSet_Ioc
    intro t _
    simp
  exact h'.mono_set Set.Ioo_subset_Ioc_self

end

end GaloisForLFunctions.HTGeometry
