import GaloisForLFunctions.TransMetzlerWeilPositivity.FixedOverlapHasLogarithmicDivisorRows
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.BoundaryVanishingControlsTheTouchingAutocorrelation

/-!
# The actual successor fiber has an open support threshold

The explicit plateau has positive autocorrelation exactly for lags of absolute
value less than one. Its endpoint values vanish. Thus the actual successor
fiber becomes positive strictly after `N log(1+1/N)`, a threshold below one
at every finite horizon and tending to one with the horizon.
-/

noncomputable section

set_option autoImplicit false

open MeasureTheory Filter Topology

namespace GaloisForLFunctions.TransMetzlerWeilPositivity

open SpacingScaleHarmonicAnalysis CriticalArithmeticCorrelationTheory
  RenormalizedArithmeticPotentialTheory

/-- The endpoint autocorrelation vanishes as well as the exterior autocorrelation. -/
theorem transMetzlerProfile_bumpCorr_eq_zero {t : ℝ} (ht : 1 ≤ |t|) :
    bumpCorr transMetzlerProfile t = 0 := by
  rcases ht.eq_or_lt with heq | hlt
  · have h := abs_bumpAutocorr_le_endpoint_square
      contDiff_transMetzlerProfile.continuous
      (fun u hu => transMetzlerProfile_eq_zero hu) zero_le_one
      (by norm_num : (0 : ℝ) ≤ 8000)
      (fun x y => abs_transMetzlerProfile_sub_le y x) (z := t)
    change |bumpCorr transMetzlerProfile t| ≤
      ((8000 : ℝ) ^ 2 * 1 / 4) * (1 - |t|) ^ 2 at h
    rw [← heq, sub_self, zero_pow (by norm_num : (2 : ℕ) ≠ 0), mul_zero] at h
    exact abs_eq_zero.mp (le_antisymm h (abs_nonneg _))
  · exact bumpCorr_eq_zero (fun u hu => transMetzlerProfile_eq_zero hu) hlt

/-- The autocorrelation's positive set is the exact open difference-support interval. -/
theorem transMetzlerProfile_bumpCorr_pos_iff (t : ℝ) :
    0 < bumpCorr transMetzlerProfile t ↔ |t| < 1 := by
  constructor
  · intro h
    by_contra ht
    rw [transMetzlerProfile_bumpCorr_eq_zero (not_lt.mp ht)] at h
    exact (lt_irrefl 0) h
  · exact transMetzlerProfile_bumpCorr_pos

/-- At or below its exact support threshold, the actual successor fiber is zero. -/
theorem plateauSuccessorFiber_eq_zero_of_le {c : ℝ} (hc : 0 < c) {N : ℕ} (hN : 1 ≤ N)
    (hcut : c ≤ firstExteriorOverlap N) : plateauSuccessorFiber c N = 0 := by
  have hlag : 1 ≤ |firstExteriorOverlap N / c| := by
    rw [abs_of_pos (div_pos (firstExteriorOverlap_pos hN) hc)]
    exact (one_le_div hc).mpr hcut
  rw [plateauSuccessorFiber_eq hc hN, transMetzlerProfile_bumpCorr_eq_zero hlag,
    mul_zero, zero_div]

/-- Geometric eligibility has a closed endpoint; a positive plateau fiber has an open one. -/
theorem plateauSuccessorFiber_pos_iff {c : ℝ} (hc : 0 < c) {N : ℕ} (hN : 1 ≤ N) :
    0 < plateauSuccessorFiber c N ↔ firstExteriorOverlap N < c := by
  constructor
  · intro h
    by_contra hcut
    rw [plateauSuccessorFiber_eq_zero_of_le hc hN (not_lt.mp hcut)] at h
    exact (lt_irrefl 0) h
  · intro hcut
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
    have hsucc : (1 : ℝ) < (N + 1 : ℕ) := by exact_mod_cast (show 1 < N + 1 by omega)
    have hcorr : 0 < bumpCorr transMetzlerProfile (firstExteriorOverlap N / c) := by
      apply transMetzlerProfile_bumpCorr_pos
      rw [abs_of_pos (div_pos (firstExteriorOverlap_pos hN) hc)]
      exact (div_lt_one hc).mpr hcut
    rw [plateauSuccessorFiber_eq hc hN]
    exact div_pos (mul_pos (mul_pos
      (Real.sqrt_pos.mpr (div_pos hN0 (zero_lt_one.trans hsucc)))
      (Real.log_pos hsucc)) hcorr) integral_transMetzlerProfile_sq_pos

/-- Touching carries a positive successor fiber at every finite positive horizon. -/
theorem plateauSuccessorFiber_one_pos {N : ℕ} (hN : 1 ≤ N) :
    0 < plateauSuccessorFiber 1 N :=
  (plateauSuccessorFiber_pos_iff zero_lt_one hN).mpr (firstExteriorOverlap_lt_one hN)

/-- Every fixed overlap below one eventually has an exactly zero successor fiber. -/
theorem eventually_plateauSuccessorFiber_eq_zero {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1) :
    ∀ᶠ N : ℕ in atTop, plateauSuccessorFiber c N = 0 := by
  filter_upwards [tendsto_firstExteriorOverlap.eventually (lt_mem_nhds hc1),
    eventually_ge_atTop (1 : ℕ)] with N hcut hN
  exact plateauSuccessorFiber_eq_zero_of_le hc0 hN hcut.le

end GaloisForLFunctions.TransMetzlerWeilPositivity

#print axioms GaloisForLFunctions.TransMetzlerWeilPositivity.transMetzlerProfile_bumpCorr_pos_iff
#print axioms GaloisForLFunctions.TransMetzlerWeilPositivity.plateauSuccessorFiber_pos_iff
#print axioms GaloisForLFunctions.TransMetzlerWeilPositivity.plateauSuccessorFiber_one_pos
#print axioms GaloisForLFunctions.TransMetzlerWeilPositivity.eventually_plateauSuccessorFiber_eq_zero
