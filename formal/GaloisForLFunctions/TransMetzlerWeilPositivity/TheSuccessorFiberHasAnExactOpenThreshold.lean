import GaloisForLFunctions.TransMetzlerWeilPositivity.FixedOverlapHasLogarithmicDivisorRows
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.BoundaryVanishingControlsTheTouchingAutocorrelation

/-!
# The actual successor fiber has an open support threshold

The explicit plateau has positive autocorrelation exactly for lags of absolute
value less than one. Its endpoint values vanish. Thus the actual successor
fiber becomes positive strictly after `N log(1+1/N)`, a threshold below one
at every finite horizon and tending to one with the horizon. At touching,
the positive fiber is `O(log N/N²)` and tends to zero.
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

/-- Endpoint vanishing gives a quantitative touching bound despite finite-horizon positivity. -/
theorem plateauSuccessorFiber_one_le {N : ℕ} (hN : 1 ≤ N) :
    plateauSuccessorFiber 1 N ≤
      ((8000 : ℝ) ^ 2 / 4) * (Real.log (N + 1 : ℕ) / (N : ℝ) ^ 2) /
        (∫ u, transMetzlerProfile u ^ 2) := by
  have ht0 := firstExteriorOverlap_pos hN
  have ht1 := firstExteriorOverlap_lt_one hN
  have hδ : 1 - firstExteriorOverlap N ≤ 1 / (N : ℝ) := by
    linarith only [one_sub_inv_lt_firstExteriorOverlap hN]
  have hsq := pow_le_pow_left₀ (sub_nonneg.mpr ht1.le) hδ 2
  have hraw := abs_bumpAutocorr_le_endpoint_square
    contDiff_transMetzlerProfile.continuous
    (fun u hu => transMetzlerProfile_eq_zero hu) zero_le_one
    (by norm_num : (0 : ℝ) ≤ 8000)
    (fun x y => abs_transMetzlerProfile_sub_le y x) (z := firstExteriorOverlap N)
  change |bumpCorr transMetzlerProfile (firstExteriorOverlap N)| ≤
    ((8000 : ℝ) ^ 2 * 1 / 4) * (1 - |firstExteriorOverlap N|) ^ 2 at hraw
  rw [mul_one, abs_of_pos ht0] at hraw
  have hcorr : bumpCorr transMetzlerProfile (firstExteriorOverlap N) ≤
      ((8000 : ℝ) ^ 2 / 4) * (1 / (N : ℝ)) ^ 2 :=
    (le_abs_self _).trans (hraw.trans (mul_le_mul_of_nonneg_left hsq (by positivity)))
  have hcorr0 : 0 ≤ bumpCorr transMetzlerProfile (firstExteriorOverlap N) :=
    (transMetzlerProfile_bumpCorr_pos (by rwa [abs_of_pos ht0])).le
  have hratio : (N : ℝ) / (N + 1 : ℕ) ≤ 1 :=
    (div_le_one (by positivity)).mpr (by exact_mod_cast Nat.le_succ N)
  have hsqrt : Real.sqrt ((N : ℝ) / (N + 1 : ℕ)) ≤ 1 := by
    have hs := Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (N : ℝ) / (N + 1 : ℕ))
    nlinarith only [hs, hratio, Real.sqrt_nonneg ((N : ℝ) / (N + 1 : ℕ))]
  have hlog := Real.log_natCast_nonneg (N + 1)
  have hM := integral_transMetzlerProfile_sq_pos
  rw [plateauSuccessorFiber_eq zero_lt_one hN]
  simp only [div_one]
  calc
    _ ≤ (Real.log (N + 1 : ℕ) * bumpCorr transMetzlerProfile (firstExteriorOverlap N)) /
        (∫ u, transMetzlerProfile u ^ 2) := by
      apply div_le_div_of_nonneg_right _ hM.le
      calc
        _ = Real.sqrt ((N : ℝ) / (N + 1 : ℕ)) *
            (Real.log (N + 1 : ℕ) * bumpCorr transMetzlerProfile (firstExteriorOverlap N)) := by ring
        _ ≤ 1 * (Real.log (N + 1 : ℕ) * bumpCorr transMetzlerProfile (firstExteriorOverlap N)) :=
          mul_le_mul_of_nonneg_right hsqrt (mul_nonneg hlog hcorr0)
        _ = _ := one_mul _
    _ ≤ (Real.log (N + 1 : ℕ) * (((8000 : ℝ) ^ 2 / 4) * (1 / (N : ℝ)) ^ 2)) /
        (∫ u, transMetzlerProfile u ^ 2) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hcorr hlog) hM.le
    _ = _ := by
      rw [div_pow, one_pow]
      ring

/-- A simpler inverse-horizon bound suffices to pass the touching fiber to zero. -/
theorem plateauSuccessorFiber_one_le_inv {N : ℕ} (hN : 1 ≤ N) :
    plateauSuccessorFiber 1 N ≤
      ((8000 : ℝ) ^ 2 / (4 * ∫ u, transMetzlerProfile u ^ 2)) / N := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hsucc : (1 : ℝ) < (N + 1 : ℕ) := by exact_mod_cast (show 1 < N + 1 by omega)
  have hlog : Real.log (N + 1 : ℕ) ≤ (N : ℝ) := by
    have h := Real.log_lt_sub_one_of_pos (zero_lt_one.trans hsucc) (ne_of_gt hsucc)
    simpa only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right] using h.le
  have hfrac : Real.log (N + 1 : ℕ) / (N : ℝ) ^ 2 ≤ 1 / (N : ℝ) := by
    calc
      _ ≤ (N : ℝ) / (N : ℝ) ^ 2 := div_le_div_of_nonneg_right hlog (sq_nonneg _)
      _ = _ := by field_simp [hN0.ne']
  have hM := integral_transMetzlerProfile_sq_pos
  calc
    _ ≤ ((8000 : ℝ) ^ 2 / 4) * (Real.log (N + 1 : ℕ) / (N : ℝ) ^ 2) /
        (∫ u, transMetzlerProfile u ^ 2) := plateauSuccessorFiber_one_le hN
    _ ≤ ((8000 : ℝ) ^ 2 / 4) * (1 / (N : ℝ)) / (∫ u, transMetzlerProfile u ^ 2) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hfrac (by positivity)) hM.le
    _ = _ := by field_simp [hN0.ne', hM.ne']

/-- At touching the successor fiber is positive at every finite horizon and tends to zero. -/
theorem tendsto_plateauSuccessorFiber_one :
    Tendsto (plateauSuccessorFiber 1) atTop (𝓝 0) := by
  have hlim : Tendsto (fun N : ℕ =>
      ((8000 : ℝ) ^ 2 / (4 * ∫ u, transMetzlerProfile u ^ 2)) / N) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  refine squeeze_zero' ?_ ?_ hlim
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
    exact (plateauSuccessorFiber_one_pos hN).le
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
    exact plateauSuccessorFiber_one_le_inv hN

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
#print axioms GaloisForLFunctions.TransMetzlerWeilPositivity.plateauSuccessorFiber_one_le
#print axioms GaloisForLFunctions.TransMetzlerWeilPositivity.tendsto_plateauSuccessorFiber_one
#print axioms GaloisForLFunctions.TransMetzlerWeilPositivity.eventually_plateauSuccessorFiber_eq_zero
