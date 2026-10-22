import GaloisForLFunctions.RHTower.CCM.CCMThetaArithmeticCorrelation

/-!
# The full theta prime pairing equals the finite CCM prime source

Compact support of the actual complex source removes exactly those prime
translations outside the aperture. The normalization is the same square-root
von Mangoldt weight at every surviving prime power.
-/

noncomputable section

open MeasureTheory Filter Set
open scoped SchwartzMap ComplexConjugate BigOperators

namespace RHTower

open ThetaSourceWard

theorem theta_primeCoefficient_re_eq_criticalMellinAtomWeight (n : ℕ) :
    (primeCoefficient n).re = criticalMellinAtomWeight n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [primeCoefficient, criticalMellinAtomWeight]
  rw [primeCoefficient_eq, Complex.ofReal_re,
    criticalMellinAtomWeight_eq_primePairWeight (Nat.pos_of_ne_zero hn)]
  unfold GaloisForLFunctions.HTGeometry.primePairWeight
  ring

theorem thetaPrimeScalingCrossDensity_ccmProfile {a : SuzukiPositiveAperture}
    (u : CCMComplexSmoothInteriorSource a) (n : ℕ) (x : ℝ) :
    thetaPrimeScalingCrossDensity thetaCuspTiltSource thetaCuspTiltSource
        (ccmThetaGroundProfile u).toBoundedContinuousFunction (n, x) =
      criticalMellinAtomWeight n * (u (x + Real.log n) * conj (u x)).re := by
  rw [← theta_primeCoefficient_re_eq_criticalMellinAtomWeight]
  conv_rhs => rw [← ccmThetaGroundProfile_reconstruct u (x + Real.log n),
    ← ccmThetaGroundProfile_reconstruct u x]
  simp only [thetaPrimeScalingCrossDensity, thetaPrimeLinkDensity, primeShiftActionDensity,
    thetaCuspTiltSource_k, SchwartzMap.toBoundedContinuousFunction_apply, primeCoefficient_eq,
    map_mul, Complex.conj_ofReal, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_mul, sub_zero, add_zero]
  ring

/-- No prime powers are dropped until the source support makes their pairing exactly zero. -/
theorem thetaPrimeScalingCross_ccmProfile {a : SuzukiPositiveAperture}
    (u : CCMComplexSmoothInteriorSource a) :
    thetaPrimeScalingCross thetaCuspTiltSource thetaCuspTiltSource
        (ccmThetaGroundProfile u).toBoundedContinuousFunction =
      ∑ n ∈ Finset.Icc 2 (Nat.floor (Real.exp (2 * a.1))),
        criticalMellinAtomWeight n * (ccmComplexSmoothCrossCorrelation u u (Real.log n)).re := by
  have hi := integrable_thetaPrimeScalingCrossDensity thetaCuspTiltSource thetaCuspTiltSource
    (ccmThetaGroundProfile u).toBoundedContinuousFunction
  rw [thetaPrimeScalingCross, integral_prod _ hi, integral_countable hi.integral_prod_left]
  simp only [count_real_singleton, one_smul]
  simp_rw [thetaPrimeScalingCrossDensity_ccmProfile, integral_const_mul,
    integral_ccmTheta_source_cross_re]
  apply tsum_eq_sum
  intro n hn
  rcases eq_or_ne n 0 with rfl | hn0
  · simp [criticalMellinAtomWeight]
  rcases eq_or_ne n 1 with rfl | hn1
  · simp [criticalMellinAtomWeight]
  have hn2 : 2 ≤ n := by omega
  have hfloor : Nat.floor (Real.exp (2 * a.1)) < n := by
    simp only [Finset.mem_Icc, hn2, true_and, not_le] at hn
    exact hn
  have hexp : Real.exp (2 * a.1) < (n : ℝ) :=
    (Nat.floor_lt (Real.exp_pos _).le).mp hfloor
  have hlog : 2 * a.1 < Real.log n :=
    (Real.lt_log_iff_exp_lt (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn0))).mpr hexp
  rw [ccmComplexSmoothCrossCorrelation_eq_zero_of_two_aperture_le_abs u u
    (hlog.le.trans (le_abs_self _)), Complex.zero_re, mul_zero]

/-- Both conjugate prime channels in CCM equal twice the theta prime cross pairing. -/
theorem thetaPrimeScalingCross_ccmProfile_twoSided {a : SuzukiPositiveAperture}
    (u : CCMComplexSmoothInteriorSource a) :
    2 * thetaPrimeScalingCross thetaCuspTiltSource thetaCuspTiltSource
        (ccmThetaGroundProfile u).toBoundedContinuousFunction =
      (∑ n ∈ Finset.Icc 2 (Nat.floor (Real.exp (2 * a.1))),
        (criticalMellinAtomWeight n : ℂ) *
          (ccmComplexSmoothCrossCorrelation u u (Real.log n) +
            ccmComplexSmoothCrossCorrelation u u (-Real.log n))).re := by
  rw [thetaPrimeScalingCross_ccmProfile, Finset.mul_sum]
  rw [← Complex.reCLM_apply, map_sum]
  simp only [Complex.reCLM_apply, Complex.re_ofReal_mul, Complex.add_re, ccmTheta_correlation_neg_re]
  apply Finset.sum_congr rfl
  intro n hn
  ring

end RHTower
