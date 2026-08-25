import GaloisForLFunctions.RHTower.ArithmeticThreeChartStableBoundary
import GaloisForLFunctions.RHTower.MobiusThetaCofinalMultiplicityAnomaly
import GaloisForLFunctions.RHTower.RiemannDerivedPolarizationLaw

/-!
# Stable-class central-anomaly transgression

The arithmetic mixed-rate stable class, weight-one Hodge curvature, and normalized cofinal
paracyclic anomaly are one object in additive, infinitesimal, and multiplicative coordinates.

After the complete multiplicity-bearing Xi jet frame is removed, the remaining anomaly is the
exponential holonomy of the stable class.  Thus multiplicity is a longitudinal weight-zero datum,
while horizontal displacement is a central secondary class.  This module identifies those objects
unconditionally; it does not force the class or anomaly to vanish and does not assert RH.
-/

open Complex

namespace RHTower

noncomputable section

/-- The mixed prime/depth stable coordinate is exactly weight-one Hodge purity curvature. -/
theorem mixedRateQuotientEquiv_sourceChartClass_eq_weightOnePurityCurvature
    (s : ℂ) :
    (mixedRateQuotientEquiv (sourceChartClass s) : ℂ) =
      weightOnePurityCurvature s := by
  rw [mixedRateQuotientEquiv_sourceChartClass]
  apply Complex.ext
  · simp [weightOnePurityCurvature]
    ring
  · simp [weightOnePurityCurvature]

/-- **Central transgression law.**  The normalized cofinal anomaly is the exponential holonomy of
the additive stable class.  Its matrix rank is only the multiplicity-bearing carrier dimension;
the horizontal obstruction is one central scalar independent of every jet direction. -/
theorem thetaInternalJetNormalizedCofinalAnomalyMatrix_eq_exp_sourceChartClass
    (n m : ℕ) (rho : XiDivisorSupport) (p : Nat.Primes) :
    thetaInternalJetNormalizedCofinalAnomalyMatrix n m rho p =
      (((Real.exp
          (-mixedRateQuotientEquiv (sourceChartClass (rho : ℂ)) * Real.log n) : ℝ) : ℂ) - 1) •
        (1 : Matrix (Fin (xiSupportMultiplicity rho))
          (Fin (xiSupportMultiplicity rho)) ℂ) := by
  rw [thetaInternalJetNormalizedCofinalAnomalyMatrix_eq_smul_one,
    deningerHalfDensityMateGain, mixedRateQuotientEquiv_sourceChartClass]
  congr 3
  all_goals ring_nf

/-- The orbitwise Hodge commutator is scalar multiplication by the negative stable coordinate. -/
theorem deningerArithmeticOrientedHodge_commutator_apply_eq_sourceChartClass
    (a : DeningerArithmeticGradedH1) (q : XiZeroCopy) :
    (deningerArithmeticGradedTheta
          (deningerArithmeticGradedOrientedHodge.sigma a) -
        deningerArithmeticGradedOrientedHodge.sigma
          (deningerArithmeticGradedTheta a)) q =
      -(mixedRateQuotientEquiv (sourceChartClass (q.1 : ℂ)) : ℂ) *
        deningerArithmeticGradedOrientedHodge.sigma a q := by
  rw [deningerArithmeticOrientedHodge_commutator_apply_eq_purityCurvature,
    mixedRateQuotientEquiv_sourceChartClass_eq_weightOnePurityCurvature]

/-- At every nontrivial formation clock, the central anomaly vanishes exactly when the stable
source-provenance class vanishes.  Exponentiation creates no extra neutral points. -/
theorem thetaInternalJetNormalizedCofinalAnomalyMatrix_eq_zero_iff_sourceChartClass
    {n : ℕ} (hn : 2 ≤ n) (m : ℕ) (rho : XiDivisorSupport) (p : Nat.Primes) :
    thetaInternalJetNormalizedCofinalAnomalyMatrix n m rho p = 0 ↔
      sourceChartClass (rho : ℂ) = 0 := by
  rw [sourceChartClass_eq_zero_iff]
  constructor
  · intro hmatrix
    let i : Fin (xiSupportMultiplicity rho) :=
      ⟨0, xiSupportMultiplicity_pos rho⟩
    have hdiag := congrArg (fun M => M i i) hmatrix
    rw [thetaInternalJetNormalizedCofinalAnomalyMatrix_eq_smul_one] at hdiag
    simp only [Matrix.smul_apply, Matrix.one_apply, if_pos, smul_eq_mul, mul_one,
      Matrix.zero_apply] at hdiag
    have hgainC : (deningerHalfDensityMateGain n (rho : ℂ) : ℂ) = 1 :=
      sub_eq_zero.mp hdiag
    have hgain : deningerHalfDensityMateGain n (rho : ℂ) = 1 := by
      exact_mod_cast hgainC
    exact (deningerHalfDensityMateGain_eq_one_iff_re_eq_half hn _).mp hgain
  · intro hline
    rw [thetaInternalJetNormalizedCofinalAnomalyMatrix_eq_smul_one]
    have hgain : deningerHalfDensityMateGain n (rho : ℂ) = 1 :=
      (deningerHalfDensityMateGain_eq_one_iff_re_eq_half hn _).mpr hline
    rw [hgain]
    norm_num

end

end RHTower
