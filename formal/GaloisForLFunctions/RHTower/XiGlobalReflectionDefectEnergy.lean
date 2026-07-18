import GaloisForLFunctions.RHTower.XiHedenmalmReciprocalOperator
import GaloisForLFunctions.RHTower.PrimeArchCentralMomentGerm
import GaloisForLFunctions.HTGeometry.BalancedHilbertDefectPolarization

/-!
# The global Xi reflection-defect energy

The reciprocal centered Xi divisor has two distinct global quadratic channels.  Its Hermitian
mass is the sum of the squared reciprocal moduli, while its holomorphic quadratic moment is the
central curvature of the continued prime--Gamma source.  Their gap is exactly one half of the
squared distance between the reciprocal divisor and its conjugate.

This produces a quantitative source--divisor identity.  The Hermitian mass always dominates the
prime--Gamma curvature, and equality is equivalent to RH.  Thus the remaining analytic direction
is one sharply oriented source estimate: the reverse inequality.
-/

open Complex

namespace RHTower

noncomputable section

/-- The reciprocal centered coordinate of one multiplicity copy of the Xi divisor. -/
def xiReciprocalCoordinate (q : XiZeroCopy) : ℂ :=
  (xiSpectralPoint q)⁻¹

/-- The Hermitian inverse-square mass of the complete Xi divisor. -/
def xiReciprocalHermitianMass : ℝ :=
  ∑' q : XiZeroCopy, ‖xiReciprocalCoordinate q‖ ^ 2

/-- The global squared distance of the reciprocal divisor from conjugation invariance. -/
def xiGlobalReflectionDefectEnergy : ℝ :=
  ∑' q : XiZeroCopy,
    ‖xiReciprocalCoordinate q -
      (starRingEnd ℂ) (xiReciprocalCoordinate q)‖ ^ 2

/-- The central curvature read from the normalized continued prime--Gamma source germ. -/
def primeArchCentralCurvature : ℝ :=
  analyticTraceMoments
    (normalizedTraceMomentGerm continuedPrimeArchSourceRelativeTrace) 0

/-- Pointwise polarization identity underlying the global defect formula. -/
lemma norm_sub_conj_sq (z : ℂ) :
    ‖z - (starRingEnd ℂ) z‖ ^ 2 =
      2 * ‖z‖ ^ 2 - 2 * (z ^ 2).re := by
  rw [Complex.sq_norm, Complex.normSq_apply, Complex.sq_norm,
    Complex.normSq_apply]
  simp [Complex.conj_re, Complex.conj_im, pow_two, Complex.mul_re]
  ring

/-- The complete reflection-defect energy is absolutely summable. -/
theorem summable_xiGlobalReflectionDefectEnergy :
    Summable (fun q : XiZeroCopy =>
      ‖xiReciprocalCoordinate q -
        (starRingEnd ℂ) (xiReciprocalCoordinate q)‖ ^ 2) := by
  have hH : Summable (fun q : XiZeroCopy =>
      ‖xiReciprocalCoordinate q‖ ^ 2) := by
    simpa [xiReciprocalCoordinate] using summable_norm_xiSpectralPoint_inv_sq
  have hstar : Summable (fun q : XiZeroCopy =>
      ‖(starRingEnd ℂ) (xiReciprocalCoordinate q)‖ ^ 2) := by
    simpa only [norm_star] using hH
  exact
    GaloisForLFunctions.HTGeometry.summable_norm_sub_sq_of_summable_norm_sq hH hstar

/-- The global reflection-defect energy is nonnegative. -/
theorem xiGlobalReflectionDefectEnergy_nonneg :
    0 ≤ xiGlobalReflectionDefectEnergy := by
  exact tsum_nonneg (fun q => sq_nonneg _)

/-- Exact global decomposition into Hermitian mass minus holomorphic divisor moment. -/
theorem xiGlobalReflectionDefectEnergy_eq_mass_sub_moment :
    xiGlobalReflectionDefectEnergy =
      2 * (xiReciprocalHermitianMass - (xiCentralReciprocalMoment 0).re) := by
  have hH : Summable (fun q : XiZeroCopy =>
      ‖xiReciprocalCoordinate q‖ ^ 2) := by
    simpa [xiReciprocalCoordinate] using summable_norm_xiSpectralPoint_inv_sq
  have hstar : Summable (fun q : XiZeroCopy =>
      ‖(starRingEnd ℂ) (xiReciprocalCoordinate q)‖ ^ 2) := by
    simpa only [norm_star] using hH
  have hC : Summable (fun q : XiZeroCopy =>
      xiZeroCopyReciprocalSquare q) := summable_xiZeroCopyReciprocalSquare
  have hsum :
      (∑' q : XiZeroCopy, xiZeroCopyReciprocalSquare q) =
        xiCentralReciprocalMoment 0 := by
    simpa using tsum_xiZeroCopyReciprocalSquare_pow 0
  have hpolar :=
    GaloisForLFunctions.HTGeometry.tsum_norm_sub_sq_eq_two_mul_mass_sub_re_inner_of_norm_eq
      hH hstar (fun q => norm_star (xiReciprocalCoordinate q))
  have hcross :
      (∑' q : XiZeroCopy,
        RCLike.re (inner ℂ (xiReciprocalCoordinate q)
          ((starRingEnd ℂ) (xiReciprocalCoordinate q)))) =
        ∑' q : XiZeroCopy, (xiZeroCopyReciprocalSquare q).re := by
    apply tsum_congr
    intro q
    rw [GaloisForLFunctions.HTGeometry.re_inner_complex_eq_mul_conj_re,
      starRingEnd_self_apply, xiZeroCopyReciprocalSquare,
      xiReciprocalCoordinate, pow_two]
  rw [hcross] at hpolar
  calc
    xiGlobalReflectionDefectEnergy =
        2 * ((∑' q : XiZeroCopy, ‖xiReciprocalCoordinate q‖ ^ 2) -
          ∑' q : XiZeroCopy, (xiZeroCopyReciprocalSquare q).re) := by
      rw [xiGlobalReflectionDefectEnergy]
      exact hpolar
    _ = 2 * (xiReciprocalHermitianMass -
        (xiCentralReciprocalMoment 0).re) := by
      rw [xiReciprocalHermitianMass, ← Complex.re_tsum hC, hsum]

/-- The holomorphic divisor moment is exactly the central prime--Gamma source curvature. -/
theorem primeArchCentralCurvature_eq_moment_re :
    primeArchCentralCurvature = (xiCentralReciprocalMoment 0).re := by
  have h := primeArchSourceMoment_eq_xiCentralReciprocalMoment 0
  have hre := congrArg Complex.re h
  simpa [primeArchCentralCurvature] using hre

/-- **Global source--divisor gap identity.**  The reflection defect is twice the gap between the
Hermitian reciprocal mass and the central curvature of the explicit prime--Gamma source. -/
theorem xiGlobalReflectionDefectEnergy_eq_mass_sub_source :
    xiGlobalReflectionDefectEnergy =
      2 * (xiReciprocalHermitianMass - primeArchCentralCurvature) := by
  rw [xiGlobalReflectionDefectEnergy_eq_mass_sub_moment,
    primeArchCentralCurvature_eq_moment_re]

/-- Unconditionally, the central prime--Gamma curvature is bounded above by the Hermitian
reciprocal-divisor mass. -/
theorem primeArchCentralCurvature_le_xiReciprocalHermitianMass :
    primeArchCentralCurvature ≤ xiReciprocalHermitianMass := by
  have h := xiGlobalReflectionDefectEnergy_nonneg
  rw [xiGlobalReflectionDefectEnergy_eq_mass_sub_source] at h
  linarith

/-- Vanishing of the global reflection-defect energy is exactly RH. -/
theorem xiGlobalReflectionDefectEnergy_eq_zero_iff_rh :
    xiGlobalReflectionDefectEnergy = 0 ↔ RiemannHypothesis := by
  have hH : Summable (fun q : XiZeroCopy =>
      ‖xiReciprocalCoordinate q‖ ^ 2) := by
    simpa [xiReciprocalCoordinate] using summable_norm_xiSpectralPoint_inv_sq
  have hstar : Summable (fun q : XiZeroCopy =>
      ‖(starRingEnd ℂ) (xiReciprocalCoordinate q)‖ ^ 2) := by
    simpa only [norm_star] using hH
  have hfixed :=
    GaloisForLFunctions.HTGeometry.tsum_norm_sub_sq_eq_zero_iff hH hstar
  rw [xiGlobalReflectionDefectEnergy, hfixed]
  constructor
  · intro hfix
    apply riemannHypothesis_of_xiSpectralPoint_real
    intro q
    have hcoord := hfix q
    have hspectral : xiSpectralPoint q =
        (starRingEnd ℂ) (xiSpectralPoint q) := by
      have hinv := congrArg Inv.inv hcoord
      simpa [xiReciprocalCoordinate, map_inv₀,
        xiSpectralPoint_ne_zero q] using hinv
    have him : (xiSpectralPoint q).im = 0 := by
      have himEq := congrArg Complex.im hspectral
      change (xiSpectralPoint q).im = -(xiSpectralPoint q).im at himEq
      linarith
    refine ⟨(xiSpectralPoint q).re, ?_⟩
    apply Complex.ext
    · simp
    · simp [him]
  · intro hRH q
    obtain ⟨t, ht⟩ := xiSpectralPoint_real_of_rh hRH q
    rw [xiReciprocalCoordinate, ht]
    simp

/-- **Sharp RH estimate.**  Equality between Hermitian reciprocal mass and prime--Gamma central
curvature is equivalent to RH.  In view of the unconditional opposite inequality above, the only
missing direction is the source estimate `xiReciprocalHermitianMass ≤ primeArchCentralCurvature`. -/
theorem xiReciprocalHermitianMass_eq_primeArchCentralCurvature_iff_rh :
    xiReciprocalHermitianMass = primeArchCentralCurvature ↔ RiemannHypothesis := by
  rw [← xiGlobalReflectionDefectEnergy_eq_zero_iff_rh,
    xiGlobalReflectionDefectEnergy_eq_mass_sub_source]
  constructor <;> intro h
  · rw [h, sub_self, mul_zero]
  · have htwo : (2 : ℝ) ≠ 0 := by norm_num
    have hsub : xiReciprocalHermitianMass - primeArchCentralCurvature = 0 :=
      (mul_eq_zero.mp h).resolve_left htwo
    exact sub_eq_zero.mp hsub

end

end RHTower
