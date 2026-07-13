import GaloisForLFunctions.RHTower.XiHedenmalmReciprocalOperator
import GaloisForLFunctions.RHTower.PrimeArchCentralMomentGerm

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
  have hmajor : Summable (fun q : XiZeroCopy =>
      4 * ‖xiReciprocalCoordinate q‖ ^ 2) := by
    exact summable_norm_xiSpectralPoint_inv_sq.mul_left 4
  refine Summable.of_nonneg_of_le (fun q => sq_nonneg _) (fun q => ?_) hmajor
  have hnorm :
      ‖xiReciprocalCoordinate q -
          (starRingEnd ℂ) (xiReciprocalCoordinate q)‖ ≤
        2 * ‖xiReciprocalCoordinate q‖ := by
    calc
      _ ≤ ‖xiReciprocalCoordinate q‖ +
          ‖(starRingEnd ℂ) (xiReciprocalCoordinate q)‖ := norm_sub_le _ _
      _ = 2 * ‖xiReciprocalCoordinate q‖ := by simp; ring
  nlinarith [norm_nonneg (xiReciprocalCoordinate q),
    norm_nonneg (xiReciprocalCoordinate q -
      (starRingEnd ℂ) (xiReciprocalCoordinate q))]

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
  have hC : Summable (fun q : XiZeroCopy =>
      xiZeroCopyReciprocalSquare q) := summable_xiZeroCopyReciprocalSquare
  have hR : Summable (fun q : XiZeroCopy =>
      (xiZeroCopyReciprocalSquare q).re) := by
    exact Summable.of_norm_bounded hC.norm (fun q => by
      rw [Real.norm_eq_abs]
      exact abs_re_le_norm _)
  have hsum :
      (∑' q : XiZeroCopy, xiZeroCopyReciprocalSquare q) =
        xiCentralReciprocalMoment 0 := by
    simpa using tsum_xiZeroCopyReciprocalSquare_pow 0
  calc
    xiGlobalReflectionDefectEnergy =
        ∑' q : XiZeroCopy,
          (2 * ‖xiReciprocalCoordinate q‖ ^ 2 -
            2 * (xiZeroCopyReciprocalSquare q).re) := by
      apply tsum_congr
      intro q
      rw [norm_sub_conj_sq]
      rfl
    _ = (∑' q : XiZeroCopy, 2 * ‖xiReciprocalCoordinate q‖ ^ 2) -
        ∑' q : XiZeroCopy, 2 * (xiZeroCopyReciprocalSquare q).re :=
      (hH.mul_left 2).tsum_sub (hR.mul_left 2)
    _ = 2 * xiReciprocalHermitianMass -
        2 * (xiCentralReciprocalMoment 0).re := by
      rw [tsum_mul_left, tsum_mul_left, xiReciprocalHermitianMass,
        ← Complex.re_tsum hC, hsum]
    _ = 2 * (xiReciprocalHermitianMass -
        (xiCentralReciprocalMoment 0).re) := by ring

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
  constructor
  · intro hzero
    apply riemannHypothesis_of_xiSpectralPoint_real
    intro q
    have hterm :
        ‖xiReciprocalCoordinate q -
          (starRingEnd ℂ) (xiReciprocalCoordinate q)‖ ^ 2 = 0 := by
      by_contra hne
      have hpos : 0 < ‖xiReciprocalCoordinate q -
          (starRingEnd ℂ) (xiReciprocalCoordinate q)‖ ^ 2 :=
        lt_of_le_of_ne (sq_nonneg _) (Ne.symm hne)
      have hsumpos := summable_xiGlobalReflectionDefectEnergy.tsum_pos
        (fun r => sq_nonneg _) q hpos
      exact (ne_of_gt hsumpos) hzero
    have hcoord : xiReciprocalCoordinate q =
        (starRingEnd ℂ) (xiReciprocalCoordinate q) := by
      have hnorm : ‖xiReciprocalCoordinate q -
          (starRingEnd ℂ) (xiReciprocalCoordinate q)‖ = 0 := by
        nlinarith [norm_nonneg (xiReciprocalCoordinate q -
          (starRingEnd ℂ) (xiReciprocalCoordinate q))]
      exact sub_eq_zero.mp (norm_eq_zero.mp hnorm)
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
  · intro hRH
    rw [xiGlobalReflectionDefectEnergy]
    have hfun : (fun q : XiZeroCopy =>
        ‖xiReciprocalCoordinate q -
          (starRingEnd ℂ) (xiReciprocalCoordinate q)‖ ^ 2) = 0 := by
      funext q
      obtain ⟨t, ht⟩ := xiSpectralPoint_real_of_rh hRH q
      rw [xiReciprocalCoordinate, ht]
      simp
    rw [hfun]
    exact tsum_zero

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
