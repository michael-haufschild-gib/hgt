import GaloisForLFunctions.RHTower.XiShiftedReciprocalHankelTailCriterion

/-!
# Power-64 Hermitian/source criterion

The tail-from-64 endpoint does not require an all-degree Hankel cone.  It is enough to compare one
Hermitian power mass with one holomorphic prime--Gamma moment.  The ordinary triangle inequality
always gives the source moment below the Hermitian mass.  The reverse inequality forces equality
term by term, hence every sixty-fourth-power seam atom lies on the nonnegative real ray.  All later
dyadic signs follow by taking powers, and the tail-from-64 theorem gives RH.

Thus the remaining right-edge problem is a single scalar anti-holomorphic/source comparison, not an
all-degree positivity problem.
-/

open Complex

namespace RHTower

noncomputable section

/-- Hermitian mass of the sixty-fourth powers of the shift-one squared-Xi seam atoms. -/
def xiSquaredSeamPowerSixtyFourHermitianMass : ℝ :=
  ∑' q : XiZeroCopy, ‖xiSquaredSeamOneCoordinate q ^ 64‖

/-- Pointwise triangle defects at power `64`, summed over the multiplicity-exact Xi divisor. -/
def xiSquaredSeamPowerSixtyFourDefectEnergy : ℝ :=
  ∑' q : XiZeroCopy,
    (‖xiSquaredSeamOneCoordinate q ^ 64‖ -
      (xiSquaredSeamOneCoordinate q ^ 64).re)

/-- The single transverse charge hidden in the power-64 Hermitian/holomorphic gap. -/
def xiSquaredSeamPowerThirtyTwoTransverseCharge : ℝ :=
  ∑' q : XiZeroCopy, (xiSquaredSeamOneCoordinate q ^ 32).im ^ 2

/-- The single reverse source inequality left by the tail-from-64 reduction. -/
def XiSquaredSeamPowerSixtyFourSourceDominated : Prop :=
  xiSquaredSeamPowerSixtyFourHermitianMass ≤
    (primeArchShiftedReciprocalMoment 1 63).re

theorem summable_xiSquaredSeamOneCoordinate_pow_sixtyFour :
    Summable (fun q : XiZeroCopy => xiSquaredSeamOneCoordinate q ^ 64) := by
  simpa only [xiShiftedReciprocalSquare_one_eq_xiSquaredSeamOneCoordinate]
    using summable_xiShiftedReciprocalSquare_pow (y := 1) (by norm_num) 63

theorem summable_xiSquaredSeamOneCoordinate_pow_sixtyFour_re :
    Summable (fun q : XiZeroCopy => (xiSquaredSeamOneCoordinate q ^ 64).re) := by
  simpa using summable_xiSquaredSeamOneCoordinate_pow_sixtyFour.map
    Complex.reCLM Complex.reCLM.continuous

theorem summable_xiSquaredSeamPowerSixtyFourDefect :
    Summable (fun q : XiZeroCopy =>
      ‖xiSquaredSeamOneCoordinate q ^ 64‖ -
        (xiSquaredSeamOneCoordinate q ^ 64).re) :=
  summable_xiSquaredSeamOneCoordinate_pow_sixtyFour.norm.sub
    summable_xiSquaredSeamOneCoordinate_pow_sixtyFour_re

theorem summable_xiSquaredSeamPowerThirtyTwoTransverseCharge :
    Summable (fun q : XiZeroCopy =>
      (xiSquaredSeamOneCoordinate q ^ 32).im ^ 2) := by
  apply Summable.of_nonneg_of_le (fun q => sq_nonneg _)
    (fun q => ?_) summable_xiSquaredSeamOneCoordinate_pow_sixtyFour.norm
  let u := xiSquaredSeamOneCoordinate q ^ 32
  have him : u.im ^ 2 ≤ ‖u‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    nlinarith [sq_nonneg u.re]
  calc
    (xiSquaredSeamOneCoordinate q ^ 32).im ^ 2 ≤ ‖u‖ ^ 2 := him
    _ = ‖u ^ 2‖ := by simp only [u, norm_pow]
    _ = ‖xiSquaredSeamOneCoordinate q ^ 64‖ := by
      congr 1
      simp only [u]
      ring

/-- The holomorphic power-64 trace is exactly the explicit shift-one prime--Gamma source moment. -/
theorem primeArchShiftedReciprocalMoment_one_sixtyThree_re_eq_powerSixtyFourTrace :
    (primeArchShiftedReciprocalMoment 1 63).re =
      ∑' q : XiZeroCopy, (xiSquaredSeamOneCoordinate q ^ 64).re := by
  rw [← xiShiftedReciprocalMoment_eq_primeArchShiftedReciprocalMoment
    (y := 1) (by norm_num) (by norm_num) 63]
  rw [xiShiftedReciprocalMoment,
    Complex.re_tsum (summable_xiShiftedReciprocalSquare_pow
      (y := 1) (by norm_num) 63)]
  apply tsum_congr
  intro q
  rw [xiShiftedReciprocalSquare_one_eq_xiSquaredSeamOneCoordinate]

/-- Exact power-64 Hermitian/holomorphic gap identity. -/
theorem xiSquaredSeamPowerSixtyFourHermitianMass_sub_source_eq_defect :
    xiSquaredSeamPowerSixtyFourHermitianMass -
        (primeArchShiftedReciprocalMoment 1 63).re =
      xiSquaredSeamPowerSixtyFourDefectEnergy := by
  rw [xiSquaredSeamPowerSixtyFourHermitianMass,
    primeArchShiftedReciprocalMoment_one_sixtyThree_re_eq_powerSixtyFourTrace,
    xiSquaredSeamPowerSixtyFourDefectEnergy,
    ← summable_xiSquaredSeamOneCoordinate_pow_sixtyFour.norm.tsum_sub
      summable_xiSquaredSeamOneCoordinate_pow_sixtyFour_re]

/-- The power-64 triangle defect is exactly twice the degree-32 transverse square. -/
theorem norm_pow_sixtyFour_sub_re_eq_two_mul_pow_thirtyTwo_im_sq (z : ℂ) :
    ‖z ^ 64‖ - (z ^ 64).re = 2 * (z ^ 32).im ^ 2 := by
  let u := z ^ 32
  rw [show z ^ 64 = u ^ 2 by simp only [u]; ring, norm_pow,
    Complex.sq_norm, Complex.normSq_apply]
  simp only [pow_two, Complex.mul_re]
  ring

/-- Exact identification of the remaining scalar gap with one positive transverse charge. -/
theorem xiSquaredSeamPowerSixtyFourDefectEnergy_eq_two_mul_transverseCharge :
    xiSquaredSeamPowerSixtyFourDefectEnergy =
      2 * xiSquaredSeamPowerThirtyTwoTransverseCharge := by
  rw [xiSquaredSeamPowerSixtyFourDefectEnergy,
    xiSquaredSeamPowerThirtyTwoTransverseCharge, ← tsum_mul_left]
  apply tsum_congr
  intro q
  exact norm_pow_sixtyFour_sub_re_eq_two_mul_pow_thirtyTwo_im_sq _

/-- The forward triangle inequality is unconditional. -/
theorem primeArchShiftedReciprocalMoment_one_sixtyThree_re_le_hermitianMass :
    (primeArchShiftedReciprocalMoment 1 63).re ≤
      xiSquaredSeamPowerSixtyFourHermitianMass := by
  rw [primeArchShiftedReciprocalMoment_one_sixtyThree_re_eq_powerSixtyFourTrace,
    xiSquaredSeamPowerSixtyFourHermitianMass]
  exact Summable.tsum_le_tsum
    (fun q => Complex.re_le_norm (xiSquaredSeamOneCoordinate q ^ 64))
    summable_xiSquaredSeamOneCoordinate_pow_sixtyFour_re
    summable_xiSquaredSeamOneCoordinate_pow_sixtyFour.norm

theorem xiSquaredSeamPowerSixtyFourDefectEnergy_nonneg :
    0 ≤ xiSquaredSeamPowerSixtyFourDefectEnergy := by
  rw [xiSquaredSeamPowerSixtyFourDefectEnergy]
  exact tsum_nonneg fun q =>
    sub_nonneg.mpr (Complex.re_le_norm (xiSquaredSeamOneCoordinate q ^ 64))

/-- Equality in `re z ≤ ‖z‖` puts `z` on the nonnegative real ray. -/
theorem complex_nonnegativeReal_of_norm_sub_re_eq_zero
    {z : ℂ} (h : ‖z‖ - z.re = 0) :
    z.im = 0 ∧ 0 ≤ z.re := by
  have hre : z.re = ‖z‖ := by linarith
  constructor
  · have hnorm := Complex.sq_norm z
    rw [Complex.normSq_apply, hre] at hnorm
    nlinarith [sq_nonneg z.im]
  · rw [hre]
    exact norm_nonneg z

/-- Vanishing of the global power-64 defect forces every summand to vanish. -/
theorem xiSquaredSeamOneCoordinate_pow_sixtyFour_nonnegativeReal_of_defect_zero
    (hzero : xiSquaredSeamPowerSixtyFourDefectEnergy = 0)
    (q : XiZeroCopy) :
    (xiSquaredSeamOneCoordinate q ^ 64).im = 0 ∧
      0 ≤ (xiSquaredSeamOneCoordinate q ^ 64).re := by
  let d : XiZeroCopy → ℝ := fun r =>
    ‖xiSquaredSeamOneCoordinate r ^ 64‖ -
      (xiSquaredSeamOneCoordinate r ^ 64).re
  have hdnonneg (r : XiZeroCopy) : 0 ≤ d r := by
    exact sub_nonneg.mpr (Complex.re_le_norm _)
  have hdsum : Summable d := by
    simpa only [d] using summable_xiSquaredSeamPowerSixtyFourDefect
  have hdle : d q ≤ 0 := by
    apply le_of_not_gt
    intro hdpos
    have htotal : 0 < xiSquaredSeamPowerSixtyFourDefectEnergy := by
      rw [xiSquaredSeamPowerSixtyFourDefectEnergy]
      exact hdsum.tsum_pos hdnonneg q hdpos
    linarith
  have hdeq : d q = 0 := le_antisymm hdle (hdnonneg q)
  exact complex_nonnegativeReal_of_norm_sub_re_eq_zero (by simpa only [d] using hdeq)

/-- A zero power-64 defect supplies every dyadic sign in the tail beginning at `64`. -/
theorem xiSquaredSeamDyadicTailFromSix_of_powerSixtyFourDefect_zero
    (hzero : xiSquaredSeamPowerSixtyFourDefectEnergy = 0) :
    XiSquaredSeamDyadicTailFromSix := by
  intro q k hk
  have h64 :=
    xiSquaredSeamOneCoordinate_pow_sixtyFour_nonnegativeReal_of_defect_zero hzero q
  have hexp : 2 ^ k = 64 * 2 ^ (k - 6) := by
    rw [show k = 6 + (k - 6) by omega, pow_add]
    norm_num
  have hreal : xiSquaredSeamOneCoordinate q ^ 64 =
      (((xiSquaredSeamOneCoordinate q ^ 64).re : ℝ) : ℂ) := by
    apply Complex.ext
    · simp
    · simpa using h64.1
  rw [hexp, pow_mul, hreal]
  simpa only [← Complex.ofReal_pow, Complex.ofReal_re] using
    pow_nonneg h64.2 (2 ^ (k - 6))

/-- RH kills the power-64 triangle defect term by term. -/
theorem xiSquaredSeamPowerSixtyFourDefectEnergy_eq_zero_of_riemannHypothesis
  (hRH : RiemannHypothesis) :
    xiSquaredSeamPowerSixtyFourDefectEnergy = 0 := by
  rw [xiSquaredSeamPowerSixtyFourDefectEnergy]
  calc
    (∑' q : XiZeroCopy,
        (‖xiSquaredSeamOneCoordinate q ^ 64‖ -
          (xiSquaredSeamOneCoordinate q ^ 64).re)) =
        ∑' _q : XiZeroCopy, (0 : ℝ) := by
      apply tsum_congr
      intro q
      obtain ⟨x, hx, hcoord⟩ :=
        xiShiftedReciprocalSquare_pos_real_of_riemannHypothesis
          hRH (y := 1) (by norm_num) q
      have hseam : xiSquaredSeamOneCoordinate q = (x : ℂ) := by
        rw [← xiShiftedReciprocalSquare_one_eq_xiSquaredSeamOneCoordinate]
        exact hcoord
      rw [hseam]
      simp only [← Complex.ofReal_pow, Complex.norm_real, Real.norm_eq_abs,
        Complex.ofReal_re]
      rw [abs_of_nonneg (pow_nonneg hx.le 64), sub_self]
    _ = 0 := tsum_zero

/-- The one degree-32 transverse charge vanishes exactly on RH. -/
theorem xiSquaredSeamPowerThirtyTwoTransverseCharge_eq_zero_iff_riemannHypothesis :
    xiSquaredSeamPowerThirtyTwoTransverseCharge = 0 ↔ RiemannHypothesis := by
  constructor
  · intro hcharge
    have hdefect : xiSquaredSeamPowerSixtyFourDefectEnergy = 0 := by
      rw [xiSquaredSeamPowerSixtyFourDefectEnergy_eq_two_mul_transverseCharge,
        hcharge, mul_zero]
    exact xiSquaredSeamDyadicTailFromSix_iff_riemannHypothesis.mp
      (xiSquaredSeamDyadicTailFromSix_of_powerSixtyFourDefect_zero hdefect)
  · intro hRH
    have hdefect :=
      xiSquaredSeamPowerSixtyFourDefectEnergy_eq_zero_of_riemannHypothesis hRH
    rw [xiSquaredSeamPowerSixtyFourDefectEnergy_eq_two_mul_transverseCharge] at hdefect
    nlinarith

/-- Reverse Hermitian/source domination is exactly vanishing of the one transverse charge. -/
theorem xiSquaredSeamPowerSixtyFourSourceDominated_iff_transverseCharge_zero :
    XiSquaredSeamPowerSixtyFourSourceDominated ↔
      xiSquaredSeamPowerThirtyTwoTransverseCharge = 0 := by
  constructor
  · intro hdom
    have heq : xiSquaredSeamPowerSixtyFourHermitianMass =
        (primeArchShiftedReciprocalMoment 1 63).re :=
      le_antisymm hdom
        primeArchShiftedReciprocalMoment_one_sixtyThree_re_le_hermitianMass
    have hdefect : xiSquaredSeamPowerSixtyFourDefectEnergy = 0 := by
      rw [← xiSquaredSeamPowerSixtyFourHermitianMass_sub_source_eq_defect,
        heq, sub_self]
    rw [xiSquaredSeamPowerSixtyFourDefectEnergy_eq_two_mul_transverseCharge] at hdefect
    nlinarith
  · intro hcharge
    have hgap := xiSquaredSeamPowerSixtyFourHermitianMass_sub_source_eq_defect
    rw [xiSquaredSeamPowerSixtyFourDefectEnergy_eq_two_mul_transverseCharge,
      hcharge, mul_zero] at hgap
    exact (sub_eq_zero.mp hgap).le

/-- **Single-scalar power-64 RH law.**  The reverse inequality between one Hermitian mass and
one explicit prime--Gamma shifted moment is equivalent to RH. -/
theorem xiSquaredSeamPowerSixtyFourSourceDominated_iff_riemannHypothesis :
    XiSquaredSeamPowerSixtyFourSourceDominated ↔ RiemannHypothesis := by
  exact xiSquaredSeamPowerSixtyFourSourceDominated_iff_transverseCharge_zero.trans
    xiSquaredSeamPowerThirtyTwoTransverseCharge_eq_zero_iff_riemannHypothesis

end

end RHTower
