import GaloisForLFunctions.RHTower.XiHurwitzOrientationPositivePairedSource
import GaloisForLFunctions.RHTower.PrimeArchReciprocalSquareSectorGate
import GaloisForLFunctions.RHTower.PrimeArchThetaCumulantMinor

/-!
# Positive-paired diagonal and reciprocal-square sector

The diagonal of the one-sided Schwarz-paired continued Cauchy kernel is exactly the
reciprocal-square sector observable.  This is the algebraic bridge behind the paper-level
reduction from matrix passivity to a scalar continued prime--Gamma sign condition.

The theorem is source-pure: it uses only the two already defined continued-source value
functions.  It does not assert the sign of either side.
-/

open Complex

namespace RHTower

noncomputable section

/-- Away from the centered origin, the continued reciprocal-square trace is exactly the
normalized prime--archimedean moment germ. -/
theorem continuedPrimeArchReciprocalSquareTrace_eq_normalizedPrimeArchMomentGerm
    {z : ℂ} (hz : z ≠ 0) :
    continuedPrimeArchReciprocalSquareTrace z =
      normalizedPrimeArchMomentGerm z := by
  rw [continuedPrimeArchReciprocalSquareTrace, normalizedPrimeArchMomentGerm,
    normalizedTraceMomentGerm, dslope_of_ne _ hz, slope_def_module,
    continuedPrimeArchSourceRelativeTrace_zero]
  simp only [sub_zero, smul_eq_mul]
  field_simp [hz]

/-- The positive-paired diagonal is the continued prime--Gamma reciprocal-square sector
observable. -/
theorem ccmPositivePairedReducedKernel_self_eq_reciprocalSquareSector
    {z : ℂ} (hzim : z.im ≠ 0) :
    ccmPositivePairedReducedKernel z z =
      2 * (z.re / z.im) * (continuedPrimeArchReciprocalSquareTrace z).im := by
  have hz : z ≠ 0 := by
    intro h
    subst z
    exact hzim rfl
  simp only [ccmPositivePairedReducedKernel,
    continuedPrimeArchReciprocalSquareTrace, Complex.conj_re, Complex.conj_im,
    Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
    Complex.div_re, Complex.div_im, Complex.neg_re, Complex.neg_im,
    Complex.normSq_apply]
  field_simp [hzim, hz]
  ring

/-- In the upper half-plane, nonnegativity of the paired diagonal is exactly the
reciprocal-square sector sign. -/
theorem ccmPositivePairedReducedKernel_self_nonneg_iff_re_mul_reciprocalSquare_im_nonneg
    {z : ℂ} (hzim : 0 < z.im) :
    0 ≤ ccmPositivePairedReducedKernel z z ↔
      0 ≤ z.re * (continuedPrimeArchReciprocalSquareTrace z).im := by
  rw [ccmPositivePairedReducedKernel_self_eq_reciprocalSquareSector hzim.ne']
  have hfactor : 0 < 2 / z.im := div_pos (by norm_num) hzim
  have hrearrange :
      2 * (z.re / z.im) * (continuedPrimeArchReciprocalSquareTrace z).im =
        (2 / z.im) *
          (z.re * (continuedPrimeArchReciprocalSquareTrace z).im) := by
    field_simp
  rw [hrearrange]
  exact mul_nonneg_iff_of_pos_left hfactor

/-- Moment-germ form of the paired-diagonal identity. -/
theorem ccmPositivePairedReducedKernel_self_eq_momentGermSector
    {z : ℂ} (hzim : z.im ≠ 0) :
    ccmPositivePairedReducedKernel z z =
      2 * (z.re / z.im) * (normalizedPrimeArchMomentGerm z).im := by
  have hz : z ≠ 0 := by
    intro h
    subst z
    exact hzim rfl
  rw [ccmPositivePairedReducedKernel_self_eq_reciprocalSquareSector hzim,
    continuedPrimeArchReciprocalSquareTrace_eq_normalizedPrimeArchMomentGerm hz]

/-- Nonnegativity of the one-sided paired diagonal only on the positive-frequency exterior of a
fixed radius.  The hypothesis is stated entirely on the regular continued prime--Gamma domain. -/
def ContinuedPrimeArchPositiveExteriorPairedDiagonalNonnegative (R : ℝ) : Prop :=
  ∀ z : ℂ, 0 < z.im → z.im < 1 / 2 → R < z.re →
    riemannZeta (1 / 2 + z * I) ≠ 0 →
      0 ≤ ccmPositivePairedReducedKernel z z

/-- A positive-frequency off-line Xi zero beyond `R` produces a negative paired diagonal at a
regular point that remains beyond `R`. -/
theorem exists_ccmPositivePairedReducedKernel_self_neg_above_of_zero
    {R : ℝ} {alpha : ℂ}
    (haim : 0 < alpha.im) (haimhalf : alpha.im < 1 / 2)
    (hRnonneg : 0 ≤ R) (hR : R < alpha.re) (haXi : XiC alpha = 0) :
    ∃ z : ℂ, 0 < z.im ∧ z.im < 1 / 2 ∧ R < z.re ∧ XiC z ≠ 0 ∧
      ccmPositivePairedReducedKernel z z < 0 := by
  have hare : alpha.re ≠ 0 := ne_of_gt (lt_of_le_of_lt hRnonneg hR)
  let r : ℝ := (alpha.re - R) / 2
  have hr : 0 < r := by dsimp only [r]; linarith
  obtain ⟨z, hzim, hzimhalf, hzXi, hnear, hsector⟩ :=
    exists_xiReciprocalSquareUpperSector_neg_near_of_zero
      haim haimhalf hare haXi r hr
  have hreAbs : |z.re - alpha.re| < r := by
    calc
      |z.re - alpha.re| = |(z - alpha).re| := by rw [sub_re]
      _ ≤ ‖z - alpha‖ := Complex.abs_re_le_norm _
      _ = dist z alpha := by rw [dist_eq_norm]
      _ < r := hnear
  have hzR : R < z.re := by
    have hleft := (abs_lt.mp hreAbs).1
    dsimp only [r] at hleft
    linarith
  have hspos : 0 < (1 / 2 + z * I).re := by
    simp [mul_re]
    linarith
  have hs1 : 1 / 2 + z * I ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    simp [mul_re] at hre
    linarith
  have hzeta : riemannZeta (1 / 2 + z * I) ≠ 0 :=
    (xi_eq_zero_iff hspos hs1).not.mp (by simpa only [XiC] using hzXi)
  have hsource : continuedPrimeArchSourceRelativeTrace z = logDeriv XiC z := by
    rw [continuedPrimeArchSourceRelativeTrace_eq_xiRelativeResolventTrace
      hspos hs1 hzeta]
    symm
    exact logDeriv_XiC_eq_relativeResolventTrace hzXi
  have hsourceSector :
      z.re * (continuedPrimeArchReciprocalSquareTrace z).im < 0 := by
    rw [continuedPrimeArchReciprocalSquareTrace, hsource]
    exact hsector
  have hdiag : ccmPositivePairedReducedKernel z z < 0 := by
    apply lt_of_not_ge
    intro hnonneg
    have hsectorNonneg :=
      (ccmPositivePairedReducedKernel_self_nonneg_iff_re_mul_reciprocalSquare_im_nonneg
        hzim).mp hnonneg
    exact (not_lt_of_ge hsectorNonneg) hsourceSector
  exact ⟨z, hzim, hzimhalf, hzR, hzXi, hdiag⟩

/-- At every exact off-line-quartet radius, exterior paired-diagonal nonnegativity already proves
RH.  No off-diagonal source value or finite matrix inequality is used. -/
theorem riemannHypothesis_of_continuedPrimeArchPositiveExteriorPairedDiagonalNonnegative
    (R : ℝ) (hband : XiOffLineQuartetAccretiveBand R)
    (hdiag : ContinuedPrimeArchPositiveExteriorPairedDiagonalNonnegative R) :
    RiemannHypothesis := by
  rw [rh_iff_xi_ne_zero_right]
  intro rho hrho hzero
  have hrhoGt : 1 / 2 < rho.re := mem_rightHalf.mp hrho
  have hrhoPos : 0 < rho.re := lt_trans (by norm_num) hrhoGt
  have hrhoLt : rho.re < 1 := xi_zero_re_lt_one hrhoPos hzero
  have hrhoIm : rho.im ≠ 0 := by
    intro him
    have heq : rho = (rho.re : ℂ) := by
      apply Complex.ext
      · simp
      · simpa using him
    have hzreal : xi (rho.re : ℂ) = 0 := by
      rw [← heq]
      exact hzero
    exact (xi_ne_zero_real_anchor hrhoPos hrhoLt) hzreal
  let tau : ℂ := if rho.im < 0 then rho else (starRingEnd ℂ) rho
  have htauZero : xi tau = 0 := by
    by_cases hneg : rho.im < 0
    · simpa [tau, hneg] using hzero
    · simp only [tau, if_neg hneg]
      rw [xi_conj, hzero, map_zero]
  have htauRe : tau.re = rho.re := by
    by_cases hneg : rho.im < 0 <;> simp [tau, hneg]
  have htauImNeg : tau.im < 0 := by
    by_cases hneg : rho.im < 0
    · simp [tau, hneg]
    · have hpos : 0 < rho.im := lt_of_le_of_ne (not_lt.mp hneg) hrhoIm.symm
      simp [tau, hneg, hpos]
  let qSupport : XiDivisorSupport :=
    ⟨tau, mem_xi_divisor_support_of_eq_zero htauZero⟩
  let q : XiZeroCopy := xiFirstZeroCopy qSupport
  have hqOff : (q.1 : ℂ).re ≠ 1 / 2 := by
    have : tau.re ≠ 1 / 2 := ne_of_gt (by rw [htauRe]; exact hrhoGt)
    simpa [q, qSupport] using this
  have hheight :=
    xiOffLineQuartetAccretiveBand_add_half_lt_abs_im_of_offLine
      R hband q hqOff
  have hheight' : R + 1 / 2 < -tau.im := by
    simpa [q, qSupport, abs_of_neg htauImNeg] using hheight
  let sigma : ℂ := 1 - tau
  let alpha : ℂ := (sigma - 1 / 2) * (-I)
  have hsigmaZero : xi sigma = 0 := by
    dsimp only [sigma]
    rw [xi_one_sub, htauZero]
  have halphaIm : alpha.im = tau.re - 1 / 2 := by
    simp [alpha, sigma, mul_im]
    ring
  have halphaRe : alpha.re = -tau.im := by
    simp [alpha, sigma, mul_re]
  have halphaImPos : 0 < alpha.im := by rw [halphaIm, htauRe]; linarith
  have halphaImHalf : alpha.im < 1 / 2 := by rw [halphaIm, htauRe]; linarith
  have hRalpha : R < alpha.re := by rw [halphaRe]; linarith
  have hcoord : 1 / 2 + alpha * I = sigma := by
    dsimp only [alpha]
    rw [mul_assoc]
    have hI : (-I) * I = (1 : ℂ) := by rw [neg_mul, I_mul_I]; ring
    rw [hI, mul_one]
    ring
  have halphaXi : XiC alpha = 0 := by
    rw [XiC, hcoord]
    exact hsigmaZero
  obtain ⟨z, hzim, hzimhalf, hzR, hzXi, hzdiag⟩ :=
    exists_ccmPositivePairedReducedKernel_self_neg_above_of_zero
      halphaImPos halphaImHalf hband.1 hRalpha halphaXi
  have hspos : 0 < (1 / 2 + z * I).re := by
    simp [mul_re]
    linarith
  have hs1 : 1 / 2 + z * I ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    simp [mul_re] at hre
    linarith
  have hzeta : riemannZeta (1 / 2 + z * I) ≠ 0 :=
    (xi_eq_zero_iff hspos hs1).not.mp (by simpa only [XiC] using hzXi)
  exact (not_lt_of_ge (hdiag z hzim hzimhalf hzR hzeta)) hzdiag

/-- RH supplies the sharp exterior paired-diagonal sign at every radius. -/
theorem continuedPrimeArchPositiveExteriorPairedDiagonalNonnegative_of_riemannHypothesis
    (R : ℝ) (hRH : RiemannHypothesis) :
    ContinuedPrimeArchPositiveExteriorPairedDiagonalNonnegative R := by
  have hsector :=
    continuedPrimeArchReciprocalSquareUpperSectorNonnegative_of_riemannHypothesis hRH
  intro z hzim hzimhalf _hzR hzeta
  exact
    (ccmPositivePairedReducedKernel_self_nonneg_iff_re_mul_reciprocalSquare_im_nonneg
      hzim).2 (hsector z hzim hzimhalf hzeta)

/-- **Exact exterior diagonal criterion.**  At every exact quartet-admissible radius, RH is
equivalent to nonnegativity of the single positive-paired source diagonal on the exterior strip. -/
theorem continuedPrimeArchPositiveExteriorPairedDiagonalNonnegative_iff_riemannHypothesis
    (R : ℝ) (hband : XiOffLineQuartetAccretiveBand R) :
    ContinuedPrimeArchPositiveExteriorPairedDiagonalNonnegative R ↔ RiemannHypothesis :=
  ⟨riemannHypothesis_of_continuedPrimeArchPositiveExteriorPairedDiagonalNonnegative R hband,
    continuedPrimeArchPositiveExteriorPairedDiagonalNonnegative_of_riemannHypothesis R⟩

/-- The fully discharged rational exterior radius. -/
theorem continuedPrimeArchPositiveExteriorPairedDiagonalNonnegative_twoHundredEighteen_twentyFifths_iff_rh :
    ContinuedPrimeArchPositiveExteriorPairedDiagonalNonnegative (218 / 25) ↔
      RiemannHypothesis :=
  continuedPrimeArchPositiveExteriorPairedDiagonalNonnegative_iff_riemannHypothesis
    (218 / 25) xiOffLineQuartetAccretiveBand_twoHundredEighteen_twentyFifths

/-- At an exact quartet radius, the scalar exterior diagonal condition and positivity of every
finite reduced source matrix are equivalent.  The reverse implication uses the Xi-specific RH
capstones, not a generic diagonal-to-matrix positivity principle. -/
theorem continuedPrimeArchPositiveExteriorPairedDiagonalNonnegative_iff_reducedSourcePassivity
    (R : ℝ) (hband : XiOffLineQuartetAccretiveBand R) :
    ContinuedPrimeArchPositiveExteriorPairedDiagonalNonnegative R ↔
      XiPositivePairedReducedSourcePassivity R :=
  (continuedPrimeArchPositiveExteriorPairedDiagonalNonnegative_iff_riemannHypothesis
    R hband).trans (positivePairedReducedSourcePassivity_iff_riemannHypothesis R hband).symm

end


end RHTower
