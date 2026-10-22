import GaloisForLFunctions.RHTower.CCM.CCMRestrictedWeilCanonicalGroundHeadEnergy
import GaloisForLFunctions.RHTower.CCM.CCMPolarPrimeStieltjesAutocorrelation

/-!
# Completed-error balance on canonical Gamma--Slepian heads

This module gives a regularity-free normal form for the Route O sign problem.  For an actual
physical aperture head `f`, every finite von Mangoldt translation is split into its scalar mass
and the nonnegative squared translation loss

`J_prime(f) = sum_n Lambda(n) / sqrt(n) * ||U_(log n) f - f||^2`.

The polar compression is retained as the signed autocorrelation debt

`J_polar(f) = 8 sinh(a) ||f||^2 - re <Polar f, f>`.

The endpoint scalar left by the prime--polar cancellation is exactly twice the completed critical
Mellin error `D(2a)`.  Consequently the literal restricted-Weil source quadratic is exactly

`GammaFormEnergy + (gammaScalar + 2 D(2a)) ||f||^2 + J_prime(f) - J_polar(f)`.

No derivative or smoothness of the actual head autocorrelation is used.  Specializing to the
canonical exact-ground Gamma--Slepian heads identifies literal reverse-prime control with
nonnegativity of this signed balance, without a common-clock or prolate substitution.
-/

open Complex MeasureTheory Set Filter Topology
open scoped ENNReal InnerProduct InnerProductSpace BigOperators

noncomputable section

namespace RHTower

def ccmPrimeTranslationDefectEnergy
    (a : SuzukiPositiveAperture) (f : suzukiApertureHilbert a) : ℝ :=
  ∑ n ∈ Finset.Icc 2 (Nat.floor (Real.exp (2 * a.1))),
    criticalMellinAtomWeight n *
      ‖logTranslationCLM (Real.log n) f.1 - f.1‖ ^ 2

theorem logTranslation_norm (h : ℝ) (f : SoninL2) :
    ‖logTranslationCLM h f‖ = ‖f‖ := by
  exact (MellinL2.additiveTranslationUnitary h).norm_map f

theorem logTranslation_defect_eq
    (h : ℝ) (f : SoninL2) :
    ‖logTranslationCLM h f - f‖ ^ 2 =
      2 * ‖f‖ ^ 2 -
        (inner ℂ (logTranslationCLM h f) f +
          inner ℂ (logTranslationCLM (-h) f) f).re := by
  rw [norm_sub_sq (𝕜 := ℂ), logTranslation_norm]
  simp only [RCLike.re_to_complex]
  have hadj : inner ℂ (logTranslationCLM (-h) f) f =
      inner ℂ f (logTranslationCLM h f) := by
    rw [inner_logTranslationCLM (-h)]
    simp
  rw [hadj]
  have hre : (inner ℂ f (logTranslationCLM h f)).re =
      (inner ℂ (logTranslationCLM h f) f).re := by
    simpa using inner_re_symm (𝕜 := ℂ) f (logTranslationCLM h f)
  simp only [Complex.add_re, hre]
  ring_nf

theorem criticalMellinAtomWeight_eq_div_sqrt
    (n : ℕ) :
    criticalMellinAtomWeight n =
      ArithmeticFunction.vonMangoldt n / Real.sqrt n := by
  unfold criticalMellinAtomWeight
  have hn0 : (0 : ℝ) ≤ n := by positivity
  rw [show (-1 / 2 : ℝ) = -(1 / 2 : ℝ) by ring, Real.rpow_neg hn0,
    ← Real.sqrt_eq_rpow]
  ring

theorem ccmPrimeTranslationDefectEnergy_nonneg
    (a : SuzukiPositiveAperture) (f : suzukiApertureHilbert a) :
    0 ≤ ccmPrimeTranslationDefectEnergy a f := by
  unfold ccmPrimeTranslationDefectEnergy
  exact Finset.sum_nonneg fun n hn => mul_nonneg
    (by
      rw [criticalMellinAtomWeight_eq_div_sqrt n]
      exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _))
    (sq_nonneg _)

theorem re_inner_ccmPrimeTransportOperator_eq_defect
    (a : SuzukiPositiveAperture) (n : ℕ)
    (f : suzukiApertureHilbert a) :
    (inner ℂ (ccmPrimeTransportOperator a n f) f).re =
      2 / Real.sqrt n * ‖f‖ ^ 2 -
        (1 / Real.sqrt n) *
          ‖logTranslationCLM (Real.log n) f.1 - f.1‖ ^ 2 := by
  rw [inner_ccmPrimeTransportOperator]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, Complex.add_re]
  rw [logTranslation_defect_eq]
  simp only [Submodule.coe_norm, Complex.add_re]
  ring

theorem re_inner_ccmFinitePrimeOperator_eq_mass_sub_defect
    (a : SuzukiPositiveAperture) (f : suzukiApertureHilbert a) :
    (inner ℂ (ccmFinitePrimeOperator a f) f).re =
      2 * criticalMellinPrimeMass (2 * a.1) * ‖f‖ ^ 2 -
        ccmPrimeTranslationDefectEnergy a f := by
  rw [inner_ccmFinitePrimeOperator]
  rw [Complex.re_sum]
  simp_rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  have hterm : ∀ n ∈ Finset.Icc 2 (Nat.floor (Real.exp (2 * a.1))),
      (inner ℂ (ccmPrimeTransportOperator a n f) f).re =
        2 / Real.sqrt n * ‖f‖ ^ 2 -
          (1 / Real.sqrt n) *
            ‖logTranslationCLM (Real.log n) f.1 - f.1‖ ^ 2 := by
    intro n hn
    exact re_inner_ccmPrimeTransportOperator_eq_defect a n f
  rw [show (∑ n ∈ Finset.Icc 2 (Nat.floor (Real.exp (2 * a.1))),
      ArithmeticFunction.vonMangoldt n *
        (inner ℂ (ccmPrimeTransportOperator a n f) f).re) =
      ∑ n ∈ Finset.Icc 2 (Nat.floor (Real.exp (2 * a.1))),
        ArithmeticFunction.vonMangoldt n *
          (2 / Real.sqrt n * ‖f‖ ^ 2 -
            (1 / Real.sqrt n) *
              ‖logTranslationCLM (Real.log n) f.1 - f.1‖ ^ 2) by
    apply Finset.sum_congr rfl
    intro n hn
    rw [hterm n hn]]
  rw [criticalMellinPrimeMass_eq_atomSum]
  unfold ccmPrimeTranslationDefectEnergy
  have hsum : (∑ n ∈ Finset.Icc 2 (Nat.floor (Real.exp (2 * a.1))),
      ArithmeticFunction.vonMangoldt n *
        (2 / Real.sqrt n * ‖f‖ ^ 2 -
          (1 / Real.sqrt n) *
            ‖logTranslationCLM (Real.log n) f.1 - f.1‖ ^ 2)) =
      (∑ n ∈ Finset.Icc 2 (Nat.floor (Real.exp (2 * a.1))),
        (2 * criticalMellinAtomWeight n * ‖f‖ ^ 2 -
          criticalMellinAtomWeight n *
            ‖logTranslationCLM (Real.log n) f.1 - f.1‖ ^ 2)) := by
    apply Finset.sum_congr rfl
    intro n hn
    rw [criticalMellinAtomWeight_eq_div_sqrt n]
    ring
  rw [hsum]
  rw [Finset.sum_sub_distrib]
  congr 1
  rw [Finset.mul_sum, Finset.sum_mul]

theorem norm_sq_ccmPolarApertureVector_half
    (a : SuzukiPositiveAperture) :
    ‖ccmPolarApertureVector a (1 / 2)‖ ^ 2 = 2 * Real.sinh a.1 := by
  change ‖ccmPolarL2Vector a (1 / 2)‖ ^ 2 = _
  rw [norm_sq_eq_integral]
  have hcoe := ccmPolarL2Vector_coeFn a (1 / 2)
  calc
    (∫ x : ℝ, ‖(ccmPolarL2Vector a (1 / 2) : ℝ → ℂ) x‖ ^ 2) =
        ∫ x in centralInterval a.1, Real.exp x := by
      rw [← integral_indicator (measurableSet_centralInterval a.1)]
      apply integral_congr_ae
      filter_upwards [hcoe] with x hx
      rw [hx]
      by_cases hmem : x ∈ centralInterval a.1
      · rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hmem]
        simp only [ccmPolarProfile, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (Real.exp_pos _)]
        rw [← Real.exp_nat_mul]
        congr 1
        ring
      · rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem hmem]
        simp
    _ = ∫ x in (-a.1)..a.1, Real.exp x := by
      rw [intervalIntegral.integral_of_le (by linarith [a.property])]
      unfold centralInterval
      rw [MeasureTheory.integral_Icc_eq_integral_Ioc]
    _ = Real.exp a.1 - Real.exp (-a.1) := by rw [integral_exp]
    _ = 2 * Real.sinh a.1 := by rw [Real.sinh_eq]; ring

theorem norm_sq_ccmPolarApertureVector_neg_half
    (a : SuzukiPositiveAperture) :
    ‖ccmPolarApertureVector a (-1 / 2)‖ ^ 2 = 2 * Real.sinh a.1 := by
  change ‖ccmPolarL2Vector a (-1 / 2)‖ ^ 2 = _
  rw [norm_sq_eq_integral]
  have hcoe := ccmPolarL2Vector_coeFn a (-1 / 2)
  calc
    (∫ x : ℝ, ‖(ccmPolarL2Vector a (-1 / 2) : ℝ → ℂ) x‖ ^ 2) =
        ∫ x in centralInterval a.1, Real.exp (-x) := by
      rw [← integral_indicator (measurableSet_centralInterval a.1)]
      apply integral_congr_ae
      filter_upwards [hcoe] with x hx
      rw [hx]
      by_cases hmem : x ∈ centralInterval a.1
      · rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hmem]
        simp only [ccmPolarProfile, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos (Real.exp_pos _)]
        rw [← Real.exp_nat_mul]
        congr 1
        ring
      · rw [Set.indicator_of_notMem hmem, Set.indicator_of_notMem hmem]
        simp
    _ = ∫ x in (-a.1)..a.1, Real.exp (-x) := by
      rw [intervalIntegral.integral_of_le (by linarith [a.property])]
      unfold centralInterval
      rw [MeasureTheory.integral_Icc_eq_integral_Ioc]
    _ = Real.exp a.1 - Real.exp (-a.1) := by
      have h := intervalIntegral.integral_comp_neg
        (f := Real.exp) (a := -a.1) (b := a.1)
      simp only [neg_neg] at h
      rw [h, integral_exp]
    _ = 2 * Real.sinh a.1 := by rw [Real.sinh_eq]; ring

def ccmPolarAutocorrelationDefect
    (a : SuzukiPositiveAperture) (f : suzukiApertureHilbert a) : ℝ :=
  8 * Real.sinh a.1 * ‖f‖ ^ 2 -
    (inner ℂ (ccmPolarOperator a f) f).re

theorem re_inner_ccmPolarOperator_le
    (a : SuzukiPositiveAperture) (f : suzukiApertureHilbert a) :
    (inner ℂ (ccmPolarOperator a f) f).re ≤
      4 * Real.sinh a.1 * ‖f‖ ^ 2 := by
  let xm : ℂ := inner ℂ (ccmPolarApertureVector a (-1 / 2)) f
  let xp : ℂ := inner ℂ (ccmPolarApertureVector a (1 / 2)) f
  have hrepr : (inner ℂ (ccmPolarOperator a f) f).re =
      2 * (star xm * xp).re := by
    rw [inner_ccmPolarOperator]
    dsimp only [xm, xp]
    simp only [Complex.star_def, Complex.add_re, Complex.mul_re,
      Complex.conj_re, Complex.conj_im]
    ring
  have hre : (star xm * xp).re ≤ ‖xm‖ * ‖xp‖ := by
    exact (Complex.re_le_norm _).trans_eq (by simp)
  have hamgm : 2 * (‖xm‖ * ‖xp‖) ≤ ‖xm‖ ^ 2 + ‖xp‖ ^ 2 := by
    nlinarith [sq_nonneg (‖xm‖ - ‖xp‖)]
  have hxm : ‖xm‖ ≤ ‖ccmPolarApertureVector a (-1 / 2)‖ * ‖f‖ := by
    simpa only [xm] using
      (norm_inner_le_norm (ccmPolarApertureVector a (-1 / 2)) f)
  have hxp : ‖xp‖ ≤ ‖ccmPolarApertureVector a (1 / 2)‖ * ‖f‖ := by
    simpa only [xp] using
      (norm_inner_le_norm (ccmPolarApertureVector a (1 / 2)) f)
  have hxm2 : ‖xm‖ ^ 2 ≤
      ‖ccmPolarApertureVector a (-1 / 2)‖ ^ 2 * ‖f‖ ^ 2 := by
    nlinarith [norm_nonneg xm, norm_nonneg f,
      norm_nonneg (ccmPolarApertureVector a (-1 / 2)),
      mul_nonneg (sub_nonneg.mpr hxm)
        (add_nonneg (norm_nonneg xm)
          (mul_nonneg (norm_nonneg (ccmPolarApertureVector a (-1 / 2)))
            (norm_nonneg f)))]
  have hxp2 : ‖xp‖ ^ 2 ≤
      ‖ccmPolarApertureVector a (1 / 2)‖ ^ 2 * ‖f‖ ^ 2 := by
    nlinarith [norm_nonneg xp, norm_nonneg f,
      norm_nonneg (ccmPolarApertureVector a (1 / 2)),
      mul_nonneg (sub_nonneg.mpr hxp)
        (add_nonneg (norm_nonneg xp)
          (mul_nonneg (norm_nonneg (ccmPolarApertureVector a (1 / 2)))
            (norm_nonneg f)))]
  rw [hrepr]
  calc
    2 * (star xm * xp).re ≤ 2 * (‖xm‖ * ‖xp‖) := by linarith
    _ ≤ ‖xm‖ ^ 2 + ‖xp‖ ^ 2 := hamgm
    _ ≤ ‖ccmPolarApertureVector a (-1 / 2)‖ ^ 2 * ‖f‖ ^ 2 +
        ‖ccmPolarApertureVector a (1 / 2)‖ ^ 2 * ‖f‖ ^ 2 :=
      add_le_add hxm2 hxp2
    _ = 4 * Real.sinh a.1 * ‖f‖ ^ 2 := by
      rw [norm_sq_ccmPolarApertureVector_neg_half,
        norm_sq_ccmPolarApertureVector_half]
      ring

theorem ccmPolarAutocorrelationDefect_nonneg
    (a : SuzukiPositiveAperture) (f : suzukiApertureHilbert a) :
    0 ≤ ccmPolarAutocorrelationDefect a f := by
  unfold ccmPolarAutocorrelationDefect
  have hsinh : 0 ≤ Real.sinh a.1 := (Real.sinh_nonneg_iff.mpr a.property.le)
  have hpolar := re_inner_ccmPolarOperator_le a f
  nlinarith [mul_nonneg hsinh (sq_nonneg ‖f‖)]

theorem ccmRestrictedWeilSourceQuadratic_eq_completedError_defects
    (a : SuzukiPositiveAperture) (u : CCMArchimedeanFormDomain a) :
    ccmRestrictedWeilSourceQuadratic a u =
      ‖u‖ ^ 2 +
        (2 * gammaHardyPhaseRate 0 - 1 +
            2 * criticalMellinCompletedError (2 * a.1)) *
          ‖ccmArchimedeanFormToAperture a u‖ ^ 2 +
        ccmPrimeTranslationDefectEnergy a
          (ccmArchimedeanFormToAperture a u) -
        ccmPolarAutocorrelationDefect a
          (ccmArchimedeanFormToAperture a u) := by
  rw [← ccmRestrictedWeilForm_self_re_eq_source]
  rw [ccmRestrictedWeilForm_self_re_eq_norm_add_physicalRemainder]
  rw [inner_ccmRestrictedWeilBoundedRemainder]
  rw [Complex.sub_re, Complex.add_re, Complex.mul_re]
  simp only [ccmArchimedeanRemainderScalar, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]
  have hself :
      (inner ℂ (ccmArchimedeanFormToAperture a u)
        (ccmArchimedeanFormToAperture a u)).re =
        ‖ccmArchimedeanFormToAperture a u‖ ^ 2 :=
    (InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ)
      (ccmArchimedeanFormToAperture a u)).symm
  rw [hself]
  rw [re_inner_ccmFinitePrimeOperator_eq_mass_sub_defect]
  unfold ccmPolarAutocorrelationDefect
  rw [criticalMellinCompletedError_eq_polar_sub_primeMass]
  ring_nf

/-- Numeric signed producer, with full form-domain Gamma energy and the actual
physical-head prime and polar autocorrelation defects kept separate. -/
def ccmRestrictedWeilCompletedErrorDefectBalance
    (a : SuzukiPositiveAperture) (u : CCMArchimedeanFormDomain a) : ℝ :=
  ‖u‖ ^ 2 +
      (2 * gammaHardyPhaseRate 0 - 1 +
          2 * criticalMellinCompletedError (2 * a.1)) *
        ‖ccmArchimedeanFormToAperture a u‖ ^ 2 +
      ccmPrimeTranslationDefectEnergy a
        (ccmArchimedeanFormToAperture a u) -
    ccmPolarAutocorrelationDefect a
      (ccmArchimedeanFormToAperture a u)

theorem ccmRestrictedWeilCompletedErrorDefectBalance_eq_sourceQuadratic
    (a : SuzukiPositiveAperture) (u : CCMArchimedeanFormDomain a) :
    ccmRestrictedWeilCompletedErrorDefectBalance a u =
      ccmRestrictedWeilSourceQuadratic a u := by
  rw [ccmRestrictedWeilSourceQuadratic_eq_completedError_defects]
  rfl

/-- Signed completed-error control furnished by nonnegativity of the numeric balance. -/
def CCMRestrictedWeilCompletedErrorDefectControl
    (a : SuzukiPositiveAperture) (u : CCMArchimedeanFormDomain a) : Prop :=
  0 ≤ ccmRestrictedWeilCompletedErrorDefectBalance a u

theorem ccmRestrictedWeilCompletedErrorDefectControl_iff
    (a : SuzukiPositiveAperture) (u : CCMArchimedeanFormDomain a) :
    CCMRestrictedWeilCompletedErrorDefectControl a u ↔
      ccmPolarAutocorrelationDefect a
          (ccmArchimedeanFormToAperture a u) ≤
        ‖u‖ ^ 2 +
          (2 * gammaHardyPhaseRate 0 - 1 +
              2 * criticalMellinCompletedError (2 * a.1)) *
            ‖ccmArchimedeanFormToAperture a u‖ ^ 2 +
          ccmPrimeTranslationDefectEnergy a
            (ccmArchimedeanFormToAperture a u) := by
  unfold CCMRestrictedWeilCompletedErrorDefectControl
  unfold ccmRestrictedWeilCompletedErrorDefectBalance
  exact sub_nonneg

theorem ccmRestrictedWeilSourceQuadratic_nonneg_iff_completedErrorDefectControl
    (a : SuzukiPositiveAperture) (u : CCMArchimedeanFormDomain a) :
    0 ≤ ccmRestrictedWeilSourceQuadratic a u ↔
      CCMRestrictedWeilCompletedErrorDefectControl a u := by
  unfold CCMRestrictedWeilCompletedErrorDefectControl
  rw [ccmRestrictedWeilCompletedErrorDefectBalance_eq_sourceQuadratic]

/-- The signed producer on the literal canonical finite Gamma--Slepian ground head. -/
def CCMRestrictedWeilCanonicalGroundHeadCompletedErrorDefectControl
    (a : SuzukiPositiveAperture) (n : ℕ) : Prop :=
  CCMRestrictedWeilCompletedErrorDefectControl a
    (ccmRestrictedWeilCanonicalGroundHead a n)

theorem ccmRestrictedWeilCanonicalGroundHead_reversePrimeBound_iff_completedErrorDefectControl
    (a : SuzukiPositiveAperture) (n : ℕ) :
    CCMRestrictedWeilCanonicalGroundHeadReversePrimeBound a n ↔
      CCMRestrictedWeilCanonicalGroundHeadCompletedErrorDefectControl a n := by
  rw [ccmRestrictedWeilCanonicalGroundHead_reversePrimeBound_iff_source_nonneg]
  exact ccmRestrictedWeilSourceQuadratic_nonneg_iff_completedErrorDefectControl
    a (ccmRestrictedWeilCanonicalGroundHead a n)

/-- Exact weld to the canonical head/tail theorem: the completed-error balance is the true ground
floor times physical head mass plus the nonnegative omitted-tail defect. -/
theorem ccmRestrictedWeilCanonicalGroundHead_completedErrorDefectBalance_eq_ground_add_tail
    (a : SuzukiPositiveAperture) (n : ℕ) :
    ccmRestrictedWeilCompletedErrorDefectBalance a
        (ccmRestrictedWeilCanonicalGroundHead a n) =
      ccmRestrictedWeilGroundEnergy a *
          ‖ccmArchimedeanFormToAperture a
            (ccmRestrictedWeilCanonicalGroundHead a n)‖ ^ 2 +
        ccmRestrictedWeilCanonicalGroundHeadDefect a n := by
  rw [ccmRestrictedWeilCompletedErrorDefectBalance_eq_sourceQuadratic]
  unfold ccmRestrictedWeilCanonicalGroundHeadDefect
  ring

theorem ccmRestrictedWeilCanonicalGroundHead_ground_part_le_completedErrorDefectBalance
    (a : SuzukiPositiveAperture) (n : ℕ) :
    ccmRestrictedWeilGroundEnergy a *
        ‖ccmArchimedeanFormToAperture a
          (ccmRestrictedWeilCanonicalGroundHead a n)‖ ^ 2 ≤
      ccmRestrictedWeilCompletedErrorDefectBalance a
        (ccmRestrictedWeilCanonicalGroundHead a n) := by
  rw [ccmRestrictedWeilCanonicalGroundHead_completedErrorDefectBalance_eq_ground_add_tail]
  exact le_add_of_nonneg_right
    (ccmRestrictedWeilCanonicalGroundHeadDefect_nonneg a n)

/-- The balance's excess over the exact-ground part is precisely the already-certified vanishing
head error, with the source-aligned quantitative rate. -/
theorem ccmRestrictedWeilCanonicalGroundHead_completedErrorDefectBalance_sub_ground_le_rate
    (a : SuzukiPositiveAperture) (n : ℕ) :
    ccmRestrictedWeilCompletedErrorDefectBalance a
          (ccmRestrictedWeilCanonicalGroundHead a n) -
        ccmRestrictedWeilGroundEnergy a *
          ‖ccmArchimedeanFormToAperture a
            (ccmRestrictedWeilCanonicalGroundHead a n)‖ ^ 2 ≤
      ccmRestrictedWeilSourceAccuracyThreshold a
          (ccmRestrictedWeilCanonicalHeadAccuracy n) *
          ‖ccmRestrictedWeilCanonicalGroundForcing a‖ ^ 2 +
        (‖ccmRestrictedWeilBoundedRemainder a‖ +
            |ccmRestrictedWeilGroundEnergy a|) *
          (ccmRestrictedWeilSourceAccuracyThreshold a
            (ccmRestrictedWeilCanonicalHeadAccuracy n)) ^ 2 *
          ‖ccmRestrictedWeilCanonicalGroundForcing a‖ ^ 2 := by
  rw [ccmRestrictedWeilCanonicalGroundHead_completedErrorDefectBalance_eq_ground_add_tail]
  convert ccmRestrictedWeilCanonicalGroundHeadDefect_le_rate a n using 1
  ring

end RHTower
