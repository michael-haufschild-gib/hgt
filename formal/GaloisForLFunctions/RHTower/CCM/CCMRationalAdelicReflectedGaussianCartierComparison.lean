import GaloisForLFunctions.RHTower.CCM.CCMRationalAdelicPrimeIsotropyStokesRegulator
import GaloisForLFunctions.RHTower.Deninger.DeningerMeyerReflectedGaussianHarmonicSourcePrimitive
import GaloisForLFunctions.RHTower.Deninger.DeningerMeyerReflectedGaussianCompletedGreenDefect

/-!
# Rational-adelic atom to reflected-Gaussian Cartier comparison

This file joins two independently constructed source objects. The period-one ordinary-prime
relative class is read by the bilateral rational-adelic Stokes regulator and used as coefficient
of the fixed reflected-Gaussian singular Cartier residue. The resulting map is coefficient-faithful
on the detected quotient, its retained atom is reconstructed from both absolute-Euler Gamma Cauchy
boundary lines, and its harmonic Green mate preserves the fixed Xi Hilbert polarization.

The final Green-provenance image is still the known horizontal defect: its vanishing is equivalent
to RH. Thus this construction closes source provenance, two-sided non-erasure, singular admission,
and fixed-polarization Hodge transport, but does not assert the missing same-fibre physical
annihilation.
-/

open Complex

namespace RHTower

noncomputable section

open DeningerMeyerGaussianGreen

/-- Period coefficient times the source-graded singular Cartier residue. -/
def ccmRationalAdelicPrimeReflectedGaussianCartierComparison
    (p : Nat.Primes) :
    (ccmRationalAdelicPrimeRelativeComplex p).H1 →ₗ[ℂ] XiDivisorL2 :=
  (LinearMap.toSpanSingleton ℂ XiDivisorL2
      reflectedGaussianHorizonAdmittedResidue).comp
    (ccmRationalAdelicPrimeRelativeH1StokesRegulator p)

@[simp]
theorem ccmRationalAdelicPrimeReflectedGaussianCartierComparison_apply
    (p : Nat.Primes)
    (x : (ccmRationalAdelicPrimeRelativeComplex p).H1) :
    ccmRationalAdelicPrimeReflectedGaussianCartierComparison p x =
      ccmRationalAdelicPrimeRelativeH1StokesRegulator p x •
        reflectedGaussianHorizonAdmittedResidue :=
  rfl

/-- Singular Cartier residue and reflected-Gaussian horizon are the same completed vector. -/
theorem reflectedGaussianHorizonAdmittedResidue_eq_gradeL2 :
    reflectedGaussianHorizonAdmittedResidue =
      reflectedGaussianHorizonGradeL2 := by
  ext q
  rw [reflectedGaussianHorizonAdmittedResidue_apply,
    reflectedGaussianHorizonGradeL2_apply]

/-- Exact landing of the retained rational-adelic cyclic atom. -/
theorem ccmRationalAdelicPrimeReflectedGaussianCartierComparison_class
    (p : Nat.Primes) :
    ccmRationalAdelicPrimeReflectedGaussianCartierComparison p
        (ccmRationalAdelicPrimeRelativeClass p) =
      reflectedGaussianHorizonAdmittedResidue := by
  rw [ccmRationalAdelicPrimeReflectedGaussianCartierComparison_apply,
    ccmRationalAdelicPrimeRelativeH1StokesRegulator_class, one_smul]

/-- The comparison loses exactly the kernel of the independent Stokes period, and no coefficient
beyond it. -/
theorem ccmRationalAdelicPrimeReflectedGaussianCartierComparison_eq_zero_iff
    (p : Nat.Primes)
    (x : (ccmRationalAdelicPrimeRelativeComplex p).H1) :
    ccmRationalAdelicPrimeReflectedGaussianCartierComparison p x = 0 ↔
      ccmRationalAdelicPrimeRelativeH1StokesRegulator p x = 0 := by
  constructor
  · intro hx
    let q : XiZeroCopy := Classical.choice inferInstance
    have hq := congrArg (fun a : XiDivisorL2 => a q) hx
    rw [ccmRationalAdelicPrimeReflectedGaussianCartierComparison_apply,
      lp.coeFn_smul, Pi.smul_apply, reflectedGaussianHorizonAdmittedResidue_apply,
      ] at hq
    change ccmRationalAdelicPrimeRelativeH1StokesRegulator p x *
      reflectedGaussianHorizonGrade q = 0 at hq
    exact (mul_eq_zero.mp hq).resolve_right
      (reflectedGaussianHorizonGrade_ne_zero q)
  · intro hx
    rw [ccmRationalAdelicPrimeReflectedGaussianCartierComparison_apply, hx, zero_smul]

/-- The period-one cyclic atom is retained by the singular Cartier comparison. -/
theorem ccmRationalAdelicPrimeReflectedGaussianCartierComparison_class_ne_zero
    (p : Nat.Primes) :
    ccmRationalAdelicPrimeReflectedGaussianCartierComparison p
        (ccmRationalAdelicPrimeRelativeClass p) ≠ 0 := by
  intro hzero
  have hperiod :=
    (ccmRationalAdelicPrimeReflectedGaussianCartierComparison_eq_zero_iff
      p (ccmRationalAdelicPrimeRelativeClass p)).1 hzero
  rw [ccmRationalAdelicPrimeRelativeH1StokesRegulator_class] at hperiod
  exact one_ne_zero hperiod

/-- Upper absolute-Euler Gamma boundary leg with its source Gaussian coefficient. -/
def ccmRationalAdelicPrimeReflectedGaussianUpperComparison
    (p : Nat.Primes) (t : ℝ) :
    (ccmRationalAdelicPrimeRelativeComplex p).H1 →ₗ[ℂ] XiDivisorL2 :=
  (LinearMap.toSpanSingleton ℂ XiDivisorL2
      (reflectedGaussianCauchyProfile ((t : ℂ) + Complex.I) •
        reflectedGaussianUpperCauchyColumn t)).comp
    (ccmRationalAdelicPrimeRelativeH1StokesRegulator p)

/-- Lower absolute-Euler Gamma boundary leg with its source Gaussian coefficient. -/
def ccmRationalAdelicPrimeReflectedGaussianLowerComparison
    (p : Nat.Primes) (t : ℝ) :
    (ccmRationalAdelicPrimeRelativeComplex p).H1 →ₗ[ℂ] XiDivisorL2 :=
  (LinearMap.toSpanSingleton ℂ XiDivisorL2
      (reflectedGaussianCauchyProfile ((t : ℂ) - Complex.I) •
        reflectedGaussianLowerCauchyColumn t)).comp
    (ccmRationalAdelicPrimeRelativeH1StokesRegulator p)

@[simp]
theorem ccmRationalAdelicPrimeReflectedGaussianUpperComparison_class
    (p : Nat.Primes) (t : ℝ) :
    ccmRationalAdelicPrimeReflectedGaussianUpperComparison p t
        (ccmRationalAdelicPrimeRelativeClass p) =
      reflectedGaussianCauchyProfile ((t : ℂ) + Complex.I) •
        reflectedGaussianUpperCauchyColumn t := by
  simp [ccmRationalAdelicPrimeReflectedGaussianUpperComparison,
    ccmRationalAdelicPrimeRelativeH1StokesRegulator_class]

@[simp]
theorem ccmRationalAdelicPrimeReflectedGaussianLowerComparison_class
    (p : Nat.Primes) (t : ℝ) :
    ccmRationalAdelicPrimeReflectedGaussianLowerComparison p t
        (ccmRationalAdelicPrimeRelativeClass p) =
      reflectedGaussianCauchyProfile ((t : ℂ) - Complex.I) •
        reflectedGaussianLowerCauchyColumn t := by
  simp [ccmRationalAdelicPrimeReflectedGaussianLowerComparison,
    ccmRationalAdelicPrimeRelativeH1StokesRegulator_class]

private theorem reflectedGaussianUpperCauchyBoundaryVector_ne_zero
    (t : ℝ) :
    reflectedGaussianCauchyProfile ((t : ℂ) + Complex.I) •
        reflectedGaussianUpperCauchyColumn t ≠ 0 := by
  intro hzero
  let q : XiZeroCopy := Classical.choice inferInstance
  have hq := congrArg (fun a : XiDivisorL2 => a q) hzero
  rw [lp.coeFn_smul, Pi.smul_apply,
    reflectedGaussianUpperCauchyColumn_apply] at hq
  change reflectedGaussianCauchyProfile ((t : ℂ) + Complex.I) *
    (xiSpectralPoint q - ((t : ℂ) + Complex.I))⁻¹ = 0 at hq
  apply (mul_ne_zero (Complex.exp_ne_zero _)) at hq
  · exact hq
  · apply inv_ne_zero
    apply sub_ne_zero.mpr
    intro heq
    apply (reflectedGaussianUpperCauchyPoint t).property
    change XiC ((t : ℂ) + Complex.I) = 0
    rw [← heq]
    exact XiC_xiSpectralPoint_eq_zero q

private theorem reflectedGaussianLowerCauchyBoundaryVector_ne_zero
    (t : ℝ) :
    reflectedGaussianCauchyProfile ((t : ℂ) - Complex.I) •
        reflectedGaussianLowerCauchyColumn t ≠ 0 := by
  intro hzero
  let q : XiZeroCopy := Classical.choice inferInstance
  have hq := congrArg (fun a : XiDivisorL2 => a q) hzero
  rw [lp.coeFn_smul, Pi.smul_apply,
    reflectedGaussianLowerCauchyColumn_apply] at hq
  change reflectedGaussianCauchyProfile ((t : ℂ) - Complex.I) *
    (xiSpectralPoint q - ((t : ℂ) - Complex.I))⁻¹ = 0 at hq
  apply (mul_ne_zero (Complex.exp_ne_zero _)) at hq
  · exact hq
  · apply inv_ne_zero
    apply sub_ne_zero.mpr
    intro heq
    apply (reflectedGaussianLowerCauchyPoint t).property
    change XiC ((t : ℂ) - Complex.I) = 0
    rw [← heq]
    exact XiC_xiSpectralPoint_eq_zero q

/-- The retained cyclic atom survives the upper Gamma orientation at every boundary parameter. -/
theorem ccmRationalAdelicPrimeReflectedGaussianUpperComparison_class_ne_zero
    (p : Nat.Primes) (t : ℝ) :
    ccmRationalAdelicPrimeReflectedGaussianUpperComparison p t
        (ccmRationalAdelicPrimeRelativeClass p) ≠ 0 := by
  rw [ccmRationalAdelicPrimeReflectedGaussianUpperComparison_class]
  exact reflectedGaussianUpperCauchyBoundaryVector_ne_zero t

/-- The retained cyclic atom survives the lower Gamma orientation at every boundary parameter. -/
theorem ccmRationalAdelicPrimeReflectedGaussianLowerComparison_class_ne_zero
    (p : Nat.Primes) (t : ℝ) :
    ccmRationalAdelicPrimeReflectedGaussianLowerComparison p t
        (ccmRationalAdelicPrimeRelativeClass p) ≠ 0 := by
  rw [ccmRationalAdelicPrimeReflectedGaussianLowerComparison_class]
  exact reflectedGaussianLowerCauchyBoundaryVector_ne_zero t

/-- The cyclic atom's Cartier landing is exactly the integral of its two retained Gamma legs. -/
theorem ccmRationalAdelicPrimeReflectedGaussianCartierComparison_class_eq_twoSidedGammaIntegral
    (p : Nat.Primes) :
    ccmRationalAdelicPrimeReflectedGaussianCartierComparison p
        (ccmRationalAdelicPrimeRelativeClass p) =
      ∫ t : ℝ, reflectedGaussianPrimeGammaCauchyBoundary t := by
  rw [ccmRationalAdelicPrimeReflectedGaussianCartierComparison_class,
    reflectedGaussianHorizonAdmittedResidue_eq_gradeL2,
    integral_reflectedGaussianPrimeGammaCauchyBoundary_eq_horizonGradeL2]

/-- Fixed-polarization harmonic mate of the Cartier comparison. -/
def ccmRationalAdelicPrimeReflectedGaussianHodgeComparison
    (p : Nat.Primes) :
    (ccmRationalAdelicPrimeRelativeComplex p).H1 →ₗ[ℂ] XiDivisorL2 :=
  -(deningerArithmeticCompletedSourceGreenIsometry.toLinearMap.comp
    (ccmRationalAdelicPrimeReflectedGaussianCartierComparison p))

@[simp]
theorem ccmRationalAdelicPrimeReflectedGaussianHodgeComparison_apply
    (p : Nat.Primes)
    (x : (ccmRationalAdelicPrimeRelativeComplex p).H1) :
    ccmRationalAdelicPrimeReflectedGaussianHodgeComparison p x =
      -deningerArithmeticCompletedSourceGreen
        (ccmRationalAdelicPrimeReflectedGaussianCartierComparison p x) := by
  rfl

/-- The atom's Hodge mate is the unique completed Green primitive. -/
theorem ccmRationalAdelicPrimeReflectedGaussianHodgeComparison_class
    (p : Nat.Primes) :
    ccmRationalAdelicPrimeReflectedGaussianHodgeComparison p
        (ccmRationalAdelicPrimeRelativeClass p) =
      reflectedGaussianHorizonCompletedGreenPrimitive := by
  rw [ccmRationalAdelicPrimeReflectedGaussianHodgeComparison_apply,
    ccmRationalAdelicPrimeReflectedGaussianCartierComparison_class]
  rfl

/-- Fixed Xi Hilbert polarization is preserved by passage to the source Hodge mate. -/
theorem ccmRationalAdelicPrimeReflectedGaussianHodgeComparison_inner
    (p : Nat.Primes)
    (x y : (ccmRationalAdelicPrimeRelativeComplex p).H1) :
    inner ℂ (ccmRationalAdelicPrimeReflectedGaussianHodgeComparison p x)
        (ccmRationalAdelicPrimeReflectedGaussianHodgeComparison p y) =
      inner ℂ (ccmRationalAdelicPrimeReflectedGaussianCartierComparison p x)
        (ccmRationalAdelicPrimeReflectedGaussianCartierComparison p y) := by
  rw [ccmRationalAdelicPrimeReflectedGaussianHodgeComparison_apply,
    ccmRationalAdelicPrimeReflectedGaussianHodgeComparison_apply,
    inner_neg_left, inner_neg_right, neg_neg]
  exact deningerArithmeticCompletedSourceGreenIsometry.inner_map_map _ _

/-- The Hodge comparison is coefficient-faithful on exactly the same Stokes quotient. -/
theorem ccmRationalAdelicPrimeReflectedGaussianHodgeComparison_eq_zero_iff
    (p : Nat.Primes)
    (x : (ccmRationalAdelicPrimeRelativeComplex p).H1) :
    ccmRationalAdelicPrimeReflectedGaussianHodgeComparison p x = 0 ↔
      ccmRationalAdelicPrimeRelativeH1StokesRegulator p x = 0 := by
  rw [← ccmRationalAdelicPrimeReflectedGaussianCartierComparison_eq_zero_iff]
  constructor
  · intro hx
    rw [ccmRationalAdelicPrimeReflectedGaussianHodgeComparison_apply] at hx
    exact deningerArithmeticCompletedSourceGreenIsometry.injective
      ((neg_eq_zero.mp hx).trans (map_zero _).symm)
  · intro hx
    rw [ccmRationalAdelicPrimeReflectedGaussianHodgeComparison_apply, hx, map_zero, neg_zero]

/-- The oriented two-Gamma-line source integrates to the atom's Hodge mate. -/
theorem ccmRationalAdelicPrimeReflectedGaussianHodgeComparison_class_eq_orientedGammaIntegral
    (p : Nat.Primes) :
    ccmRationalAdelicPrimeReflectedGaussianHodgeComparison p
        (ccmRationalAdelicPrimeRelativeClass p) =
      ∫ t : ℝ, reflectedGaussianPrimeGammaOrientedCauchyBoundary t := by
  rw [ccmRationalAdelicPrimeReflectedGaussianHodgeComparison_class,
    integral_reflectedGaussianPrimeGammaOrientedCauchyBoundary_eq_greenPrimitive]

/-- Functional-equation reflection retains the cyclic atom coefficient pointwise. -/
theorem ccmRationalAdelicPrimeReflectedGaussianCartierComparison_class_reflect
    (p : Nat.Primes) (q : XiZeroCopy) :
    ccmRationalAdelicPrimeReflectedGaussianCartierComparison p
        (ccmRationalAdelicPrimeRelativeClass p) (xiZeroCopyReflectEquiv q) =
      ccmRationalAdelicPrimeReflectedGaussianCartierComparison p
        (ccmRationalAdelicPrimeRelativeClass p) q := by
  rw [ccmRationalAdelicPrimeReflectedGaussianCartierComparison_class,
    reflectedGaussianHorizonAdmittedResidue_apply,
    reflectedGaussianHorizonAdmittedResidue_apply,
    reflectedGaussianHorizonGrade_reflect]

/-- Hermitian line conjugation retains the cyclic atom in the opposite Gamma orientation. -/
theorem ccmRationalAdelicPrimeReflectedGaussianCartierComparison_class_lineConj
    (p : Nat.Primes) (q : XiZeroCopy) :
    ccmRationalAdelicPrimeReflectedGaussianCartierComparison p
        (ccmRationalAdelicPrimeRelativeClass p) (xiZeroCopyLineConjEquiv q) =
      (starRingEnd ℂ)
        (ccmRationalAdelicPrimeReflectedGaussianCartierComparison p
          (ccmRationalAdelicPrimeRelativeClass p) q) := by
  rw [ccmRationalAdelicPrimeReflectedGaussianCartierComparison_class,
    reflectedGaussianHorizonAdmittedResidue_apply,
    reflectedGaussianHorizonAdmittedResidue_apply,
    reflectedGaussianHorizonGrade_lineConj]

/-- Physical Green defect carried by the rational-adelic source comparison. -/
def ccmRationalAdelicPrimeReflectedGaussianPhysicalDefect
    (p : Nat.Primes)
    (x : (ccmRationalAdelicPrimeRelativeComplex p).H1) : XiDivisorL2 :=
  deningerArithmeticCompletedGreenProvenance
    (ccmRationalAdelicPrimeReflectedGaussianCartierComparison p x)

/-- On the cyclic atom this is exactly the existing fixed reflected-Gaussian global defect. -/
theorem ccmRationalAdelicPrimeReflectedGaussianPhysicalDefect_class
    (p : Nat.Primes) :
    ccmRationalAdelicPrimeReflectedGaussianPhysicalDefect p
        (ccmRationalAdelicPrimeRelativeClass p) =
      reflectedGaussianHorizonGreenProvenance := by
  rw [ccmRationalAdelicPrimeReflectedGaussianPhysicalDefect,
    ccmRationalAdelicPrimeReflectedGaussianCartierComparison_class,
    reflectedGaussianHorizonGreenProvenance,
    reflectedGaussianHorizonAdmittedResidue_eq_gradeL2]

/-- Exact remaining frontier: annihilating this now coefficient-faithful, fixed-polarized source
image is equivalent to RH. No vanishing premise is introduced. -/
theorem ccmRationalAdelicPrimeReflectedGaussianPhysicalDefect_class_eq_zero_iff_riemannHypothesis
    (p : Nat.Primes) :
    ccmRationalAdelicPrimeReflectedGaussianPhysicalDefect p
        (ccmRationalAdelicPrimeRelativeClass p) = 0 ↔
      RiemannHypothesis := by
  rw [ccmRationalAdelicPrimeReflectedGaussianPhysicalDefect_class,
    reflectedGaussianHorizonGreenProvenance_eq_zero_iff_riemannHypothesis]

end

end RHTower
