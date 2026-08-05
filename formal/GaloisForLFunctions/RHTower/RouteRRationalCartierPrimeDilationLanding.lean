import GaloisForLFunctions.RHTower.RouteRFixedTraceTailRoos
import GaloisForLFunctions.RHTower.XiCriticalLineIntegrality

open Polynomial Complex

namespace RHTower

noncomputable section

/-- A polynomial presentation of a rational Cartier potential with a fixed coefficient at one and
an eigenrelation under dilation by `q`. -/
structure RationalCartierDilationPresentation
    (q gain coefficient : ℂ) where
  numerator : ℂ[X]
  denominator : ℂ[X]
  denominator_ne_zero : denominator ≠ 0
  regularAtOne : denominator.eval 1 ≠ 0
  coefficientFaithful : numerator.eval 1 = coefficient * denominator.eval 1
  primeDilation :
    numerator.comp (C q * X) * denominator =
      C gain * numerator * denominator.comp (C q * X)

namespace RationalCartierDilationPresentation

variable {q gain coefficient : ℂ}

def toRatFunc (H : RationalCartierDilationPresentation q gain coefficient) : RatFunc ℂ :=
  algebraMap ℂ[X] (RatFunc ℂ) H.numerator /
    algebraMap ℂ[X] (RatFunc ℂ) H.denominator

/-- The same rational presentation after the geometric coordinate is dilated by `q`. -/
def primeDilatedRatFunc
    (H : RationalCartierDilationPresentation q gain coefficient) : RatFunc ℂ :=
  algebraMap ℂ[X] (RatFunc ℂ) (H.numerator.comp (C q * X)) /
    algebraMap ℂ[X] (RatFunc ℂ) (H.denominator.comp (C q * X))

theorem numerator_ne_zero
    (H : RationalCartierDilationPresentation q gain coefficient)
    (hcoefficient : coefficient ≠ 0) :
    H.numerator ≠ 0 := by
  intro hzero
  have hright : coefficient * H.denominator.eval 1 ≠ 0 :=
    mul_ne_zero hcoefficient H.regularAtOne
  have hfaithful := H.coefficientFaithful
  rw [hzero] at hfaithful
  simp only [eval_zero] at hfaithful
  exact hright hfaithful.symm

theorem toRatFunc_ne_zero
    (H : RationalCartierDilationPresentation q gain coefficient)
    (hcoefficient : coefficient ≠ 0) :
    H.toRatFunc ≠ 0 := by
  rw [toRatFunc]
  exact div_ne_zero
    (RatFunc.algebraMap_ne_zero (H.numerator_ne_zero hcoefficient))
    (RatFunc.algebraMap_ne_zero H.denominator_ne_zero)

theorem denominator_comp_ne_zero
    (H : RationalCartierDilationPresentation q gain coefficient)
    (hq : q ≠ 0) :
    H.denominator.comp (C q * X) ≠ 0 := by
  rw [← leadingCoeff_ne_zero]
  rw [leadingCoeff_comp (by rw [natDegree_C_mul_X q hq]; exact one_ne_zero),
    leadingCoeff_C_mul_X]
  exact mul_ne_zero (leadingCoeff_ne_zero.mpr H.denominator_ne_zero) (pow_ne_zero _ hq)

/-- The cross-multiplied field in the presentation is exactly the rational-function eigenrelation
`H(qz) = gain * H(z)`. -/
theorem primeDilatedRatFunc_eq_gain_mul
    (H : RationalCartierDilationPresentation q gain coefficient)
    (hq : q ≠ 0) :
    H.primeDilatedRatFunc = RatFunc.C gain * H.toRatFunc := by
  rw [primeDilatedRatFunc, toRatFunc]
  have hden : algebraMap ℂ[X] (RatFunc ℂ) H.denominator ≠ 0 :=
    RatFunc.algebraMap_ne_zero H.denominator_ne_zero
  have hdenComp :
      algebraMap ℂ[X] (RatFunc ℂ) (H.denominator.comp (C q * X)) ≠ 0 :=
    RatFunc.algebraMap_ne_zero (H.denominator_comp_ne_zero hq)
  rw [← mul_div_assoc, div_eq_div_iff hdenComp hden]
  rw [← RatFunc.algebraMap_C, ← map_mul, ← map_mul, ← map_mul]
  exact congrArg (algebraMap ℂ[X] (RatFunc ℂ)) H.primeDilation

/-- Valuation at infinity of a nonzero rational dilation eigenvector identifies its eigenvalue
with the integral degree character. -/
theorem gain_mul_prime_pow_eq_prime_pow
    (H : RationalCartierDilationPresentation q gain coefficient)
    (hq : q ≠ 0) (hcoefficient : coefficient ≠ 0) :
    gain * q ^ H.denominator.natDegree = q ^ H.numerator.natDegree := by
  have hqDegree : (C q * X : ℂ[X]).natDegree = 1 :=
    natDegree_C_mul_X q hq
  have hqDegreeNe : (C q * X : ℂ[X]).natDegree ≠ 0 := by
    rw [hqDegree]
    exact one_ne_zero
  have hnum : H.numerator ≠ 0 := H.numerator_ne_zero hcoefficient
  have hnumCompLC :
      (H.numerator.comp (C q * X)).leadingCoeff =
        H.numerator.leadingCoeff * q ^ H.numerator.natDegree := by
    rw [leadingCoeff_comp hqDegreeNe, leadingCoeff_C_mul_X]
  have hdenCompLC :
      (H.denominator.comp (C q * X)).leadingCoeff =
        H.denominator.leadingCoeff * q ^ H.denominator.natDegree := by
    rw [leadingCoeff_comp hqDegreeNe, leadingCoeff_C_mul_X]
  have hlc := congrArg Polynomial.leadingCoeff H.primeDilation
  simp only [leadingCoeff_mul, leadingCoeff_C, hnumCompLC, hdenCompLC] at hlc
  have hcancel : H.numerator.leadingCoeff * H.denominator.leadingCoeff ≠ 0 :=
    mul_ne_zero (leadingCoeff_ne_zero.mpr hnum)
      (leadingCoeff_ne_zero.mpr H.denominator_ne_zero)
  have hfactored :
      (H.numerator.leadingCoeff * H.denominator.leadingCoeff) *
          (q ^ H.numerator.natDegree - gain * q ^ H.denominator.natDegree) = 0 := by
    linear_combination hlc
  have hdegree := (mul_eq_zero.mp hfactored).resolve_left hcancel
  exact (sub_eq_zero.mp hdegree).symm

end RationalCartierDilationPresentation

/-- Multiplicity-leading Xi coefficient retained by the rational Cartier presentation. -/
def ccmRationalAdelicPrimeXiCartierCoefficient (rho : XiDivisorSupport) : ℂ :=
  iteratedDeriv (xiSupportMultiplicity rho) XiC (xiSpectralPointSupport rho)

theorem ccmRationalAdelicPrimeXiCartierCoefficient_ne_zero (rho : XiDivisorSupport) :
    ccmRationalAdelicPrimeXiCartierCoefficient rho ≠ 0 := by
  exact iteratedDeriv_XiC_ne_zero_at_supportMultiplicity rho

/-- Exact specialized interface for the still-open source producer. -/
def CCMRationalAdelicPrimeXiRationalCartierLanding
    (p : Nat.Primes) (rho : XiDivisorSupport) : Prop :=
  Nonempty (RationalCartierDilationPresentation
    (p : ℂ) (deningerHalfDensityMateGain p (rho : ℂ) : ℂ)
    (ccmRationalAdelicPrimeXiCartierCoefficient rho))

/-- A nonzero coefficient-faithful rational prime-dilation potential forces integral centered
weight. -/
theorem ccmRationalAdelicPrimeXiRationalCartierLanding_centeredRate_eq_int
    (p : Nat.Primes) (rho : XiDivisorSupport)
    (hlanding : CCMRationalAdelicPrimeXiRationalCartierLanding p rho) :
    ∃ k : ℤ, primeDepthBVWoldXiCenteredRate rho = (k : ℝ) := by
  rcases hlanding with ⟨H⟩
  have hpNat : 2 ≤ (p : ℕ) := p.2.two_le
  have hpRealPos : 0 < (p : ℝ) := by exact_mod_cast p.2.pos
  have hpRealOne : 1 < (p : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le Nat.one_lt_two hpNat)
  have hpComplex : (p : ℂ) ≠ 0 := by exact_mod_cast p.2.ne_zero
  have hdegreeComplex := H.gain_mul_prime_pow_eq_prime_pow hpComplex
    (ccmRationalAdelicPrimeXiCartierCoefficient_ne_zero rho)
  have hdegreeReal :
      deningerHalfDensityMateGain p (rho : ℂ) *
          (p : ℝ) ^ H.denominator.natDegree =
        (p : ℝ) ^ H.numerator.natDegree := by
    exact_mod_cast hdegreeComplex
  have hgainPos := deningerHalfDensityMateGain_pos p (rho : ℂ)
  have hpNe : (p : ℝ) ≠ 0 := ne_of_gt hpRealPos
  have hlog := congrArg Real.log hdegreeReal
  rw [Real.log_mul (ne_of_gt hgainPos) (pow_ne_zero _ hpNe),
    Real.log_pow, Real.log_pow] at hlog
  change
    Real.log (Real.exp ((2 * (rho : ℂ).re - 1) * Real.log (p : ℕ))) +
        (H.denominator.natDegree : ℝ) * Real.log (p : ℝ) =
      (H.numerator.natDegree : ℝ) * Real.log (p : ℝ) at hlog
  rw [Real.log_exp] at hlog
  have hlogp : 0 < Real.log (p : ℝ) := Real.log_pos hpRealOne
  have hrate : primeDepthBVWoldXiCenteredRate rho =
      (H.numerator.natDegree : ℝ) - H.denominator.natDegree := by
    rw [primeDepthBVWoldXiCenteredRate]
    have hmul :
        (primeDepthBVWoldXiCenteredRate rho -
          ((H.numerator.natDegree : ℝ) - H.denominator.natDegree)) *
            Real.log (p : ℝ) = 0 := by
      rw [primeDepthBVWoldXiCenteredRate]
      linear_combination hlog
    exact sub_eq_zero.mp ((mul_eq_zero.mp hmul).resolve_right (ne_of_gt hlogp))
  refine ⟨(H.numerator.natDegree : ℤ) - H.denominator.natDegree, ?_⟩
  rw [hrate]
  push_cast
  ring

/-- Bonnet-style orbit rigidity in the open Xi strip: the rational Cartier landing annihilates the
centered Route-R rate. -/
theorem ccmRationalAdelicPrimeXiRationalCartierLanding_centeredRate_eq_zero
    (p : Nat.Primes) (rho : XiDivisorSupport)
    (hlanding : CCMRationalAdelicPrimeXiRationalCartierLanding p rho) :
    primeDepthBVWoldXiCenteredRate rho = 0 := by
  obtain ⟨k, hk⟩ :=
    ccmRationalAdelicPrimeXiRationalCartierLanding_centeredRate_eq_int p rho hlanding
  have hstrip := xi_divisor_support_re_mem_open_unit rho
  have hkLower : (-1 : ℝ) < (k : ℝ) := by
    rw [← hk, primeDepthBVWoldXiCenteredRate]
    linarith
  have hkUpper : (k : ℝ) < 1 := by
    rw [← hk, primeDepthBVWoldXiCenteredRate]
    linarith
  have hkZero : k = 0 := by
    have hLowerInt : (-1 : ℤ) < k := by exact_mod_cast hkLower
    have hUpperInt : k < 1 := by exact_mod_cast hkUpper
    omega
  rw [hkZero] at hk
  simpa using hk

theorem ccmRationalAdelicPrimeXiRationalCartierLanding_hodgeMateCoefficient_eq_zero
    (p : Nat.Primes) (rho : XiDivisorSupport)
    (hlanding : CCMRationalAdelicPrimeXiRationalCartierLanding p rho) :
    ccmRationalAdelicPrimeXiHodgeMateCoefficient p rho = 0 := by
  rw [ccmRationalAdelicPrimeXiHodgeMateCoefficient_eq_zero_iff_re_eq_half]
  exact (primeDepthBVWoldXiCenteredRate_eq_zero_iff rho).mp
    (ccmRationalAdelicPrimeXiRationalCartierLanding_centeredRate_eq_zero p rho hlanding)

theorem ccmRationalAdelicPrimeXiRationalCartierLanding_of_hodgeMateCoefficient_eq_zero
    (p : Nat.Primes) (rho : XiDivisorSupport)
    (hzero : ccmRationalAdelicPrimeXiHodgeMateCoefficient p rho = 0) :
    CCMRationalAdelicPrimeXiRationalCartierLanding p rho := by
  have hre :=
    (ccmRationalAdelicPrimeXiHodgeMateCoefficient_eq_zero_iff_re_eq_half p rho).mp hzero
  have hgain : deningerHalfDensityMateGain p (rho : ℂ) = 1 :=
    (deningerHalfDensityMateGain_eq_one_iff_re_eq_half p.2.two_le (rho : ℂ)).2 hre
  refine ⟨{
    numerator := C (ccmRationalAdelicPrimeXiCartierCoefficient rho)
    denominator := 1
    denominator_ne_zero := one_ne_zero
    regularAtOne := by simp
    coefficientFaithful := by simp
    primeDilation := ?_
  }⟩
  rw [hgain]
  simp

theorem ccmRationalAdelicPrimeXiRationalCartierLanding_iff_hodgeMateCoefficient_eq_zero
    (p : Nat.Primes) (rho : XiDivisorSupport) :
    CCMRationalAdelicPrimeXiRationalCartierLanding p rho ↔
      ccmRationalAdelicPrimeXiHodgeMateCoefficient p rho = 0 := by
  exact ⟨ccmRationalAdelicPrimeXiRationalCartierLanding_hodgeMateCoefficient_eq_zero p rho,
    ccmRationalAdelicPrimeXiRationalCartierLanding_of_hodgeMateCoefficient_eq_zero p rho⟩

theorem ccmRationalAdelicPrimeXiRationalCartierLanding_iff_re_eq_half
    (p : Nat.Primes) (rho : XiDivisorSupport) :
    CCMRationalAdelicPrimeXiRationalCartierLanding p rho ↔
      (rho : ℂ).re = 1 / 2 := by
  rw [ccmRationalAdelicPrimeXiRationalCartierLanding_iff_hodgeMateCoefficient_eq_zero,
    ccmRationalAdelicPrimeXiHodgeMateCoefficient_eq_zero_iff_re_eq_half]

theorem ccmRationalAdelicPrimeXiRationalCartierLanding_iff_mateGain_eq_one
    (p : Nat.Primes) (rho : XiDivisorSupport) :
    CCMRationalAdelicPrimeXiRationalCartierLanding p rho ↔
      deningerHalfDensityMateGain p (rho : ℂ) = 1 := by
  rw [ccmRationalAdelicPrimeXiRationalCartierLanding_iff_re_eq_half,
    deningerHalfDensityMateGain_eq_one_iff_re_eq_half p.2.two_le]

/-- The leading Xi coefficient transforms with exact jet parity under the functional-equation
Gamma orientation. -/
theorem ccmRationalAdelicPrimeXiCartierCoefficient_reflection
    (rho : XiDivisorSupport) :
    ccmRationalAdelicPrimeXiCartierCoefficient (xiZeroReflectEquiv rho) =
      (-1 : ℂ) ^ xiSupportMultiplicity rho *
        ccmRationalAdelicPrimeXiCartierCoefficient rho := by
  rw [ccmRationalAdelicPrimeXiCartierCoefficient,
    ccmRationalAdelicPrimeXiCartierCoefficient,
    xiSupportMultiplicity_reflect, xiSpectralPointSupport_reflect,
    iteratedDeriv_XiC_neg]

/-- Existence of the specialized rational Cartier eigenpotential is equivalent in both Gamma
orientations.  This does not construct the required functorial relation between the potentials. -/
theorem ccmRationalAdelicPrimeXiRationalCartierLanding_reflection_iff
    (p : Nat.Primes) (rho : XiDivisorSupport) :
    CCMRationalAdelicPrimeXiRationalCartierLanding p (xiZeroReflectEquiv rho) ↔
      CCMRationalAdelicPrimeXiRationalCartierLanding p rho := by
  rw [ccmRationalAdelicPrimeXiRationalCartierLanding_iff_re_eq_half,
    ccmRationalAdelicPrimeXiRationalCartierLanding_iff_re_eq_half,
    xiZeroReflectEquiv_apply]
  simp only [sub_re, one_re]
  constructor <;> intro h <;> linarith

theorem ccmRationalAdelicPrimeXiRationalCartierLanding_iff_sameFiberNormIdentity
    (p : Nat.Primes) (rho : XiDivisorSupport) :
    CCMRationalAdelicPrimeXiRationalCartierLanding p rho ↔
      CCMRationalAdelicPrimeXiSameFiberNormIdentity p rho := by
  rw [ccmRationalAdelicPrimeXiRationalCartierLanding_iff_hodgeMateCoefficient_eq_zero,
    ccmRationalAdelicPrimeXiSameFiberNormIdentity_iff_hodgeMateCoefficient_eq_zero]

theorem ccmRationalAdelicPrimeXiRationalCartierLanding_iff_sourceDaggerIdentity
    (p : Nat.Primes) (rho : XiDivisorSupport) :
    CCMRationalAdelicPrimeXiRationalCartierLanding p rho ↔
      CCMRationalAdelicPrimeXiSourceDaggerIdentity p rho := by
  rw [ccmRationalAdelicPrimeXiRationalCartierLanding_iff_hodgeMateCoefficient_eq_zero,
    ccmRationalAdelicPrimeXiSourceDaggerIdentity_iff_hodgeMateCoefficient_eq_zero]

theorem forall_ccmRationalAdelicPrimeXiRationalCartierLanding_iff_riemannHypothesis
    (p : Nat.Primes) :
    (∀ rho : XiDivisorSupport,
      CCMRationalAdelicPrimeXiRationalCartierLanding p rho) ↔ RiemannHypothesis := by
  rw [← forall_ccmRationalAdelicPrimeXiSameFiberNormIdentity_iff_riemannHypothesis p]
  exact forall_congr' fun rho =>
    ccmRationalAdelicPrimeXiRationalCartierLanding_iff_sameFiberNormIdentity p rho

end

end RHTower

