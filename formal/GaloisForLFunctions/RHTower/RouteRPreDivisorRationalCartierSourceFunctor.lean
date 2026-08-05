import GaloisForLFunctions.RHTower.RouteRRationalCartierPrimeDilationLanding

/-!
# Pre-divisor rational Cartier source functor

The literal degree-one rational-adelic cyclic source has a canonical rational potential before
any Xi divisor is selected.  Multiply its cyclic trace by an independently graded Xi jet and
regard the resulting scalar as a constant rational function.  This construction is linear in the
source, invariant under cyclic rotation, and fixed by every geometric dilation.

At the retained ordinary-prime atom and the first nonzero Xi jet, the potential is exactly the
nonzero multiplicity-leading Xi coefficient.  Its failure to intertwine the physical prime
dilation is `(1 - gain) * coefficient`.  This file proves that this scalar, and its constant
rational-function image, are the negative of the canonical coordinate of the already constructed
cofinal central Bockstein class.

Thus source rationality, coefficient faithfulness, and non-erasure are unconditional.  Physical
equivariance remains exactly the source-null-homology/RH-bearing theorem; no vanishing is asserted
here.
-/

open Polynomial Complex

namespace RHTower

noncomputable section

/-- Pre-divisor coefficient functor: an independent Xi jet times the literal cyclic source
trace. -/
def ccmRationalAdelicPreDivisorCartierCoefficient
    (k : ℕ) (w : ℂ) :
    CCMRationalAdelicDegreeOneCyclicSource →ₗ[ℂ] ℂ :=
  (iteratedDeriv k XiC w) • ccmRationalAdelicDegreeOneTrace

@[simp]
theorem ccmRationalAdelicPreDivisorCartierCoefficient_apply
    (k : ℕ) (w : ℂ) (x : CCMRationalAdelicDegreeOneCyclicSource) :
    ccmRationalAdelicPreDivisorCartierCoefficient k w x =
      iteratedDeriv k XiC w * ccmRationalAdelicDegreeOneTrace x := by
  rfl

/-- Genuine source cyclic rotation leaves the pre-divisor Cartier coefficient fixed. -/
theorem ccmRationalAdelicPreDivisorCartierCoefficient_rotate
    (k : ℕ) (w : ℂ) (x : CCMRationalAdelicDegreeOneCyclicSource) :
    ccmRationalAdelicPreDivisorCartierCoefficient k w
        (ccmRationalAdelicDegreeOneCyclicRotation x) =
      ccmRationalAdelicPreDivisorCartierCoefficient k w x := by
  simp [ccmRationalAdelicDegreeOneTrace_rotate]

/-- Canonical constant rational Cartier presentation supplied functorially by pre-divisor source
data.  Its source dilation character is the unit character for every geometric dilation `q`. -/
def ccmRationalAdelicPreDivisorRationalCartierPresentation
    (q : ℂ) (k : ℕ) (w : ℂ)
    (x : CCMRationalAdelicDegreeOneCyclicSource) :
    RationalCartierDilationPresentation q 1
      (ccmRationalAdelicPreDivisorCartierCoefficient k w x) where
  numerator := C (ccmRationalAdelicPreDivisorCartierCoefficient k w x)
  denominator := 1
  denominator_ne_zero := one_ne_zero
  regularAtOne := by simp
  coefficientFaithful := by simp
  primeDilation := by simp

/-- Rational-function semantics of the source presentation is the constant source coefficient. -/
@[simp]
theorem ccmRationalAdelicPreDivisorRationalCartierPresentation_toRatFunc
    (q : ℂ) (k : ℕ) (w : ℂ)
    (x : CCMRationalAdelicDegreeOneCyclicSource) :
    (ccmRationalAdelicPreDivisorRationalCartierPresentation q k w x).toRatFunc =
      RatFunc.C (ccmRationalAdelicPreDivisorCartierCoefficient k w x) := by
  simp [ccmRationalAdelicPreDivisorRationalCartierPresentation,
    RationalCartierDilationPresentation.toRatFunc]

/-- Every geometric dilation fixes the source rational potential. -/
@[simp]
theorem ccmRationalAdelicPreDivisorRationalCartierPresentation_primeDilatedRatFunc
    (q : ℂ) (k : ℕ) (w : ℂ)
    (x : CCMRationalAdelicDegreeOneCyclicSource) :
    (ccmRationalAdelicPreDivisorRationalCartierPresentation q k w x).primeDilatedRatFunc =
      RatFunc.C (ccmRationalAdelicPreDivisorCartierCoefficient k w x) := by
  simp [ccmRationalAdelicPreDivisorRationalCartierPresentation,
    RationalCartierDilationPresentation.primeDilatedRatFunc]

/-- The retained ordinary-prime atom evaluates the source coefficient functor to the chosen Xi
jet, because its literal cyclic trace is one. -/
@[simp]
theorem ccmRationalAdelicPreDivisorCartierCoefficient_primeAtom
    (p : Nat.Primes) (k : ℕ) (w : ℂ) :
    ccmRationalAdelicPreDivisorCartierCoefficient k w
        (ccmRationalAdelicOrdinaryPrimeCycleAtom p) =
      iteratedDeriv k XiC w := by
  rw [ccmRationalAdelicPreDivisorCartierCoefficient_apply,
    ccmRationalAdelicOrdinaryPrimeCycleAtom_trace_eq_one, mul_one]

/-- Specialization to the first nonzero Xi jet is coefficient-faithful. -/
theorem ccmRationalAdelicPreDivisorCartierCoefficient_primeAtom_xi
    (p : Nat.Primes) (rho : XiDivisorSupport) :
    ccmRationalAdelicPreDivisorCartierCoefficient
        (xiSupportMultiplicity rho) (xiSpectralPointSupport rho)
        (ccmRationalAdelicOrdinaryPrimeCycleAtom p) =
      ccmRationalAdelicPrimeXiCartierCoefficient rho := by
  rw [ccmRationalAdelicPreDivisorCartierCoefficient_apply,
    ccmRationalAdelicOrdinaryPrimeCycleAtom_trace_eq_one, mul_one]
  rfl

/-- The source rational potential does not erase the retained atom at any actual Xi support
point. -/
theorem ccmRationalAdelicPreDivisorRationalCartierPresentation_primeAtom_ne_zero
    (p : Nat.Primes) (rho : XiDivisorSupport) :
    (ccmRationalAdelicPreDivisorRationalCartierPresentation (p : ℂ)
      (xiSupportMultiplicity rho) (xiSpectralPointSupport rho)
      (ccmRationalAdelicOrdinaryPrimeCycleAtom p)).toRatFunc ≠ 0 := by
  rw [ccmRationalAdelicPreDivisorRationalCartierPresentation_toRatFunc,
    ccmRationalAdelicPreDivisorCartierCoefficient_primeAtom_xi]
  simpa using RatFunc.C_injective.ne
    (ccmRationalAdelicPrimeXiCartierCoefficient_ne_zero rho)

/-- The source coefficient has exact functional-equation parity in the reflected Gamma
orientation. -/
theorem ccmRationalAdelicPreDivisorCartierCoefficient_primeAtom_xi_reflection
    (p : Nat.Primes) (rho : XiDivisorSupport) :
    ccmRationalAdelicPreDivisorCartierCoefficient
        (xiSupportMultiplicity (xiZeroReflectEquiv rho))
        (xiSpectralPointSupport (xiZeroReflectEquiv rho))
        (ccmRationalAdelicOrdinaryPrimeCycleAtom p) =
      (-1 : ℂ) ^ xiSupportMultiplicity rho *
        ccmRationalAdelicPreDivisorCartierCoefficient
          (xiSupportMultiplicity rho) (xiSpectralPointSupport rho)
          (ccmRationalAdelicOrdinaryPrimeCycleAtom p) := by
  rw [ccmRationalAdelicPreDivisorCartierCoefficient_primeAtom_xi,
    ccmRationalAdelicPreDivisorCartierCoefficient_primeAtom_xi,
    ccmRationalAdelicPrimeXiCartierCoefficient_reflection]

/-- Scalar failure of the canonical source potential to intertwine the physical Xi prime
dilation. -/
def ccmRationalAdelicPrimeXiSourceCartierPhysicalDilationDefect
    (p : Nat.Primes) (rho : XiDivisorSupport) : ℂ :=
  ccmRationalAdelicPreDivisorCartierCoefficient
      (xiSupportMultiplicity rho) (xiSpectralPointSupport rho)
      (ccmRationalAdelicOrdinaryPrimeCycleAtom p) -
    (deningerHalfDensityMateGain p (rho : ℂ) : ℂ) *
      ccmRationalAdelicPreDivisorCartierCoefficient
        (xiSupportMultiplicity rho) (xiSpectralPointSupport rho)
        (ccmRationalAdelicOrdinaryPrimeCycleAtom p)

/-- Constant rational-function form of the physical dilation defect. -/
def ccmRationalAdelicPrimeXiSourceCartierPhysicalRatFuncDefect
    (p : Nat.Primes) (rho : XiDivisorSupport) : RatFunc ℂ :=
  (ccmRationalAdelicPreDivisorRationalCartierPresentation (p : ℂ)
      (xiSupportMultiplicity rho) (xiSpectralPointSupport rho)
      (ccmRationalAdelicOrdinaryPrimeCycleAtom p)).primeDilatedRatFunc -
    RatFunc.C (deningerHalfDensityMateGain p (rho : ℂ) : ℂ) *
      (ccmRationalAdelicPreDivisorRationalCartierPresentation (p : ℂ)
        (xiSupportMultiplicity rho) (xiSpectralPointSupport rho)
        (ccmRationalAdelicOrdinaryPrimeCycleAtom p)).toRatFunc

/-- Exact nondivisive factorization of the source/physical comparison defect. -/
theorem ccmRationalAdelicPrimeXiSourceCartierPhysicalDilationDefect_eq
    (p : Nat.Primes) (rho : XiDivisorSupport) :
    ccmRationalAdelicPrimeXiSourceCartierPhysicalDilationDefect p rho =
      (1 - (deningerHalfDensityMateGain p (rho : ℂ) : ℂ)) *
        ccmRationalAdelicPrimeXiCartierCoefficient rho := by
  rw [ccmRationalAdelicPrimeXiSourceCartierPhysicalDilationDefect,
    ccmRationalAdelicPreDivisorCartierCoefficient_primeAtom_xi]
  ring

/-- The rational-function defect is the constant embedding of the scalar defect. -/
theorem ccmRationalAdelicPrimeXiSourceCartierPhysicalRatFuncDefect_eq
    (p : Nat.Primes) (rho : XiDivisorSupport) :
    ccmRationalAdelicPrimeXiSourceCartierPhysicalRatFuncDefect p rho =
      RatFunc.C
        (ccmRationalAdelicPrimeXiSourceCartierPhysicalDilationDefect p rho) := by
  rw [ccmRationalAdelicPrimeXiSourceCartierPhysicalRatFuncDefect,
    ccmRationalAdelicPreDivisorRationalCartierPresentation_primeDilatedRatFunc,
    ccmRationalAdelicPreDivisorRationalCartierPresentation_toRatFunc]
  rw [← map_mul, ← map_sub]
  rfl

/-- **Source-to-Cartier comparison identity.**  Physical failure of the canonical rational source
potential is exactly the negative canonical coordinate of the cofinal central Bockstein class. -/
theorem ccmRationalAdelicPrimeXiSourceCartierPhysicalDilationDefect_eq_neg_cofinalReadout
    (p : Nat.Primes) (rho : XiDivisorSupport) (m : ℕ) :
    ccmRationalAdelicPrimeXiSourceCartierPhysicalDilationDefect p rho =
      -tateClockCofinalRelativeH1Equiv m
        (ccmMobiusThetaCofinalSourceHomologyLanding (p : ℕ)
          (xiSupportMultiplicity rho) m (rho : ℂ)
          (xiSpectralPointSupport rho)
          (ccmRationalAdelicOrdinaryPrimeCycleAtom p)) := by
  rw [ccmMobiusThetaCofinalSourceHomologyLanding_readout,
    ccmRationalAdelicOrdinaryPrimeCycleAtom_trace_eq_one,
    mul_one, ccmRationalAdelicPrimeXiSourceCartierPhysicalDilationDefect_eq,
    ccmRationalAdelicPrimeXiCartierCoefficient]
  ring

/-- Vanishing of the physical rational-source comparison defect is literally null-homology of
the explicit cofinal central Bockstein class. -/
theorem ccmRationalAdelicPrimeXiSourceCartierPhysicalDilationDefect_eq_zero_iff_sourceNull
    (p : Nat.Primes) (rho : XiDivisorSupport) (m : ℕ) :
    ccmRationalAdelicPrimeXiSourceCartierPhysicalDilationDefect p rho = 0 ↔
      CCMMobiusThetaPhysicalDefectSourceNullHomologous (p : ℕ) rho p m := by
  rw [
    ccmRationalAdelicPrimeXiSourceCartierPhysicalDilationDefect_eq_neg_cofinalReadout]
  unfold CCMMobiusThetaPhysicalDefectSourceNullHomologous
  constructor
  · intro h
    have hread : tateClockCofinalRelativeH1Equiv m
        (ccmMobiusThetaCofinalSourceHomologyLanding (p : ℕ)
          (xiSupportMultiplicity rho) m (rho : ℂ)
          (xiSpectralPointSupport rho)
          (ccmRationalAdelicOrdinaryPrimeCycleAtom p)) = 0 := by
      exact neg_eq_zero.mp h
    exact (tateClockCofinalRelativeH1Equiv m).injective
      (by rw [map_zero]; exact hread)
  · intro h
    rw [h, map_zero, neg_zero]

/-- The source/physical rational comparison defect vanishes exactly on the critical line. -/
theorem ccmRationalAdelicPrimeXiSourceCartierPhysicalDilationDefect_eq_zero_iff_re_eq_half
    (p : Nat.Primes) (rho : XiDivisorSupport) (m : ℕ) :
    ccmRationalAdelicPrimeXiSourceCartierPhysicalDilationDefect p rho = 0 ↔
      (rho : ℂ).re = 1 / 2 :=
  (ccmRationalAdelicPrimeXiSourceCartierPhysicalDilationDefect_eq_zero_iff_sourceNull
    p rho m).trans
    (ccmMobiusThetaPhysicalDefectSourceNullHomologous_iff
      p.2.two_le rho p m)

/-- The canonical source potential becomes the physical rational Cartier landing exactly when its
explicit comparison defect vanishes. -/
theorem ccmRationalAdelicPrimeXiSourceCartierPhysicalDilationDefect_eq_zero_iff_landing
    (p : Nat.Primes) (rho : XiDivisorSupport) (m : ℕ) :
    ccmRationalAdelicPrimeXiSourceCartierPhysicalDilationDefect p rho = 0 ↔
      CCMRationalAdelicPrimeXiRationalCartierLanding p rho :=
  (ccmRationalAdelicPrimeXiSourceCartierPhysicalDilationDefect_eq_zero_iff_re_eq_half
    p rho m).trans
    (ccmRationalAdelicPrimeXiRationalCartierLanding_iff_re_eq_half p rho).symm

/-- The same comparison defect is exactly the Route-R Hodge-mate coefficient wall. -/
theorem
    ccmRationalAdelicPrimeXiSourceCartierPhysicalDilationDefect_eq_zero_iff_hodgeMateCoefficient
    (p : Nat.Primes) (rho : XiDivisorSupport) (m : ℕ) :
    ccmRationalAdelicPrimeXiSourceCartierPhysicalDilationDefect p rho = 0 ↔
      ccmRationalAdelicPrimeXiHodgeMateCoefficient p rho = 0 :=
  (ccmRationalAdelicPrimeXiSourceCartierPhysicalDilationDefect_eq_zero_iff_re_eq_half
    p rho m).trans
    (ccmRationalAdelicPrimeXiHodgeMateCoefficient_eq_zero_iff_re_eq_half p rho).symm

/-- Rational-function comparison has the same exact source-null-homology wall. -/
theorem ccmRationalAdelicPrimeXiSourceCartierPhysicalRatFuncDefect_eq_zero_iff_sourceNull
    (p : Nat.Primes) (rho : XiDivisorSupport) (m : ℕ) :
    ccmRationalAdelicPrimeXiSourceCartierPhysicalRatFuncDefect p rho = 0 ↔
      CCMMobiusThetaPhysicalDefectSourceNullHomologous (p : ℕ) rho p m := by
  rw [ccmRationalAdelicPrimeXiSourceCartierPhysicalRatFuncDefect_eq,
    ← map_zero (RatFunc.C (K := ℂ))]
  exact (RatFunc.C_injective.eq_iff).trans
    (ccmRationalAdelicPrimeXiSourceCartierPhysicalDilationDefect_eq_zero_iff_sourceNull
      p rho m)

end


end RHTower
