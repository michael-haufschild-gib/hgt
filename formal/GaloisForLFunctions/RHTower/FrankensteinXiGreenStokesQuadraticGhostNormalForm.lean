import GaloisForLFunctions.RHTower.FrankensteinXiFullIntegralGammaEvaluationProducer
import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmThetaDivisorPolarizedInterpolation
import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmThetaGreenReflectionPairNoGo

/-!
# Xi-selected Green--Stokes normal form for the quadratic inversion ghost

Functional-equation reflection folds the two compact theta divisor eigenvectors into an odd
mean-zero mode and an even mode.  The compact source inverse exchanges the folds, but the even
mode differs from its mean-zero representative by one explicit `pinnedOne` term.  Thus the
reflection-folded source obstruction is rank one, not an unspecified boundary error.

The full-Laurent Gamma quadratic ghost has the same exact Green--Stokes normal form: its canonical
coefficient multiplies `pinnedOne`.  The adjoint closed derivative kills this vector
unconditionally because `pinnedOne` is its cokernel.  This killing is not coefficient-faithful.
By contrast, admission to the physical derivative range, or annihilation by any reporter nonzero
on `pinnedOne`, is equivalent to the critical line.  These statements isolate the precise missing
source law without postulating it.
-/

open Complex MeasureTheory
open scoped ENNReal

namespace RHTower.HedenmalmThetaSource

noncomputable section

open HedenmalmQuantile HedenmalmHilbertSchmidt HedenmalmClosedWeightedDerivative

private abbrev ThetaH := Lp ℂ 2 unitIntervalMeasure

/-- Reflection-odd theta divisor fold. -/
def thetaXiReflectionOddMode (q : XiZeroCopy) : ThetaH :=
  thetaXiDivisorEigenvector q -
    thetaXiDivisorEigenvector (xiZeroCopyReflectEquiv q)

/-- Raw reflection-even theta divisor fold. -/
def thetaXiReflectionEvenRawMode (q : XiZeroCopy) : ThetaH :=
  thetaXiDivisorEigenvector q +
    thetaXiDivisorEigenvector (xiZeroCopyReflectEquiv q)

/-- Mean-zero representative of the reflection-even fold. -/
def thetaXiReflectionEvenCenteredMode (q : XiZeroCopy) : ThetaH :=
  thetaXiReflectionEvenRawMode q -
    ((2 : ℂ) * (Real.sqrt thetaSource.mass : ℂ)) • pinnedOne

/-- Reflection removes the common Xi monopole from the odd fold. -/
theorem pinnedMean_thetaXiReflectionOddMode (q : XiZeroCopy) :
    pinnedMean (thetaXiReflectionOddMode q) = 0 := by
  calc
    pinnedMean (thetaXiReflectionOddMode q) =
        thetaPinnedMeanCLM (thetaXiReflectionOddMode q) :=
      (thetaPinnedMeanCLM_apply _).symm
    _ = 0 := by
      rw [thetaXiReflectionOddMode, map_sub,
        thetaPinnedMeanCLM_apply, thetaPinnedMeanCLM_apply,
        pinnedMean_thetaXiDivisorEigenvector_eq_sqrt_mass,
        pinnedMean_thetaXiDivisorEigenvector_eq_sqrt_mass]
      ring

/-- Subtracting the two retained monopoles centers the even fold. -/
theorem pinnedMean_thetaXiReflectionEvenCenteredMode (q : XiZeroCopy) :
    pinnedMean (thetaXiReflectionEvenCenteredMode q) = 0 := by
  calc
    pinnedMean (thetaXiReflectionEvenCenteredMode q) =
        thetaPinnedMeanCLM (thetaXiReflectionEvenCenteredMode q) :=
      (thetaPinnedMeanCLM_apply _).symm
    _ = 0 := by
      rw [thetaXiReflectionEvenCenteredMode, thetaXiReflectionEvenRawMode,
        map_sub, map_add, map_smul, thetaPinnedMeanCLM_apply,
        thetaPinnedMeanCLM_apply, thetaPinnedMeanCLM_apply,
        pinnedMean_thetaXiDivisorEigenvector_eq_sqrt_mass,
        pinnedMean_thetaXiDivisorEigenvector_eq_sqrt_mass,
        pinnedMean_pinnedOne]
      simp only [smul_eq_mul]
      ring

/-- The entire difference between raw and centered reflection folds is one explicit rank-one
boundary ghost. -/
theorem thetaXiReflectionEvenRaw_sub_centered_eq_pinnedGhost (q : XiZeroCopy) :
    thetaXiReflectionEvenRawMode q - thetaXiReflectionEvenCenteredMode q =
      ((2 : ℂ) * (Real.sqrt thetaSource.mass : ℂ)) • pinnedOne := by
  rw [thetaXiReflectionEvenCenteredMode]
  module

/-- The compact theta source inverse exchanges the odd fold with the raw even fold. -/
theorem thetaCompactSourceInverse_thetaXiReflectionOddMode (q : XiZeroCopy) :
    thetaCompactSourceInverse (thetaXiReflectionOddMode q) =
      thetaXiReciprocalEigenvalue q • thetaXiReflectionEvenRawMode q := by
  rw [thetaXiReflectionOddMode, thetaXiReflectionEvenRawMode, map_sub,
    thetaCompactSourceInverse_thetaXi_eigen,
    thetaCompactSourceInverse_thetaXi_eigen,
    thetaXiReciprocalEigenvalue_reflect]
  module

/-- The compact theta source inverse sends the raw even fold back to the odd fold. -/
theorem thetaCompactSourceInverse_thetaXiReflectionEvenRawMode (q : XiZeroCopy) :
    thetaCompactSourceInverse (thetaXiReflectionEvenRawMode q) =
      thetaXiReciprocalEigenvalue q • thetaXiReflectionOddMode q := by
  rw [thetaXiReflectionEvenRawMode, thetaXiReflectionOddMode, map_add,
    thetaCompactSourceInverse_thetaXi_eigen,
    thetaCompactSourceInverse_thetaXi_eigen,
    thetaXiReciprocalEigenvalue_reflect]
  module

/-- Centering the even fold does not change its compact-source image because the source inverse
kills the constant boundary vector. -/
theorem thetaCompactSourceInverse_thetaXiReflectionEvenCenteredMode (q : XiZeroCopy) :
    thetaCompactSourceInverse (thetaXiReflectionEvenCenteredMode q) =
      thetaXiReciprocalEigenvalue q • thetaXiReflectionOddMode q := by
  have hpinned : thetaCompactSourceInverse pinnedOne = 0 := by
    rw [← thetaKernelOperator_eq_thetaCompactSourceInverse,
      thetaKernelOperator_pinnedOne]
  rw [thetaXiReflectionEvenCenteredMode, map_sub, map_smul,
    thetaCompactSourceInverse_thetaXiReflectionEvenRawMode, hpinned,
    smul_zero, sub_zero]

/-- Canonical real coefficient of the full-Laurent quadratic inversion ghost on one retained Xi
divisor and one ordinary-prime clock. -/
def thetaXiIntegralQuadraticGhostCoefficient
    (rho : XiDivisorSupport) (p : Nat.Primes) : ℝ :=
  (deningerXiFullIntegralGammaProducer rho p).evaluation
    (deningerIntegralGammaMultiplicityQuadraticGhost
      (xiSupportMultiplicity rho))

/-- Hilbert-space Green--Stokes normal form of the same quadratic ghost. -/
def thetaXiIntegralQuadraticGhostVector
    (rho : XiDivisorSupport) (p : Nat.Primes) : ThetaH :=
  (thetaXiIntegralQuadraticGhostCoefficient rho p : ℂ) • pinnedOne

theorem thetaXiIntegralQuadraticGhostCoefficient_eq_zero_iff
    (rho : XiDivisorSupport) (p : Nat.Primes) :
    thetaXiIntegralQuadraticGhostCoefficient rho p = 0 ↔
      (rho : ℂ).re = 1 / 2 := by
  exact DeningerXiFullIntegralGammaProducer.quadraticGhost_eq_zero_iff_line
    (deningerXiFullIntegralGammaProducer rho p)

/-- The Laurent quadratic ghost is exactly the negative of the positive paired Gamma curvature,
with the Xi divisor multiplicity retained.  This is the coefficient-faithful bridge from the
integral Cartier source to the Gauss--Hodge energy channel. -/
theorem thetaXiIntegralQuadraticGhostCoefficient_eq_neg_pairedCurvature
    (rho : XiDivisorSupport) (p : Nat.Primes) :
    thetaXiIntegralQuadraticGhostCoefficient rho p =
      -(xiSupportMultiplicity rho : ℝ) *
        sourceHorizontalGammaSixUnitOppositeBoundaryCurvature
          (Real.log (p : ℝ) * primeDepthBVWoldXiCenteredRate rho) := by
  rw [thetaXiIntegralQuadraticGhostCoefficient,
    (deningerXiFullIntegralGammaProducer rho p).quadraticGhost_coefficient,
    sourceHorizontalGammaSixUnitOppositeBoundaryCurvature_eq_neg_mul_defects]
  ring

/-- The coefficient has a fixed sign on every Xi fibre.  Positivity of the paired Gamma channel
therefore confirms the ghost rather than annihilating it. -/
theorem thetaXiIntegralQuadraticGhostCoefficient_nonpos
    (rho : XiDivisorSupport) (p : Nat.Primes) :
    thetaXiIntegralQuadraticGhostCoefficient rho p ≤ 0 := by
  rw [thetaXiIntegralQuadraticGhostCoefficient_eq_neg_pairedCurvature]
  exact mul_nonpos_of_nonpos_of_nonneg
    (neg_nonpos.mpr (Nat.cast_nonneg _))
    (sourceHorizontalGammaSixUnitOppositeBoundaryCurvature_nonneg _)

/-- Off the critical line the quadratic inversion ghost is strictly negative. -/
theorem thetaXiIntegralQuadraticGhostCoefficient_neg_iff
    (rho : XiDivisorSupport) (p : Nat.Primes) :
    thetaXiIntegralQuadraticGhostCoefficient rho p < 0 ↔
      (rho : ℂ).re ≠ 1 / 2 := by
  constructor
  · intro hneg hline
    have hzero :=
      (thetaXiIntegralQuadraticGhostCoefficient_eq_zero_iff rho p).2 hline
    linarith
  · intro hoff
    have hle := thetaXiIntegralQuadraticGhostCoefficient_nonpos rho p
    have hne : thetaXiIntegralQuadraticGhostCoefficient rho p ≠ 0 :=
      (thetaXiIntegralQuadraticGhostCoefficient_eq_zero_iff rho p).not.mpr hoff
    exact lt_of_le_of_ne hle hne

/-- Positive Gamma/Gauss--Hodge curvature in the same pinned harmonic carrier. -/
def thetaXiIntegralPairedCurvatureVector
    (rho : XiDivisorSupport) (p : Nat.Primes) : ThetaH :=
  (((xiSupportMultiplicity rho : ℝ) *
      sourceHorizontalGammaSixUnitOppositeBoundaryCurvature
        (Real.log (p : ℝ) * primeDepthBVWoldXiCenteredRate rho) : ℝ) : ℂ) • pinnedOne

/-- Xi- and prime-selected physical anomaly of the literal Deninger cyclic boundary.  Both
reflection orientations are evaluated on the same canonical source primitive before entering the
one-dimensional theta harmonic carrier. -/
def thetaXiIntegralCyclicBoundaryAnomalyVector
    (rho : XiDivisorSupport) (p : Nat.Primes) : ThetaH :=
  (((xiSupportMultiplicity rho : ℝ) *
      (sourceHorizontalGammaSixUnitForwardBoundaryDefect
          (Real.log (p : ℝ) * primeDepthBVWoldXiCenteredRate rho) +
        sourceHorizontalGammaSixUnitReflectedBoundaryDefect
          (Real.log (p : ℝ) * primeDepthBVWoldXiCenteredRate rho)) : ℝ) : ℂ) • pinnedOne

/-- The selected failure of physical-character evaluation to be a cyclic chain map is exactly the
positive paired Gamma curvature, with prime label and Xi multiplicity unchanged. -/
theorem thetaXiIntegralCyclicBoundaryAnomalyVector_eq_pairedCurvatureVector
    (rho : XiDivisorSupport) (p : Nat.Primes) :
    thetaXiIntegralCyclicBoundaryAnomalyVector rho p =
      thetaXiIntegralPairedCurvatureVector rho p := by
  rw [thetaXiIntegralCyclicBoundaryAnomalyVector,
    thetaXiIntegralPairedCurvatureVector,
    sourceHorizontalGammaSixUnitBoundaryDefect_add_reflected_eq_curvature]

/-- **Exact source Ward double.**  The positive paired curvature cancels the negative Laurent
ghost in the harmonic line.  This is an unconditional cancellation law, but it retains both
nonzero terms and hence is not quadratic-ghost erasure. -/
theorem thetaXiIntegralQuadraticGhostVector_add_pairedCurvatureVector
    (rho : XiDivisorSupport) (p : Nat.Primes) :
    thetaXiIntegralQuadraticGhostVector rho p +
        thetaXiIntegralPairedCurvatureVector rho p = 0 := by
  rw [thetaXiIntegralQuadraticGhostVector,
    thetaXiIntegralQuadraticGhostCoefficient_eq_neg_pairedCurvature,
    thetaXiIntegralPairedCurvatureVector]
  push_cast
  module

/-- The curvature partner is literally the negative of the quadratic ghost vector. -/
theorem thetaXiIntegralPairedCurvatureVector_eq_neg_quadraticGhostVector
    (rho : XiDivisorSupport) (p : Nat.Primes) :
    thetaXiIntegralPairedCurvatureVector rho p =
      -thetaXiIntegralQuadraticGhostVector rho p := by
  exact eq_neg_of_add_eq_zero_right
    (thetaXiIntegralQuadraticGhostVector_add_pairedCurvatureVector rho p)

/-- **Xi-selected Green--Stokes law on a literal source boundary.**  The full Laurent quadratic
ghost is the negative physical chain-map anomaly of the two reflected characters on the canonical
Deninger cyclic primitive.  No scalar is fitted and no quotient erases either term. -/
theorem thetaXiIntegralQuadraticGhostVector_add_cyclicBoundaryAnomalyVector
    (rho : XiDivisorSupport) (p : Nat.Primes) :
    thetaXiIntegralQuadraticGhostVector rho p +
        thetaXiIntegralCyclicBoundaryAnomalyVector rho p = 0 := by
  rw [thetaXiIntegralCyclicBoundaryAnomalyVector_eq_pairedCurvatureVector]
  exact thetaXiIntegralQuadraticGhostVector_add_pairedCurvatureVector rho p

/-- The normal-form vector retains the full scalar coefficient: it vanishes exactly on the
critical line. -/
theorem thetaXiIntegralQuadraticGhostVector_eq_zero_iff
    (rho : XiDivisorSupport) (p : Nat.Primes) :
    thetaXiIntegralQuadraticGhostVector rho p = 0 ↔
      (rho : ℂ).re = 1 / 2 := by
  constructor
  · intro hzero
    have hmean := congrArg pinnedMean hzero
    rw [thetaXiIntegralQuadraticGhostVector, pinnedMean_smul,
      pinnedMean_pinnedOne, mul_one] at hmean
    have hpinnedZero : pinnedMean (0 : ThetaH) = 0 := by
      rw [← thetaPinnedMeanCLM_apply]
      exact map_zero thetaPinnedMeanCLM
    rw [hpinnedZero] at hmean
    have hmean' : (thetaXiIntegralQuadraticGhostCoefficient rho p : ℂ) = 0 := by
      exact hmean
    have hcoeff : thetaXiIntegralQuadraticGhostCoefficient rho p = 0 := by
      exact_mod_cast hmean'
    exact (thetaXiIntegralQuadraticGhostCoefficient_eq_zero_iff rho p).1 hcoeff
  · intro hline
    have hcoeff :=
      (thetaXiIntegralQuadraticGhostCoefficient_eq_zero_iff rho p).2 hline
    rw [thetaXiIntegralQuadraticGhostVector, hcoeff]
    simp

/-- The literal selected cyclic boundary is physically Stokes-flat exactly on the critical line.
Thus source exactness alone cannot annihilate its physical anomaly. -/
theorem thetaXiIntegralCyclicBoundaryAnomalyVector_eq_zero_iff
    (rho : XiDivisorSupport) (p : Nat.Primes) :
    thetaXiIntegralCyclicBoundaryAnomalyVector rho p = 0 ↔
      (rho : ℂ).re = 1 / 2 := by
  rw [thetaXiIntegralCyclicBoundaryAnomalyVector_eq_pairedCurvatureVector,
    thetaXiIntegralPairedCurvatureVector_eq_neg_quadraticGhostVector, neg_eq_zero]
  exact thetaXiIntegralQuadraticGhostVector_eq_zero_iff rho p

/-- **Unconditional adjoint Green--Stokes killing.**  The adjoint derivative kills the quadratic
ghost vector for every Xi divisor because that vector lies in its one-dimensional cokernel. -/
theorem thetaXiIntegralQuadraticGhostVector_mem_adjointKernel
    (rho : XiDivisorSupport) (p : Nat.Primes) :
    thetaXiIntegralQuadraticGhostVector rho p ∈
      thetaWeightedDerivative.adjoint.kernel := by
  rw [thetaWeightedDerivative_adjoint_kernel]
  exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self pinnedOne)

/-- Adjoint Stokes also kills the cyclic chain-map anomaly, confirming that this operation forgets
the entire harmonic Ward double rather than proving either coefficient zero. -/
theorem thetaXiIntegralCyclicBoundaryAnomalyVector_mem_adjointKernel
    (rho : XiDivisorSupport) (p : Nat.Primes) :
    thetaXiIntegralCyclicBoundaryAnomalyVector rho p ∈
      thetaWeightedDerivative.adjoint.kernel := by
  rw [thetaXiIntegralCyclicBoundaryAnomalyVector_eq_pairedCurvatureVector,
    thetaXiIntegralPairedCurvatureVector_eq_neg_quadraticGhostVector]
  exact thetaWeightedDerivative.adjoint.kernel.neg_mem
    (thetaXiIntegralQuadraticGhostVector_mem_adjointKernel rho p)

/-- **Unconditional relative-boundary killing.**  The rank-two pinned-Volterra boundary operator
absorbs the quadratic ghost for every Xi divisor.  This statement preserves the coefficient in
the representative but the quotient kills every scalar multiple of `pinnedOne`. -/
theorem thetaXiIntegralQuadraticGhostVector_mem_pinnedBoundaryRange
    (rho : XiDivisorSupport) (p : Nat.Primes) :
    thetaXiIntegralQuadraticGhostVector rho p ∈
      LinearMap.range pinnedBoundaryCLM.toLinearMap := by
  rw [thetaXiIntegralQuadraticGhostVector]
  exact Submodule.smul_mem _ _ pinnedOne_mem_range_pinnedBoundaryCLM

/-- The positive cyclic anomaly is absorbed by the same artificial relative-boundary channel. -/
theorem thetaXiIntegralCyclicBoundaryAnomalyVector_mem_pinnedBoundaryRange
    (rho : XiDivisorSupport) (p : Nat.Primes) :
    thetaXiIntegralCyclicBoundaryAnomalyVector rho p ∈
      LinearMap.range pinnedBoundaryCLM.toLinearMap := by
  rw [thetaXiIntegralCyclicBoundaryAnomalyVector_eq_pairedCurvatureVector,
    thetaXiIntegralPairedCurvatureVector_eq_neg_quadraticGhostVector]
  exact (LinearMap.range pinnedBoundaryCLM.toLinearMap).neg_mem
    (thetaXiIntegralQuadraticGhostVector_mem_pinnedBoundaryRange rho p)

/-- **Coefficient-faithful Green--Stokes admission wall.**  Unlike adjoint-kernel killing,
admission of the same vector to the physical derivative range is exactly the critical line. -/
theorem thetaXiIntegralQuadraticGhostVector_mem_derivativeRange_iff
    (rho : XiDivisorSupport) (p : Nat.Primes) :
    thetaXiIntegralQuadraticGhostVector rho p ∈
        thetaWeightedDerivative.rangeSubmodule ↔
      (rho : ℂ).re = 1 / 2 := by
  rw [thetaWeightedDerivative_range, mem_thetaCentered_iff,
    thetaXiIntegralQuadraticGhostVector, pinnedMean_smul,
    pinnedMean_pinnedOne, mul_one, Complex.ofReal_eq_zero,
    thetaXiIntegralQuadraticGhostCoefficient_eq_zero_iff]

/-- Replacing the ghost by its positive paired-curvature partner does not improve Green--Stokes
admission: that partner enters the physical derivative range exactly on the critical line. -/
theorem thetaXiIntegralPairedCurvatureVector_mem_derivativeRange_iff
    (rho : XiDivisorSupport) (p : Nat.Primes) :
    thetaXiIntegralPairedCurvatureVector rho p ∈
        thetaWeightedDerivative.rangeSubmodule ↔
      (rho : ℂ).re = 1 / 2 := by
  rw [thetaXiIntegralPairedCurvatureVector_eq_neg_quadraticGhostVector]
  constructor
  · intro h
    exact (thetaXiIntegralQuadraticGhostVector_mem_derivativeRange_iff rho p).1
      (by simpa using thetaWeightedDerivative.rangeSubmodule.neg_mem h)
  · intro hline
    exact thetaWeightedDerivative.rangeSubmodule.neg_mem
      ((thetaXiIntegralQuadraticGhostVector_mem_derivativeRange_iff rho p).2 hline)

/-- The actual selected cyclic chain-map anomaly reaches the physical Green--Stokes derivative
range exactly when the Xi horizontal character is neutral. -/
theorem thetaXiIntegralCyclicBoundaryAnomalyVector_mem_derivativeRange_iff
    (rho : XiDivisorSupport) (p : Nat.Primes) :
    thetaXiIntegralCyclicBoundaryAnomalyVector rho p ∈
        thetaWeightedDerivative.rangeSubmodule ↔
      (rho : ℂ).re = 1 / 2 := by
  rw [thetaXiIntegralCyclicBoundaryAnomalyVector_eq_pairedCurvatureVector]
  exact thetaXiIntegralPairedCurvatureVector_mem_derivativeRange_iff rho p

/-- Every scalar reporter that is nonzero on the pinned boundary vector reads the full quadratic
ghost faithfully.  Its selected annihilation is therefore exactly critical-line placement. -/
theorem coefficientFaithfulReporter_quadraticGhost_eq_zero_iff
    (L : ThetaH →ₗ[ℂ] ℂ) (hL : L pinnedOne ≠ 0)
    (rho : XiDivisorSupport) (p : Nat.Primes) :
    L (thetaXiIntegralQuadraticGhostVector rho p) = 0 ↔
      (rho : ℂ).re = 1 / 2 := by
  rw [thetaXiIntegralQuadraticGhostVector, map_smul, smul_eq_mul,
    mul_eq_zero]
  simp only [hL, or_false, Complex.ofReal_eq_zero]
  exact thetaXiIntegralQuadraticGhostCoefficient_eq_zero_iff rho p

/-- The exact global source-range admission requested by ghost erasure is not weaker than RH. -/
theorem everyThetaXiIntegralQuadraticGhostVector_mem_derivativeRange_iff_riemannHypothesis :
    (∀ (rho : XiDivisorSupport) (p : Nat.Primes),
      thetaXiIntegralQuadraticGhostVector rho p ∈
        thetaWeightedDerivative.rangeSubmodule) ↔ RiemannHypothesis := by
  constructor
  · intro h
    apply riemannHypothesis_of_forall_xiDivisorSupport_re_eq_half
    intro rho
    exact (thetaXiIntegralQuadraticGhostVector_mem_derivativeRange_iff rho
      (⟨2, Nat.prime_two⟩ : Nat.Primes)).1
        (h rho (⟨2, Nat.prime_two⟩ : Nat.Primes))
  · intro hRH rho p
    exact (thetaXiIntegralQuadraticGhostVector_mem_derivativeRange_iff rho p).2
      (xi_divisor_support_re_eq_half_of_rh hRH rho)

/-- Global physical Stokes-flatness of the literal selected cyclic boundaries is exactly RH.  The
unconditional Ward-double identity therefore cannot be promoted to standalone ghost erasure by
ordinary boundary exactness. -/
theorem everyThetaXiIntegralCyclicBoundaryAnomalyVector_eq_zero_iff_riemannHypothesis :
    (∀ (rho : XiDivisorSupport) (p : Nat.Primes),
      thetaXiIntegralCyclicBoundaryAnomalyVector rho p = 0) ↔
        RiemannHypothesis := by
  constructor
  · intro h
    apply riemannHypothesis_of_forall_xiDivisorSupport_re_eq_half
    intro rho
    exact (thetaXiIntegralCyclicBoundaryAnomalyVector_eq_zero_iff rho
      (⟨2, Nat.prime_two⟩ : Nat.Primes)).1
        (h rho (⟨2, Nat.prime_two⟩ : Nat.Primes))
  · intro hRH rho p
    exact (thetaXiIntegralCyclicBoundaryAnomalyVector_eq_zero_iff rho p).2
      (xi_divisor_support_re_eq_half_of_rh hRH rho)

end

end RHTower.HedenmalmThetaSource
