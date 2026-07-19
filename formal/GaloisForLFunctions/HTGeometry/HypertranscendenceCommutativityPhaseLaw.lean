import GaloisForLFunctions.HTGeometry.CommutativeHorizonExactClassification
import GaloisForLFunctions.HTGeometry.FreeCommutingHorizonPhaseBoundary
import GaloisForLFunctions.HTGeometry.FreeHorizonMaximalCommutatorRank
import GaloisForLFunctions.HTGeometry.PrimeProfileClockSaturationLaw

/-!
# The commutativity--hypertranscendence phase law

This module packages the sharp structural boundary exposed by the horizon and prime-clock
classifications.

For every autonomous one-root linear representation of a commutative law algebra, the complete
directional algebraic-dependence horizon is a vector subspace, and every vector subspace is
realized by an explicit symmetric-algebra regular representation.  Conversely, every finite
homogeneous projective zero locus is the exact complete horizon of a free-word realization whose
exterior commutator symbol is injective.  Thus nonlinear horizon topology is an intrinsic
obstruction to the autonomous commutative phase, rather than an artifact of a particular
presentation.

The prime-profile corollary records the field-level form of the same linearization: differential
field generation is operator saturation, and relative differential algebraicity is polynomial
clock torsion in the saturated source quotient.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open MvPolynomial ArithmeticFunction Set
open scoped Differential

universe u v w x

variable {K : Type u} {A : Type v} {M : Type w}
  [Field K] [CharZero K] [CommRing A] [Algebra K A]
  [AddCommGroup M] [Module K M]

variable {iota eta : Type x} [Fintype iota] [Fintype eta]

/-- **Commutativity--hypertranscendence phase law.**  The complete horizon of an arbitrary
autonomous one-root commutative linear representation is a vector subspace.  Hence it cannot equal
any prescribed nonlinear finite homogeneous zero cone.  Every such cone nevertheless occurs as
the exact complete horizon of a free-word realization whose exterior commutator symbol is
injective.

The conclusion is sharp in both directions: the first equality identifies the entire commuting
horizon, while the final witness realizes the same nonlinear cone with maximal detectable
noncommutativity. -/
theorem commutativityHypertranscendencePhaseLaw
    (rho : A →ₐ[K] Module.End K M) (m : M) (L : (iota → K) →ₗ[K] A)
    (P : eta → MvPolynomial iota K) (degree : eta → Nat)
    [Nonempty iota] [Nonempty eta]
    (hP : forall j, (P j).IsHomogeneous (degree j))
    (hNonlinear : forall H : Submodule K (iota → K),
      (H : Set (iota → K)) ≠ finiteLawZeroCone P) :
    ({v : iota → K |
        ¬ AlgebraicIndependent K (commutativeRepresentationJet rho m L v)} =
        (commutativeRepresentationHorizon rho m L : Set (iota → K))) ∧
      (∀ H : Submodule K (iota → K),
        {v : iota → K |
            ¬ AlgebraicIndependent K
              (commutativeRepresentationJet
                (subspaceCommutativeRegularRepresentation H)
                (1 : SubspaceCommutativeLawAlgebra H)
                (subspaceCommutativeLawMap H) v)} =
          (H : Set (iota → K))) ∧
      {v : iota → K |
          ¬ AlgebraicIndependent K (commutativeRepresentationJet rho m L v)} ≠
        finiteLawZeroCone P ∧
      ∃ a : CommonDegreeEquationIndex iota degree → ProjectiveWordState iota → K,
        (forall (c : iota → K), (∃ i, c i ≠ 0) →
          ((¬ AlgebraicIndependent K
              (fun r : Nat ↦ directionalJet
                (projectiveCompleteDerivation a ((∑ j, degree j) + 1)) c r
                (projectiveCompleteRoot
                  (K := K) (ι := iota)
                    (η := CommonDegreeEquationIndex iota degree)))) ↔
            c ∈ finiteLawZeroCone P)) ∧
        Function.Injective
          (derivationCommutatorMap
            (projectiveCompleteLawMap a ((∑ j, degree j) + 1))) := by
  have hlinear := commutativeRepresentation_dependenceHorizon_eq_submodule rho m L
  refine ⟨hlinear, subspaceCommutative_dependenceHorizon_eq, ?_, ?_⟩
  · rw [hlinear]
    exact hNonlinear (commutativeRepresentationHorizon rho m L)
  letI : Nonempty (CommonDegreeEquationIndex iota degree) :=
    ⟨⟨Classical.choice inferInstance, fun _ ↦ Classical.choice inferInstance⟩⟩
  obtain ⟨a, hrealizes, hcommutator⟩ :=
    exists_completeJet_horizon_eq_finiteHomogeneousZeroLocus_and_commutatorMap_injective
      P degree hP
  refine ⟨a, ?_, hcommutator⟩
  intro c hc
  simpa only [finiteLawZeroCone, Set.mem_setOf_eq] using hrealizes c hc

/-- **Prime-profile operational-torsion realization.**  For every source subspace, differential
adjunction is exactly ordinary field generation after prime-clock saturation.  Over that saturated
field, a new source is differentially algebraic exactly when a nonzero polynomial clock orbit
enters the saturated old source space. -/
theorem primeProfileOperationalTorsionLaw
    (W : Submodule ℂ PrimeProfileClockQuotient)
    (f : ArithmeticFunction ℂ)
    (hfsupport : PrimeProfileSupportedOnPositivePrimePowers f) :
    GaloisForLFunctions.differentialAdjoin finitePrimeCoefficientField
        (Set.range (fun i => algebraMap (ArithmeticFunction ℂ)
          arithmeticFunctionFractionField (primeProfileGrassmannSource W i))) =
        primeProfileGrassmannField (primeProfileClockSaturation W) ∧
      (GaloisForLFunctions.DifferentialAlgebraicOver
          (primeProfileGrassmannField (primeProfileClockSaturation W))
          (algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField f) ↔
        PrimeProfileClockSaturatedIn (primeProfileClockSaturation W) f) := by
  exact ⟨differentialAdjoin_grassmannSource_eq_grassmannField_saturation W,
    differentialAlgebraic_fractionPrimeProfile_over_grassmannField_iff
      (primeProfileClockSaturation W)
      (primeProfileClockSaturation_invariant W) f hfsupport⟩

end

end GaloisForLFunctions.HTGeometry
