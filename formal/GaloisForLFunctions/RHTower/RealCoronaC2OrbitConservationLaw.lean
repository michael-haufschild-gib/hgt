import GaloisForLFunctions.RHTower.RealCoronaFreeCrossedProductMatrix
import GaloisForLFunctions.RHTower.RealCoronaLocalDetectabilityFracture

/-!
# The `C₂` orbit-algebra conservation law

Every orbit of an involution is either a free two-cycle or a fixed point.  On crossed products
these two atoms have different, exhaustive normal forms:

* a free orbit is one full `2 × 2` matrix block, whose corona orientation is the sign grading;
* a fixed orbit is two Fourier-character blocks, and coefficient inclusion is diagonal.

The free grading commutator detects exactly off-diagonal entries.  In an unbounded realization
this becomes smoothness--detectability conservation: bounded commutator is equivalent to bounded
odd part, so all remaining unboundedness lies in the even part.  Fixed coefficient `K₀`, by
contrast, is duplicated across the two character blocks and retains support rather than local
multiplicity.  These are the two exhaustive channels behind the four Real-corona problems.
-/

noncomputable section

namespace GaloisForLFunctions.RHTower

/-- An involution orbit is either a fixed point or an exact two-cycle. -/
theorem involution_orbit_fixed_or_free
    {α : Type*} (sigma : α → α) (hsigma : Function.Involutive sigma) (x : α) :
    sigma x = x ∨ (sigma x ≠ x ∧ sigma (sigma x) = x) := by
  by_cases hfix : sigma x = x
  · exact Or.inl hfix
  · exact Or.inr ⟨hfix, hsigma x⟩

/-- Coherent normal-form certificate for both and only both `C₂` orbit atoms. -/
structure C2AtomicOrbitAlgebraLaw where
  freeNormalForm :
    letI := freeCoordinateFunctionAction
    SkewMonoidAlgebra (ReflectionParity → ℂ) ReflectionParity ≃+*
      Matrix ReflectionParity ReflectionParity ℂ
  freeOrientationImage :
    letI := freeCoordinateFunctionAction
    freeNormalForm freeOrbitOrientationCrossed = freeOrbitOrientationMatrix
  freeCommutatorEntry : ∀
    (M : Matrix ReflectionParity ReflectionParity ℂ) (p q : ReflectionParity),
    (M * freeOrbitOrientationMatrix - freeOrbitOrientationMatrix * M) p q =
      (freeOrbitOrientation q - freeOrbitOrientation p) * M p q
  fixedNormalForm : ∀ ι : Type,
    letI := fixedCoordinateFunctionAction ι
    SkewMonoidAlgebra (ι → ℂ) ReflectionParity ≃+* ((ι → ℂ) × (ι → ℂ))
  fixedCoefficientImage : ∀ (ι : Type) (a : ι → ℂ),
    letI := fixedCoordinateFunctionAction ι
    fixedNormalForm ι (SkewMonoidAlgebra.single (1 : ReflectionParity) a) = (a, a)

/-- The exact `C₂` orbit-algebra law, constructed without assumptions. -/
def c2AtomicOrbitAlgebraLaw : C2AtomicOrbitAlgebraLaw where
  freeNormalForm := freeReflectionMatrixRingEquiv
  freeOrientationImage := freeReflectionMatrixRingEquiv_orientation
  freeCommutatorEntry := freeOrbitOrientationMatrix_commutator_entry
  fixedNormalForm := fixedReflectionFourierRingEquiv
  fixedCoefficientImage := fixedReflectionFourierRingEquiv_coefficient

section UnboundedShadow

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

/-- Unbounded free-channel shadow of the atomic orbit law: the first commutator detects exactly
the odd/off-diagonal part, while bounded smoothness conserves all unboundedness in the even part. -/
theorem c2Orbit_unbounded_smoothnessDetectabilityConservation
    (D : V →ₗ.[ℂ] V) (m : Module.End ℂ V)
    (hdomm : ∀ x : D.domain, m x ∈ D.domain)
    (hm : m * m = 1) (hiso : ∀ y : V, ‖m y‖ = ‖y‖)
    (hD : IsGenuinelyUnboundedLinearPMap D) :
    HasLinearPMapBoundOnDomain
        (linearPMapOrientationCommutator D m hdomm) ↔
      IsGenuinelyUnboundedLinearPMap
          (linearPMapOrientationEven D m hdomm) ∧
        HasLinearPMapBoundOnDomain
          (linearPMapOrientationOdd D m hdomm) :=
  bounded_orientationCommutator_iff_unbounded_even_and_bounded_odd
    D m hdomm hm hiso hD

end UnboundedShadow

/-- Fixed-channel `K₀` shadow: after the exact fixed crossed-product Fourier normal form, both
character evaluations see the same support indicator, while analytic multiplicity survives only
when it is at most one. -/
theorem c2Orbit_fixedKZeroSupportMultiplicityConservation
    {T : Type*} (F : CompletedSelfDualAnalyticFamily T) (t : T) :
    (fixedReflectionCrossedProductKZeroPlusEvaluationRank F.center
        (F.fixedCrossedProductKZeroClass t) =
          (F.toSelfDualRealZeroFamily.analyticRank t : ℤ) ↔
        F.toSelfDualRealZeroFamily.analyticRank t ≤ 1) ∧
      (fixedReflectionCrossedProductKZeroMinusEvaluationRank F.center
        (F.fixedCrossedProductKZeroClass t) =
          (F.toSelfDualRealZeroFamily.analyticRank t : ℤ) ↔
        F.toSelfDualRealZeroFamily.analyticRank t ≤ 1) :=
  ⟨F.centralFixedCrossedPlusKZero_eq_analyticRank_iff t,
    F.centralFixedCrossedMinusKZero_eq_analyticRank_iff t⟩

end GaloisForLFunctions.RHTower
