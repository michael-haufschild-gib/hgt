import GaloisForLFunctions.RHTower.SchanuelStageTwoDefectSlopeProjectiveRationalSmoothPath
import GaloisForLFunctions.HTGeometry.ComplexAnalytificationSmoothPath

/-!
# Smooth analytification paths on the stage-two projective normalization

This file closes the analytic comparison in clause 5 of the stage-two defect-slope normal form.
Smoothness is ordinary chartwise smoothness in the affine atlas of the complex analytification:
the path stays locally in every affine chart through its current point, and every regular function
in that chart evaluates to a `C∞` function.  The generic analytification theorem proves, rather
than assumes, that every rational function regular along such a path has a smooth pullback.

The source is an actual smooth `AlgNum`-point, the target is the canonical exponential complex
point, and divisor avoidance is exactly the paper statement.  No coordinate differentiability,
rational-observable smoothness, or comparison hypothesis occurs in the path structure.
-/

namespace GaloisForLFunctions.RHTower

open AlgebraicGeometry GaloisForLFunctions.HTGeometry Set

noncomputable section

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 1000000

/-- A smooth divisor-avoiding path in the complex analytification of the actual projective
normalization, from an actual algebraic point to the canonical exponential target. -/
structure StageTwoProjectiveAnalytificationDivisorAvoidingPath
    (x : Fin 2 → ℂ) (core : StageTwoDefectSlopeCore x) (a b : ℝ) where
  point : ℝ → StageTwoProjectiveCoordinatePoint x core
  smooth : Scheme.ComplexAnalytification.IsSmoothPath
    (stageTwoSlopeProjectiveModel x core) (fun t => (point t).point.hom)
  algebraicBasePoint :
    (stageTwoSlopeProjectiveModel x core).BaseFieldPointOver AlgNum
      (stageTwoSlopeProjectiveNormalizationToAlgNum x core)
  parameter_order : a ≤ b
  source_factorization :
    (point a).point.hom = algebraicBasePoint.toComplexPoint.hom
  smoothAlgebraicBase :
    ((stageTwoSlopeProjectiveNormalizationToAlgNum x core).stalkMap
      algebraicBasePoint.center).hom.FormallySmooth
  target : point b = stageTwoProjectiveGenericCoordinatePoint x core
  avoids_multiplicative_divisor : ∀ i t, t ∈ Icc a b →
    (point t).exponentialValue i ≠ 0

/-- Forget an ordinary analytification-smooth path to the already established rational-observable
path interface.  Rational smoothness is derived by the generic affine-chart theorem. -/
noncomputable def StageTwoProjectiveAnalytificationDivisorAvoidingPath.toRationallySmoothPath
    {x : Fin 2 → ℂ} {core : StageTwoDefectSlopeCore x} {a b : ℝ}
    (path : StageTwoProjectiveAnalytificationDivisorAvoidingPath x core a b) :
    StageTwoProjectiveRationallySmoothDivisorAvoidingPath x core a b where
  point := path.point
  smooth := path.smooth.isRationallySmooth
  algebraicBasePoint := path.algebraicBasePoint
  parameter_order := path.parameter_order
  source_factorization := path.source_factorization
  smoothAlgebraicBase := path.smoothAlgebraicBase
  target := path.target
  avoids_multiplicative_divisor := path.avoids_multiplicative_divisor

/-- The literal four evaluated coordinate paths attached to an ordinary smooth path in the
projective complex analytification.  All derivatives are derived downstream. -/
noncomputable def StageTwoProjectiveAnalytificationDivisorAvoidingPath.toCoordinatePath
    {x : Fin 2 → ℂ} {core : StageTwoDefectSlopeCore x} {a b : ℝ}
    (path : StageTwoProjectiveAnalytificationDivisorAvoidingPath x core a b) :
    StageTwoDivisorAvoidingCoordinatePath x a b :=
  path.toRationallySmoothPath.toCoordinatePath

/-- Exact simultaneous regulator identities for every ordinary smooth divisor-avoiding path in
the complex analytification of the whole projective normalization. -/
theorem exists_stageTwoProjectiveAnalytificationPathRegulatorWitness
    {x : Fin 2 → ℂ} {core : StageTwoDefectSlopeCore x} {a b : ℝ}
    (path : StageTwoProjectiveAnalytificationDivisorAvoidingPath x core a b) :
    Nonempty (StageTwoRegulatorWitness path.toCoordinatePath) :=
  exists_stageTwoProjectiveRationallySmoothPathRegulatorWitness
    path.toRationallySmoothPath

/-- All five clauses of the canonical stage-two defect-slope normal form: the exact algebraic
core and exponential-algebraic closure statement, actual proper projective normalization with the
concrete function field, and the regulator law for every ordinary smooth divisor-avoiding path in
its complex analytification from an actual smooth algebraic point to the canonical target. -/
structure StageTwoDefectSlopeProjectiveAnalytificationPackage (x : Fin 2 → ℂ) where
  core : StageTwoDefectSlopeCore x
  essential : IsEssentialSchanuelCounterexample x
  slope_mem_exponentialAlgebraicClosure :
    (core.rho : ℂ) ∈ complexExponentialAlgebraicClosure
  exponentialAlgebraicClosure_countable :
    Set.Countable (complexExponentialAlgebraicClosure : Set ℂ)
  functionFieldEquiv :
    stageTwoValueField (x 0) (x 1) ≃+*
      (stageTwoSlopeProjectiveModel x core).functionField
  proper : IsProper (stageTwoSlopeProjectiveNormalizationToGradeZero x core)
  regulator : ∀ {a b : ℝ}
    (path : StageTwoProjectiveAnalytificationDivisorAvoidingPath x core a b),
    Nonempty (StageTwoRegulatorWitness path.toCoordinatePath)

/-- Unconditional all-clauses package under exactly the stage-two counterexample assumptions. -/
theorem exists_stageTwoDefectSlopeProjectiveAnalytificationPackage
    (x : Fin 2 → ℂ) (hx : LinearIndependent ℚ x)
    (hlt : Algebra.trdeg AlgNum (stageTwoValueField (x 0) (x 1)) < 2) :
    Nonempty (StageTwoDefectSlopeProjectiveAnalytificationPackage x) := by
  obtain ⟨core, hessential, hecl⟩ :=
    exists_stageTwoDefectSlopeCore_essential_ecl x hx hlt
  exact ⟨{
    core := core
    essential := hessential
    slope_mem_exponentialAlgebraicClosure := hecl
    exponentialAlgebraicClosure_countable :=
      countable_complexExponentialAlgebraicClosure
    functionFieldEquiv :=
      stageTwoSlopeProjectiveNormalizationFunctionFieldEquiv x core
    proper := inferInstance
    regulator := fun path =>
      exists_stageTwoProjectiveAnalytificationPathRegulatorWitness path
  }⟩

/-- Extraction-failure form of the unconditional all-clauses analytification package. -/
theorem exists_stageTwoDefectSlopeProjectiveAnalytificationPackage_of_extraction_failure
    (x : Fin 2 → ℂ) (hx : LinearIndependent ℚ x)
    (hfail : ¬ SchanuelExtractionFor x) :
    Nonempty (StageTwoDefectSlopeProjectiveAnalytificationPackage x) :=
  exists_stageTwoDefectSlopeProjectiveAnalytificationPackage x hx
    ((not_schanuelExtractionFor_two_iff_stageTwoValueField_trdeg_lt x).mp hfail)

end

end GaloisForLFunctions.RHTower
