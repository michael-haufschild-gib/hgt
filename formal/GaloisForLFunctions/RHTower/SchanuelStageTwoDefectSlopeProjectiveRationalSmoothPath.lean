import GaloisForLFunctions.RHTower.SchanuelStageTwoDefectSlopeGenericTargetPoint
import GaloisForLFunctions.HTGeometry.ComplexPointRationalSmoothPath
import GaloisForLFunctions.HTGeometry.BaseFieldPointComplexification

/-!
# Rationally smooth regulator paths on the global projective normalization

This file removes the supplied derivative fields from the global projective path interface.
A projective path is rationally smooth when every rational function represented by regular germs
at every point has a `C∞` evaluated pullback.  The four stage-two coordinates are actual rational
functions on the actual proper projective normalization, so their differentiability and continuous
derivatives follow from this intrinsic smoothness condition.

The source remains an actual `AlgNum`-valued point, the target is the canonical generic complex
point whose values are the literal tuple `(x₁,x₂,exp x₁,exp x₂)`, and the multiplicative coordinate
divisors are avoided.  The resulting regulator theorem is global: the path need not remain inside
the normalized standard affine chart.
-/

namespace GaloisForLFunctions.RHTower

open AlgebraicGeometry GaloisForLFunctions.HTGeometry Set

noncomputable section

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 1000000

/-- A rationally smooth, divisor-avoiding path on the actual projective normalization from an
actual algebraic point to the canonical exponential target. -/
structure StageTwoProjectiveRationallySmoothDivisorAvoidingPath
    (x : Fin 2 → ℂ) (core : StageTwoDefectSlopeCore x) (a b : ℝ) where
  point : ℝ → StageTwoProjectiveCoordinatePoint x core
  smooth : Scheme.ComplexPointPath.IsRationallySmooth
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

/-- Every additive coordinate at the actual algebraic source point is algebraic.  This is derived
from source factorization and scalar-extension naturality of stalk evaluation. -/
theorem StageTwoProjectiveRationallySmoothDivisorAvoidingPath.algebraic_exponentValue
    {x : Fin 2 → ℂ} {core : StageTwoDefectSlopeCore x} {a b : ℝ}
    (path : StageTwoProjectiveRationallySmoothDivisorAvoidingPath x core a b)
    (i : Fin 2) : (path.point a).exponentValue i ∈ AlgNum := by
  unfold StageTwoProjectiveCoordinatePoint.exponentValue
  unfold Scheme.RationalFunctionRegularAtComplexPoint.value
  rw [Scheme.ComplexPoint.stalkEval_transport path.source_factorization]
  rw [path.algebraicBasePoint.toComplexPoint_stalkEval]
  exact (path.algebraicBasePoint.stalkEvalAtComplexCenter
    (path.source_factorization ▸ ((path.point a).exponentRegular i).germ)).property

/-- Every multiplicative coordinate at the actual algebraic source point is algebraic.  This too
is derived rather than supplied as endpoint data. -/
theorem StageTwoProjectiveRationallySmoothDivisorAvoidingPath.algebraic_exponentialValue
    {x : Fin 2 → ℂ} {core : StageTwoDefectSlopeCore x} {a b : ℝ}
    (path : StageTwoProjectiveRationallySmoothDivisorAvoidingPath x core a b)
    (i : Fin 2) : (path.point a).exponentialValue i ∈ AlgNum := by
  unfold StageTwoProjectiveCoordinatePoint.exponentialValue
  unfold Scheme.RationalFunctionRegularAtComplexPoint.value
  rw [Scheme.ComplexPoint.stalkEval_transport path.source_factorization]
  rw [path.algebraicBasePoint.toComplexPoint_stalkEval]
  exact (path.algebraicBasePoint.stalkEvalAtComplexCenter
    (path.source_factorization ▸ ((path.point a).exponentialRegular i).germ)).property

/-- Additive projective-coordinate evaluation is smooth; no derivative field is supplied. -/
theorem StageTwoProjectiveRationallySmoothDivisorAvoidingPath.contDiff_exponentValue
    {x : Fin 2 → ℂ} {core : StageTwoDefectSlopeCore x} {a b : ℝ}
    (path : StageTwoProjectiveRationallySmoothDivisorAvoidingPath x core a b)
    (i : Fin 2) :
    ContDiff ℝ ⊤ (fun t => (path.point t).exponentValue i) := by
  simpa only [StageTwoProjectiveCoordinatePoint.exponentValue] using
    path.smooth.contDiff_value
      (stageTwoSlopeProjectiveExponentCoordinate x core i)
      (fun t => (path.point t).exponentRegular i)

/-- Multiplicative projective-coordinate evaluation is smooth; no derivative field is supplied. -/
theorem StageTwoProjectiveRationallySmoothDivisorAvoidingPath.contDiff_exponentialValue
    {x : Fin 2 → ℂ} {core : StageTwoDefectSlopeCore x} {a b : ℝ}
    (path : StageTwoProjectiveRationallySmoothDivisorAvoidingPath x core a b)
    (i : Fin 2) :
    ContDiff ℝ ⊤ (fun t => (path.point t).exponentialValue i) := by
  simpa only [StageTwoProjectiveCoordinatePoint.exponentialValue] using
    path.smooth.contDiff_value
      (stageTwoSlopeProjectiveExponentialCoordinate x core i)
      (fun t => (path.point t).exponentialRegular i)

/-- Forget a rationally smooth global projective path to the four evaluated coordinate paths.
Every derivative and continuous-derivative field is derived from rational smoothness. -/
noncomputable def StageTwoProjectiveRationallySmoothDivisorAvoidingPath.toCoordinatePath
    {x : Fin 2 → ℂ} {core : StageTwoDefectSlopeCore x} {a b : ℝ}
    (path : StageTwoProjectiveRationallySmoothDivisorAvoidingPath x core a b) :
    StageTwoDivisorAvoidingCoordinatePath x a b where
  X i t := (path.point t).exponentValue i
  Y i t := (path.point t).exponentialValue i
  X' i := deriv fun t => (path.point t).exponentValue i
  Y' i := deriv fun t => (path.point t).exponentialValue i
  parameter_order := path.parameter_order
  hasDeriv_X i t _ :=
    ((path.contDiff_exponentValue i).differentiable (by simp) t).hasDerivAt
  hasDeriv_Y i t _ :=
    ((path.contDiff_exponentialValue i).differentiable (by simp) t).hasDerivAt
  continuous_X' i :=
    ((path.contDiff_exponentValue i).continuous_deriv (by simp)).continuousOn
  continuous_Y' i :=
    ((path.contDiff_exponentialValue i).continuous_deriv (by simp)).continuousOn
  avoids_multiplicative_divisor := path.avoids_multiplicative_divisor
  algebraic_base_X := path.algebraic_exponentValue
  algebraic_base_Y := path.algebraic_exponentialValue
  terminal_X i := by
    rw [path.target]
    exact stageTwoProjectiveGenericCoordinatePoint_exponentValue x core i
  terminal_Y i := by
    rw [path.target]
    exact stageTwoProjectiveGenericCoordinatePoint_exponentialValue x core i

/-- Exact simultaneous regulator identities for every rationally smooth divisor-avoiding path on
the whole projective normalization from an algebraic point to the canonical exponential target. -/
theorem exists_stageTwoProjectiveRationallySmoothPathRegulatorWitness
    {x : Fin 2 → ℂ} {core : StageTwoDefectSlopeCore x} {a b : ℝ}
    (path : StageTwoProjectiveRationallySmoothDivisorAvoidingPath x core a b) :
    Nonempty (StageTwoRegulatorWitness path.toCoordinatePath) :=
  exists_stageTwoRegulatorWitness path.toCoordinatePath

/-- Clauses 1--4, the actual proper projective normalization with concrete function field, and the
exact regulator law for every global rationally smooth divisor-avoiding path from an algebraic
point to the canonical target. -/
structure StageTwoDefectSlopeRationalSmoothProjectivePackage (x : Fin 2 → ℂ) where
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
    (path : StageTwoProjectiveRationallySmoothDivisorAvoidingPath x core a b),
    Nonempty (StageTwoRegulatorWitness path.toCoordinatePath)

/-- Unconditional rationally smooth projective package under exactly the stage-two counterexample
assumptions. -/
theorem exists_stageTwoDefectSlopeRationalSmoothProjectivePackage
    (x : Fin 2 → ℂ) (hx : LinearIndependent ℚ x)
    (hlt : Algebra.trdeg AlgNum (stageTwoValueField (x 0) (x 1)) < 2) :
    Nonempty (StageTwoDefectSlopeRationalSmoothProjectivePackage x) := by
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
      exists_stageTwoProjectiveRationallySmoothPathRegulatorWitness path
  }⟩

/-- Extraction-failure form of the rationally smooth projective package. -/
theorem exists_stageTwoDefectSlopeRationalSmoothProjectivePackage_of_extraction_failure
    (x : Fin 2 → ℂ) (hx : LinearIndependent ℚ x)
    (hfail : ¬ SchanuelExtractionFor x) :
    Nonempty (StageTwoDefectSlopeRationalSmoothProjectivePackage x) :=
  exists_stageTwoDefectSlopeRationalSmoothProjectivePackage x hx
    ((not_schanuelExtractionFor_two_iff_stageTwoValueField_trdeg_lt x).mp hfail)

end

end GaloisForLFunctions.RHTower
