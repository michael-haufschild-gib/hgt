import GaloisForLFunctions.RHTower.SchanuelStageTwoDefectSlopeProjectiveFunctionField
import GaloisForLFunctions.HTGeometry.ComplexPointRationalFunctionEvaluation
import Mathlib.RingTheory.Smooth.Basic

/-!
# Regulator paths on the projective stage-two slope normalization

This file places the four stage-two coordinate rational functions on the actual proper projective
relative normalization.  A path consists of complex-valued scheme points where those functions
are represented by local germs; its analytic data are the derivatives of their literal evaluated
pullbacks.  Every such divisor-avoiding path has simultaneous logarithm lifts and the two exact
regulator identities.
-/

namespace GaloisForLFunctions.RHTower

open CategoryTheory AlgebraicGeometry GaloisForLFunctions.HTGeometry Set

noncomputable section

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 1000000

/-- The global projective model attached to the canonical defect slope. -/
abbrev stageTwoSlopeProjectiveModel
    (x : Fin 2 → ℂ) (core : StageTwoDefectSlopeCore x) :=
  stageTwoSlopeProjectiveNormalization x core

/-- The spectrum of the degree-zero homogeneous ring is the algebraic-number spectrum. -/
noncomputable def stageTwoSlopeGradeZeroSpecIso :
    Spec (.of (stageTwoSlopeProjectiveLineGrading 0)) ≅ Spec (.of AlgNum) where
  hom := Spec.map (stageTwoSlopeGradeZeroRingEquiv.toCommRingCatIso.inv)
  inv := Spec.map (stageTwoSlopeGradeZeroRingEquiv.toCommRingCatIso.hom)
  hom_inv_id := by
    rw [← Spec.map_comp, stageTwoSlopeGradeZeroRingEquiv.toCommRingCatIso.hom_inv_id,
      Spec.map_id]
  inv_hom_id := by
    rw [← Spec.map_comp, stageTwoSlopeGradeZeroRingEquiv.toCommRingCatIso.inv_hom_id,
      Spec.map_id]

/-- Structural morphism of the projective model to the literal algebraic-number spectrum. -/
noncomputable def stageTwoSlopeProjectiveNormalizationToAlgNum
    (x : Fin 2 → ℂ) (core : StageTwoDefectSlopeCore x) :
    stageTwoSlopeProjectiveModel x core ⟶ Spec (.of AlgNum) :=
  stageTwoSlopeProjectiveNormalizationToGradeZero x core ≫
    stageTwoSlopeGradeZeroSpecIso.hom

/-- The projective stage-two slope model is proper over the algebraic numbers. -/
noncomputable instance stageTwoSlopeProjectiveNormalizationToAlgNum_isProper
    (x : Fin 2 → ℂ) (core : StageTwoDefectSlopeCore x) :
    IsProper (stageTwoSlopeProjectiveNormalizationToAlgNum x core) := by
  change IsProper (stageTwoSlopeProjectiveNormalizationToGradeZero x core ≫
    stageTwoSlopeGradeZeroSpecIso.hom)
  infer_instance

/-- Additive stage-two coordinate as a rational function on the global projective model. -/
noncomputable def stageTwoSlopeProjectiveExponentCoordinate
    (x : Fin 2 → ℂ) (core : StageTwoDefectSlopeCore x) (i : Fin 2) :
    (stageTwoSlopeProjectiveModel x core).functionField :=
  stageTwoSlopeProjectiveNormalizationFunctionFieldEquiv x core
    (stageTwoExponentIn x i)

/-- Multiplicative stage-two coordinate as a rational function on the global projective model. -/
noncomputable def stageTwoSlopeProjectiveExponentialCoordinate
    (x : Fin 2 → ℂ) (core : StageTwoDefectSlopeCore x) (i : Fin 2) :
    (stageTwoSlopeProjectiveModel x core).functionField :=
  stageTwoSlopeProjectiveNormalizationFunctionFieldEquiv x core
    (stageTwoExponentialIn x i)

/-- A complex-valued point of the projective model at which all four coordinate rational
functions are regular. -/
structure StageTwoProjectiveCoordinatePoint
    (x : Fin 2 → ℂ) (core : StageTwoDefectSlopeCore x) where
  point : (stageTwoSlopeProjectiveModel x core).ComplexPointOver AlgNum
    (stageTwoSlopeProjectiveNormalizationToAlgNum x core)
  exponentRegular : ∀ i,
    (stageTwoSlopeProjectiveModel x core).RationalFunctionRegularAtComplexPoint point.hom
      (stageTwoSlopeProjectiveExponentCoordinate x core i)
  exponentialRegular : ∀ i,
    (stageTwoSlopeProjectiveModel x core).RationalFunctionRegularAtComplexPoint point.hom
      (stageTwoSlopeProjectiveExponentialCoordinate x core i)

/-- Evaluated additive coordinate at a regular complex-valued point. -/
noncomputable def StageTwoProjectiveCoordinatePoint.exponentValue
    {x : Fin 2 → ℂ} {core : StageTwoDefectSlopeCore x}
    (p : StageTwoProjectiveCoordinatePoint x core) (i : Fin 2) : ℂ :=
  (p.exponentRegular i).value

/-- Evaluated multiplicative coordinate at a regular complex-valued point. -/
noncomputable def StageTwoProjectiveCoordinatePoint.exponentialValue
    {x : Fin 2 → ℂ} {core : StageTwoDefectSlopeCore x}
    (p : StageTwoProjectiveCoordinatePoint x core) (i : Fin 2) : ℂ :=
  (p.exponentialRegular i).value

/-- A coordinate-smooth path of complex-valued points on the actual projective normalization,
regular for all four coordinates and disjoint from the multiplicative zero divisors.  Its endpoint
conditions say exactly that the source coordinates are algebraic and the target is `(x, exp x)`. -/
structure StageTwoProjectiveDivisorAvoidingPath
    (x : Fin 2 → ℂ) (core : StageTwoDefectSlopeCore x) (a b : ℝ) where
  point : ℝ → StageTwoProjectiveCoordinatePoint x core
  X' : Fin 2 → ℝ → ℂ
  Y' : Fin 2 → ℝ → ℂ
  parameter_order : a ≤ b
  hasDeriv_X : ∀ i t, t ∈ Icc a b →
    HasDerivAt (fun s => (point s).exponentValue i) (X' i t) t
  hasDeriv_Y : ∀ i t, t ∈ Icc a b →
    HasDerivAt (fun s => (point s).exponentialValue i) (Y' i t) t
  continuous_X' : ∀ i, ContinuousOn (X' i) (Icc a b)
  continuous_Y' : ∀ i, ContinuousOn (Y' i) (Icc a b)
  avoids_multiplicative_divisor : ∀ i t, t ∈ Icc a b →
    (point t).exponentialValue i ≠ 0
  algebraic_base_X : ∀ i, (point a).exponentValue i ∈ AlgNum
  algebraic_base_Y : ∀ i, (point a).exponentialValue i ∈ AlgNum
  smooth_base :
    ((stageTwoSlopeProjectiveNormalizationToAlgNum x core).stalkMap
      (point a).point.hom.center).hom.FormallySmooth
  terminal_X : ∀ i, (point b).exponentValue i = x i
  terminal_Y : ∀ i, (point b).exponentialValue i = Complex.exp (x i)

/-- Forget a scheme-valued projective path to its literal evaluated coordinate path. -/
noncomputable def StageTwoProjectiveDivisorAvoidingPath.toCoordinatePath
    {x : Fin 2 → ℂ} {core : StageTwoDefectSlopeCore x} {a b : ℝ}
    (path : StageTwoProjectiveDivisorAvoidingPath x core a b) :
    StageTwoDivisorAvoidingCoordinatePath x a b where
  X i t := (path.point t).exponentValue i
  Y i t := (path.point t).exponentialValue i
  X' := path.X'
  Y' := path.Y'
  parameter_order := path.parameter_order
  hasDeriv_X := path.hasDeriv_X
  hasDeriv_Y := path.hasDeriv_Y
  continuous_X' := path.continuous_X'
  continuous_Y' := path.continuous_Y'
  avoids_multiplicative_divisor := path.avoids_multiplicative_divisor
  algebraic_base_X := path.algebraic_base_X
  algebraic_base_Y := path.algebraic_base_Y
  terminal_X := path.terminal_X
  terminal_Y := path.terminal_Y

/-- Exact simultaneous logarithm lifts and regulator identities for every coordinate-smooth,
divisor-avoiding complex-point path on the actual projective normalization. -/
theorem exists_stageTwoProjectivePathRegulatorWitness
    {x : Fin 2 → ℂ} {core : StageTwoDefectSlopeCore x} {a b : ℝ}
    (path : StageTwoProjectiveDivisorAvoidingPath x core a b) :
    Nonempty (StageTwoRegulatorWitness path.toCoordinatePath) :=
  exists_stageTwoRegulatorWitness path.toCoordinatePath

/-- Clauses 1--4, the proper projective relative normalization with concrete function field, and
the regulator law for every scheme-valued path satisfying the card's regularity, divisor, and
endpoint conditions. -/
structure StageTwoDefectSlopeProjectiveNormalizationPackage (x : Fin 2 → ℂ) where
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
    (path : StageTwoProjectiveDivisorAvoidingPath x core a b),
    Nonempty (StageTwoRegulatorWitness path.toCoordinatePath)

/-- Unconditional projective-normalization package under exactly the stage-two counterexample
assumptions of the card.  No geometric or analytic gap hypothesis is added. -/
theorem exists_stageTwoDefectSlopeProjectiveNormalizationPackage
    (x : Fin 2 → ℂ) (hx : LinearIndependent ℚ x)
    (hlt : Algebra.trdeg AlgNum (stageTwoValueField (x 0) (x 1)) < 2) :
    Nonempty (StageTwoDefectSlopeProjectiveNormalizationPackage x) := by
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
    regulator := fun path => exists_stageTwoProjectivePathRegulatorWitness path
  }⟩

/-- Extraction-failure form of the projective-normalization package. -/
theorem exists_stageTwoDefectSlopeProjectiveNormalizationPackage_of_extraction_failure
    (x : Fin 2 → ℂ) (hx : LinearIndependent ℚ x)
    (hfail : ¬ SchanuelExtractionFor x) :
    Nonempty (StageTwoDefectSlopeProjectiveNormalizationPackage x) :=
  exists_stageTwoDefectSlopeProjectiveNormalizationPackage x hx
    ((not_schanuelExtractionFor_two_iff_stageTwoValueField_trdeg_lt x).mp hfail)

end


end GaloisForLFunctions.RHTower
