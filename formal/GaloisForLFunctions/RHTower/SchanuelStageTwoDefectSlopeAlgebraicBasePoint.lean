import GaloisForLFunctions.RHTower.SchanuelStageTwoDefectSlopeProjectiveRegulator
import GaloisForLFunctions.HTGeometry.BaseFieldPointComplexification

/-!
# Algebraic source points for stage-two projective regulator paths

The paper's regulator law starts at an algebraic smooth point.  Algebraicity of the four displayed
coordinate values is weaker than algebraicity of the scheme point itself.  This module records the
literal factorization through `Spec AlgNum`, states smoothness at that algebraic point's stalk, and
then applies the existing regulator theorem to every divisor-avoiding path with such a source.

No existence of an analytified smooth path is asserted; that is the remaining analytic interface.
-/

namespace GaloisForLFunctions.RHTower

open CategoryTheory AlgebraicGeometry GaloisForLFunctions.HTGeometry Set

noncomputable section

/-- A divisor-avoiding projective regulator path whose source is an actual smooth
`AlgNum`-valued point, not merely a complex point with four algebraic coordinate values. -/
structure StageTwoProjectiveDivisorAvoidingPathWithAlgebraicBase
    (x : Fin 2 → ℂ) (core : StageTwoDefectSlopeCore x) (a b : ℝ)
    extends StageTwoProjectiveDivisorAvoidingPath x core a b where
  algebraicBasePoint :
    (stageTwoSlopeProjectiveModel x core).BaseFieldPointOver AlgNum
      (stageTwoSlopeProjectiveNormalizationToAlgNum x core)
  algebraicBaseFactorization :
    (toStageTwoProjectiveDivisorAvoidingPath.point a).point.hom =
      algebraicBasePoint.toComplexPoint.hom
  smoothAlgebraicBase :
    ((stageTwoSlopeProjectiveNormalizationToAlgNum x core).stalkMap
      algebraicBasePoint.center).hom.FormallySmooth

/-- The source complex point literally factors through its `AlgNum`-valued point. -/
theorem StageTwoProjectiveDivisorAvoidingPathWithAlgebraicBase.source_factors
    {x : Fin 2 → ℂ} {core : StageTwoDefectSlopeCore x} {a b : ℝ}
    (path : StageTwoProjectiveDivisorAvoidingPathWithAlgebraicBase x core a b) :
    (path.toStageTwoProjectiveDivisorAvoidingPath.point a).point.hom =
      Spec.map (CommRingCat.ofHom (algebraMap AlgNum ℂ)) ≫
        path.algebraicBasePoint.hom := by
  rw [path.algebraicBaseFactorization]
  rfl

/-- Exact regulator witness for every coordinate-smooth divisor-avoiding path whose source is an
actual smooth algebraic point of the projective normalization. -/
theorem exists_stageTwoProjectivePathRegulatorWitness_of_algebraicBase
    {x : Fin 2 → ℂ} {core : StageTwoDefectSlopeCore x} {a b : ℝ}
    (path : StageTwoProjectiveDivisorAvoidingPathWithAlgebraicBase x core a b) :
    Nonempty (StageTwoRegulatorWitness
      path.toStageTwoProjectiveDivisorAvoidingPath.toCoordinatePath) :=
  exists_stageTwoProjectivePathRegulatorWitness
    path.toStageTwoProjectiveDivisorAvoidingPath

end

end GaloisForLFunctions.RHTower
