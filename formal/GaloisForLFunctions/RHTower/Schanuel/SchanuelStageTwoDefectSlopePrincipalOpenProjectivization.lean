import GaloisForLFunctions.RHTower.Schanuel.SchanuelStageTwoDefectSlopePrincipalOpenRegulator
import GaloisForLFunctions.RHTower.Schanuel.SchanuelStageTwoDefectSlopeProjectiveRegulator

/-!
# Projectivization of the common stage-two principal open

The common coordinate localization is not merely an affine proxy.  Its spectrum maps through the
computed normalized standard chart into the actual proper projective normalization.  The map is an
open immersion because it is the composite of the principal-localization open immersion, two
isomorphisms, and the normalized chart inclusion.

Every relative complex point and every smooth affine path therefore gives a literal scheme-valued
point or path on the projective model.  At the source, this construction factors through the actual
`AlgNum`-valued point; at the target, it carries the canonical point with coordinate values
`(x₁,x₂,exp x₁,exp x₂)`.
-/

namespace GaloisForLFunctions.RHTower

open CategoryTheory AlgebraicGeometry GaloisForLFunctions.HTGeometry

noncomputable section

set_option synthInstance.maxHeartbeats 1000000

/-- The common coordinate principal localization as an open subscheme of the actual projective
normalization. -/
noncomputable def stageTwoSlopeCoordinatePrincipalOpenToProjectiveNormalization
    (x : Fin 2 → ℂ) (core : StageTwoDefectSlopeCore x) :
    Spec (.of (stageTwoSlopeCoordinatePrincipalOpenRing x core)) ⟶
      stageTwoSlopeProjectiveNormalization x core := by
  let N := stageTwoSlopeProjectiveNormalization x core
  let U := stageTwoSlopeProjectiveNormalizationAffineChart x core
  let R := stageTwoSlopeAffineNormalizationRing x core
  let S := stageTwoSlopeCoordinatePrincipalOpenRing x core
  let e : Γ(N, U) ≃+* R :=
    stageTwoSlopeProjectiveNormalizationAffineChartSectionsRingEquiv x core
  let eCat : Γ(N, U) ≅ CommRingCat.of R := e.toCommRingCatIso
  let hU : IsAffineOpen U :=
    stageTwoSlopeProjectiveNormalizationAffineChart_isAffine x core
  exact
    Spec.map (CommRingCat.ofHom (algebraMap R S)) ≫
      Spec.map eCat.hom ≫ hU.isoSpec.inv ≫ U.ι

/-- The common coordinate localization is genuinely an open subscheme of the projective
normalization. -/
noncomputable instance stageTwoSlopeCoordinatePrincipalOpenToProjectiveNormalization_isOpenImmersion
    (x : Fin 2 → ℂ) (core : StageTwoDefectSlopeCore x) :
    IsOpenImmersion
      (stageTwoSlopeCoordinatePrincipalOpenToProjectiveNormalization x core) := by
  dsimp only [stageTwoSlopeCoordinatePrincipalOpenToProjectiveNormalization]
  infer_instance

/-- A relative complex point of the principal localization, regarded as a complex-valued point of
the actual projective normalization. -/
noncomputable def stageTwoSlopeCoordinatePrincipalOpenProjectiveComplexPoint
    {x : Fin 2 → ℂ} {core : StageTwoDefectSlopeCore x}
    (p : RelativeAlgSpec AlgNum (stageTwoSlopeCoordinatePrincipalOpenRing x core)) :
    (stageTwoSlopeProjectiveNormalization x core).ComplexPoint :=
  Spec.map (CommRingCat.ofHom p.toRingHom) ≫
    stageTwoSlopeCoordinatePrincipalOpenToProjectiveNormalization x core

/-- An `AlgNum`-valued point of the principal localization, regarded as an algebraic point of the
actual projective normalization. -/
noncomputable def stageTwoSlopeCoordinatePrincipalOpenAlgebraicProjectivePoint
    {x : Fin 2 → ℂ} {core : StageTwoDefectSlopeCore x}
    (q : stageTwoSlopeCoordinatePrincipalOpenRing x core →ₐ[AlgNum] AlgNum) :
    Spec (.of AlgNum) ⟶ stageTwoSlopeProjectiveNormalization x core :=
  Spec.map (CommRingCat.ofHom q.toRingHom) ≫
    stageTwoSlopeCoordinatePrincipalOpenToProjectiveNormalization x core

/-- Complexifying an algebraic point before projectivization is exactly the same as first mapping
the algebraic point into the projective normalization and then extending the base point to
`Spec ℂ`. -/
theorem stageTwoSlopeCoordinatePrincipalOpenBaseComplexPoint_projectiveFactorization
    {x : Fin 2 → ℂ} {core : StageTwoDefectSlopeCore x}
    (q : stageTwoSlopeCoordinatePrincipalOpenRing x core →ₐ[AlgNum] AlgNum) :
    stageTwoSlopeCoordinatePrincipalOpenProjectiveComplexPoint
        (stageTwoSlopeCoordinatePrincipalOpenBaseComplexPoint q) =
      Spec.map (CommRingCat.ofHom (algebraMap AlgNum ℂ)) ≫
        stageTwoSlopeCoordinatePrincipalOpenAlgebraicProjectivePoint q := by
  unfold stageTwoSlopeCoordinatePrincipalOpenProjectiveComplexPoint
  unfold stageTwoSlopeCoordinatePrincipalOpenBaseComplexPoint
  unfold stageTwoSlopeCoordinatePrincipalOpenAlgebraicProjectivePoint
  rw [← Category.assoc]
  rw [← Spec.map_comp]
  congr 1

/-- Projectivization of a smooth path in the common principal localization. -/
noncomputable def StageTwoCoordinatePrincipalOpenSmoothPath.projectivePoint
    {x : Fin 2 → ℂ} {core : StageTwoDefectSlopeCore x} {a b : ℝ}
    (path : StageTwoCoordinatePrincipalOpenSmoothPath x core a b) :
    ℝ → (stageTwoSlopeProjectiveNormalization x core).ComplexPoint :=
  fun t => stageTwoSlopeCoordinatePrincipalOpenProjectiveComplexPoint (path.point t)

/-- The projectivized smooth path starts at the complexification of its actual algebraic point. -/
theorem StageTwoCoordinatePrincipalOpenSmoothPath.projectivePoint_source
    {x : Fin 2 → ℂ} {core : StageTwoDefectSlopeCore x} {a b : ℝ}
    (path : StageTwoCoordinatePrincipalOpenSmoothPath x core a b) :
    path.projectivePoint a =
      Spec.map (CommRingCat.ofHom (algebraMap AlgNum ℂ)) ≫
        stageTwoSlopeCoordinatePrincipalOpenAlgebraicProjectivePoint path.basePoint := by
  unfold StageTwoCoordinatePrincipalOpenSmoothPath.projectivePoint
  rw [path.source]
  exact stageTwoSlopeCoordinatePrincipalOpenBaseComplexPoint_projectiveFactorization
    path.basePoint

/-- The projectivized smooth path ends at the projectivization of the canonical target point. -/
theorem StageTwoCoordinatePrincipalOpenSmoothPath.projectivePoint_target
    {x : Fin 2 → ℂ} {core : StageTwoDefectSlopeCore x} {a b : ℝ}
    (path : StageTwoCoordinatePrincipalOpenSmoothPath x core a b) :
    path.projectivePoint b =
      stageTwoSlopeCoordinatePrincipalOpenProjectiveComplexPoint
        (stageTwoSlopeCoordinatePrincipalOpenTargetPoint x core) := by
  unfold StageTwoCoordinatePrincipalOpenSmoothPath.projectivePoint
  rw [path.target]

end

end GaloisForLFunctions.RHTower
