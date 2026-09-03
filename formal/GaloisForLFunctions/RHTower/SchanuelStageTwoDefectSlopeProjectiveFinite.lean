import GaloisForLFunctions.RHTower.SchanuelStageTwoDefectSlopeAffineChartCompatibility
import GaloisForLFunctions.RHTower.SchanuelStageTwoDefectSlopeInfinityChartCompatibility
import GaloisForLFunctions.HTGeometry.IntegralClosureRingEquiv
import GaloisForLFunctions.HTGeometry.FiniteMorphismAffineRestriction

/-!
# Finiteness of the stage-two Schanuel projective normalization

The affine slope chart and inverse-slope chart identify the normalization section rings with the
finite integral closures already constructed in the concrete value field. Since these two affine
charts cover the projective line, the relative normalization is finite and hence proper over the
degree-zero coefficient spectrum.
-/

namespace GaloisForLFunctions.RHTower

open CategoryTheory AlgebraicGeometry GaloisForLFunctions.HTGeometry

noncomputable section

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 1000000

private theorem affine_app_finite (x : Fin 2 → ℂ)
    (core : StageTwoDefectSlopeCore x) :
    RingHom.Finite
      ((stageTwoSlopeProjectiveNormalizationToLine x core).app
        stageTwoSlopeProjectiveAffineChart).hom := by
  let f := stageTwoSlopeGenericMap x core
  have hAlgMap : RingHom.Finite
      (algebraMap
        Γ(stageTwoSlopeProjectiveLine, stageTwoSlopeProjectiveAffineChart)
        (@integralClosure
          Γ(stageTwoSlopeProjectiveLine, stageTwoSlopeProjectiveAffineChart)
          Γ(Spec (.of (stageTwoValueField (x 0) (x 1))),
            stageTwoSlopeGenericMap x core ⁻¹ᵁ
              stageTwoSlopeProjectiveAffineChart)
          _ _ ((stageTwoSlopeGenericMap x core).app
            stageTwoSlopeProjectiveAffineChart).hom.toAlgebra)) := by
    letI : Module.Finite (stageTwoSlopeCoordinateRing x core)
        (@integralClosure
          (stageTwoSlopeCoordinateRing x core)
          (stageTwoValueField (x 0) (x 1)) _ _
          (stageTwoSlopeCoordinateRing x core).val.toRingHom.toAlgebra) := by
      change Module.Finite (stageTwoSlopeCoordinateRing x core)
        (stageTwoSlopeAffineNormalizationRing x core)
      exact stageTwoSlopeAffineNormalizationRing_finite x core
    apply ringHomFinite_integralClosure_of_equiv_square
      ((stageTwoSlopeGenericMap x core).app
        stageTwoSlopeProjectiveAffineChart).hom
      (stageTwoSlopeCoordinateRing x core).val.toRingHom
      (stageTwoSlopeProjectiveAffineChartSectionsRingEquiv x core)
      (stageTwoSlopeGenericAffineChartSectionsRingEquivAligned x core)
      (stageTwoSlopeGenericAffineChart_app_compatibility x core)
  change RingHom.Finite
    (((stageTwoSlopeGenericMap x core).fromNormalization.app
      stageTwoSlopeProjectiveAffineChart).hom)
  rw [Scheme.Hom.fromNormalization_app]
  apply RingHom.Finite.comp
  · apply RingHom.Finite.of_surjective
    exact (commRingCatIsoRingEquiv
      ((stageTwoSlopeGenericMap x core).normalizationObjIso
        stageTwoSlopeProjectiveAffineChart_isAffine).symm).surjective
  · exact hAlgMap

private theorem infinity_app_finite (x : Fin 2 → ℂ)
    (core : StageTwoDefectSlopeCore x) :
    RingHom.Finite
      ((stageTwoSlopeProjectiveNormalizationToLine x core).app
        stageTwoSlopeProjectiveInfinityChart).hom := by
  have hAlgMap : RingHom.Finite
      (algebraMap
        Γ(stageTwoSlopeProjectiveLine, stageTwoSlopeProjectiveInfinityChart)
        (@integralClosure
          Γ(stageTwoSlopeProjectiveLine, stageTwoSlopeProjectiveInfinityChart)
          Γ(Spec (.of (stageTwoValueField (x 0) (x 1))),
            stageTwoSlopeGenericMap x core ⁻¹ᵁ
              stageTwoSlopeProjectiveInfinityChart)
          _ _ ((stageTwoSlopeGenericMap x core).app
            stageTwoSlopeProjectiveInfinityChart).hom.toAlgebra)) := by
    letI : Module.Finite (stageTwoInverseSlopeCoordinateRing x core)
        (@integralClosure
          (stageTwoInverseSlopeCoordinateRing x core)
          (stageTwoValueField (x 0) (x 1)) _ _
          (stageTwoInverseSlopeCoordinateRing x core).val.toRingHom.toAlgebra) := by
      change Module.Finite (stageTwoInverseSlopeCoordinateRing x core)
        (stageTwoInverseSlopeAffineNormalizationRing x core)
      exact stageTwoInverseSlopeAffineNormalizationRing_finite x core
    apply ringHomFinite_integralClosure_of_equiv_square
      ((stageTwoSlopeGenericMap x core).app
        stageTwoSlopeProjectiveInfinityChart).hom
      (stageTwoInverseSlopeCoordinateRing x core).val.toRingHom
      (stageTwoSlopeProjectiveInfinityChartSectionsRingEquiv x core)
      (stageTwoSlopeGenericInfinityChartSectionsRingEquivAligned x core)
      (stageTwoSlopeGenericInfinityChart_app_compatibility x core)
  change RingHom.Finite
    (((stageTwoSlopeGenericMap x core).fromNormalization.app
      stageTwoSlopeProjectiveInfinityChart).hom)
  rw [Scheme.Hom.fromNormalization_app]
  apply RingHom.Finite.comp
  · apply RingHom.Finite.of_surjective
    exact (commRingCatIsoRingEquiv
      ((stageTwoSlopeGenericMap x core).normalizationObjIso
        stageTwoSlopeProjectiveInfinityChart_isAffine).symm).surjective
  · exact hAlgMap

/-- The relative normalization is finite over the projective slope line. -/
noncomputable instance stageTwoSlopeProjectiveNormalizationToLine_isFinite
    (x : Fin 2 → ℂ) (core : StageTwoDefectSlopeCore x) :
    IsFinite (stageTwoSlopeProjectiveNormalizationToLine x core) := by
  apply isFinite_of_iSup_eq_top_finite_app
    (stageTwoSlopeProjectiveNormalizationToLine x core)
    (fun i : Option PUnit.{1} =>
      Proj.basicOpen stageTwoSlopeProjectiveLineGrading (MvPolynomial.X i))
    stageTwoSlopeProjectiveStandardCharts_cover
  · intro i
    rcases i with (_ | ⟨⟩)
    · exact stageTwoSlopeProjectiveAffineChart_isAffine
    · exact stageTwoSlopeProjectiveInfinityChart_isAffine
  · intro i
    rcases i with (_ | ⟨⟩)
    · exact affine_app_finite x core
    · exact infinity_app_finite x core

/-- The normalized projective slope model is proper over the degree-zero coefficient spectrum. -/
noncomputable instance stageTwoSlopeProjectiveNormalizationToGradeZero_isProper
    (x : Fin 2 → ℂ) (core : StageTwoDefectSlopeCore x) :
    IsProper (stageTwoSlopeProjectiveNormalizationToGradeZero x core) := by
  change IsProper
    ((stageTwoSlopeGenericMap x core).fromNormalization ≫
      Proj.toSpecZero stageTwoSlopeProjectiveLineGrading)
  infer_instance

end
end GaloisForLFunctions.RHTower
