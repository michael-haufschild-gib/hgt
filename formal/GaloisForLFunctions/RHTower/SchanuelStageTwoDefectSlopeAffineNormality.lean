import GaloisForLFunctions.RHTower.SchanuelStageTwoDefectSlopeNormalForm
import GaloisForLFunctions.HTGeometry.SchemeNormalStalkDVR
import GaloisForLFunctions.HTGeometry.SpecStalkLocalization
import Mathlib.RingTheory.DedekindDomain.IntegralClosure

/-!
# Normality of the stage-two Schanuel slope chart

The proved transcendence of the canonical slope identifies its polynomial coordinate ring with
`AlgNum[X]`.  Consequently that ring is a principal ideal domain and a Dedekind domain.  Since the
concrete stage-two value field is already proved finite over the slope rational-function field, its
integral closure is again a Dedekind domain.  Thus the affine normalization chart constructed in
`SchanuelStageTwoDefectSlopeNormalForm` is genuinely Noetherian and normal, with no extra geometric
or analytic premise.
-/

namespace GaloisForLFunctions.RHTower

open IntermediateField Set Order
open scoped IntermediateField.algebraAdjoinAdjoin

set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 4000000

noncomputable section

/-- Evaluation at the canonical slope, with codomain restricted to its polynomial coordinate
ring. -/
noncomputable def stageTwoSlopePolynomialAlgHom
    (x : Fin 2 → ℂ) (core : StageTwoDefectSlopeCore x) :
    Polynomial AlgNum →ₐ[AlgNum] stageTwoSlopeCoordinateRing x core :=
  (Polynomial.aeval core.rho).codRestrict
    (stageTwoSlopeCoordinateRing x core) (fun p => by
      change (Polynomial.aeval core.rho) p ∈
        Algebra.adjoin AlgNum ({core.rho} : Set (stageTwoValueField (x 0) (x 1)))
      have hEq := Algebra.adjoin_singleton_eq_range_aeval AlgNum core.rho
      rw [hEq]
      exact ⟨p, rfl⟩)

/-- Transcendence of the canonical slope makes polynomial evaluation injective. -/
theorem stageTwoSlopePolynomialAlgHom_injective
    (x : Fin 2 → ℂ) (core : StageTwoDefectSlopeCore x) :
    Function.Injective (stageTwoSlopePolynomialAlgHom x core) := by
  intro p q hpq
  apply sub_eq_zero.mp
  apply (transcendental_iff.mp core.rho_transcendental)
  have h := congrArg Subtype.val hpq
  change (Polynomial.aeval core.rho) p = (Polynomial.aeval core.rho) q at h
  simpa only [map_sub, sub_eq_zero] using h

/-- Every element of the slope coordinate ring is a polynomial in the canonical slope. -/
theorem stageTwoSlopePolynomialAlgHom_surjective
    (x : Fin 2 → ℂ) (core : StageTwoDefectSlopeCore x) :
    Function.Surjective (stageTwoSlopePolynomialAlgHom x core) := by
  intro y
  have hy : (y : stageTwoValueField (x 0) (x 1)) ∈
      (Polynomial.aeval core.rho : Polynomial AlgNum →ₐ[AlgNum]
        stageTwoValueField (x 0) (x 1)).range := by
    rw [← Algebra.adjoin_singleton_eq_range_aeval]
    exact y.property
  obtain ⟨p, hp⟩ := hy
  refine ⟨p, Subtype.ext ?_⟩
  exact hp

/-- The canonical slope coordinate ring is exactly the polynomial ring over the algebraic
numbers. -/
noncomputable def stageTwoSlopePolynomialAlgEquiv
    (x : Fin 2 → ℂ) (core : StageTwoDefectSlopeCore x) :
    Polynomial AlgNum ≃ₐ[AlgNum] stageTwoSlopeCoordinateRing x core :=
  AlgEquiv.ofBijective (stageTwoSlopePolynomialAlgHom x core)
    ⟨stageTwoSlopePolynomialAlgHom_injective x core,
      stageTwoSlopePolynomialAlgHom_surjective x core⟩

/-- The coordinate ring of the canonical slope line is a principal ideal ring. -/
noncomputable instance stageTwoSlopeCoordinateRing_isPrincipalIdealRing
    (x : Fin 2 → ℂ) (core : StageTwoDefectSlopeCore x) :
    IsPrincipalIdealRing (stageTwoSlopeCoordinateRing x core) :=
  IsPrincipalIdealRing.of_surjective (stageTwoSlopePolynomialAlgHom x core)
    (stageTwoSlopePolynomialAlgHom_surjective x core)

/-- The coordinate ring of the canonical slope line is a Dedekind domain. -/
noncomputable instance stageTwoSlopeCoordinateRing_isDedekindDomain
    (x : Fin 2 → ℂ) (core : StageTwoDefectSlopeCore x) :
    IsDedekindDomain (stageTwoSlopeCoordinateRing x core) := by
  infer_instance

/-- The actual integral-closure normalization ring is a Dedekind domain.  Finiteness is supplied
by the proved stage-two defect-slope core; separability follows in characteristic zero. -/
noncomputable instance stageTwoSlopeAffineNormalizationRing_isDedekindDomain
    (x : Fin 2 → ℂ) (core : StageTwoDefectSlopeCore x) :
    IsDedekindDomain (stageTwoSlopeAffineNormalizationRing x core) := by
  letI algSlopeValue : Algebra (stageTwoSlopeRationalField x core)
      (stageTwoValueField (x 0) (x 1)) :=
    (stageTwoSlopeRationalField x core).val.toAlgebra
  letI : IsScalarTower AlgNum (stageTwoSlopeRationalField x core)
      (stageTwoValueField (x 0) (x 1)) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  letI towerCoordinateSlopeValue : IsScalarTower (stageTwoSlopeCoordinateRing x core)
      (stageTwoSlopeRationalField x core) (stageTwoValueField (x 0) (x 1)) :=
    IntermediateField.algebraAdjoinAdjoin.instIsScalarTowerSubtypeMemSubalgebraAdjoinAdjoin_1
      AlgNum ({core.rho} : Set (stageTwoValueField (x 0) (x 1)))
      (stageTwoValueField (x 0) (x 1))
  letI hfinite : FiniteDimensional (stageTwoSlopeRationalField x core)
      (stageTwoValueField (x 0) (x 1)) := core.finite_over_slope
  letI : Algebra.IsAlgebraic (stageTwoSlopeRationalField x core)
      (stageTwoValueField (x 0) (x 1)) :=
    @Algebra.IsAlgebraic.of_finite
      (stageTwoSlopeRationalField x core)
      (stageTwoValueField (x 0) (x 1)) _ _ _ algSlopeValue hfinite
  letI : Algebra.IsSeparable (stageTwoSlopeRationalField x core)
      (stageTwoValueField (x 0) (x 1)) := inferInstance
  exact @IsIntegralClosure.isDedekindDomain
    (stageTwoSlopeCoordinateRing x core)
    (stageTwoSlopeRationalField x core)
    inferInstance inferInstance inferInstance inferInstance
    (stageTwoValueField (x 0) (x 1))
    inferInstance
    (stageTwoSlopeAffineNormalizationRing x core)
    inferInstance algSlopeValue inferInstance towerCoordinateSlopeValue
    inferInstance inferInstance inferInstance inferInstance hfinite
    inferInstance inferInstance inferInstance inferInstance

/-- The affine normalization ring is finite as a module over the polynomial slope coordinate
ring.  This is the module-finiteness statement inside the Dedekind integral-closure theorem,
exported explicitly for the finite-morphism construction of the projective normalization. -/
noncomputable instance stageTwoSlopeAffineNormalizationRing_finite
    (x : Fin 2 → ℂ) (core : StageTwoDefectSlopeCore x) :
    Module.Finite (stageTwoSlopeCoordinateRing x core)
      (stageTwoSlopeAffineNormalizationRing x core) := by
  letI algSlopeValue : Algebra (stageTwoSlopeRationalField x core)
      (stageTwoValueField (x 0) (x 1)) :=
    (stageTwoSlopeRationalField x core).val.toAlgebra
  letI : IsScalarTower AlgNum (stageTwoSlopeRationalField x core)
      (stageTwoValueField (x 0) (x 1)) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  letI towerCoordinateSlopeValue : IsScalarTower (stageTwoSlopeCoordinateRing x core)
      (stageTwoSlopeRationalField x core) (stageTwoValueField (x 0) (x 1)) :=
    IntermediateField.algebraAdjoinAdjoin.instIsScalarTowerSubtypeMemSubalgebraAdjoinAdjoin_1
      AlgNum ({core.rho} : Set (stageTwoValueField (x 0) (x 1)))
      (stageTwoValueField (x 0) (x 1))
  letI hfinite : FiniteDimensional (stageTwoSlopeRationalField x core)
      (stageTwoValueField (x 0) (x 1)) := core.finite_over_slope
  letI : Algebra.IsAlgebraic (stageTwoSlopeRationalField x core)
      (stageTwoValueField (x 0) (x 1)) :=
    @Algebra.IsAlgebraic.of_finite
      (stageTwoSlopeRationalField x core)
      (stageTwoValueField (x 0) (x 1)) _ _ _ algSlopeValue hfinite
  letI : Algebra.IsSeparable (stageTwoSlopeRationalField x core)
      (stageTwoValueField (x 0) (x 1)) := inferInstance
  letI : IsNoetherian (stageTwoSlopeCoordinateRing x core)
      (stageTwoSlopeAffineNormalizationRing x core) :=
    @IsIntegralClosure.isNoetherian
      (stageTwoSlopeCoordinateRing x core)
      (stageTwoSlopeRationalField x core)
      inferInstance inferInstance inferInstance inferInstance
      (stageTwoValueField (x 0) (x 1))
      inferInstance
      (stageTwoSlopeAffineNormalizationRing x core)
      inferInstance algSlopeValue inferInstance towerCoordinateSlopeValue
      inferInstance inferInstance inferInstance inferInstance hfinite
      inferInstance inferInstance inferInstance inferInstance
  exact ⟨IsNoetherian.noetherian ⊤⟩

/-- The affine normalization chart is locally Noetherian. -/
noncomputable instance stageTwoSlopeAffineNormalizationScheme_isLocallyNoetherian
    (x : Fin 2 → ℂ) (core : StageTwoDefectSlopeCore x) :
    AlgebraicGeometry.IsLocallyNoetherian
      (stageTwoSlopeAffineNormalizationScheme x core) := by
  infer_instance

private theorem specStalk_isIntegrallyClosed_of_isDedekindDomain
    (R : Type*) [CommRing R] [IsDedekindDomain R]
    (z : AlgebraicGeometry.Spec (.of R)) :
    IsIntegrallyClosed ((AlgebraicGeometry.Spec (.of R)).presheaf.stalk z) := by
  let p : Ideal R := z.asIdeal
  letI : p.IsPrime := z.isPrime
  haveI : IsIntegrallyClosed (Localization.AtPrime p) := by
    exact isIntegrallyClosed_of_isLocalization (Localization.AtPrime p)
      p.primeCompl (Ideal.primeCompl_le_nonZeroDivisors _)
  exact IsIntegrallyClosed.of_equiv
    (_root_.HTGeometry.specStalkRingEquiv (.of R) z)

/-- Every local ring of the affine normalization chart is integrally closed. -/
theorem stageTwoSlopeAffineNormalization_stalk_isIntegrallyClosed
    (x : Fin 2 → ℂ) (core : StageTwoDefectSlopeCore x)
    (z : stageTwoSlopeAffineNormalizationScheme x core) :
    IsIntegrallyClosed
      ((stageTwoSlopeAffineNormalizationScheme x core).presheaf.stalk z) := by
  exact specStalk_isIntegrallyClosed_of_isDedekindDomain
    (stageTwoSlopeAffineNormalizationRing x core) z

/-- Every codimension-one local ring of the affine normalization chart is a discrete valuation
ring. -/
theorem stageTwoSlopeAffineNormalization_stalk_isDiscreteValuationRing
    (x : Fin 2 → ℂ) (core : StageTwoDefectSlopeCore x)
    (z : stageTwoSlopeAffineNormalizationScheme x core)
    (hz : coheight z = 1) :
    IsDiscreteValuationRing
      ((stageTwoSlopeAffineNormalizationScheme x core).presheaf.stalk z) := by
  letI := stageTwoSlopeAffineNormalization_stalk_isIntegrallyClosed x core z
  exact GaloisForLFunctions.HTGeometry.isDiscreteValuationRing_stalk hz

end

end GaloisForLFunctions.RHTower
