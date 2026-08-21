import Mathlib.Analysis.Complex.Circle
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Basic
import Mathlib.LinearAlgebra.Orientation

/-!
# Smooth four-dimensional and Hodge infrastructure for Seiberg--Witten theory

Mathlib supplies smooth real manifolds and smooth vector bundles, but not a packaged
Seiberg--Witten geometry.  This module fixes the four-dimensional Euclidean model, exposes the
actual smooth-manifold and smooth rank-two complex-vector-bundle predicates used below, and adds
the algebraic Hodge-star interface needed to select self-dual curvature.

`ModelOrientedSmoothFourManifold` deliberately records only an orientation of the local model
space.  `SeibergWitten.Orientation` upgrades that first layer to an atlas-compatible orientation
using actual tangent-coordinate changes.
-/

noncomputable section

open scoped Manifold

namespace GaloisForLFunctions.HTGeometry.SeibergWitten

/-- The real four-dimensional Euclidean local model. -/
abbrev FourSpace := EuclideanSpace ℝ (Fin 4)

/-- Smooth manifold model without boundary used for four-dimensional gauge theory. -/
abbrev fourModel : ModelWithCorners ℝ FourSpace FourSpace :=
  modelWithCornersSelf ℝ FourSpace

/-- A smooth manifold modeled on real four-space. -/
class SmoothFourManifold (M : Type*) [TopologicalSpace M] [ChartedSpace FourSpace M] : Prop where
  smooth : IsManifold fourModel (⊤ : WithTop ℕ∞) M

attribute [instance] SmoothFourManifold.smooth

/-- Smooth four-manifold together with a chosen orientation of its local Euclidean model. -/
structure ModelOrientedSmoothFourManifold
    (M : Type*) [TopologicalSpace M] [ChartedSpace FourSpace M] where
  smooth : SmoothFourManifold M
  modelOrientation : Orientation ℝ FourSpace (Fin 4)

/-- The Euclidean model is itself a smooth four-manifold. -/
theorem flatFourSpace_isSmooth :
    IsManifold fourModel (⊤ : WithTop ℕ∞) FourSpace :=
  inferInstance

/-- The Euclidean four-model, registered as a smooth four-manifold. -/
instance flatFourSpace_smoothFourManifold : SmoothFourManifold FourSpace :=
  ⟨flatFourSpace_isSmooth⟩

/-- Canonical orientation of Euclidean four-space, transported from its coordinate basis. -/
noncomputable def flatFourSpaceOrientation : Orientation ℝ FourSpace (Fin 4) :=
  Orientation.map (Fin 4) (EuclideanSpace.equiv (Fin 4) ℝ).symm
    (Pi.basisFun ℝ (Fin 4)).orientation

/-- Closed smooth, model-oriented Euclidean four-space datum. -/
noncomputable def flatModelOrientedFourSpace :
    ModelOrientedSmoothFourManifold FourSpace where
  smooth := ⟨flatFourSpace_isSmooth⟩
  modelOrientation := flatFourSpaceOrientation

/-- Actual smooth complex rank-two positive/negative spinor bundles and a determinant line
bundle, expressed using mathlib's vector-bundle predicates.

This is the smooth vector-bundle layer.  `SeibergWitten.PrincipalSpinC` separately constructs the
algebraic principal `Spinᶜ(4)` lift.  `SeibergWitten.FlatAssociatedSmooth` identifies the associated
and smooth total spaces in the closed flat case; nontrivial global association remains separate. -/
structure SmoothSpinCBundlePrelude
    (M : Type u) [TopologicalSpace M] [ChartedSpace FourSpace M] [SmoothFourManifold M]
    (SPlus SMinus Determinant : M → Type v)
    [∀ x, AddCommMonoid (SPlus x)] [∀ x, Module ℂ (SPlus x)] [∀ x, Module ℝ (SPlus x)]
    [∀ x, AddCommMonoid (SMinus x)] [∀ x, Module ℂ (SMinus x)] [∀ x, Module ℝ (SMinus x)]
    [∀ x, AddCommMonoid (Determinant x)] [∀ x, Module ℂ (Determinant x)]
    [∀ x, Module ℝ (Determinant x)]
    [TopologicalSpace (Bundle.TotalSpace (Fin 2 → ℂ) SPlus)]
    [∀ x, TopologicalSpace (SPlus x)] [FiberBundle (Fin 2 → ℂ) SPlus]
    [VectorBundle ℂ (Fin 2 → ℂ) SPlus] [VectorBundle ℝ (Fin 2 → ℂ) SPlus]
    [TopologicalSpace (Bundle.TotalSpace (Fin 2 → ℂ) SMinus)]
    [∀ x, TopologicalSpace (SMinus x)] [FiberBundle (Fin 2 → ℂ) SMinus]
    [VectorBundle ℂ (Fin 2 → ℂ) SMinus] [VectorBundle ℝ (Fin 2 → ℂ) SMinus]
    [TopologicalSpace (Bundle.TotalSpace ℂ Determinant)]
    [∀ x, TopologicalSpace (Determinant x)] [FiberBundle ℂ Determinant]
    [VectorBundle ℂ ℂ Determinant] [VectorBundle ℝ ℂ Determinant] : Prop where
  positiveSmooth : ContMDiffVectorBundle (⊤ : WithTop ℕ∞) (Fin 2 → ℂ) SPlus fourModel
  negativeSmooth : ContMDiffVectorBundle (⊤ : WithTop ℕ∞) (Fin 2 → ℂ) SMinus fourModel
  determinantSmooth : ContMDiffVectorBundle (⊤ : WithTop ℕ∞) ℂ Determinant fourModel

/-- Constant positive-chirality rank-two complex bundle on Euclidean four-space. -/
abbrev flatPositiveSpinorBundle : FourSpace → Type := fun _ => Fin 2 → ℂ

/-- Constant negative-chirality rank-two complex bundle on Euclidean four-space. -/
abbrev flatNegativeSpinorBundle : FourSpace → Type := fun _ => Fin 2 → ℂ

/-- Constant complex determinant line on Euclidean four-space. -/
abbrev flatDeterminantLineBundle : FourSpace → Type := fun _ => ℂ

/-- The constant spinor fibers form actual smooth complex vector bundles in mathlib. -/
theorem flatSmoothSpinCBundlePrelude :
    SmoothSpinCBundlePrelude FourSpace flatPositiveSpinorBundle flatNegativeSpinorBundle
      flatDeterminantLineBundle where
  positiveSmooth := inferInstance
  negativeSmooth := inferInstance
  determinantSmooth := inferInstance

/-- A real Hodge-star operator on a space of two-forms. -/
structure HodgeStar (TwoForms : Type*) [AddCommGroup TwoForms] [Module ℝ TwoForms] where
  toLinearMap : TwoForms →ₗ[ℝ] TwoForms
  sq : toLinearMap.comp toLinearMap = LinearMap.id

/-- Self-duality with respect to a Hodge star. -/
def HodgeStar.isSelfDual {TwoForms : Type*} [AddCommGroup TwoForms] [Module ℝ TwoForms]
    (star : HodgeStar TwoForms) (ω : TwoForms) : Prop :=
  star.toLinearMap ω = ω

/-- Algebraic projection of a two-form to its self-dual component. -/
def HodgeStar.selfDualPart {TwoForms : Type*} [AddCommGroup TwoForms] [Module ℝ TwoForms]
    (star : HodgeStar TwoForms) (ω : TwoForms) : TwoForms :=
  (2 : ℝ)⁻¹ • (ω + star.toLinearMap ω)

/-- The algebraic Hodge projection is self-dual under every involutive Hodge star. -/
theorem HodgeStar.selfDualPart_isSelfDual
    {TwoForms : Type*} [AddCommGroup TwoForms] [Module ℝ TwoForms]
    (star : HodgeStar TwoForms) (ω : TwoForms) :
    star.isSelfDual (star.selfDualPart ω) := by
  have hsq : star.toLinearMap (star.toLinearMap ω) = ω := by
    have h := LinearMap.congr_fun star.sq ω
    simpa using h
  change star.toLinearMap ((2 : ℝ)⁻¹ • (ω + star.toLinearMap ω)) =
    (2 : ℝ)⁻¹ • (ω + star.toLinearMap ω)
  rw [map_smul, map_add, hsq]
  module

end GaloisForLFunctions.HTGeometry.SeibergWitten
