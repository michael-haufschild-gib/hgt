import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.SmoothStalkDomains
import Mathlib.AlgebraicGeometry.Geometrically.Reduced
import Mathlib.RingTheory.Smooth.NoetherianDescent

/-! Smooth morphisms have geometrically reduced fibres and preserve reduced bases. -/

open AlgebraicGeometry CategoryTheory Limits

namespace GlobalTheory

/-- A smooth scheme over a field is reduced, since its local rings are domains. -/
theorem isReduced_smooth_of_field {K : Type*} [Field K] {X : Scheme}
    (s : X ⟶ Spec (.of K)) [Smooth s] : IsReduced X := by
  haveI : ∀ x : X, _root_.IsReduced (X.presheaf.stalk x) := fun x => by
    haveI := UpperTheory.Cb.isDomain_stalk_of_smooth_over_field s x
    infer_instance
  exact isReduced_of_isReduced_stalk X

/-- Smoothness persists on the field-valued fibres. -/
theorem geometricallyReduced_of_smooth {X S : Scheme} (f : X ⟶ S) [Smooth f] :
    GeometricallyReduced f := by
  refine ⟨fun K _ y Z fst snd h => ?_⟩
  haveI : Smooth snd := MorphismProperty.of_isPullback h ‹Smooth f›
  exact isReduced_smooth_of_field snd

end GlobalTheory

open GlobalTheory in
private theorem isReduced_algebra_of_smooth_of_isNoetherianRing (A B : Type) [CommRing A] [CommRing B]
    [Algebra A B] [Algebra.Smooth A B] [IsNoetherianRing A] [_root_.IsReduced A] :
    _root_.IsReduced B := by
  let f : Spec (CommRingCat.of B) ⟶ Spec (CommRingCat.of A) :=
    Spec.map (CommRingCat.ofHom (algebraMap A B))
  have : Smooth f := HasRingHomProperty.Spec_iff.mpr (RingHom.smooth_algebraMap.mpr inferInstance)
  have : GeometricallyReduced f := geometricallyReduced_of_smooth f
  have : _root_.IsReduced (CommRingCat.of A) := inferInstanceAs (_root_.IsReduced A)
  have : IsNoetherianRing (CommRingCat.of A) := inferInstanceAs (IsNoetherianRing A)
  have : IsReduced (Spec (CommRingCat.of B)) :=
    GeometricallyReduced.isReduced_of_flat_of_isLocallyNoetherian f
  exact (affine_isReduced_iff (CommRingCat.of B)).mp inferInstance

private theorem isReduced_algebra_of_smooth_of_isReduced (A B : Type) [CommRing A] [CommRing B]
    [Algebra A B] [Algebra.Smooth A B] [_root_.IsReduced A] :
    _root_.IsReduced B := by
  obtain ⟨A₀, B₀, _, _, hfg, hsm, ⟨e⟩⟩ := Algebra.Smooth.exists_subalgebra_fg ℤ A B
  have : Algebra.FiniteType ℤ A₀ := (Subalgebra.fg_iff_finiteType A₀).mp hfg
  have : IsNoetherianRing A₀ := Algebra.FiniteType.isNoetherianRing ℤ A₀
  have : Module.Flat A₀ B₀ := Algebra.Smooth.flat A₀ B₀
  have key : _root_.IsReduced (TensorProduct A₀ B₀ A) := by
    refine IsReduced.tensorProduct_of_flat_of_forall_fg (fun D hD => ?_)
    have : Algebra.FiniteType A₀ D := (Subalgebra.fg_iff_finiteType D).mp hD
    have : IsNoetherianRing D := Algebra.FiniteType.isNoetherianRing A₀ D
    have : _root_.IsReduced D := isReduced_of_injective D.val Subtype.val_injective
    have : _root_.IsReduced (TensorProduct A₀ D B₀) :=
      isReduced_algebra_of_smooth_of_isNoetherianRing D (TensorProduct A₀ D B₀)
    exact isReduced_of_injective (Algebra.TensorProduct.comm A₀ B₀ D).toRingHom
      (Algebra.TensorProduct.comm A₀ B₀ D).injective
  exact isReduced_of_injective
    ((Algebra.TensorProduct.comm A₀ A B₀).toRingHom.comp e.toRingHom)
    ((Algebra.TensorProduct.comm A₀ A B₀).injective.comp e.injective)

private theorem isReduced_of_smooth_of_isAffine_of_isReduced {Y T : Scheme.{0}} (g : Y ⟶ T) [Smooth g]
    [IsAffine T] [IsReduced T] : IsReduced Y := by
  have hι : ∀ j, Smooth (Y.affineOpenCover.f j) := fun j => inferInstance
  refine @IsReduced.of_openCover _ Y.affineOpenCover.openCover (fun j => ?_)

  have h₁ : Smooth (g ≫ T.isoSpec.hom) := inferInstance
  have h₂ : Smooth (Y.affineOpenCover.f j ≫ g ≫ T.isoSpec.hom) :=
    MorphismProperty.comp_mem _ _ _ (hι j) h₁
  have hs : Smooth (Spec.map (Spec.preimage (Y.affineOpenCover.f j ≫ g ≫ T.isoSpec.hom))) := by
    rw [Spec.map_preimage]; exact h₂
  letI := (Spec.preimage (Y.affineOpenCover.f j ≫ g ≫ T.isoSpec.hom)).hom.toAlgebra
  haveI : Algebra.Smooth Γ(T, ⊤) (Y.affineOpenCover.X j) := HasRingHomProperty.Spec_iff.mp hs
  have : _root_.IsReduced (Y.affineOpenCover.X j) :=
    isReduced_algebra_of_smooth_of_isReduced Γ(T, ⊤) (Y.affineOpenCover.X j)
  show IsReduced (Spec (Y.affineOpenCover.X j))
  infer_instance

/-- The source of a smooth morphism over a reduced base is reduced. -/
theorem GlobalTheory.isReduced_of_smooth_of_isReduced {X S : Scheme.{0}}
    (f : X ⟶ S) [Smooth f] [IsReduced S] : IsReduced X := by
  refine @IsReduced.of_openCover _ (S.affineCover.pullback₁ f) ?_
  intro i
  let u := S.affineCover.f i
  have hsm : Smooth (pullback.snd f u) :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback f u) ‹Smooth f›
  have hr : IsReduced (S.affineCover.X i) := isReduced_of_isOpenImmersion u
  exact @isReduced_of_smooth_of_isAffine_of_isReduced _ _ (pullback.snd f u) hsm inferInstance hr
