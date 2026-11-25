import Mathlib.AlgebraicGeometry.Geometrically.Integral
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! Global functions on proper geometrically integral schemes over fields. -/

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace GlobalTheory.ProperFunctions

private theorem isIso_of_isPushout_of_faithfullyFlat {R A K P : CommRingCat.{u}} {φ : R ⟶ A} {ψ : R ⟶ K}
    {inl : A ⟶ P} {inr : K ⟶ P} (H : IsPushout φ ψ inl inr) (hψ : ψ.hom.FaithfullyFlat)
    [IsIso inr] : IsIso φ := by
  have hb : Function.Bijective inr.hom := ConcreteCategory.bijective_of_isIso inr
  algebraize [φ.hom, ψ.hom, inl.hom, inr.hom, (φ ≫ inl).hom]
  have : IsScalarTower R A P := .of_algebraMap_eq' rfl
  have : IsScalarTower R K P := .of_algebraMap_eq' congr($(H.w).hom)
  have : Algebra.IsPushout R A K P := CommRingCat.isPushout_iff_isPushout.mp H
  have := RingHom.FaithfullyFlat.codescendsAlong_bijective (R := R) (S := A) (R' := K) (S' := P)
    hψ hb
  exact (ConcreteCategory.isIso_iff_bijective φ).mpr this

theorem appLE_top_top {X Y : Scheme.{u}} (p : X ⟶ Y)
    (h : (⊤ : X.Opens) ≤ p ⁻¹ᵁ ⊤) : p.appLE ⊤ ⊤ h = p.appTop :=
  (Scheme.Hom.app_eq_appLE p (U := ⊤)).symm

section BaseChange

variable {X Y S T : Scheme.{u}} {f : T ⟶ S} {g : Y ⟶ X} {p : X ⟶ S} {q : Y ⟶ T}

/-- Flat base change gives the pushout square on global functions over affine bases. -/
theorem isPushout_appTop (H : IsPullback g q p f) [IsAffine S] [IsAffine T] [Flat f]
    [QuasiCompact p] [QuasiSeparated p] :
    IsPushout p.appTop f.appTop g.appTop q.appTop := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  have : QuasiSeparatedSpace X := (quasiSeparated_iff_quasiSeparatedSpace p).mp inferInstance
  have := isIso_pushoutSection_of_isQuasiSeparated_of_flat_right H (US := ⊤) (UT := ⊤) (UX := ⊤)
    (UY := ⊤) (le_top) (le_top) (by simp)
    (isAffineOpen_top S) (isAffineOpen_top T)
    (by simpa using isCompact_univ) (by simpa using isQuasiSeparated_univ)
  simpa only [appLE_top_top] using (isIso_pushoutSection_iff ..).mp this

/-- The global-section isomorphism descends along faithfully flat affine base change. -/
theorem isIso_appTop_of_isPullback_of_surjective (H : IsPullback g q p f)
    [IsAffine S] [IsAffine T] [Flat f] [Surjective f] [QuasiCompact p] [QuasiSeparated p]
    [IsIso q.appTop] : IsIso p.appTop :=
  isIso_of_isPushout_of_faithfullyFlat (isPushout_appTop H)
    ((Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine f).mp ⟨inferInstance, inferInstance⟩)

end BaseChange

section Field

variable {X : Scheme.{u}}

private theorem isIso_appTop_of_isAlgClosed {k : Type u} [Field k] [IsAlgClosed k]
    (p : X ⟶ Spec (.of k)) [IsIntegral X] [UniversallyClosed p] : IsIso p.appTop := by
  let F := (Scheme.ΓSpecIso (.of k)).inv ≫ p.appTop
  have hF : F.hom.IsIntegral := by
    apply RingHom.isIntegral_respectsIso.2 (e := (Scheme.ΓSpecIso _).symm.commRingCatIsoToRingEquiv)
    exact isIntegral_appTop_of_universallyClosed p
  have : IsIso F := by
    algebraize [F.hom]
    exact (ConcreteCategory.isIso_iff_bijective F).mpr
      (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := k) (K := Γ(X, ⊤)))
  exact IsIso.of_isIso_comp_left (Scheme.ΓSpecIso (.of k)).inv p.appTop

/-- A scalar after extension to the algebraic closure descends to the field. -/
theorem isIso_appTop_of_field {k : Type u} [Field k]
    (p : X ⟶ Spec (.of k)) [GeometricallyIntegral p] [IsProper p] : IsIso p.appTop := by
  let f : Spec (.of (AlgebraicClosure k)) ⟶ Spec (.of k) :=
    Spec.map (CommRingCat.ofHom (algebraMap k (AlgebraicClosure k)))
  have : IsIntegral (pullback p f) :=
    GeometricallyIntegral.geometrically_isIntegral _ _ _ (.of_hasPullback p f)
  have := isIso_appTop_of_isAlgClosed (pullback.snd p f)
  have : Surjective f := ⟨fun x ↦ ⟨default, Subsingleton.elim _ _⟩⟩
  exact isIso_appTop_of_isPullback_of_surjective (IsPullback.of_hasPullback p f)

end Field

end GlobalTheory.ProperFunctions
