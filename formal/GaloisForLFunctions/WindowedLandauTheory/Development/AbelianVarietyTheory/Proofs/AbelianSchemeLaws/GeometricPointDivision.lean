import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IsogenyEtaleTranslation.GroupMultiplicationEtale
import GaloisForLFunctions.HTGeometry.AlgebraicPointDescent

/-! Division of geometric points by an invertible integer on an abelian scheme. -/

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj

namespace GlobalTheory.GrpTangent

/-- A finite nonempty scheme over an algebraically closed field has a rational point. -/
theorem exists_section_of_finite_over_algClosed {k : Type} [Field k] [IsAlgClosed k]
    {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of k)) [IsFinite f] [Surjective f] :
    ∃ s : Spec (CommRingCat.of k) ⟶ X, s ≫ f = 𝟙 _ := by
  haveI : IsAffine X := isAffine_of_isAffineHom f
  obtain ⟨x, _⟩ := Surjective.surj (f := f) (IsLocalRing.closedPoint k)
  haveI : Nonempty (⊤ : X.Opens) := ⟨⟨x, trivial⟩⟩
  let e := Scheme.ΓSpecIso (CommRingCat.of k)
  let a : k →+* Γ(X, ⊤) := f.appTop.hom.comp e.inv.hom
  letI : Algebra k Γ(X, ⊤) := a.toAlgebra
  have ha : a.Finite := (IsFinite.finite_app f ⊤ (isAffineOpen_top _)).comp
    (RingHom.Finite.of_surjective _ (ConcreteCategory.bijective_of_isIso e.inv).2)
  haveI : Module.Finite k Γ(X, ⊤) := ha
  obtain ⟨r⟩ := GaloisForLFunctions.HTGeometry.nonempty_algHom_of_finiteType k k Γ(X, ⊤)
  let φ : Γ(X, ⊤) ⟶ Γ(Spec (CommRingCat.of k), ⊤) := CommRingCat.ofHom r.toRingHom ≫ e.inv
  have hφ : f.appTop ≫ φ = 𝟙 _ := by
    ext b
    obtain ⟨c, rfl⟩ := (ConcreteCategory.bijective_of_isIso e.inv).2 b
    change e.inv.hom (r ((algebraMap k Γ(X, ⊤)) c)) = e.inv.hom c
    rw [r.commutes, Algebra.algebraMap_self_apply]
  have hn : X.isoSpec.inv ≫ f =
      Spec.map f.appTop ≫ (Spec (CommRingCat.of k)).isoSpec.inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, Scheme.isoSpec_hom_naturality, Category.assoc,
      Iso.hom_inv_id, Category.comp_id]
  refine ⟨(Spec (CommRingCat.of k)).isoSpec.hom ≫ Spec.map φ ≫ X.isoSpec.inv, ?_⟩
  rw [Category.assoc, Category.assoc, hn, ← Category.assoc (Spec.map φ), ← Spec.map_comp,
    hφ, Spec.map_id, Category.id_comp, Iso.hom_inv_id]

/-- A finite surjection is surjective on geometric points over the base. -/
theorem exists_lift_geometric_point {S : Scheme.{0}} {A B : Over S} (f : A ⟶ B)
    [IsFinite f.left] [Surjective f.left]
    {k : Type} [Field k] [IsAlgClosed k] {x : Spec (CommRingCat.of k) ⟶ S}
    (y : Over.mk x ⟶ B) : ∃ z : Over.mk x ⟶ A, z ≫ f = y := by
  let g := pullback.snd f.left y.left
  have hfinite : IsFinite g := inferInstanceAs (IsFinite (pullback.snd f.left y.left))
  have hsurj : Surjective g := inferInstanceAs (Surjective (pullback.snd f.left y.left))
  obtain ⟨t, ht⟩ := @exists_section_of_finite_over_algClosed k _ _ _ g hfinite hsurj
  let u : (Over.mk x).left ⟶ pullback f.left y.left := t
  have hu : u ≫ pullback.snd f.left y.left = 𝟙 (Over.mk x).left := ht
  let z := u ≫ pullback.fst f.left y.left
  have hz : z ≫ f.left = y.left := by
    dsimp only [z]
    rw [Category.assoc, pullback.condition, ← Category.assoc, hu, Category.id_comp]
  have hw : z ≫ A.hom = (Over.mk x).hom := by
    rw [← Over.w f, ← Category.assoc, hz, Over.w y]
  exact ⟨Over.homMk z hw, Over.OverMorphism.ext hz⟩

/-- Multiplication by an invertible scalar is surjective on geometric points. -/
theorem exists_pow_eq_geometric_point {S : Scheme.{0}} (A : Over S) [GrpObj A] [IsCommMonObj A]
    [Smooth A.hom] [IsProper A.hom] [GeometricallyConnected A.hom]
    {k : Type} [Field k] [IsAlgClosed k] {x : Spec (CommRingCat.of k) ⟶ S}
    {n : ℕ} (hn : IsUnit (n : Γ(S, ⊤))) (y : Over.mk x ⟶ A) :
    ∃ z : Over.mk x ⟶ A, z ^ n = y := by
  obtain ⟨hfinite, _, hsurj⟩ := finiteEtaleSurjective_mulN A hn
  letI : IsFinite (mulN A n).left := hfinite
  letI : Surjective (mulN A n).left := hsurj
  obtain ⟨z, hz⟩ := exists_lift_geometric_point (mulN A n) y
  rw [comp_mulN] at hz
  exact ⟨z, hz⟩

end GlobalTheory.GrpTangent
