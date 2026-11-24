import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IsogenyEtaleTranslation.GeometricEtaleDescent
import Mathlib.AlgebraicGeometry.Morphisms.Finite
import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
import Mathlib.CategoryTheory.Monoidal.Cartesian.Over

/-! A finite étale quotient of a smooth group scheme is determined
by its kernel on geometric points. -/

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj

namespace GlobalTheory.GrpTangent

variable {S : Scheme.{0}}

private theorem epi_of_flat_surjective {X Y : Over S} (f : X ⟶ Y) [Flat f.left] [Surjective f.left] :
    Epi f := by
  have hepi : Epi f.left := Flat.epi_of_flat_of_surjective f.left
  exact (Over.forget S).epi_of_epi_map hepi

private lemma whiskerRight_left_of_isStableUnderBaseChange (P : MorphismProperty Scheme.{0})
    [P.IsStableUnderBaseChange] {X Y : Over S} (f : X ⟶ Y) (Z : Over S) (hf : P f.left) :
    P (f ▷ Z).left := by
  have e1 : (f ▷ Z).left ≫ pullback.snd Y.hom Z.hom = pullback.snd X.hom Z.hom := by
    rw [Over.whiskerRight_left]
    exact (pullback.lift_snd _ _ _).trans (by simp)
  have e2 : (f ▷ Z).left ≫ pullback.fst Y.hom Z.hom = pullback.fst X.hom Z.hom ≫ f.left := by
    rw [Over.whiskerRight_left]
    exact (pullback.lift_fst _ _ _).trans (by simp)
  have houter : IsPullback ((f ▷ Z).left ≫ pullback.snd Y.hom Z.hom) (pullback.fst X.hom Z.hom)
      Z.hom (f.left ≫ Y.hom) := by
    rw [e1, Over.w f]
    exact (IsPullback.of_hasPullback X.hom Z.hom).flip
  exact MorphismProperty.of_isPullback
    (IsPullback.of_right houter e2 (IsPullback.of_hasPullback Y.hom Z.hom).flip).flip hf

private lemma whiskerLeft_left_of_isStableUnderBaseChange (P : MorphismProperty Scheme.{0})
    [P.IsStableUnderBaseChange] {X Y : Over S} (Z : Over S) (f : X ⟶ Y) (hf : P f.left) :
    P (Z ◁ f).left := by
  have e1 : (Z ◁ f).left ≫ pullback.fst Z.hom Y.hom = pullback.fst Z.hom X.hom := by
    rw [Over.whiskerLeft_left]
    exact (pullback.lift_fst _ _ _).trans (by simp)
  have e2 : (Z ◁ f).left ≫ pullback.snd Z.hom Y.hom = pullback.snd Z.hom X.hom ≫ f.left := by
    rw [Over.whiskerLeft_left]
    exact (pullback.lift_snd _ _ _).trans (by simp)
  have houter : IsPullback ((Z ◁ f).left ≫ pullback.fst Z.hom Y.hom) (pullback.snd Z.hom X.hom)
      Z.hom (f.left ≫ Y.hom) := by
    rw [e1, Over.w f]
    exact IsPullback.of_hasPullback Z.hom X.hom
  exact MorphismProperty.of_isPullback
    (IsPullback.of_right houter e2 (IsPullback.of_hasPullback Z.hom Y.hom)).flip hf


private theorem epi_tensorHom {X Y X' Y' : Over S} (f : X ⟶ Y) (g : X' ⟶ Y')
    [hf : Flat f.left] [hf' : Surjective f.left] [hg : Flat g.left] [hg' : Surjective g.left] :
    Epi (f ⊗ₘ g) := by
  haveI : Flat (f ▷ X').left := whiskerRight_left_of_isStableUnderBaseChange @Flat f X' hf
  haveI : Surjective (f ▷ X').left := whiskerRight_left_of_isStableUnderBaseChange @Surjective f X' hf'
  haveI : Flat (Y ◁ g).left := whiskerLeft_left_of_isStableUnderBaseChange @Flat Y g hg
  haveI : Surjective (Y ◁ g).left := whiskerLeft_left_of_isStableUnderBaseChange @Surjective Y g hg'
  haveI := epi_of_flat_surjective (f ▷ X')
  haveI := epi_of_flat_surjective (Y ◁ g)
  rw [MonoidalCategory.tensorHom_def]
  exact epi_comp _ _

private theorem exists_factor_of_geometricKernelLE [IsReduced S]
    {A B C : Over S} [GrpObj A] [GrpObj B] [GrpObj C]
    [Smooth A.hom] [IsSeparated C.hom]
    (q : A ⟶ B) (f : A ⟶ C) [IsMonHom q] [IsMonHom f]
    [IsFinite q.left] [Etale q.left] [Surjective q.left]
    (hk : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω]
      (t : Spec (CommRingCat.of Ω) ⟶ S) (a : Over.mk t ⟶ A), a ≫ q = 1 → a ≫ f = 1) :
    ∃ g : B ⟶ C, q ≫ g = f := by
  haveI : IsReduced A.left := isReduced_of_smooth_of_isReduced A.hom
  have hbase : f.left ≫ C.hom = q.left ≫ B.hom := (Over.w f).trans (Over.w q).symm
  obtain ⟨g, hg⟩ := exists_desc_of_etale_of_geometricPoints q.left B.hom C.hom f.left hbase
    (fun Ω _ _ x y hxy => by
      have hy : y ≫ A.hom = x ≫ A.hom := by
        rw [← Over.w q, ← Category.assoc, ← Category.assoc, hxy]
      let T := Over.mk (x ≫ A.hom)
      let a : T ⟶ A := Over.homMk x
      let b : T ⟶ A := Over.homMk y hy
      have e : a ≫ q = b ≫ q := Over.OverMorphism.ext hxy
      have hu : (a * b⁻¹) ≫ q = 1 := by
        rw [mul_comp, GrpObj.inv_comp, e, mul_inv_cancel]
      have hv := hk Ω (x ≫ A.hom) (a * b⁻¹) hu
      rw [mul_comp, GrpObj.inv_comp, mul_inv_eq_one] at hv
      exact congrArg Over.Hom.left hv)
  haveI : Epi q.left := Flat.epi_of_flat_of_surjective q.left
  refine ⟨Over.homMk g ?_, Over.OverMorphism.ext hg⟩
  rw [← cancel_epi q.left, ← Category.assoc, hg, hbase]

/-- Two finite étale surjections with the same geometric kernel have
isomorphic targets, compatibly with the quotient maps and group laws. -/
theorem exists_iso_of_geometricKernelEq [IsReduced S]
    {A B C : Over S} [GrpObj A] [GrpObj B] [GrpObj C] [Smooth A.hom]
    [IsSeparated B.hom] [IsSeparated C.hom]
    (q : A ⟶ B) (f : A ⟶ C) [IsMonHom q] [IsMonHom f]
    [IsFinite q.left] [Etale q.left] [Surjective q.left]
    [IsFinite f.left] [Etale f.left] [Surjective f.left]
    (hk : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω]
      (t : Spec (CommRingCat.of Ω) ⟶ S) (a : Over.mk t ⟶ A), a ≫ q = 1 ↔ a ≫ f = 1) :
    ∃ g : B ⟶ C, IsIso g ∧ IsMonHom g ∧ q ≫ g = f := by
  obtain ⟨g, hg⟩ := exists_factor_of_geometricKernelLE q f (fun Ω _ _ t a => (hk Ω t a).mp)
  obtain ⟨g', hg'⟩ := exists_factor_of_geometricKernelLE f q (fun Ω _ _ t a => (hk Ω t a).mpr)
  haveI : Epi q := epi_of_flat_surjective q
  haveI : Epi f := epi_of_flat_surjective f
  haveI : Epi (q ⊗ₘ q) := epi_tensorHom q q
  have h₁ : g ≫ g' = 𝟙 B := by
    rw [← cancel_epi q, ← Category.assoc, hg, hg', Category.comp_id]
  have h₂ : g' ≫ g = 𝟙 C := by
    rw [← cancel_epi f, ← Category.assoc, hg', hg, Category.comp_id]
  refine ⟨g, ⟨g', h₁, h₂⟩, ⟨?_, ?_⟩, hg⟩
  · rw [← IsMonHom.one_hom q, Category.assoc, hg, IsMonHom.one_hom f]
  · have e : (q ⊗ₘ q) ≫ (g ⊗ₘ g) = f ⊗ₘ f := by
      rw [tensorHom_comp_tensorHom, hg]
    rw [← cancel_epi (q ⊗ₘ q), ← Category.assoc, ← IsMonHom.mul_hom q,
      Category.assoc, hg, IsMonHom.mul_hom f, ← Category.assoc, e]

end GlobalTheory.GrpTangent
