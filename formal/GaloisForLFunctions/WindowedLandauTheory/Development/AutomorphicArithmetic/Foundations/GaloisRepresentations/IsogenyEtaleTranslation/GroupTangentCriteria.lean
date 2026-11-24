import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IsogenyEtaleTranslation.GroupTangentPowers
import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp

/-! Translation reduces the infinitesimal lifting criteria for group
morphisms to the tangent space at the identity in each geometric fibre. -/

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj

namespace GlobalTheory.GrpTangent

open TangentCrit

variable {S : Scheme.{0}} {G H : Over S} [GrpObj G] [GrpObj H]

@[reassoc]
lemma one_pullback_left_fst {S' : Scheme.{0}} (p : S' ⟶ S) (G : Over S) [GrpObj G] :
    η[(Over.pullback p).obj G].left ≫ pullback.fst G.hom p = p ≫ η[G].left := by
  let a := pullback.fst (𝟙 S) p
  let b := pullback.snd (𝟙 S) p
  have ha : a = b ≫ p := (Category.comp_id a).symm.trans pullback.condition
  have hb : inv b ≫ a = p := by rw [ha, IsIso.inv_hom_id_assoc]
  have hmap : ((Over.pullback p).map η[G]).left ≫ pullback.fst G.hom p = a ≫ η[G].left :=
    pullback.lift_fst _ _ _
  calc
    _ = inv b ≫ (((Over.pullback p).map η[G]).left ≫ pullback.fst G.hom p) := by
      rw [Functor.obj.η_def, Over.comp_left, Over.ε_pullback_left, Category.assoc]
      rfl
    _ = inv b ≫ (a ≫ η[G].left) := congrArg (inv b ≫ ·) hmap
    _ = (inv b ≫ a) ≫ η[G].left := (Category.assoc _ _ _).symm
    _ = _ := congrArg (· ≫ η[G].left) hb

section Field

variable {k : Type} [CommRing k] (p : Sp k ⟶ S)

def toFibre {X : Over S} (w : Over.mk (dualBase k ≫ p) ⟶ X) : epsR k ⟶ (Over.pullback p).obj X :=
  Over.homMk (pullback.lift w.left (dualBase k) (Over.w w)) (pullback.lift_snd _ _ _)

@[reassoc]
lemma toFibre_left_fst {X : Over S} (w : Over.mk (dualBase k ≫ p) ⟶ X) :
    (toFibre p w).left ≫ pullback.fst X.hom p = w.left := pullback.lift_fst _ _ _

lemma toFibre_injective {X : Over S} : Function.Injective (toFibre p (X := X)) := fun w w' h =>
  Over.OverMorphism.ext (by rw [← toFibre_left_fst, h, toFibre_left_fst])

lemma toFibre_surjective {X : Over S} : Function.Surjective (toFibre p (X := X)) := by
  intro w
  let a : Spec (CommRingCat.of (DualNumber k)) ⟶ pullback X.hom p := w.left
  have ha : a ≫ pullback.snd X.hom p = dualBase k := Over.w w
  have h : (a ≫ pullback.fst X.hom p) ≫ X.hom = dualBase k ≫ p := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, ha]
  let v : Over.mk (dualBase k ≫ p) ⟶ X := Over.homMk (a ≫ pullback.fst X.hom p) h
  exact ⟨v, Over.OverMorphism.ext (pullback.hom_ext (toFibre_left_fst p v)
    ((Over.w (toFibre p v)).trans ha.symm))⟩

lemma toFibre_comp {X Y : Over S} (w : Over.mk (dualBase k ≫ p) ⟶ X) (f : X ⟶ Y) :
    toFibre p (w ≫ f) = toFibre p w ≫ (Over.pullback p).map f := by
  refine Over.OverMorphism.ext (pullback.hom_ext ?_ ((Over.w _).trans (Over.w _).symm))
  let a : Spec (CommRingCat.of (DualNumber k)) ⟶ pullback X.hom p := (toFibre p w).left
  let b : pullback X.hom p ⟶ pullback Y.hom p := ((Over.pullback p).map f).left
  have ha : a ≫ pullback.fst X.hom p = w.left := toFibre_left_fst p w
  have hb : b ≫ pullback.fst Y.hom p = pullback.fst X.hom p ≫ f.left :=
    pullback.lift_fst _ _ _
  calc
    _ = w.left ≫ f.left := toFibre_left_fst p (w ≫ f)
    _ = (a ≫ pullback.fst X.hom p) ≫ f.left := congrArg (· ≫ f.left) ha.symm
    _ = a ≫ (pullback.fst X.hom p ≫ f.left) := Category.assoc _ _ _
    _ = a ≫ (b ≫ pullback.fst Y.hom p) := congrArg (a ≫ ·) hb.symm
    _ = _ := (Category.assoc _ _ _).symm

def epsZeroAt : Over.mk p ⟶ Over.mk (dualBase k ≫ p) :=
  Over.homMk (dualPt k) ((Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ p) (dualPt_dualBase k)).trans (Category.id_comp p)))

def epsBaseAt : Over.mk (dualBase k ≫ p) ⟶ Over.mk p := Over.homMk (dualBase k) rfl

@[reassoc]
lemma epsZeroAt_epsBaseAt : epsZeroAt p ≫ epsBaseAt p = 𝟙 _ :=
  Over.OverMorphism.ext (dualPt_dualBase k)

lemma isTangent_toFibre (w : Over.mk (dualBase k ≫ p) ⟶ G) :
    IsTangent (toFibre p w) ↔ epsZeroAt p ≫ w = 1 := by
  let a : Spec (CommRingCat.of (DualNumber k)) ⟶ pullback G.hom p := (toFibre p w).left
  let u : Sp k ⟶ pullback G.hom p := η[(Over.pullback p).obj G].left
  change dualPt k ≫ a = u ↔ _
  have ha : a ≫ pullback.fst G.hom p = w.left := toFibre_left_fst p w
  have hu : u ≫ pullback.fst G.hom p = (1 : Over.mk p ⟶ G).left :=
    one_pullback_left_fst p G
  have hfst : (dualPt k ≫ a) ≫ pullback.fst G.hom p = (epsZeroAt p ≫ w).left :=
    (Category.assoc _ _ _).trans (congrArg (dualPt k ≫ ·) ha)
  have hsnd : (dualPt k ≫ a) ≫ pullback.snd G.hom p = u ≫ pullback.snd G.hom p := by
    have hwa : a ≫ pullback.snd G.hom p = dualBase k := Over.w (toFibre p w)
    have hwu : u ≫ pullback.snd G.hom p = 𝟙 (Sp k) := Over.w η[(Over.pullback p).obj G]
    exact (Category.assoc _ _ _).trans
      ((congrArg (dualPt k ≫ ·) hwa).trans ((dualPt_dualBase k).trans hwu.symm))
  constructor
  · intro h
    exact Over.OverMorphism.ext (hfst.symm.trans
      ((congrArg (· ≫ pullback.fst G.hom p) h).trans hu))
  · intro h
    exact pullback.hom_ext (hfst.trans ((congrArg Over.Hom.left h).trans hu.symm)) hsnd

variable (f : G ⟶ H) [IsMonHom f]

lemma exists_lift_of_tangentMap_surjective
    (h : Function.Surjective (tangentMap ((Over.pullback p).map f))) (x : Over.mk p ⟶ G)
    (v : Over.mk (dualBase k ≫ p) ⟶ H) (hv : epsZeroAt p ≫ v = x ≫ f) :
    ∃ w : Over.mk (dualBase k ≫ p) ⟶ G, epsZeroAt p ≫ w = x ∧ w ≫ f = v := by
  obtain ⟨⟨w, hw⟩, e⟩ := h ⟨toFibre p (v * (epsBaseAt p ≫ x ≫ f)⁻¹), (isTangent_toFibre p _).mpr (by
    rw [comp_mul, GrpObj.comp_inv, epsZeroAt_epsBaseAt_assoc, hv, mul_inv_cancel])⟩
  obtain ⟨w, rfl⟩ := toFibre_surjective p w
  have e' : w ≫ f = v * (epsBaseAt p ≫ x ≫ f)⁻¹ :=
    toFibre_injective p ((toFibre_comp p w f).trans (congrArg Subtype.val e))
  refine ⟨w * (epsBaseAt p ≫ x), ?_, ?_⟩
  · rw [comp_mul, (isTangent_toFibre p w).mp hw, epsZeroAt_epsBaseAt_assoc, _root_.one_mul]
  · rw [mul_comp, e', Category.assoc, inv_mul_cancel_right]

lemma eq_of_tangentMap_injective
    (h : Function.Injective (tangentMap ((Over.pullback p).map f)))
    (w w' : Over.mk (dualBase k ≫ p) ⟶ G) (h₀ : epsZeroAt p ≫ w = epsZeroAt p ≫ w')
    (hf : w ≫ f = w' ≫ f) : w = w' := by
  let u := w * w'⁻¹
  have hu : IsTangent (toFibre p u) := (isTangent_toFibre p u).mpr (by
    dsimp only [u]
    rw [comp_mul, GrpObj.comp_inv, h₀, mul_inv_cancel])
  have hunit : IsTangent (toFibre (X := G) p 1) :=
    (isTangent_toFibre p 1).mpr (comp_one _)
  have he : u ≫ f = (1 : Over.mk (dualBase k ≫ p) ⟶ G) ≫ f := by
    dsimp only [u]
    rw [mul_comp, GrpObj.inv_comp, hf, mul_inv_cancel, one_comp]
  have e : toFibre p u ≫ (Over.pullback p).map f =
      toFibre p 1 ≫ (Over.pullback p).map f :=
    (toFibre_comp p u f).symm.trans ((congrArg (toFibre p) he).trans (toFibre_comp p 1 f))
  have h' := h (a₁ := ⟨_, hu⟩) (a₂ := ⟨_, hunit⟩) (Subtype.ext e)
  exact mul_inv_eq_one.mp (toFibre_injective p (congrArg Subtype.val h'))

end Field

theorem formallyUnramified_of_tangentMap_injective (f : G ⟶ H) [IsMonHom f]
    [LocallyOfFiniteType f.left]
    (h : ∀ (k : Type) [Field k] [IsAlgClosed k] (p : Sp k ⟶ S),
      Function.Injective (tangentMap ((Over.pullback p).map f))) :
    FormallyUnramified f.left := by
  refine formallyUnramified_of_tangent _ fun k _ _ w hw => ?_
  let p : Sp k ⟶ S := dualPt k ≫ w ≫ G.hom
  have hw' : w ≫ G.hom = dualBase k ≫ p := by
    have := congrArg (· ≫ H.hom) hw
    simpa [p] using this
  let w₀ : Over.mk (dualBase k ≫ p) ⟶ G := Over.homMk w hw'
  let w₁ := epsBaseAt p ≫ epsZeroAt p ≫ w₀
  have e : (w₀ ≫ f).left = (w₁ ≫ f).left := hw
  exact congrArg Over.Hom.left (eq_of_tangentMap_injective p f (h k p) w₀ w₁
    (by dsimp only [w₁]; rw [epsZeroAt_epsBaseAt_assoc]) (Over.OverMorphism.ext e))

theorem smooth_of_tangentMap_surjective (f : G ⟶ H) [IsMonHom f] [Smooth G.hom]
    [LocallyOfFiniteType H.hom]
    (h : ∀ (k : Type) [Field k] [IsAlgClosed k] (p : Sp k ⟶ S),
      Function.Surjective (tangentMap ((Over.pullback p).map f))) :
    Smooth f.left := by
  have : Smooth (f.left ≫ H.hom) := by rw [Over.w]; infer_instance
  refine smooth_of_tangent f.left H.hom fun k _ _ x v h₁ h₂ => ?_
  let p : Sp k ⟶ S := x ≫ f.left ≫ H.hom
  have hx : x ≫ G.hom = p := (congrArg (x ≫ ·) (Over.w f)).symm
  obtain ⟨w, hw₁, hw₂⟩ := exists_lift_of_tangentMap_surjective p f (h k p)
    (Over.homMk x hx) (Over.homMk v h₂) (Over.OverMorphism.ext h₁)
  exact ⟨w.left, congrArg Over.Hom.left hw₁, congrArg Over.Hom.left hw₂⟩

/-- Bijectivity on geometric tangent spaces at the unit implies
étaleness by translation and the relative tangent lifting criterion. -/
theorem etale_of_tangentMap_bijective (f : G ⟶ H) [IsMonHom f] [Smooth G.hom]
    [LocallyOfFiniteType H.hom]
    (h : ∀ (k : Type) [Field k] [IsAlgClosed k] (p : Sp k ⟶ S),
      Function.Bijective (tangentMap ((Over.pullback p).map f))) :
    Etale f.left := by
  have := smooth_of_tangentMap_surjective f fun k _ _ p => (h k p).2
  have := formallyUnramified_of_tangentMap_injective f fun k _ _ p => (h k p).1
  exact Etale.of_formallyUnramified_of_flat _

end GlobalTheory.GrpTangent
