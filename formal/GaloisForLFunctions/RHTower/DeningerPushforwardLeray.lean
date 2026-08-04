import GaloisForLFunctions.RHTower.DeningerFlasqueAcyclic

/-!
# Direct images of flasque sheaves and the composition law

The direct image of a flasque sheaf is flasque, hence acyclic, so its derived direct image is the
underived one and its cohomology is concentrated in degree zero, where it is the sections over the
preimage.  Direct image along a composite is the composite of direct images, so for a flasque
coefficient the derived direct image obeys the composition law with no higher terms — which is what
makes the pro-Stein relative calculation compute the relevant coefficient after arithmetic direct
image.

* `deningerPushforward_isFlasque` : direct images preserve flasqueness.
* `deningerPushforward_ext_eq_zero` : the direct image of a flasque sheaf is acyclic.
* `deningerPushforward_sectionsEquiv` : degree zero is the sections over the preimage.
* `deningerPushforward_comp` : the composition law for direct images.
-/

namespace RHTower

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian TopologicalSpace Opposite TopCat

universe w u

variable {X Y Z : TopCat.{u}}

/-- **The direct image of a flasque sheaf is flasque.** -/
theorem deningerPushforward_isFlasque (f : X ⟶ Y) (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    (hF : TopCat.Sheaf.IsFlasque F) :
    TopCat.Sheaf.IsFlasque ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).obj F) := by
  haveI := hF
  infer_instance

variable [CategoryTheory.HasExt.{w} (TopCat.Sheaf AddCommGrpCat.{u} Y)]

/-- **The direct image of a flasque sheaf has no higher cohomology.** -/
theorem deningerPushforward_ext_eq_zero (f : X ⟶ Y) (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    (hF : TopCat.Sheaf.IsFlasque F) (V : Opens Y) (n : ℕ)
    (x : deningerSheafCohomology.{w} V
      ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).obj F) (n + 1)) : x = 0 :=
  deningerFlasque_ext_eq_zero n _ (deningerPushforward_isFlasque f F hF) V x

/-- **Degree zero of the direct image is the sections over the preimage**, so for a flasque
coefficient the derived direct image is the underived one. -/
noncomputable def deningerPushforward_sectionsEquiv (f : X ⟶ Y)
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) (V : Opens Y) :
    deningerSheafCohomology.{w} V ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).obj F) 0 ≃
      ToType (F.1.obj (op ((Opens.map f).obj V))) :=
  deningerSheafCohomologyZeroEquiv V ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).obj F)

/-- **The composition law for direct images.** -/
def deningerPushforward_comp (f : X ⟶ Y) (g : Y ⟶ Z) (F : TopCat.Sheaf AddCommGrpCat.{u} X) :
    ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} (f ≫ g)).obj F).1 ≅
      ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} g).obj
        ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).obj F)).1 :=
  TopCat.Presheaf.Pushforward.comp f g F.1

end RHTower

namespace RHTower

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian TopologicalSpace Opposite TopCat

universe w u

variable {X Y Z : TopCat.{u}}

/-- **The composition law for direct images, at the level of sheaves.** -/
def deningerPushforwardSheaf_comp (f : X ⟶ Y) (g : Y ⟶ Z)
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) :
    (TopCat.Sheaf.pushforward AddCommGrpCat.{u} (f ≫ g)).obj F ≅
      (TopCat.Sheaf.pushforward AddCommGrpCat.{u} g).obj
        ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).obj F) where
  hom := ⟨(TopCat.Presheaf.Pushforward.comp f g F.1).hom⟩
  inv := ⟨(TopCat.Presheaf.Pushforward.comp f g F.1).inv⟩
  hom_inv_id := by
    refine CategoryTheory.Sheaf.hom_ext ?_
    exact (TopCat.Presheaf.Pushforward.comp f g F.1).hom_inv_id
  inv_hom_id := by
    refine CategoryTheory.Sheaf.hom_ext ?_
    exact (TopCat.Presheaf.Pushforward.comp f g F.1).inv_hom_id

variable [CategoryTheory.HasExt.{w} (TopCat.Sheaf AddCommGrpCat.{u} Z)]

/-- **`(2)`: the derived direct image along a composite has no higher terms on a flasque
coefficient.** -/
theorem deningerCompositePushforward_ext_eq_zero (f : X ⟶ Y) (g : Y ⟶ Z)
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) (hF : TopCat.Sheaf.IsFlasque F) (W : Opens Z) (n : ℕ)
    (x : deningerSheafCohomology.{w} W
      ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} (f ≫ g)).obj F) (n + 1)) : x = 0 :=
  deningerFlasque_ext_eq_zero n _ (deningerPushforward_isFlasque (f ≫ g) F hF) W x

/-- **`(2)`: on a flasque coefficient the derived direct image along a composite is the sections
over the total preimage**, which is the composition law with no higher terms. -/
noncomputable def deningerCompositePushforward_sectionsEquiv (f : X ⟶ Y) (g : Y ⟶ Z)
    (F : TopCat.Sheaf AddCommGrpCat.{u} X) (W : Opens Z) :
    deningerSheafCohomology.{w} W
        ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} (f ≫ g)).obj F) 0 ≃
      ToType (F.1.obj (op ((Opens.map f).obj ((Opens.map g).obj W)))) :=
  deningerSheafCohomologyZeroEquiv W
    ((TopCat.Sheaf.pushforward AddCommGrpCat.{u} (f ≫ g)).obj F)

end RHTower
