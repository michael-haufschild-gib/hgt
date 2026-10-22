import Mathlib.CategoryTheory.Triangulated.Pretriangulated
import Mathlib.CategoryTheory.Monoidal.Category
import Mathlib.CategoryTheory.Limits.Shapes.Terminal
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence

/-!
# Consequences of a homotopy-group isomorphism

A rank collapse in every degree propagates through the standard homotopical formalism.  The four
steps are each true in the generality that carries them, and are proved here in that generality.

* Detection.  In the derived category of an abelian category a morphism is an isomorphism as soon
  as it is an isomorphism on every homology object.  This is the Whitehead principle: homology is a
  jointly conservative family, and a homotopy-group isomorphism between two objects assembled from
  the same homotopy data is an equivalence.
* Transport.  Any functor carries an isomorphism to an isomorphism, so a base change along any
  morphism of coefficient objects carries the equivalence to an equivalence.
* Vanishing of the fibre.  In a pretriangulated category the third vertex of a distinguished
  triangle vanishes exactly when the first morphism is an isomorphism, so the cone and the fibre of
  an equivalence are zero.
* The free algebra on the zero object.  A left adjoint sends an initial object to an initial
  object.  When the unit of the target is itself initial the free algebra on the initial object is
  the unit, and tensoring over the unit is the identity.

* `RHTower.deningerIsIso_of_homologyIso` : the Whitehead principle in the derived category.
* `RHTower.deningerBaseChange_isIso` : transport along an arbitrary functor.
* `RHTower.deningerCone_isZero`, `RHTower.deningerExists_cone_isZero` : the cone of an equivalence.
* `RHTower.deningerFreeOnInitial`, `RHTower.deningerFreeOnInitialIsoUnit` : the free algebra on an
  initial object.
* `RHTower.deningerUnitTensorIso` : tensoring an equivalence over the unit.
-/

namespace RHTower

open CategoryTheory Limits Pretriangulated MonoidalCategory

section Whitehead

variable {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]

/-- **The Whitehead principle.**  A morphism of the derived category that induces an isomorphism on
every homology object is an isomorphism.  Homology plays the role of the homotopy groups, and the
statement is that this family of functors is jointly conservative. -/
theorem deningerIsIso_of_homologyIso {K L : DerivedCategory C} (f : K ⟶ L)
    (h : ∀ n : ℤ, IsIso ((DerivedCategory.homologyFunctor C n).map f)) : IsIso f :=
  (DerivedCategory.isIso_iff C f).mpr h

/-- Conversely an isomorphism induces isomorphisms on all homology, so the homotopy-group
condition is not merely sufficient but characteristic. -/
theorem deningerHomologyIso_of_isIso {K L : DerivedCategory C} (f : K ⟶ L) [IsIso f] (n : ℤ) :
    IsIso ((DerivedCategory.homologyFunctor C n).map f) :=
  (DerivedCategory.homologyFunctor C n).map_isIso f

/-- The two conditions agree. -/
theorem deningerIsIso_iff_homologyIso {K L : DerivedCategory C} (f : K ⟶ L) :
    IsIso f ↔ ∀ n : ℤ, IsIso ((DerivedCategory.homologyFunctor C n).map f) :=
  DerivedCategory.isIso_iff C f

/-- The equivalence produced by a degreewise isomorphism. -/
noncomputable def deningerHomologyIsoEquiv {K L : DerivedCategory C} (f : K ⟶ L)
    (h : ∀ n : ℤ, IsIso ((DerivedCategory.homologyFunctor C n).map f)) : K ≅ L :=
  haveI : IsIso f := deningerIsIso_of_homologyIso f h
  asIso f

end Whitehead

section Transport

variable {C : Type*} [Category C] {D : Type*} [Category D]

/-- **Base change preserves equivalences.**  Every functor carries an isomorphism to an
isomorphism, so an equivalence of coefficient objects stays an equivalence after any base change. -/
theorem deningerBaseChange_isIso (Φ : C ⥤ D) {X Y : C} (f : X ⟶ Y) [IsIso f] :
    IsIso (Φ.map f) :=
  Φ.map_isIso f

/-- Base change of the equivalence itself. -/
def deningerBaseChangeIso (Φ : C ⥤ D) {X Y : C} (e : X ≅ Y) : Φ.obj X ≅ Φ.obj Y :=
  Φ.mapIso e

end Transport

section Fibre

variable {C : Type*} [Category C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- **The cone of an equivalence vanishes.**  In a distinguished triangle the third vertex is a
zero object exactly when the first morphism is an isomorphism. -/
theorem deningerCone_isZero {X Y Z : C} (f : X ⟶ Y) [IsIso f] {g : Y ⟶ Z}
    {h : Z ⟶ (shiftFunctor C 1).obj X} (hT : Triangle.mk f g h ∈ distTriang C) : IsZero Z :=
  (Triangle.isZero₃_iff_isIso₁ _ hT).mpr (inferInstanceAs (IsIso f))

/-- Every equivalence has a vanishing cone, and hence a vanishing fibre. -/
theorem deningerExists_cone_isZero {X Y : C} (f : X ⟶ Y) [IsIso f] :
    ∃ (Z : C) (g : Y ⟶ Z) (h : Z ⟶ (shiftFunctor C 1).obj X),
      Triangle.mk f g h ∈ distTriang C ∧ IsZero Z := by
  obtain ⟨Z, g, h, hT⟩ := distinguished_cocone_triangle f
  exact ⟨Z, g, h, hT, deningerCone_isZero f hT⟩

/-- The converse: a vanishing third vertex forces the first morphism to be an isomorphism, so the
vanishing of the fibre is equivalent to the equivalence itself. -/
theorem deningerIsIso_of_cone_isZero {X Y Z : C} {f : X ⟶ Y} {g : Y ⟶ Z}
    {h : Z ⟶ (shiftFunctor C 1).obj X} (hT : Triangle.mk f g h ∈ distTriang C) (hZ : IsZero Z) :
    IsIso f :=
  (Triangle.isZero₃_iff_isIso₁ _ hT).mp hZ

end Fibre

section FreeAlgebra

variable {C : Type*} [Category C] {D : Type*} [Category D] {Free : C ⥤ D} {U : D ⥤ C}

/-- **The free algebra on an initial object is initial.**  A left adjoint preserves initial
objects: morphisms out of the free object on `X` are morphisms out of `X` into the underlying
object, and there is exactly one of those. -/
noncomputable def deningerFreeOnInitial (adj : Free ⊣ U) {X : C} (hX : IsInitial X) :
    IsInitial (Free.obj X) :=
  IsInitial.ofUniqueHom (fun Y => (adj.homEquiv X Y).symm (hX.to (U.obj Y)))
    (fun Y m => by
      have hm : adj.homEquiv X Y m = hX.to (U.obj Y) := hX.hom_ext _ _
      rw [← hm, Equiv.symm_apply_apply])

/-- **The free unital algebra on the zero object is the unit.**  Both are initial, and initial
objects are uniquely isomorphic. -/
noncomputable def deningerFreeOnInitialIsoUnit (adj : Free ⊣ U) {X : C} (hX : IsInitial X)
    {I : D} (hI : IsInitial I) : Free.obj X ≅ I :=
  (deningerFreeOnInitial adj hX).uniqueUpToIso hI

end FreeAlgebra

section UnitTensor

variable {D : Type*} [Category D] [MonoidalCategory D]

/-- **Tensoring over the unit does nothing.**  An equivalence tensored with the unit is again an
equivalence onto the target, so the derived quotient by the free algebra on the zero object
recovers the target unchanged. -/
def deningerUnitTensorIso {X Y : D} (e : X ≅ Y) : X ⊗ 𝟙_ D ≅ Y :=
  (ρ_ X) ≪≫ e

@[simp] theorem deningerUnitTensorIso_hom {X Y : D} (e : X ≅ Y) :
    (deningerUnitTensorIso e).hom = (ρ_ X).hom ≫ e.hom := rfl

/-- The same statement for an isomorphism given as a morphism. -/
theorem deningerUnitTensor_isIso {X Y : D} (f : X ⟶ Y) [IsIso f] : IsIso ((ρ_ X).hom ≫ f) :=
  IsIso.comp_isIso' inferInstance inferInstance

end UnitTensor

end RHTower
