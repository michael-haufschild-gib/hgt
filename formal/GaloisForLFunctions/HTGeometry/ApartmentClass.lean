import GaloisForLFunctions.HTGeometry.ApartmentTopHomology
import GaloisForLFunctions.HTGeometry.ApartmentOrderIso
import GaloisForLFunctions.HTGeometry.BuildingAutomorphismAction

/-!
# The apartment class of an observer frame

A frame of the space spans a Boolean sublattice of the subspaces, and the order complex of its
proper part is the Coxeter sphere of the frame.  Its top homology is one copy of the coefficients,
and the inclusion of the apartment into the building carries that copy into the Steinberg module.

The resulting map is the apartment class of the frame: the image of the fundamental class of the
sphere in the top homology of the building.
-/

namespace GaloisForLFunctions.HTGeometry

open CategoryTheory Limits Simplicial Opposite Module

universe v u

/-- A monotone map of posets induces a map of their order complexes. -/
noncomputable def orderHomNerveMap {α β : Type u} [Preorder α] [Preorder β] (f : α →o β) :
    nerveFunctor.obj (Cat.of α) ⟶ nerveFunctor.obj (Cat.of β) :=
  nerveFunctor.map f.toFunctor.toCatHom

section

variable {K V ι : Type u} [Field K] [AddCommGroup V] [Module K V] [Fintype ι]
variable {C : Type u} [Category.{v} C] [Abelian C] [HasCoproducts.{u} C]

/-- The order complex of the apartment of a frame, mapped into the building. -/
noncomputable def apartmentNerveMap (b : Basis ι K V) :
    nerveFunctor.obj (Cat.of (properPart (Set ι)))
      ⟶ nerveFunctor.obj (Cat.of (properPart (Submodule K V))) :=
  orderHomNerveMap (apartmentVertices b)

/-- **The fundamental class of the apartment**: its top homology is one copy of the
coefficients. -/
noncomputable def apartmentIso (R : C) (h3 : 3 ≤ Nat.card ι) :
    (nerveFunctor.obj (Cat.of (properPart (Set ι)))).homology R (Nat.card ι - 2) ≅ R :=
  Classical.choice (nonempty_homology_iso_apartment R ι h3)

theorem card_eq_finrank (b : Basis ι K V) : Nat.card ι = finrank K V := by
  rw [Nat.card_eq_fintype_card, Module.finrank_eq_card_basis b]

/-- The apartment class, in the degree the size of the frame gives. -/
noncomputable def apartmentClass' (b : Basis ι K V) (R : C) (h3 : 3 ≤ Nat.card ι) :
    R ⟶ (nerveFunctor.obj (Cat.of (properPart (Submodule K V)))).homology R (Nat.card ι - 2) :=
  (apartmentIso R h3).inv ≫ SSet.homologyMap (apartmentNerveMap b) R (Nat.card ι - 2)

/-- **The apartment class of an observer frame**: the fundamental class of the Coxeter sphere of the
frame, pushed into the Steinberg module along the inclusion of the apartment in the building. -/
noncomputable def apartmentClass [FiniteDimensional K V] (b : Basis ι K V) (R : C)
    (h3 : 3 ≤ Nat.card ι) :
    R ⟶ (nerveFunctor.obj (Cat.of (properPart (Submodule K V)))).homology R (finrank K V - 2) :=
  apartmentClass' b R h3 ≫ eqToHom (congrArg
    (fun n => (nerveFunctor.obj (Cat.of (properPart (Submodule K V)))).homology R n)
    (by rw [card_eq_finrank b]))

/-! ## The observer group permutes the apartment classes -/

omit [Fintype ι] in
/-- A frame transported by an observer symmetry spans the transported coordinate subspaces. -/
theorem coordSpan_map (b : Basis ι K V) (g : V ≃ₗ[K] V) (s : Set ι) :
    coordSpan (b.map g) s = Submodule.map (g : V →ₗ[K] V) (coordSpan b s) := by
  rw [coordSpan, coordSpan, Submodule.map_span, ← Set.image_comp]
  congr 1

omit [Fintype ι] in
/-- The apartment of a transported frame is the transport of the apartment. -/
theorem apartmentVertices_map (b : Basis ι K V) (g : V ≃ₗ[K] V) :
    apartmentVertices (b.map g)
      = (OrderHom.mk (properPartCongr (Submodule.orderIsoMapComap (g : V ≃ₗ[K] V)))
          (properPartCongr (Submodule.orderIsoMapComap (g : V ≃ₗ[K] V))).monotone).comp
        (apartmentVertices b) := by
  refine OrderHom.ext _ _ (funext fun s => Subtype.ext ?_)
  exact coordSpan_map b g (s : Set ι)

/-- A composite of monotone maps induces the composite map of order complexes. -/
theorem orderHomNerveMap_comp {α β γ : Type u} [Preorder α] [Preorder β] [Preorder γ]
    (f : α →o β) (f' : β →o γ) :
    orderHomNerveMap (f'.comp f) = orderHomNerveMap f ≫ orderHomNerveMap f' := by
  rw [orderHomNerveMap, orderHomNerveMap, orderHomNerveMap, ← nerveFunctor.map_comp]
  congr 1

omit [Fintype ι] in
/-- **The observer group carries apartment classes to apartment classes.**  Transporting a frame by
a linear automorphism transports its apartment class by the induced action on the homology of the
building. -/
theorem apartmentClass'_comp_homologyMap (b : Basis ι K V) (R : C) (h3 : 3 ≤ Nat.card ι)
    (g : V ≃ₗ[K] V) :
    apartmentClass' b R h3
        ≫ SSet.homologyMap
          (properPartNerveIso (Submodule.orderIsoMapComap (g : V ≃ₗ[K] V))).hom R (Nat.card ι - 2)
      = apartmentClass' (b.map g) R h3 := by
  rw [apartmentClass', apartmentClass', Category.assoc, ← SSet.homologyMap_comp]
  congr 2
  rw [apartmentNerveMap, apartmentNerveMap, apartmentVertices_map b g, orderHomNerveMap_comp]
  rfl

/-- Transporting a degree past a map induced on homology. -/
theorem eqToHom_comp_homologyMap {X Y : SSet.{u}} (f : X ⟶ Y) (R : C) {m n : ℕ} (h : m = n) :
    eqToHom (congrArg (fun k => X.homology R k) h) ≫ SSet.homologyMap f R n
      = SSet.homologyMap f R m ≫ eqToHom (congrArg (fun k => Y.homology R k) h) := by
  subst h
  simp

/-- The Steinberg representation acts by the map the order isomorphism induces. -/
theorem steinbergAction_hom [FiniteDimensional K V] (R : C) (g : V ≃ₗ[K] V) :
    (steinbergAction K V R g).hom
      = SSet.homologyMap (properPartNerveIso (Submodule.orderIsoMapComap (g : V ≃ₗ[K] V))).hom R
        (finrank K V - 2) := rfl

/-- **The observer group permutes the apartment classes.**  The class of a frame transported by a
linear automorphism is the transport of its class along the induced map of buildings. -/
theorem apartmentClass_comp_homologyMap [FiniteDimensional K V] (b : Basis ι K V) (R : C)
    (h3 : 3 ≤ Nat.card ι) (g : V ≃ₗ[K] V) :
    apartmentClass b R h3
        ≫ SSet.homologyMap (properPartNerveIso (Submodule.orderIsoMapComap (g : V ≃ₗ[K] V))).hom R
          (finrank K V - 2)
      = apartmentClass (b.map g) R h3 := by
  have hdeg : Nat.card ι - 2 = finrank K V - 2 := by rw [card_eq_finrank b]
  rw [apartmentClass, apartmentClass, Category.assoc, eqToHom_comp_homologyMap _ R hdeg,
    ← Category.assoc, apartmentClass'_comp_homologyMap b R h3 g]

/-- **The Steinberg representation permutes the apartment classes.**  Apartment classes are cycles
on which the projective observer group acts by permuting frames. -/
theorem apartmentClass_steinbergAction [FiniteDimensional K V] (b : Basis ι K V) (R : C)
    (h3 : 3 ≤ Nat.card ι) (g : V ≃ₗ[K] V) :
    apartmentClass b R h3 ≫ (steinbergAction K V R g).hom = apartmentClass (b.map g) R h3 :=
  apartmentClass_comp_homologyMap b R h3 g

end

end GaloisForLFunctions.HTGeometry
