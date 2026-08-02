import GaloisForLFunctions.HTGeometry.NerveHomotopy

/-!
# Maps out of a homologically constant simplicial set are split monomorphisms

A simplicial set whose identity acts on homology as a constant map has, in every degree, a homology
that is retracted off the homology of every simplicial set it maps into: the constant map back
supplies the retraction, because a constant map absorbs any composite in front of it.

This is what replaces a vanishing hypothesis in the Mayer--Vietoris argument at the bottom degree.
There the intersection of two pieces has nonzero homology in degree zero, and the correct input is
not that this homology vanishes but that it injects into the homology of a piece.  A conically
contractible piece supplies exactly that, in every degree, with no positivity restriction.
-/

namespace GaloisForLFunctions.HTGeometry

open CategoryTheory Simplicial

universe u

variable {C : Type*} [Category C] [Limits.HasCoproducts.{u} C] [Preadditive C]
  [CategoryWithHomology C]

/-- **The identity of a conically contractible nerve is homologically constant**, in every degree.
This is the contractibility statement before the positive-degree conclusion is drawn from it. -/
theorem homologyMap_const_eq_id_of_conical {P : Type u} [Preorder P] (p₀ : P) (F : P →o P)
    (hid : ∀ x, x ≤ F x) (hpt : ∀ x, p₀ ≤ F x) (R : C) (n : ℕ) :
    SSet.homologyMap (SSet.const (X := nerveFunctor.obj (Cat.of P))
      (Y := nerveFunctor.obj (Cat.of P)) (ComposableArrows.mk₀ p₀)) R n = 𝟙 _ := by
  have h₁ := (nerveHomotopyOfLE (OrderHom.id (α := P)) F hid).congr_homologyMap R n
  have h₂ := (nerveHomotopyOfLE (constOrderHom P p₀) F hpt).congr_homologyMap R n
  rw [show Monotone.functor (OrderHom.id (α := P)).monotone = CategoryTheory.Functor.id P from
      CategoryTheory.Functor.ext (fun _ => rfl) (fun _ _ _ => Subsingleton.elim _ _),
    show (CategoryTheory.Functor.id P).toCatHom = 𝟙 (Cat.of P) from rfl,
    nerveFunctor.map_id] at h₁
  rw [nerveFunctor_map_constOrderHom] at h₂
  rw [h₂, ← h₁, SSet.homologyMap_id]

/-- **A homologically constant simplicial set is a homology retract of anything it maps into.**  If
the constant map at a vertex acts as the identity on the homology of `Y`, then every map out of `Y`
is a split monomorphism on homology, with the constant map back as retraction. -/
theorem isSplitMono_homologyMap_of_homologyMap_const_id {Y Z : SSet.{u}} (f : Y ⟶ Z) (p : Y _⦋0⦌)
    (R : C) (n : ℕ)
    (h : SSet.homologyMap (SSet.const (X := Y) (Y := Y) p) R n = 𝟙 _) :
    IsSplitMono (SSet.homologyMap f R n) := by
  refine ⟨⟨SSet.homologyMap (SSet.const (X := Z) (Y := Y) p) R n, ?_⟩⟩
  rw [← SSet.homologyMap_comp, SSet.comp_const, h]

theorem mono_homologyMap_of_homologyMap_const_id {Y Z : SSet.{u}} (f : Y ⟶ Z) (p : Y _⦋0⦌)
    (R : C) (n : ℕ)
    (h : SSet.homologyMap (SSet.const (X := Y) (Y := Y) p) R n = 𝟙 _) :
    Mono (SSet.homologyMap f R n) :=
  have := isSplitMono_homologyMap_of_homologyMap_const_id f p R n h
  inferInstance

/-- **Being homologically constant does not depend on the vertex.**  If the constant map at one
vertex acts as the identity on homology, so does the constant map at any other: composing two
constant maps returns the second one. -/
theorem homologyMap_const_eq_id_of_vertex {Y : SSet.{u}} {v : Y _⦋0⦌} (R : C) (n : ℕ)
    (h : SSet.homologyMap (SSet.const (X := Y) (Y := Y) v) R n = 𝟙 _) (w : Y _⦋0⦌) :
    SSet.homologyMap (SSet.const (X := Y) (Y := Y) w) R n = 𝟙 _ := by
  have hcomp : SSet.homologyMap (SSet.const (X := Y) (Y := Y) w) R n
      ≫ SSet.homologyMap (SSet.const (X := Y) (Y := Y) v) R n
      = SSet.homologyMap (SSet.const (X := Y) (Y := Y) v) R n := by
    rw [← SSet.homologyMap_comp, SSet.comp_const]
  rwa [h, Category.comp_id] at hcomp

/-- Being homologically constant transports along an isomorphism of simplicial sets. -/
theorem homologyMap_const_eq_id_of_iso {Y Y' : SSet.{u}} (e : Y ≅ Y') (p' : Y' _⦋0⦌) (R : C) (n : ℕ)
    (h : SSet.homologyMap (SSet.const (X := Y') (Y := Y') p') R n = 𝟙 _) :
    SSet.homologyMap (SSet.const (X := Y) (Y := Y)
      ((ConcreteCategory.hom (e.inv.app (Opposite.op ⦋0⦌))) p')) R n = 𝟙 _ := by
  have hfac : SSet.const (X := Y) (Y := Y)
      ((ConcreteCategory.hom (e.inv.app (Opposite.op ⦋0⦌))) p')
      = e.hom ≫ SSet.const (X := Y') (Y := Y') p' ≫ e.inv := by
    rw [SSet.const_comp, SSet.comp_const]
  rw [hfac, SSet.homologyMap_comp, SSet.homologyMap_comp, h, Category.id_comp,
    ← SSet.homologyMap_comp, e.hom_inv_id, SSet.homologyMap_id]

end GaloisForLFunctions.HTGeometry
