import Mathlib.RepresentationTheory.Rep.Iso
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughProjectives

/-!
# Extension classes of representation sequences

Enough projectives provides Ext groups for representation categories in their
natural universe. Exactness in degree zero identifies vanishing of a short
exact sequence's Ext class with existence of a retraction of its inclusion.
-/

noncomputable section
open CategoryTheory CategoryTheory.Abelian
namespace GaloisForLFunctions.RepresentationLifting
universe u v w

/-- Representation categories have small Ext groups because they have enough projectives. -/
instance representationHasExt {k G : Type u} [CommRing k] [Monoid G] :
    HasExt.{u} (Rep.{u} k G) := hasExt_of_enoughProjectives.{u, u, u + 1} (Rep.{u} k G)

/-- The extension class vanishes exactly when the inclusion has a retraction. -/
theorem extClass_zero_iff_retraction {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
    (S : ShortComplex C) (hS : S.ShortExact) :
    hS.extClass = 0 ↔ ∃ r : S.X₂ ⟶ S.X₁, S.f ≫ r = 𝟙 _ := by
  constructor
  · intro hz
    have hzero : hS.extClass.comp (Ext.mk₀ (𝟙 S.X₁)) (add_zero 1) = 0 := by
      rw [hz, Ext.zero_comp]
    obtain ⟨e, he⟩ := Ext.contravariant_sequence_exact₁ hS S.X₁ (Ext.mk₀ (𝟙 S.X₁)) (add_zero 1) hzero
    obtain ⟨r, rfl⟩ := (Ext.mk₀_bijective S.X₂ S.X₁).2 e
    refine ⟨r, ?_⟩
    apply (Ext.mk₀_bijective S.X₁ S.X₁).1
    simpa only [Ext.mk₀_comp_mk₀] using he
  · rintro ⟨r, hr⟩
    have h := hS.extClass_comp_assoc (Ext.mk₀ r) (h := add_zero 1)
    simpa only [Ext.mk₀_comp_mk₀, hr, Ext.comp_mk₀_id] using h

end GaloisForLFunctions.RepresentationLifting

#print axioms GaloisForLFunctions.RepresentationLifting.representationHasExt
#print axioms GaloisForLFunctions.RepresentationLifting.extClass_zero_iff_retraction
