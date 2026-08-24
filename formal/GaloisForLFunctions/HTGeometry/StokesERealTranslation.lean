import GaloisForLFunctions.HTGeometry.StokesBorderedEReal
import Mathlib.Topology.Maps.Proper.Basic

/-!
# Translation of the compactified enhanced variable

Finite real translations extend to proper homeomorphisms of `EReal` fixing both infinities. Their
products with the identity on `X` form the additive translation action on the compactified enhanced
space, preserve its projection to `X`, and restrict to ordinary translation on the bordered
interior.
-/

namespace GaloisForLFunctions.IrregularStokes.Bordered

open CategoryTheory TopCat Topology
open CompactIndSheaf

/-- Addition by a finite real number as a homeomorphism of the extended real line. -/
noncomputable def erealTranslationHomeomorph (c : ℝ) : EReal ≃ₜ EReal where
  toFun t := t + c
  invFun t := t + (-c : ℝ)
  left_inv := fun t => by
    simpa [sub_eq_add_neg] using EReal.add_sub_cancel_right (a := t) (b := c)
  right_inv := fun t => by
    simpa [sub_eq_add_neg] using EReal.sub_add_cancel (a := t) (b := c)
  continuous_toFun := continuous_iff_continuousAt.mpr fun t => by
    convert (EReal.continuousAt_add (.inr (EReal.coe_ne_bot c))
      (.inr (EReal.coe_ne_top c))).comp
        (continuousAt_id.prodMk continuousAt_const) using 1
    all_goals rfl
  continuous_invFun := continuous_iff_continuousAt.mpr fun t => by
    convert (EReal.continuousAt_add (.inr (EReal.coe_ne_bot (-c)))
      (.inr (EReal.coe_ne_top (-c)))).comp
        (continuousAt_id.prodMk continuousAt_const) using 1
    all_goals rfl

@[simp]
theorem erealTranslationHomeomorph_apply (c : ℝ) (t : EReal) :
    erealTranslationHomeomorph c t = t + c := by
  rfl

@[simp]
theorem erealTranslationHomeomorph_symm_apply (c : ℝ) (t : EReal) :
    (erealTranslationHomeomorph c).symm t = t + (-c : ℝ) := by
  rfl

@[simp]
theorem erealTranslationHomeomorph_bot (c : ℝ) :
    erealTranslationHomeomorph c ⊥ = ⊥ := by
  simp

@[simp]
theorem erealTranslationHomeomorph_top (c : ℝ) :
    erealTranslationHomeomorph c ⊤ = ⊤ := by
  simp

@[simp]
theorem erealTranslationHomeomorph_coe (c t : ℝ) :
    erealTranslationHomeomorph c (t : EReal) = (t + c : ℝ) := by
  simp [← EReal.coe_add]

@[simp]
theorem erealTranslationHomeomorph_zero :
    erealTranslationHomeomorph 0 = Homeomorph.refl EReal := by
  ext t
  induction t <;> simp [erealTranslationHomeomorph]

/-- Extended-real translations satisfy the additive composition law. -/
theorem erealTranslationHomeomorph_trans (c d : ℝ) :
    (erealTranslationHomeomorph c).trans (erealTranslationHomeomorph d) =
      erealTranslationHomeomorph (c + d) := by
  ext t
  induction t <;> simp [erealTranslationHomeomorph, add_assoc]

/-- Enhanced translation over `X` as a product homeomorphism. -/
noncomputable def enhancedTranslationHomeomorph (X : TopCat.{0}) (c : ℝ) :
    (X × EReal) ≃ₜ (X × EReal) :=
  (Homeomorph.refl X).prodCongr (erealTranslationHomeomorph c)

/-- Enhanced translation as a morphism of compactified enhanced spaces. -/
noncomputable def enhancedTranslation (X : TopCat.{0}) (c : ℝ) :
    EnhancedCompactification X ⟶ EnhancedCompactification X :=
  TopCat.ofHom ⟨fun p => enhancedTranslationHomeomorph X c p,
    (enhancedTranslationHomeomorph X c).continuous⟩

@[simp]
theorem enhancedTranslation_zero (X : TopCat.{0}) :
    enhancedTranslation X 0 = 𝟙 _ := by
  ext p
  · rfl
  · change p.2 + (0 : ℝ) = p.2
    induction p.2 <;> simp

/-- Compactified enhanced translations form an additive action. -/
theorem enhancedTranslation_comp (X : TopCat.{0}) (c d : ℝ) :
    enhancedTranslation X c ≫ enhancedTranslation X d = enhancedTranslation X (c + d) := by
  ext p
  · rfl
  · change (p.2 + (c : ℝ)) + (d : ℝ) = p.2 + ((c + d) : ℝ)
    induction p.2 <;> simp [← EReal.coe_add, add_assoc]

/-- Ordinary translation on the finite enhanced interior. -/
noncomputable def enhancedInteriorTranslation (X : TopCat.{0}) (c : ℝ) :
    EnhancedInterior X ⟶ EnhancedInterior X :=
  TopCat.ofHom ⟨fun p => (p.1, p.2 + c),
    continuous_fst.prodMk (continuous_snd.add continuous_const)⟩

/-- Finite-real inclusion intertwines interior and compactified translations. -/
theorem enhancedFiniteInclusion_translation (X : TopCat.{0}) (c : ℝ) :
    enhancedInteriorTranslation X c ≫ enhancedFiniteInclusion X =
      enhancedFiniteInclusion X ≫ enhancedTranslation X c := by
  ext p
  · rfl
  · change ((p.2 + c : ℝ) : EReal) = (p.2 : EReal) + (c : ℝ)
    exact EReal.coe_add _ _

/-- Every compactified enhanced translation is proper. -/
theorem enhancedTranslation_isProper (X : TopCat.{0}) (c : ℝ) :
    IsProperMap (enhancedTranslation X c) := by
  change IsProperMap (fun p => enhancedTranslationHomeomorph X c p)
  exact (enhancedTranslationHomeomorph X c).isProperMap

/-- Translation of the enhanced variable leaves projection to the base unchanged. -/
theorem enhancedTranslation_comp_projection (X : TopCat.{0}) (c : ℝ) :
    enhancedTranslation X c ≫ enhancedProjection X = enhancedProjection X := by
  ext p
  rfl

end GaloisForLFunctions.IrregularStokes.Bordered
