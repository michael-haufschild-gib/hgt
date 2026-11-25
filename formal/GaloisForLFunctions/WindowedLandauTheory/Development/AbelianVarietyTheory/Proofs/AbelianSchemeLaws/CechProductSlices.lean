import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.AbelianSchemeLaws.CechProductFirstSlice
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.AbelianSchemeLaws.ProperSmoothGlobalSections

/-! Two pointed slices detect a first Čech class on a product. -/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi
open GlobalTheory.LineBundleSections

namespace GlobalTheory.CechOne

variable {K : Type} [Field K] {X Y Z : Scheme.{0}}
  {f : X ⟶ Spec (CommRingCat.of K)} {g : Y ⟶ Spec (CommRingCat.of K)}
  {p : Z ⟶ X} {q : Z ⟶ Y}
  {I : Type} {V : I → Z.Opens} {φ : ∀ i j, Γ(Z, V i ⊓ V j)}

private theorem glue_splittings_of_slice (hq : ∀ U : Y.Opens, Function.Surjective (q.app U))
    {b : Y ⟶ Z} (hb : b ≫ q = 𝟙 Y) (hc : ⨆ i, V i = ⊤)
    (ρ : ∀ i, Γ(Y, b ⁻¹ᵁ V i))
    (hρ : ∀ i j, b.app (V i ⊓ V j) (φ i j) =
      resG Y (b.preimage_mono inf_le_left) (ρ i) - resG Y (b.preimage_mono inf_le_right) (ρ j))
    (hτ : ∀ U : Y.affineOpens, ∃ τ, Splits V φ (q ⁻¹ᵁ U.1) τ) :
    ∃ χ, Splits V φ ⊤ χ := by
  choose τ hτ using hτ
  have hN (U : Y.Opens) : U ≤ b ⁻¹ᵁ q ⁻¹ᵁ U := by
    rw [← Scheme.Hom.comp_preimage, hb]
    exact le_rfl
  obtain ⟨x, hx⟩ := pullback_difference_of_coboundary hc b ρ hρ
    (fun j : Y.affineOpens => q ⁻¹ᵁ j.1) τ hτ (fun j => j.1) (fun j => hN j.1)
  refine splittings_glue (fun j : Y.affineOpens => q ⁻¹ᵁ j.1) τ hτ
    (fun j => q.appLE j.1 _ le_rfl (x j)) ?_ ⊤ ?_
  · intro j k i M hj hk hi
    let U := j.1 ⊓ k.1
    have m₁ : q ⁻¹ᵁ U ≤ q ⁻¹ᵁ j.1 := q.preimage_mono inf_le_left
    have m₂ : q ⁻¹ᵁ U ≤ q ⁻¹ᵁ k.1 := q.preimage_mono inf_le_right
    obtain ⟨d, hd⟩ := exists_difference hc (hτ j) (hτ k) m₁ m₂
    obtain ⟨r, hr⟩ := hq U d
    have hr' : q.appLE U _ le_rfl r = d :=
      (ConcreteCategory.congr_hom (q.appLE_eq_app (U := U)) r).trans hr
    have e := hx j k _ m₁ m₂ d hd U inf_le_left inf_le_right (hN U)
    rw [← hr', appLE_comp_apply hb le_rfl (hN U) (by exact le_rfl), id_appLE_self] at e
    have hM : M ≤ q ⁻¹ᵁ U := le_inf hj hk
    have h := hd i M hM hi
    rw [← hr', e] at h
    simp only [map_sub, appLE_resG, resG_appLE] at h ⊢
    exact h.symm
  · rw [← q.preimage_iSup, iSup_affineOpens_eq_top]
    exact le_top

/-- When the first projection fibre has only scalar functions under base change, a
Čech one-cocycle that is a coboundary on both pointed slices is a coboundary on the product. -/
theorem exists_coboundary_of_pointed_product (H : IsPullback p q f g)
    [CompactSpace X] [X.IsSeparated] [Y.IsSeparated] [Smooth q] [IsProper q]
    [GeometricallyConnected q] (hg : Function.Surjective g.appTop)
    {y : Spec (CommRingCat.of K) ⟶ Y} (hy : y ≫ g = 𝟙 _)
    {a : X ⟶ Z} (ha : a ≫ p = 𝟙 X) (ha' : a ≫ q = f ≫ y)
    {b : Y ⟶ Z} (hb : b ≫ q = 𝟙 Y) (hc : ⨆ i, V i = ⊤) (hφ : IsCocycle V φ)
    (h₁ : ∃ ρ : ∀ i, Γ(X, a ⁻¹ᵁ V i), ∀ i j, a.app (V i ⊓ V j) (φ i j) =
      resG X (a.preimage_mono inf_le_left) (ρ i) - resG X (a.preimage_mono inf_le_right) (ρ j))
    (h₂ : ∃ ρ : ∀ i, Γ(Y, b ⁻¹ᵁ V i), ∀ i j, b.app (V i ⊓ V j) (φ i j) =
      resG Y (b.preimage_mono inf_le_left) (ρ i) - resG Y (b.preimage_mono inf_le_right) (ρ j)) :
    ∃ ρ : ∀ i, Γ(Z, V i), ∀ i j, φ i j =
      resG Z inf_le_left (ρ i) - resG Z inf_le_right (ρ j) := by
  obtain ⟨ρ₁, hρ₁⟩ := h₁
  obtain ⟨ρ₂, hρ₂⟩ := h₂
  obtain ⟨B₀, hB₀⟩ : ∃ B₀ : Y.affineOpens, ⊤ ≤ y ⁻¹ᵁ B₀.1 := by
    have hmem : y default ∈ ⨆ U : Y.affineOpens, U.1 := by
      rw [iSup_affineOpens_eq_top]
      exact Set.mem_univ _
    obtain ⟨B, hB⟩ := Opens.mem_iSup.mp hmem
    refine ⟨B, fun z _ => ?_⟩
    rw [Subsingleton.elim z default]
    exact hB
  have hq (U : Y.Opens) : Function.Surjective (q.app U) := by
    haveI : IsIso (q.app U) := GlobalTheory.GlobalFunctions.isIso_app_of_geometricallyConnected q U
    exact (ConcreteCategory.bijective_of_isIso (q.app U)).2
  obtain ⟨χ, hχ⟩ := glue_splittings_of_slice hq hb hc ρ₂ hρ₂
    (exists_splitting_on_strip H hg hy ha ha' B₀ hB₀ hc hφ ρ₁ hρ₁)
  refine ⟨fun i => resG Z inf_le_right (χ i), fun i j => ?_⟩
  have h := hχ i j (V i ⊓ V j) le_top inf_le_left inf_le_right
  simpa only [resG_self, resG_resG] using h

end GlobalTheory.CechOne
