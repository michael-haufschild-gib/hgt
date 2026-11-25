import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.PELModuli.StructureSheafUnitGerms

/-! Germs of sections commute with pullback and restriction. -/

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

variable {X Y Z : Scheme.{0}}

open Classical in
/-- Germ of a section after pullback to a point over its open. -/
def gs (f : Y ⟶ X) (y : Y) (U : X.Opens) (a : Γ(X, U)) : Y.presheaf.stalk y :=
  if h : f y ∈ U then (Y.presheaf.germ (f ⁻¹ᵁ U) y h).hom ((f.app U).hom a) else 0

theorem gs_eq (f : Y ⟶ X) (y : Y) (U : X.Opens) (h : f y ∈ U) (a : Γ(X, U)) :
    gs f y U a = (Y.presheaf.germ (f ⁻¹ᵁ U) y h).hom ((f.app U).hom a) := by
  unfold gs
  exact dif_pos h

theorem gs_unit (f : Y ⟶ X) (y : Y) (U : X.Opens) (h : f y ∈ U) (a : Γ(X, U)ˣ) : gs f y U a.val = (gm f y U a).val := by
  rw [gs_eq f y U h]
  unfold gm
  rw [dif_pos h]
  rfl

theorem gs_mul (f : Y ⟶ X) (y : Y) (U : X.Opens) (h : f y ∈ U) (a b : Γ(X, U)) :
    gs f y U (a * b) = gs f y U a * gs f y U b := by
  simp only [gs_eq f y U h, map_mul]


theorem gs_res (f : Y ⟶ X) (y : Y) {U V : X.Opens} (hle : V ≤ U) (h : f y ∈ V) (a : Γ(X, U)) :
    gs f y V ((X.presheaf.map (homOfLE hle).op).hom a) = gs f y U a := by
  rw [gs_eq f y V h, gs_eq f y U (hle h)]
  have e := f.naturality (homOfLE hle).op
  rw [← Y.presheaf.germ_res (homOfLE (f.preimage_mono hle)) y h, CommRingCat.comp_apply]
  congr 1
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, e]
  rfl

theorem gs_pull (f : Z ⟶ Y) (g : Y ⟶ X) (z : Z) (U : X.Opens) (h : g (f z) ∈ U) (a : Γ(X, U)) :
    gs f z (g ⁻¹ᵁ U) ((g.app U).hom a) = gs (f ≫ g) z U a := by
  have h' : (f ≫ g) z ∈ U := h
  rw [gs_eq f z (g ⁻¹ᵁ U) h, gs_eq (f ≫ g) z U h']
  simp only [Scheme.Hom.comp_app]
  rfl

theorem fn_ext {V : X.Opens} {a b : Γ(X, V)} (h : ∀ x ∈ V, gs (𝟙 X) x V a = gs (𝟙 X) x V b) : a = b := by
  apply TopCat.Presheaf.section_ext X.sheaf V a b
  intro x hx
  have e := h x hx
  rw [gs_eq (𝟙 X) x V hx, gs_eq (𝟙 X) x V hx] at e
  exact e

theorem gs_stalkMap (f : Y ⟶ X) (y : Y) (U : X.Opens) (hy : f y ∈ U) (a : Γ(X, U)) :
    (f.stalkMap y).hom (gs (𝟙 X) (f y) U a) = gs f y U a := by
  have e : gs (𝟙 X) (f y) U a = (X.presheaf.germ U (f y) hy).hom a :=
    gs_eq (𝟙 X) (f y) U hy a
  exact (congrArg (f.stalkMap y).hom e).trans
    ((f.germ_stalkMap_apply U y hy a).trans (gs_eq f y U hy a).symm)

theorem gs_appLE (f : Y ⟶ X) (U : X.Opens) (V : Y.Opens) (h : V ≤ f ⁻¹ᵁ U)
    (r : Z ⟶ Y) (z : Z) (hz : r z ∈ V) (a : Γ(X, U)) :
    gs r z V ((f.appLE U V h).hom a) = gs (r ≫ f) z U a :=
  (gs_res r z h hz _).trans (gs_pull r f z U (h hz) a)

end ReciprocityTheory.ChartRestriction.G.Geo.Tor
