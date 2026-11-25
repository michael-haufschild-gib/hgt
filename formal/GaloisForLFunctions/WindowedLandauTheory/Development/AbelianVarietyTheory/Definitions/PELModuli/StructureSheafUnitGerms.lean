import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.PELModuli.PELLineBundlePullback

/-! Pullback and restriction of germs of unit sections and transition functions. -/

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G.Semi

variable {X Y Z : Scheme.{0}}

open Classical in
/-- Pull back a unit and take its germ at a point over the open. -/
def gm (f : Y ⟶ X) (y : Y) (U : X.Opens) : Γ(X, U)ˣ →* (Y.presheaf.stalk y)ˣ :=
  if h : f y ∈ U then (Units.map (Y.presheaf.germ (f ⁻¹ᵁ U) y h).hom.toMonoidHom).comp (pullU f U) else 1

theorem gm_val (f : Y ⟶ X) (y : Y) (U : X.Opens) (h : f y ∈ U) (a : Γ(X, U)ˣ) :
    (gm f y U a).val = (Y.presheaf.germ (f ⁻¹ᵁ U) y h).hom ((f.app U).hom a.val) := by
  simp [gm, h, pullU]

theorem gm_res (f : Y ⟶ X) (y : Y) {U V : X.Opens} (hle : V ≤ U) (h : f y ∈ V) (a : Γ(X, U)ˣ) :
    gm f y V (res hle a) = gm f y U a := by
  apply Units.ext
  rw [gm_val f y V h, gm_val f y U (hle h)]
  simp only [res, Units.coe_map, MonoidHom.coe_coe]
  have e1 := Scheme.Hom.naturality f (homOfLE hle).op
  rw [← Y.presheaf.germ_res (homOfLE (Scheme.Hom.preimage_mono f hle)) y h]
  rw [CommRingCat.comp_apply]
  congr 1
  rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, e1]
  rfl

theorem gm_pull (f : Z ⟶ Y) (g : Y ⟶ X) (z : Z) (U : X.Opens) (h : g (f z) ∈ U) (a : Γ(X, U)ˣ) :
    gm f z (g ⁻¹ᵁ U) (pullU g U a) = gm (f ≫ g) z U a := by
  apply Units.ext
  rw [gm_val f z _ h, gm_val (f ≫ g) z U h]
  simp only [pullU, Units.coe_map, MonoidHom.coe_coe]
  rfl

/-- A unit section is determined by its germs. -/
theorem unit_ext {V : X.Opens} {a b : Γ(X, V)ˣ} (h : ∀ x ∈ V, gm (𝟙 X) x V a = gm (𝟙 X) x V b) : a = b := by
  apply Units.ext
  apply TopCat.Presheaf.section_ext X.sheaf V
  intro x hx
  have e := congrArg Units.val (h x hx)
  rw [gm_val _ _ _ hx, gm_val _ _ _ hx] at e
  exact e

/-- Every point belongs to a trivializing chart. -/
theorem exists_chart {L : LB X} (hL : L.IsLB) (x : X) : ∃ i, x ∈ L.U i := by
  have := hL.cover
  have hx : x ∈ (⨆ i, L.U i : X.Opens) := by rw [this]; trivial
  simpa [TopologicalSpace.Opens.mem_iSup] using hx

theorem gm_cocycle {L : LB X} (hL : L.IsLB) (f : Y ⟶ X) (y : Y) {i j k : L.ι} (hi : f y ∈ L.U i) (hj : f y ∈ L.U j)
    (hk : f y ∈ L.U k) : gm f y _ (L.g i j) * gm f y _ (L.g j k) = gm f y _ (L.g i k) := by
  have hijk : f y ∈ L.U i ⊓ L.U j ⊓ L.U k := ⟨⟨hi, hj⟩, hk⟩
  rw [← gm_res f y (inf_le_left : L.U i ⊓ L.U j ⊓ L.U k ≤ L.U i ⊓ L.U j) hijk,
    ← gm_res f y (le_inf (inf_le_left.trans inf_le_right) inf_le_right :
      L.U i ⊓ L.U j ⊓ L.U k ≤ L.U j ⊓ L.U k) hijk,
    ← gm_res f y (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
      L.U i ⊓ L.U j ⊓ L.U k ≤ L.U i ⊓ L.U k) hijk,
    ← map_mul, hL.cocycle]

theorem gm_self {L : LB X} (hL : L.IsLB) (f : Y ⟶ X) (y : Y) {i : L.ι} (hi : f y ∈ L.U i) :
    gm f y (L.U i ⊓ L.U i) (L.g i i) = 1 := by
  rw [← gm_res f y (le_inf le_rfl le_rfl : L.U i ≤ L.U i ⊓ L.U i) hi, hL.g_self i, map_one]

end ReciprocityTheory.ChartRestriction.G.Geo.Tor
