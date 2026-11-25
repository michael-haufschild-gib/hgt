import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.PELModuli.AmpleChartGluing
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.PELModuli.StructureSheafSectionGerms

/-! Stalk families and their regularity along open immersions. -/

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.AmpleLocal

variable {X Y Z : Scheme.{0}}

def pb (h : Y ⟶ Z) : Fn Z →+* Fn Y :=
  RingHom.pi fun y => (h.stalkMap y).hom.comp (Pi.evalRingHom _ (h y))

theorem pb_apply (h : Y ⟶ Z) (F : Fn Z) (y : Y) : pb h F y = (h.stalkMap y).hom (F (h y)) := rfl

theorem pb_comp (h : Y ⟶ Z) (g : Z ⟶ X) (F : Fn X) : pb (h ≫ g) F = pb h (pb g F) := by
  funext y
  rw [pb_apply, Scheme.Hom.stalkMap_comp]
  rfl

theorem pb_unit (h : Y ⟶ Z) (F : Fn Z) (y : Y) : IsUnit (pb h F y) ↔ IsUnit (F (h y)) :=
  isUnit_map_iff (h.stalkMap y).hom _

theorem pb_inv (h : Y ⟶ Z) (F : Fn Z) : pb h (inv F) = inv (pb h F) := by
  funext y
  show (h.stalkMap y).hom (Ring.inverse (F (h y))) = Ring.inverse (pb h F y)
  by_cases hu : IsUnit (F (h y))
  · refine ((Ring.eq_mul_inverse_iff_mul_eq _ _ _ ((pb_unit h F y).2 hu)).2 ?_).trans (one_mul _)
    rw [pb_apply, ← map_mul, Ring.inverse_mul_cancel _ hu, map_one]
  · rw [Ring.inverse_non_unit _ hu, Ring.inverse_non_unit _ (mt (pb_unit h F y).1 hu), map_zero]

theorem gs_id (V : Z.Opens) (z : Z) (hz : z ∈ V) (a : Γ(Z, V)) : gs (𝟙 Z) z V a = (Z.presheaf.germ V z hz).hom a :=
  gs_eq (𝟙 Z) z V hz a

theorem mem_reg_iff {V : Z.Opens} {F : Fn Z} : F ∈ Reg V ↔ ∃ a : Γ(Z, V), ∀ z ∈ V, gs (𝟙 Z) z V a = F z :=
  exists_congr fun a => forall_congr' fun z => forall_congr' fun hz => by rw [gs_id V z hz]

theorem stalkMap_gs (h : Y ⟶ Z) (g : Z ⟶ X) (y : Y) (V : X.Opens) (hy : g (h y) ∈ V) (a : Γ(X, V)) :
    (h.stalkMap y).hom (gs g (h y) V a) = gs (h ≫ g) y V a := by
  rw [← gs_pull h g y V hy, ← gs_stalkMap h y (g ⁻¹ᵁ V) hy, gs_pull (𝟙 Z) g (h y) V hy, Category.id_comp]

theorem reg_gs (g : Z ⟶ X) (V : X.Opens) (a : Γ(X, V)) : (fun z => gs g z V a) ∈ Reg (g ⁻¹ᵁ V) :=
  ⟨(g.app V).hom a, fun z hz => (gs_eq g z V hz a).symm⟩

theorem reg_pull (h : Y ⟶ Z) {V : Z.Opens} {F : Fn Z} (hF : F ∈ Reg V) : pb h F ∈ Reg (h ⁻¹ᵁ V) := by
  obtain ⟨a, ha⟩ := mem_reg_iff.1 hF
  exact reg_congr (reg_gs h V a) fun y hy => (gs_stalkMap h y V hy a).symm.trans (congrArg _ (ha _ hy))

def cst (p : Z ⟶ X) : Γ(X, ⊤) →+* Fn Z :=
  RingHom.pi fun z => (Z.presheaf.germ (p ⁻¹ᵁ ⊤) z trivial).hom.comp (p.app ⊤).hom

theorem cst_apply (p : Z ⟶ X) (r : Γ(X, ⊤)) (z : Z) : cst p r z = gs p z ⊤ r := (gs_eq p z ⊤ trivial r).symm

theorem pb_cst (h : Y ⟶ Z) (p : Z ⟶ X) (r : Γ(X, ⊤)) : pb h (cst p r) = cst (h ≫ p) r := by
  funext y
  rw [pb_apply, cst_apply, cst_apply, stalkMap_gs h p y ⊤ trivial]

theorem reg_cst (p : Z ⟶ X) (r : Γ(X, ⊤)) : cst p r ∈ Reg ⊤ := ⟨(p.app ⊤).hom r, fun _ _ => rfl⟩

theorem loc_cst (r : Γ(X, ⊤)) : IsLoc (X.basicOpen r) ⊤ (cst (𝟙 X) r) := fun x =>
  (X.mem_basicOpen r x trivial).trans ⟨fun h => ⟨trivial, h⟩, fun h => h.2⟩

section Open

variable (h : Y ⟶ Z) [IsOpenImmersion h]

theorem pb_inj {F F' : Fn Z} {y : Y} (e : pb h F y = pb h F' y) : F (h y) = F' (h y) :=
  (ConcreteCategory.bijective_of_isIso (h.stalkMap y)).1 e

theorem pb_surj (F' : Fn Y) : ∃ F, pb h F = F' := by
  have : ∀ z : Z, ∃ x : Z.presheaf.stalk z, ∀ y (e : z = h y), (h.stalkMap y).hom (e ▸ x) = F' y := fun z => by
    by_cases hz : ∃ y, h y = z
    · obtain ⟨y, rfl⟩ := hz
      obtain ⟨x, hx⟩ := (ConcreteCategory.bijective_of_isIso (h.stalkMap y)).2 (F' y)
      refine ⟨x, fun y' e => ?_⟩
      obtain rfl := h.isOpenEmbedding.injective e
      exact hx
    · exact ⟨0, fun y e => (hz ⟨y, e.symm⟩).elim⟩
  choose F hF using this
  exact ⟨F, funext fun y => hF (h y) y rfl⟩

theorem reg_push {V : Y.Opens} {F : Fn Z} (hF : pb h F ∈ Reg V) : F ∈ Reg (h ''ᵁ V) := by
  obtain ⟨a, ha⟩ := mem_reg_iff.1 hF
  obtain ⟨b, rfl⟩ := (ConcreteCategory.bijective_of_isIso (h.appIso V).hom).2 a
  refine mem_reg_iff.2 ⟨b, ?_⟩
  rintro _ ⟨y, hy, rfl⟩
  refine pb_inj h (F := fun z => gs (𝟙 Z) z _ b) (Eq.trans ?_ (ha y hy))
  rw [pb_apply, gs_stalkMap h y _ (h.apply_mem_image_iff.2 hy), h.appIso_hom']
  exact ((gs_appLE h _ _ _ (𝟙 Y) y hy b).trans (by rw [Category.id_comp])).symm

theorem gen_push {V : Y.Opens} {S : Set (Fn Z)} (hS : Gen V (pb h '' S)) : Gen (h ''ᵁ V) S := by
  intro F hF
  obtain ⟨b, hb, e⟩ := hS _ (reg_mono (h.preimage_image_eq V).ge (reg_pull h hF))
  rw [← RingHom.map_closure] at hb
  obtain ⟨b, hb, rfl⟩ := hb
  refine ⟨b, hb, ?_⟩
  rintro _ ⟨y, hy, rfl⟩
  exact pb_inj h (e y hy)

theorem pack_push {ι : Type} {U : ι → Z.Opens} {G : ι → Fn Z} {S : Set (Fn Z)}
    (H : Pack (fun i => h ⁻¹ᵁ U i) (fun i => pb h (G i)) ⊤ (pb h '' S)) : Pack U G (h ''ᵁ ⊤) S := by
  obtain ⟨N, hN, M, s, D, hs, hD, cov, aff, gen⟩ := H
  choose s' e using fun j => pb_surj h (s j)
  obtain rfl : s = fun j => pb h (s' j) := funext fun j => (e j).symm
  refine ⟨N, hN, M, s', fun j => h ''ᵁ D j, fun j i => ?_, fun j z => ⟨?_, ?_⟩, ?_,
    fun j => (aff j).image_of_isOpenImmersion h, fun j => gen_push h ?_⟩
  · refine reg_mono ?_ (reg_push h (V := ⊤ ⊓ h ⁻¹ᵁ U i) (by rw [map_mul, map_pow]; exact hs j i))
    rintro _ ⟨⟨y, -, rfl⟩, hy⟩
    exact ⟨y, ⟨trivial, hy⟩, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨⟨y, trivial, rfl⟩, (pb_unit h _ y).1 ((hD j).unit hy)⟩
  · rintro ⟨⟨y, -, rfl⟩, hy⟩
    exact ⟨y, (hD j y).2 ⟨trivial, (pb_unit h _ y).2 hy⟩, rfl⟩
  · rintro _ ⟨y, -, rfl⟩
    obtain ⟨j, hj⟩ := cov y trivial
    exact ⟨j, y, hj, rfl⟩
  · have := gen j
    simpa only [Set.image_union, ← Set.range_comp', map_mul, pb_inv] using this

end Open

end GlobalTheory.AmpleLocal
