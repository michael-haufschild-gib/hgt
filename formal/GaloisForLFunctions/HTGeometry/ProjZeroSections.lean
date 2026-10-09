import GaloisForLFunctions.HTGeometry.ProjTwistedComparison
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction

/-!
# Degree-zero elements as global sections of `Proj`

For a graded ring `A = ⊕ 𝒜_n`, the structure map `Proj A → Spec 𝒜_0` corresponds, under the
`Γ ⊣ Spec` adjunction, to a ring map `𝒜_0 → Γ(Proj A, 𝒪)`.  Its restriction to a chart `D₊(f)`
(`f` homogeneous of positive degree) is the inclusion of degree-zero elements as fractions with
denominator `1`, `𝒜_0 → A_{(f)} ≅ Γ(D₊(f), 𝒪)`.

* `HTGeometry.zeroToGlobal` : the ring map `𝒜_0 → Γ(Proj A, ⊤)`.
* `HTGeometry.toSpecZero_eq` : `Proj A → Spec 𝒜_0` is `Proj A → Spec Γ → Spec 𝒜_0`.
* `HTGeometry.zeroToGlobal_restrict` : restriction to a chart.
-/

namespace HTGeometry

open AlgebraicGeometry CategoryTheory Opposite

universe u

variable {σ : Type*} {A : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- **Degree-zero elements as global sections.** -/
noncomputable def zeroToGlobal : CommRingCat.of (𝒜 0) ⟶ Γ(Proj 𝒜, ⊤) :=
  (Scheme.ΓSpecIso _).inv ≫ (Proj.toSpecZero 𝒜).appTop

/-- **The structure map through the global sections.** -/
theorem toSpecZero_eq : Proj.toSpecZero 𝒜 = (Proj 𝒜).toSpecΓ ≫ Spec.map (zeroToGlobal 𝒜) := by
  have h := Scheme.toSpecΓ_naturality (Proj.toSpecZero 𝒜)
  rw [← SpecMap_ΓSpecIso_hom] at h
  rw [zeroToGlobal, Spec.map_comp, ← Category.assoc, ← h, Category.assoc, ← Spec.map_comp,
    Iso.inv_hom_id, Spec.map_id, Category.comp_id]

/-- **Restriction of a degree-zero global section to a chart.** -/
theorem zeroToGlobal_restrict {f : A} {m : ℕ} (f_deg : f ∈ 𝒜 m) (hm : 0 < m) (x : 𝒜 0) :
    ((Proj 𝒜).presheaf.map (homOfLE (le_top : Proj.basicOpen 𝒜 f ≤ ⊤)).op).hom
        ((zeroToGlobal 𝒜).hom x)
      = (Proj.awayToSection 𝒜 f).hom (HomogeneousLocalization.fromZeroRingHom 𝒜 _ x) := by
  have h := congrArg Scheme.Hom.appTop (Proj.awayι_toSpecZero 𝒜 f f_deg hm)
  rw [Scheme.Hom.comp_appTop, Proj.awayι, Scheme.Hom.comp_appTop, Scheme.Opens.ι_appTop] at h
  set e := Proj.basicOpenIsoSpec 𝒜 f f_deg hm with he
  have he' : e.inv.appTop ≫ e.hom.appTop = 𝟙 _ := by
    rw [← Scheme.Hom.comp_appTop, e.hom_inv_id, Scheme.Hom.id_appTop]
  have hτ : e.hom.appTop = (Scheme.ΓSpecIso _).hom ≫ Proj.awayToSection 𝒜 f ≫
      (Proj.basicOpen 𝒜 f).topIso.inv := by
    rw [he, Proj.basicOpenIsoSpec_hom]
    exact Proj.basicOpenToSpec_app_top 𝒜 f
  have h2 := congrArg (· ≫ e.hom.appTop) h
  simp only [Category.assoc, he', Category.comp_id] at h2
  rw [hτ, ← Category.assoc (Scheme.Hom.appTop (Spec.map _)), Scheme.ΓSpecIso_naturality] at h2
  have h3 := congrArg (· ≫ (Proj.basicOpen 𝒜 f).topIso.hom) h2
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id] at h3
  have h4 := congrArg (fun φ => φ.hom ((Scheme.ΓSpecIso (CommRingCat.of (𝒜 0))).inv.hom x)) h3
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply,
    CommRingCat.hom_ofHom, Scheme.Opens.topIso_hom] at h4
  rw [show eqToHom (Scheme.Opens.ι_image_top (Proj.basicOpen 𝒜 f)).symm
      = homOfLE (le_of_eq (Scheme.Opens.ι_image_top (Proj.basicOpen 𝒜 f)).symm) from
    Subsingleton.elim _ _] at h4
  erw [schemeRes_res] at h4
  rw [show (Scheme.ΓSpecIso (CommRingCat.of (𝒜 0))).hom.hom
      ((Scheme.ΓSpecIso (CommRingCat.of (𝒜 0))).inv.hom x) = x by
    rw [← CommRingCat.comp_apply, Iso.inv_hom_id, CommRingCat.id_apply]] at h4
  rw [← h4]
  rfl

/-! ## Global sections from degree zero, as elements -/

section Cover

variable {K : Type*} [CommRing K] {M : Type u} [CommRing M] [Algebra K M]
  {𝒜 : ℕ → Submodule K M} [GradedAlgebra 𝒜] {ι : Type*} [DecidableEq ι] [LinearOrder ι]
  {w : ι → M} (hw : ∀ i, w i ∈ 𝒜 1)

omit [GradedAlgebra 𝒜] [DecidableEq ι] [LinearOrder ι] in
/-- The empty-subset entry of the degree-zero twisted datum consists of degree-zero elements. -/
theorem exists_zero_of_mem_twPart_empty {y : LocAt w ∅} (hy : y ∈ twPart 𝒜 w ∅ 0) :
    ∃ b : 𝒜 0, y = algebraMap M (LocAt w ∅) b := by
  refine AddSubgroup.closure_induction (p := fun y _ => ∃ b : 𝒜 0, y = algebraMap M _ b)
    ?_ ?_ ?_ ?_ hy
  · rintro _ ⟨m, i, x, hx, hdeg, rfl⟩
    rw [Finset.card_empty, mul_zero, add_zero] at hdeg
    subst hdeg
    refine ⟨⟨x, hx⟩, ?_⟩
    have h1 : (⟨wProd w ∅ ^ m, m, rfl⟩ : Submonoid.powers (wProd w ∅)) = 1 :=
      Subtype.ext (by simp [wProd])
    rw [frac, h1, Localization.mk_one_eq_algebraMap]
  · exact ⟨0, by simp⟩
  · rintro _ _ _ _ ⟨b, rfl⟩ ⟨c, rfl⟩
    exact ⟨b + c, by rw [Submodule.coe_add, map_add]⟩
  · rintro _ _ ⟨b, rfl⟩
    exact ⟨-b, by rw [Submodule.coe_neg, map_neg]⟩

omit [LinearOrder ι] in
include hw in
/-- **Every global section of `𝒪_{Proj M}` is a degree-zero element**, when the degree-zero twisted
datum of a cover by linear forms is exact in degree `0`. -/
theorem exists_zeroToGlobal_eq [LinearOrder ι] (hcov : ⨆ i, Proj.basicOpen 𝒜 (w i) = ⊤)
    (h0 : (twCech 𝒜 w hw 0).ExactAt 0) (σ : Γ(Proj 𝒜, ⊤)) :
    ∃ b : 𝒜 0, (zeroToGlobal 𝒜).hom b = σ := by
  have hE : coverInter ⊤ (projCover (𝒜 := 𝒜) w) ∅ = ⊤ := coverInter_empty _ _
  obtain ⟨y, hy⟩ := proj_globalSection_surjective hw hcov h0
    (((Proj 𝒜).presheaf.map (homOfLE (le_of_eq hE)).op).hom σ)
  obtain ⟨b, hb⟩ := exists_zero_of_mem_twPart_empty (𝒜 := 𝒜) (w := w) (y : twPart 𝒜 w ∅ 0).2
  have hb' : twVal hw (e := 0) y = algebraMap M (LocAt w ∅) b := hb
  refine ⟨b, ?_⟩
  set W : ι → (Proj 𝒜).Opens := fun k => Proj.basicOpen 𝒜 (wProd w {k}) with hW
  have hWk : ∀ k, W k = coverInter ⊤ (projCover (𝒜 := 𝒜) w) {k} := fun k =>
    (coverInter_projCover (𝒜 := 𝒜) (w := w) {k}).symm
  have hcovW : ⊤ ≤ ⨆ k, W k := by
    rw [← hcov]
    refine iSup_mono fun k => le_of_eq ?_
    rw [hW]
    simp only [wProd, Finset.prod_singleton]
  refine TopCat.Sheaf.eq_of_locally_eq' (schemeAbSheaf (Proj 𝒜)) W ⊤
    (fun _ => homOfLE le_top) hcovW _ _ fun k => ?_
  change ((Proj 𝒜).presheaf.map (homOfLE (le_top : W k ≤ ⊤)).op).hom ((zeroToGlobal 𝒜).hom b)
    = ((Proj 𝒜).presheaf.map (homOfLE (le_top : W k ≤ ⊤)).op).hom σ
  have hk : 0 < ({k} : Finset ι).card := Finset.card_pos.mpr (Finset.singleton_nonempty k)
  rw [zeroToGlobal_restrict 𝒜 (wProd_mem hw {k}) hk]
  -- the right side through the Čech datum
  have hcomm := (projCompare (𝒜 := 𝒜) hw).comm (Finset.empty_subset {k}) y
  rw [hy] at hcomm
  set a' := (twAwayEquiv hw {k}).symm ((twCech 𝒜 w hw 0).res (Finset.empty_subset {k}) y) with ha'
  have ha'val : a' = HomogeneousLocalization.fromZeroRingHom 𝒜 _ b := by
    apply HomogeneousLocalization.val_injective
    have h1 : a'.val = twVal hw (e := 0) ((twCech 𝒜 w hw 0).res (Finset.empty_subset {k}) y) := by
      rw [← twVal_twAwayEquiv hw {k} a', ha', AddEquiv.apply_symm_apply]
    rw [h1, twCech_res_val, hb', resLoc_algebraMap]
    change _ = HomogeneousLocalization.val (HomogeneousLocalization.mk ⟨0, b, 1, _⟩)
    rw [HomogeneousLocalization.val_mk, ← Localization.mk_one_eq_algebraMap]
    rfl
  change ((Proj 𝒜).presheaf.map _).hom (((Proj 𝒜).presheaf.map _).hom σ)
    = ((Proj 𝒜).presheaf.map _).hom ((Proj.awayToSection 𝒜 (wProd w {k})).hom a') at hcomm
  rw [schemeRes_res] at hcomm
  have h2 := congrArg ((Proj 𝒜).presheaf.map (homOfLE (le_of_eq (hWk k))).op).hom hcomm
  rw [schemeRes_res, schemeRes_res, schemeRes_self, ha'val] at h2
  exact h2.symm

end Cover

end HTGeometry
