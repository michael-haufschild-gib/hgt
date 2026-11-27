import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.OpenRestrictionCech
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.LineBundleKunneth
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.AbelianSchemeLaws.WeilTorsionCharacters
import Mathlib.AlgebraicGeometry.PullbackCarrier

/-! Affine base charts for the universal translation difference. -/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory
open TopologicalSpace HTGeometry GlobalTheory.LineBundleSections GlobalTheory.SchemeCohomology
open ReciprocityTheory.ChartRestriction.G.Semi

namespace GlobalTheory.MumfordFibre

/-- An affine cover of a compact scheme can meet a given closed point
on just one designated chart. -/
theorem exists_affine_cover_separating_point (X : Scheme.{0}) [CompactSpace X]
    (x : X) (hx : IsClosed {x}) :
    ∃ (n : ℕ) (V : Fin (n + 1) → X.Opens), (∀ j, IsAffineOpen (V j)) ∧
      (⨆ j, V j) = ⊤ ∧ x ∈ V 0 ∧ ∀ j, j ≠ 0 → x ∉ V j := by
  obtain ⟨_, ⟨V₀, hV₀, rfl⟩, hxV, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  have hc : IsCompact (V₀ : Set X)ᶜ := V₀.isOpen.isClosed_compl.isCompact
  obtain ⟨s, hs⟩ := hc.elim_finite_subcover
    (fun W : {W : X.Opens // IsAffineOpen W ∧ x ∉ W} => (W.1 : Set X)) (fun W => W.1.isOpen)
    (by
      intro y hy
      have hy' : y ∈ ({x} : Set X)ᶜ := by
        rintro rfl
        exact hy hxV
      obtain ⟨_, ⟨W, hW, rfl⟩, hyW, hWx⟩ :=
        X.isBasis_affineOpens.exists_subset_of_mem_open hy' hx.isOpen_compl
      exact Set.mem_iUnion.mpr ⟨⟨W, hW, fun h => hWx h rfl⟩, hyW⟩)
  refine ⟨s.card, Fin.cons V₀ (fun j => (s.equivFin.symm j).1.1),
    Fin.cases hV₀ (fun j => (s.equivFin.symm j).1.2.1), ?_, hxV, fun j hj => ?_⟩
  · refine top_le_iff.mp fun y _ => Opens.mem_iSup.mpr ?_
    by_cases hy : y ∈ V₀
    · exact ⟨0, hy⟩
    · obtain ⟨W, hW, hyW⟩ := Set.mem_iUnion₂.mp (hs hy)
      exact ⟨(s.equivFin ⟨W, hW⟩).succ, by simpa using hyW⟩
  · obtain ⟨j, rfl⟩ := Fin.exists_succ_eq.mpr hj
    exact (s.equivFin.symm j).1.2.2

/-- Intersecting the inverse image of an affine open in a separated
scheme with any affine source open gives an affine open. -/
theorem isAffineOpen_preimage_inf {X Y : Scheme.{0}} [X.IsSeparated] (g : Y ⟶ X)
    {D : X.Opens} (hD : IsAffineOpen D) {W : Y.Opens} (hW : IsAffineOpen W) :
    IsAffineOpen (g ⁻¹ᵁ D ⊓ W) := by
  letI : IsAffine W := hW
  letI : IsAffineHom (W.ι ≫ g) :=
    haveI : IsAffineHom ((W.ι ≫ g) ≫ terminal.from X) := inferInstance
    IsAffineHom.of_comp _ (terminal.from X)
  have h := (hD.preimage (W.ι ≫ g)).image_of_isOpenImmersion W.ι
  rwa [Scheme.Hom.comp_preimage, Scheme.Hom.image_preimage_eq_opensRange_inf,
    Scheme.Opens.opensRange_ι, inf_comm] at h

attribute [local instance] Over.cartesianMonoidalCategory

/-- The left cover on the product, restricted over one affine base chart,
is the inverse-image cover on the affine base change. -/
theorem exists_affine_chart_cech {K : Type} [Field K]
    {A : Over (Spec (.of K))} [A.left.IsSeparated] {W : A.left.Opens} (hW : IsAffineOpen W)
    {κ : Type} [LinearOrder κ] (U : κ → A.left.Opens)
    (hU : ∀ i, IsAffineOpen (U i)) (cU : ⨆ i, U i = ⊤)
    {L : LB (A ⊗ A).left} (hL : L.IsLB) :
    ∃ (Y : Scheme.{0}) (π : Y ⟶ (A ⊗ A).left) (f : Y ⟶ Spec Γ(A.left, W))
      (V : κ → Y.Opens), IsPullback π f (fst A A).left hW.fromSpec ∧
      (∀ i, IsAffineOpen (V i)) ∧ (⨆ i, V i) = ⊤ ∧
      Nonempty (cechOverOpen (A ⊗ A).hom (toMod L) ((fst A A).left ⁻¹ᵁ W)
        (fun i => (snd A A).left ⁻¹ᵁ U i) ≅
        cech (f ≫ hW.fromSpec ≫ A.hom) (toMod (L.pull π)) V) := by
  let p := (fst A A).left
  let q := (snd A A).left
  let t := hW.fromSpec
  let π := pullback.fst p t
  let f := pullback.snd p t
  letI : IsOpenImmersion π := inferInstanceAs (IsOpenImmersion (pullback.fst p t))
  have H : IsPullback π f p t := IsPullback.of_hasPullback _ _
  have HP : IsPullback p q A.hom A.hom := IsPullback.of_hasPullback _ _
  have HS : IsPullback (π ≫ q) f A.hom (t ≫ A.hom) := H.paste_horiz HP.flip
  have hw : π.opensRange = p ⁻¹ᵁ W := by
    ext1
    rw [Scheme.Hom.coe_opensRange]
    erw [Scheme.Pullback.range_fst]
    rw [hW.range_fromSpec]
    rfl
  have hc (s : Finset κ) :
      coverInter π.opensRange (fun i => q ⁻¹ᵁ U i) s =
        (p ⁻¹ᵁ W) ⊓ q ⁻¹ᵁ (coverInter ⊤ U s) := by
    rw [hw]
    ext y
    change y ∈ coverInter (p ⁻¹ᵁ W) (fun i => q ⁻¹ᵁ U i) s ↔
      (p y ∈ W ∧ q y ∈ coverInter ⊤ U s)
    rw [mem_coverInter, mem_coverInter]
    exact ⟨fun h => ⟨h.1, trivial, h.2⟩, fun h => ⟨h.1, h.2.2⟩⟩
  have hv (s : Finset κ) (hs : s.Nonempty) :
      IsAffineOpen (coverInter π.opensRange (fun i => q ⁻¹ᵁ U i) s) := by
    rw [hc s]
    exact isAffineOpen_product HP hW (affine_coverInter_of_affine U hU s hs)
  let V (i : κ) := π ⁻¹ᵁ (q ⁻¹ᵁ U i)
  have hV (i : κ) : IsAffineOpen (V i) := by
    simpa only [V, Scheme.Hom.preimage_top, inf_top_eq, Scheme.Hom.comp_preimage] using
      isAffineOpen_product HS (hU i) (isAffineOpen_top _)
  have cV : ⨆ i, V i = ⊤ := by
    simp only [V, ← Scheme.Hom.preimage_iSup, cU, Scheme.Hom.preimage_top]
  have hbase : π ≫ (A ⊗ A).hom = f ≫ t ≫ A.hom := by
    rw [← Over.w (fst A A), ← Category.assoc, H.w, Category.assoc]
  refine ⟨_, π, f, V, H, hV, cV, ⟨?_⟩⟩
  rw [← hw, ← hbase]
  exact openCechPullbackIso (A ⊗ A).hom (fun i => q ⁻¹ᵁ U i) π hL hv

end GlobalTheory.MumfordFibre
