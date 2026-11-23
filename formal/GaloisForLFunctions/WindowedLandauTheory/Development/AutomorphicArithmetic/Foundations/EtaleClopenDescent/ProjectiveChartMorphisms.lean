import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ProjectiveChartCoordinates
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ProjectiveRatioTransitions

/-! Morphisms into a projective coordinate chart are determined by the
pullbacks of its affine coordinates over the base. -/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open UpperTheory.Cb

namespace GlobalTheory.SchemeCohomology

attribute [local instance] MvPolynomial.gradedAlgebra

variable {K : Type} [CommRing K] {N : ℕ} {Y : Scheme.{0}}

private abbrev coord (i : Fin (N + 1)) := PSpace.coordinateOpen K N i

theorem pspaceChart_isAffine (i : Fin (N + 1)) : IsAffineOpen (coord (K := K) i) :=
  Proj.isAffineOpen_basicOpen _ _ (MvPolynomial.isHomogeneous_X K i) one_pos

private def baseRing (s : Y ⟶ Spec (CommRingCat.of K)) (U : Y.Opens) :
    CommRingCat.of K ⟶ Γ(Y, U) :=
  (Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ s.appLE ⊤ U le_top

private theorem baseRing_appLE {Z : Scheme.{0}} (s : Y ⟶ Spec (CommRingCat.of K))
    (f : Z ⟶ Y) (U : Y.Opens) (V : Z.Opens) (h : V ≤ f ⁻¹ᵁ U) :
    baseRing s U ≫ f.appLE U V h = baseRing (f ≫ s) V :=
  (Category.assoc _ _ _).trans
    (congrArg (_ ≫ ·) (Scheme.Hom.appLE_comp_appLE f s ⊤ U V le_top h))

private theorem baseRing_top_injective {f g : Y ⟶ Spec (CommRingCat.of K)}
    (h : baseRing f ⊤ = baseRing g ⊤) : f = g := by
  unfold baseRing at h
  rw [cancel_epi] at h
  apply ext_of_isAffine
  exact (f.app_eq_appLE (U := ⊤)).trans (h.trans (g.app_eq_appLE (U := ⊤)).symm)

private def chartHom (i : Fin (N + 1))
    (ρ : Γ(PSpace K N, coord (K := K) i) ⟶ Γ(Y, ⊤)) : Y ⟶ PSpace K N :=
  Y.toSpecΓ ≫ Spec.map ρ ≫ (pspaceChart_isAffine (K := K) i).fromSpec

private theorem chartHom_preimage (i : Fin (N + 1))
    (ρ : Γ(PSpace K N, coord (K := K) i) ⟶ Γ(Y, ⊤)) :
    ⊤ ≤ chartHom i ρ ⁻¹ᵁ coord (K := K) i := by
  rw [chartHom, Scheme.Hom.comp_preimage, Scheme.Hom.comp_preimage,
    IsAffineOpen.fromSpec_preimage_self]
  exact le_rfl

private theorem chartHom_appLE (i : Fin (N + 1))
    (ρ : Γ(PSpace K N, coord (K := K) i) ⟶ Γ(Y, ⊤)) :
    (chartHom i ρ).appLE _ ⊤ (chartHom_preimage i ρ) = ρ := by
  let h := pspaceChart_isAffine (K := K) i
  have h₁ : h.fromSpec.appLE _ ⊤ h.fromSpec_preimage_self.ge = (Scheme.ΓSpecIso _).inv := by
    rw [Scheme.Hom.appLE, IsAffineOpen.fromSpec_app_self, Category.assoc, ← Functor.map_comp]
    exact (congrArg _ (CategoryTheory.Functor.map_id _ _)).trans (Category.comp_id _)
  have h₂ : (Y.toSpecΓ ≫ Spec.map ρ).appLE ⊤ ⊤ le_rfl = (Scheme.ΓSpecIso _).hom ≫ ρ := by
    refine (Scheme.Hom.app_eq_appLE _).symm.trans ?_
    change (Y.toSpecΓ ≫ Spec.map ρ).appTop = _
    rw [Scheme.Hom.comp_appTop, Scheme.toSpecΓ_appTop, Scheme.ΓSpecIso_naturality]
  have h₃ := Scheme.Hom.appLE_comp_appLE (Y.toSpecΓ ≫ Spec.map ρ) h.fromSpec
    (coord (K := K) i) ⊤ ⊤ h.fromSpec_preimage_self.ge le_rfl
  rw [h₁, h₂, Iso.inv_hom_id_assoc] at h₃
  exact h₃.symm

variable [Nontrivial K]

private def coordinateAlgHom (s : Y ⟶ Spec (CommRingCat.of K)) (U : Y.Opens)
    (i : Fin (N + 1)) (r : Fin (N + 1) → Γ(Y, U)) :
    SectionRing (PSpace.str K N) (coord (K := K) i) →ₐ[K] SectionRing s U := by
  let coords (j : {j // j ≠ i}) : SectionRing s U := r j.1
  exact (MvPolynomial.aeval coords).comp (pspaceChartAlgEquiv K i).symm.toAlgHom

private abbrev coordinateHom (s : Y ⟶ Spec (CommRingCat.of K)) (U : Y.Opens)
    (i : Fin (N + 1)) (r : Fin (N + 1) → Γ(Y, U)) :
    Γ(PSpace K N, coord (K := K) i) ⟶ Γ(Y, U) :=
  CommRingCat.ofHom (coordinateAlgHom s U i r).toRingHom

private theorem coordinateHom_base (s : Y ⟶ Spec (CommRingCat.of K)) (U : Y.Opens)
    (i : Fin (N + 1)) (r : Fin (N + 1) → Γ(Y, U)) :
    baseRing (PSpace.str K N) (coord (K := K) i) ≫ coordinateHom s U i r = baseRing s U := by
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  exact (coordinateAlgHom s U i r).commutes a

private theorem coordinateHom_ratio (s : Y ⟶ Spec (CommRingCat.of K)) (U : Y.Opens)
    (i : Fin (N + 1)) (r : Fin (N + 1) → Γ(Y, U)) (hr : r i = 1) (j : Fin (N + 1)) :
    (coordinateHom s U i r).hom (pspaceChartRatio K i j) = r j := by
  change coordinateAlgHom s U i r (pspaceChartRatio K i j) = (r j : SectionRing s U)
  by_cases hj : j = i
  · subst j
    have he : pspaceChartRatio K i i = 1 :=
      homogeneousRatio_self (MvPolynomial.isHomogeneous_X K i)
    exact (congrArg (coordinateAlgHom s U i r) he).trans
      ((coordinateAlgHom s U i r).map_one.trans hr.symm)
  · let a : {j // j ≠ i} := ⟨j, hj⟩
    rw [← pspaceChartAlgEquiv_X K i a]
    let coords (j : {j // j ≠ i}) : SectionRing s U := r j.1
    let e : MvPolynomial {j // j ≠ i} K →ₐ[K] SectionRing s U := MvPolynomial.aeval coords
    change e ((pspaceChartAlgEquiv K i).symm (pspaceChartAlgEquiv K i (MvPolynomial.X a))) = r j
    rw [AlgEquiv.symm_apply_apply, MvPolynomial.aeval_X]

/-- The given sections are the ratios of the induced morphism into the
specified coordinate chart. -/
def pspaceOfCoordinates (s : Y ⟶ Spec (CommRingCat.of K)) (U : Y.Opens)
    (i : Fin (N + 1)) (r : Fin (N + 1) → Γ(Y, U)) : U.toScheme ⟶ PSpace K N :=
  chartHom i (coordinateHom s U i r ≫ U.ι.appLE U ⊤ U.ι_preimage_self.ge)

theorem pspaceOfCoordinates_preimage (s : Y ⟶ Spec (CommRingCat.of K)) (U : Y.Opens)
    (i : Fin (N + 1)) (r : Fin (N + 1) → Γ(Y, U)) :
    ⊤ ≤ pspaceOfCoordinates s U i r ⁻¹ᵁ coord (K := K) i :=
  chartHom_preimage i _

private theorem pspaceOfCoordinates_appLE (s : Y ⟶ Spec (CommRingCat.of K)) (U : Y.Opens)
    (i : Fin (N + 1)) (r : Fin (N + 1) → Γ(Y, U)) :
    (pspaceOfCoordinates s U i r).appLE _ ⊤ (pspaceOfCoordinates_preimage s U i r) =
      coordinateHom s U i r ≫ U.ι.appLE U ⊤ U.ι_preimage_self.ge :=
  chartHom_appLE i _

theorem pspaceOfCoordinates_base (s : Y ⟶ Spec (CommRingCat.of K)) (U : Y.Opens)
    (i : Fin (N + 1)) (r : Fin (N + 1) → Γ(Y, U)) :
    pspaceOfCoordinates s U i r ≫ PSpace.str K N = U.ι ≫ s := by
  apply baseRing_top_injective
  let V := coord (K := K) i
  let g := pspaceOfCoordinates s U i r
  let a := baseRing (PSpace.str K N) V
  let b := coordinateHom s U i r
  let c := U.ι.appLE U ⊤ U.ι_preimage_self.ge
  calc
    _ = a ≫ g.appLE V ⊤ (pspaceOfCoordinates_preimage s U i r) :=
      (baseRing_appLE _ _ _ _ _).symm
    _ = a ≫ b ≫ c := congrArg (a ≫ ·) (pspaceOfCoordinates_appLE s U i r)
    _ = (a ≫ b) ≫ c := (Category.assoc a b c).symm
    _ = baseRing s U ≫ c := congrArg (· ≫ c) (coordinateHom_base s U i r)
    _ = _ := baseRing_appLE s U.ι U ⊤ U.ι_preimage_self.ge

theorem pspaceOfCoordinates_ratio (s : Y ⟶ Spec (CommRingCat.of K)) (U : Y.Opens)
    (i : Fin (N + 1)) (r : Fin (N + 1) → Γ(Y, U)) (hr : r i = 1) (j : Fin (N + 1)) :
    ((pspaceOfCoordinates s U i r).appLE _ ⊤ (pspaceOfCoordinates_preimage s U i r)).hom
      (pspaceChartRatio K i j) = (U.ι.appLE U ⊤ U.ι_preimage_self.ge).hom (r j) := by
  exact (ConcreteCategory.congr_hom (pspaceOfCoordinates_appLE s U i r) _).trans
    (congrArg (U.ι.appLE U ⊤ U.ι_preimage_self.ge).hom (coordinateHom_ratio s U i r hr j))

/-- Pullback of a ratio to any open contained in a chart preimage. -/
def pspacePullRatio (f : Y ⟶ PSpace K N) (W : Y.Opens) (i : Fin (N + 1))
    (hW : W ≤ f ⁻¹ᵁ PSpace.coordinateOpen K N i) (j : Fin (N + 1)) : Γ(Y, W) :=
  (f.appLE _ W hW).hom (pspaceChartRatio K i j)

omit [Nontrivial K] in
theorem basicOpen_pspacePullRatio (f : Y ⟶ PSpace K N) (W : Y.Opens)
    (i : Fin (N + 1)) (hW : W ≤ f ⁻¹ᵁ PSpace.coordinateOpen K N i) (j : Fin (N + 1)) :
    Y.basicOpen (pspacePullRatio f W i hW j) = W ⊓ f ⁻¹ᵁ PSpace.coordinateOpen K N j := by
  let U := PSpace.coordinateOpen K N i
  let V := PSpace.coordinateOpen K N j
  have hr : (PSpace K N).basicOpen (pspaceChartRatio K i j) = U ⊓ V :=
    basicOpen_homogeneousRatio (MvPolynomial.isHomogeneous_X K i) (MvPolynomial.isHomogeneous_X K j)
  refine (Scheme.basicOpen_appLE f W U hW (pspaceChartRatio K i j)).trans ?_
  rw [hr]
  exact le_antisymm (inf_le_inf_left _ (f.preimage_mono inf_le_right))
    (le_inf inf_le_left (le_inf (inf_le_left.trans hW) inf_le_right))

omit [Nontrivial K] in
theorem pspacePullRatio_mul (f : Y ⟶ PSpace K N) (W : Y.Opens)
    (i j k : Fin (N + 1)) (hi : W ≤ f ⁻¹ᵁ PSpace.coordinateOpen K N i)
    (hj : W ≤ f ⁻¹ᵁ PSpace.coordinateOpen K N j) :
    pspacePullRatio f W i hi j * pspacePullRatio f W j hj k = pspacePullRatio f W i hi k := by
  let U := PSpace.coordinateOpen K N i
  let V := PSpace.coordinateOpen K N j
  have h : W ≤ f ⁻¹ᵁ (U ⊓ V) := fun x hx => ⟨hi hx, hj hx⟩
  have he := congrArg (f.appLE (U ⊓ V) W h).hom
    (homogeneousRatio_mul (MvPolynomial.isHomogeneous_X K i)
      (MvPolynomial.isHomogeneous_X K j) (MvPolynomial.isHomogeneous_X K k))
  have hl (a : Γ(PSpace K N, U)) :
      (f.appLE (U ⊓ V) W h).hom
        ((PSpace K N).presheaf.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op a) =
      (f.appLE U W hi).hom a :=
    ConcreteCategory.congr_hom (f.map_appLE h (homOfLE (inf_le_left : U ⊓ V ≤ U)).op) a
  have hr (a : Γ(PSpace K N, V)) :
      (f.appLE (U ⊓ V) W h).hom
        ((PSpace K N).presheaf.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op a) =
      (f.appLE V W hj).hom a :=
    ConcreteCategory.congr_hom (f.map_appLE h (homOfLE (inf_le_right : U ⊓ V ≤ V)).op) a
  change (f.appLE (U ⊓ V) W h).hom
        (((PSpace K N).presheaf.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op
            (pspaceChartRatio K i j)) *
          ((PSpace K N).presheaf.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op
            (pspaceChartRatio K j k))) =
      (f.appLE (U ⊓ V) W h).hom
        ((PSpace K N).presheaf.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op
          (pspaceChartRatio K i k)) at he
  simpa only [map_mul, hl, hr, pspacePullRatio] using he

theorem pspace_appLE_ext {f g : Y ⟶ PSpace K N}
    (hs : f ≫ PSpace.str K N = g ≫ PSpace.str K N)
    (W : Y.Opens) (i : Fin (N + 1))
    (hf : W ≤ f ⁻¹ᵁ PSpace.coordinateOpen K N i) (hg : W ≤ g ⁻¹ᵁ PSpace.coordinateOpen K N i)
    (h : ∀ j, pspacePullRatio f W i hf j = pspacePullRatio g W i hg j) :
    f.appLE _ W hf = g.appLE _ W hg := by
  let V := PSpace.coordinateOpen K N i
  let E := pspaceChartAlgEquiv K i
  let a := f.appLE V W hf
  let b := g.appLE V W hg
  have e : a.hom.comp E.toRingEquiv.toRingHom = b.hom.comp E.toRingEquiv.toRingHom := by
    refine MvPolynomial.ringHom_ext (fun r => ?_) (fun j => ?_)
    · have he : baseRing (PSpace.str K N) V ≫ a = baseRing (PSpace.str K N) V ≫ b :=
        (baseRing_appLE _ f V W hf).trans
          ((congrArg (fun φ => baseRing φ W) hs).trans (baseRing_appLE _ g V W hg).symm)
      change a.hom (E (MvPolynomial.C r)) = b.hom (E (MvPolynomial.C r))
      have hr : E (MvPolynomial.C r) = (baseRing (PSpace.str K N) V).hom r :=
        E.commutes r
      rw [hr]
      exact congrArg (fun a : CommRingCat.of K ⟶ Γ(Y, W) => a.hom r) he
    · change a.hom (E (MvPolynomial.X j)) = b.hom (E (MvPolynomial.X j))
      have hj : E (MvPolynomial.X j) = pspaceChartRatio K i j.1 := pspaceChartAlgEquiv_X K i j
      exact (congrArg a.hom hj).trans ((h j.1).trans (congrArg b.hom hj).symm)
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro z
  obtain ⟨p, rfl⟩ := E.surjective z
  exact RingHom.congr_fun e p

theorem pspace_restrict_eq_of_ratios {f g : Y ⟶ PSpace K N}
    (hs : f ≫ PSpace.str K N = g ≫ PSpace.str K N)
    (W : Y.Opens) (i : Fin (N + 1))
    (hf : W ≤ f ⁻¹ᵁ PSpace.coordinateOpen K N i) (hg : W ≤ g ⁻¹ᵁ PSpace.coordinateOpen K N i)
    (h : ∀ j, pspacePullRatio f W i hf j = pspacePullRatio g W i hg j) :
    W.ι ≫ f = W.ι ≫ g := by
  let V := PSpace.coordinateOpen K N i
  let hV := pspaceChart_isAffine (K := K) i
  have ht (a : Y ⟶ PSpace K N) (ha : W ≤ a ⁻¹ᵁ V) :
      W.ι ≫ a = W.toSpecΓ ≫ Spec.map (a.appLE V W ha) ≫ hV.fromSpec := by
    rw [Scheme.Opens.toSpecΓ_SpecMap_appLE_assoc, IsAffineOpen.toSpecΓ_fromSpec,
      Scheme.Hom.resLE_comp_ι]
  rw [ht f hf, ht g hg, pspace_appLE_ext hs W i hf hg h]

theorem pspacePullRatio_comp_ofCoordinates {Z : Scheme.{0}}
    (s : Y ⟶ Spec (CommRingCat.of K)) (U : Y.Opens)
    (i : Fin (N + 1)) (r : Fin (N + 1) → Γ(Y, U)) (hr : r i = 1)
    (a : Z ⟶ U.toScheme) (W : Z.Opens)
    (h : W ≤ (a ≫ pspaceOfCoordinates s U i r) ⁻¹ᵁ PSpace.coordinateOpen K N i)
    (h' : W ≤ (a ≫ U.ι) ⁻¹ᵁ U) (j : Fin (N + 1)) :
    pspacePullRatio (a ≫ pspaceOfCoordinates s U i r) W i h j =
      ((a ≫ U.ι).appLE U W h').hom (r j) := by
  let b := pspaceOfCoordinates s U i r
  let V := PSpace.coordinateOpen K N i
  have hb := pspaceOfCoordinates_preimage s U i r
  calc
    _ = (a.appLE ⊤ W le_top).hom ((b.appLE V ⊤ hb).hom (pspaceChartRatio K i j)) :=
      (ConcreteCategory.congr_hom (Scheme.Hom.appLE_comp_appLE a b V ⊤ W hb le_top)
        (pspaceChartRatio K i j)).symm
    _ = (a.appLE ⊤ W le_top).hom ((U.ι.appLE U ⊤ U.ι_preimage_self.ge).hom (r j)) :=
      congrArg (a.appLE ⊤ W le_top).hom (pspaceOfCoordinates_ratio s U i r hr j)
    _ = _ := ConcreteCategory.congr_hom
      (Scheme.Hom.appLE_comp_appLE a U.ι U ⊤ W U.ι_preimage_self.ge le_top) (r j)

end GlobalTheory.SchemeCohomology
