import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.AffineMixedCechComparison
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.ExternalProductCechKunneth
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.LineBundleQuasicoherent

/-! Over a field, coherent cohomology of an external product of line bundles
has dimensions given by the convolution of the two factor dimensions. -/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace HTGeometry
open GlobalTheory.SchemeCohomology GlobalTheory.WH ReciprocityTheory.ChartRestriction.G.Semi
open Finset.HasAntidiagonal

namespace GlobalTheory.LineBundleSections

private theorem affine_preimage_inf {X Z : Scheme.{0}} [X.IsSeparated] (p : Z ⟶ X)
    {U : X.Opens} (hU : IsAffineOpen U) {W : Z.Opens} (hW : IsAffineOpen W) :
    IsAffineOpen (p ⁻¹ᵁ U ⊓ W) := by
  letI : IsAffine W := hW
  letI : IsAffineHom ((W.ι ≫ p) ≫ terminal.from X) := inferInstance
  letI : IsAffineHom (W.ι ≫ p) := IsAffineHom.of_comp _ (terminal.from X)
  have h := (hU.preimage (W.ι ≫ p)).image_of_isOpenImmersion W.ι
  rwa [Scheme.Hom.comp_preimage, Scheme.Hom.image_preimage_eq_opensRange_inf,
    Scheme.Opens.opensRange_ι, inf_comm] at h

/-- Every nonempty finite intersection of affine opens in a separated scheme is affine. -/
theorem affine_coverInter_of_affine {X : Scheme.{0}} [X.IsSeparated]
    {ι : Type} [LinearOrder ι] (U : ι → X.Opens) (hU : ∀ i, IsAffineOpen (U i))
    (I : Finset ι) (hI : I.Nonempty) : IsAffineOpen (coverInter ⊤ U I) := by
  obtain ⟨i, hi⟩ := hI
  have hle : I.inf U ≤ U i := Finset.inf_le hi
  have h : coverInter (U i) U I = coverInter ⊤ U I := by
    rw [coverInter, coverInter, inf_eq_right.mpr hle, top_inf_eq]
  exact h ▸ affine_coverInter_of_inter_affine U (fun j W hW => (hU j).inf hW) (hU i) I

variable {K : Type} [Field K] {X Y Z : Scheme.{0}} [X.IsSeparated] [Y.IsSeparated] [Z.IsSeparated]
  [HasExt.{0} (TopCat.Sheaf AddCommGrpCat.{0} Z)]
  {f : X ⟶ Spec (.of K)} {g : Y ⟶ Spec (.of K)} {p : Z ⟶ X} {q : Z ⟶ Y}
  {ι κ ν : Type} [LinearOrder ι] [LinearOrder κ] [LinearOrder ν]
  [Fintype ι] [Fintype κ] [Fintype ν]
  {M : LB X} {N : LB Y} (U : ι → X.Opens) (V : κ → Y.Opens) (W : ν → Z.Opens)

/-- The Čech dimension formula is independent of the affine cover used on the product. -/
theorem finrank_cech_externalProduct (H : IsPullback p q f g)
    (hM : M.IsLB) (hN : N.IsLB)
    (hU : ∀ i, IsAffineOpen (U i)) (hV : ∀ j, IsAffineOpen (V j)) (hW : ∀ k, IsAffineOpen (W k))
    (hchartU : ∀ i, ∃ a : M.ι, U i ≤ M.U a) (hchartV : ∀ j, ∃ b : N.ι, V j ≤ N.U b)
    (cU : ⨆ i, U i = ⊤) (cV : ⨆ j, V j = ⊤) (cW : ⨆ k, W k = ⊤)
    (hFinU : ∀ n, Module.Finite K ((cech f (toMod M) U).homology n))
    (hFinV : ∀ n, Module.Finite K ((cech g (toMod N) V).homology n)) (n : ℕ) :
    Module.finrank K ((cech (p ≫ f) (toMod (twist (M.pull p) (N.pull q) 1)) W).homology n) =
      ∑ x ∈ antidiagonal n, Module.finrank K ((cech f (toMod M) U).homology x.1) *
        Module.finrank K ((cech g (toMod N) V).homology x.2) := by
  let E := twist (M.pull p) (N.pull q) 1
  letI : (toMod E).IsQuasicoherent := isQuasicoherent_toMod (twist_isLB (hM.pull p) (hN.pull q) 1)
  have hCov₁ : ⨆ i, p ⁻¹ᵁ U i = ⊤ := by rw [← Scheme.Hom.preimage_iSup, cU]; rfl
  have hCov₂ : ⨆ j, q ⁻¹ᵁ V j = ⊤ := by rw [← Scheme.Hom.preimage_iSup, cV]; rfl
  obtain ⟨e⟩ := nonempty_homology_equiv_affine_mixed (p ≫ f) (toMod E)
    (fun i => p ⁻¹ᵁ U i) (fun j => q ⁻¹ᵁ V j) W
    (fun i _ h => affine_preimage_inf p (hU i) h)
    (fun j _ h => affine_preimage_inf q (hV j) h)
    (fun k _ h => (hW k).inf h) hW
    (fun i j => isAffineOpen_product H (hU i) (hV j)) hCov₁ hCov₂ cW n
  have hchartU' (I : Finset ι) (hI : I.Nonempty) : ∃ a : M.ι, coverInter ⊤ U I ≤ M.U a := by
    obtain ⟨i, hi⟩ := hI
    obtain ⟨a, ha⟩ := hchartU i
    exact ⟨a, (inf_le_right.trans (Finset.inf_le hi)).trans ha⟩
  have hchartV' (J : Finset κ) (hJ : J.Nonempty) : ∃ b : N.ι, coverInter ⊤ V J ≤ N.U b := by
    obtain ⟨j, hj⟩ := hJ
    obtain ⟨b, hb⟩ := hchartV j
    exact ⟨b, (inf_le_right.trans (Finset.inf_le hj)).trans hb⟩
  exact e.finrank_eq.trans (finrank_cech_externalProduct_joined U V H hM hN
    (affine_coverInter_of_affine U hU) (affine_coverInter_of_affine V hV) hchartU' hchartV' hFinU hFinV n)

end GlobalTheory.LineBundleSections
