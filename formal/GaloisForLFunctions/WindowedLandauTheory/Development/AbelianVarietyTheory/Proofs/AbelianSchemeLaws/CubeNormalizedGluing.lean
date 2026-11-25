import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.AbelianSchemeLaws.CubeGeneratorGluing
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.AbelianSchemeLaws.ThetaScalarRatio
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.AbelianSchemeLaws.ProperSmoothGlobalSections

/-! Local generators normalized on a section glue when global functions descend to the base. -/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.AbLaw.Cube

private theorem normalized_values_eq {X Y T : Scheme.{0}} {L : LB X} (hL : L.IsLB)
    {I J : Type} [Fintype I] [Fintype J]
    {f : I → (Y ⟶ X)} {d : I → ℤ} {g : J → (Y ⟶ X)} {e : J → ℤ}
    (hf : FormEq f d g e) (p : Y ⟶ T) [IsIso p.appTop] (s : T ⟶ Y) (hs : s ≫ p = 𝟙 T)
    {u : (LB.LinComb L f d).Gen} {v : (LB.LinComb L g e).Gen}
    (hu : u.IsGen) (hv : v.IsGen)
    (h : ∀ y K, Good L y K → val u s y K = val v s y K)
    {Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z) (K : (Z ⟶ X) → L.ι) (hK : Good L z K) :
    val u r z K = val v r z K := by
  obtain ⟨c, hc⟩ := GlobalTheory.CommPairing.exists_ratio hL hf p hu hv
  have h₁ : c = 1 := by
    apply unit_ext
    intro y _
    choose J hJ using fun ψ : T ⟶ X => exists_chart hL (ψ y)
    have h₂ := hc T s y J hJ
    rw [hs, h y J hJ] at h₂
    exact (mul_eq_left.mp h₂.symm).trans (map_one _).symm
  simpa only [h₁, map_one, mul_one] using hc Z r z K hK

/-- Normalize over the section, then glue the resulting generators over the whole base. -/
theorem exists_gen_of_local_triviality {X Y T : Scheme.{0}} {L : LB X} (hL : L.IsLB)
    {I : Type} [Fintype I] (f : I → (Y ⟶ X)) (d : I → ℤ)
    (p : Y ⟶ T) [Smooth p] [IsProper p] [GeometricallyConnected p]
    (s : T ⟶ Y) (hs : s ≫ p = 𝟙 T)
    (cancel : ∀ (Z : Scheme.{0}) (b : Z ⟶ T) (U : Type) [CommGroup U] (k : (Z ⟶ X) → U),
      ∏ i, k ((b ≫ s) ≫ f i) ^ d i = 1)
    (localGen : ∀ t : T, ∃ V : T.Opens, t ∈ V ∧
      ∃ u : (LB.LinComb L (fun i => (p ⁻¹ᵁ V).ι ≫ f i) d).Gen, u.IsGen) :
    ∃ u : (LB.LinComb L f d).Gen, u.IsGen := by
  have localNormalized (t : T) :
      ∃ V : T.Opens, t ∈ V ∧
        ∃ u : (LB.LinComb L (fun i => (p ⁻¹ᵁ V).ι ≫ f i) d).Gen, u.IsGen ∧
          ∀ (Z : Scheme.{0}) (r : Z ⟶ (p ⁻¹ᵁ V).toScheme) (b : Z ⟶ T) (z : Z) (K : (Z ⟶ X) → L.ι),
            Good L z K → r ≫ (p ⁻¹ᵁ V).ι = b ≫ s → val u r z K = 1 := by
    obtain ⟨V, ht, u, hu⟩ := localGen t
    let W := p ⁻¹ᵁ V
    let n := IsOpenImmersion.lift W.ι ((W.ι ≫ p) ≫ s) (by
      rintro _ ⟨y, rfl⟩
      rw [Scheme.Opens.range_ι]
      exact (congrArg (fun q : T ⟶ T => q (p y.1) ∈ V) hs).mpr y.2)
    have hn : n ≫ W.ι = (W.ι ≫ p) ≫ s := IsOpenImmersion.lift_fac _ _ _
    let g (i : I) := W.ι ≫ f i
    have hF : FormEq (Sum.elim g (fun i => n ≫ g i)) (Sum.elim d (fun i => -d i)) g d := by
      intro U _ k
      have he := cancel W.toScheme (W.ι ≫ p) U k
      rw [← hn] at he
      simp only [Category.assoc] at he
      rw [Fintype.prod_sum_type]
      simp only [Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib, g, he, inv_one, mul_one]
    obtain ⟨v, hv, he⟩ := exists_gen_of_formEq hL hF
      (LB.mulGen L g d _ _ u (LB.invGen L _ _ (LB.pullGen L g d u n)))
      (mulGen_isGen hu (invGen_isGen (hu.pullGen g d n)))
    refine ⟨V, ht, v, hv, fun Z r b z K hK hr => ?_⟩
    have hrn : r ≫ n = r := by
      rw [← cancel_mono W.ι, Category.assoc, hn, ← Category.assoc, ← Category.assoc, hr,
        Category.assoc b, hs, Category.comp_id]
    rw [he Z r z K hK, val_mul hK, val_inv, val_pull hK, hrn, mul_inv_cancel]
  choose V hV u hu hn using localNormalized
  have agree (i j : T) (Z : Scheme.{0}) (r : Z ⟶ (p ⁻¹ᵁ V i).toScheme)
      (r' : Z ⟶ (p ⁻¹ᵁ V j).toScheme) (z : Z) (K : (Z ⟶ X) → L.ι) (hK : Good L z K)
      (hr : r ≫ (p ⁻¹ᵁ V i).ι = r' ≫ (p ⁻¹ᵁ V j).ι) : val (u i) r z K = val (u j) r' z K := by
    let D := V i ⊓ V j
    let W := p ⁻¹ᵁ D
    let q := p ∣_ D
    let H := (isPullback_morphismRestrict p D).flip
    haveI : Smooth q := MorphismProperty.of_isPullback H (inferInstance : Smooth p)
    haveI : IsProper q := MorphismProperty.of_isPullback H (inferInstance : IsProper p)
    haveI : GeometricallyConnected q :=
      MorphismProperty.of_isPullback H (inferInstance : GeometricallyConnected p)
    haveI : IsIso q.appTop := GlobalTheory.GlobalFunctions.isIso_app_of_geometricallyConnected q ⊤
    let a := Y.homOfLE (p.preimage_mono (inf_le_left : D ≤ V i))
    let b := Y.homOfLE (p.preimage_mono (inf_le_right : D ≤ V j))
    have ha : a ≫ (p ⁻¹ᵁ V i).ι = W.ι := Y.homOfLE_ι _
    have hb : b ≫ (p ⁻¹ᵁ V j).ι = W.ι := Y.homOfLE_ι _
    have hD : (D.ι ≫ s) ≫ p = (𝟙 D.toScheme) ≫ D.ι := by simp only [Category.assoc, hs, Category.comp_id, Category.id_comp]
    let e := H.lift (D.ι ≫ s) (𝟙 _) hD
    have he : e ≫ W.ι = D.ι ≫ s := H.lift_fst _ _ _
    have heq : e ≫ q = 𝟙 _ := H.lift_snd _ _ _
    let fᵢ (k : I) := (p ⁻¹ᵁ V i).ι ≫ f k
    let fⱼ (k : I) := (p ⁻¹ᵁ V j).ι ≫ f k
    have hF : FormEq (fun k => a ≫ fᵢ k) d (fun k => b ≫ fⱼ k) d := by
      intro U _ c
      apply Finset.prod_congr rfl
      intro k _
      simp only [fᵢ, fⱼ, ← Category.assoc, ha, hb]
    let ρ := IsOpenImmersion.lift W.ι (r ≫ (p ⁻¹ᵁ V i).ι) (by
      rintro _ ⟨y, rfl⟩
      rw [Scheme.Opens.range_ι]
      exact ⟨(r y).2, (congrArg (fun v : Z ⟶ Y => p (v y) ∈ V j) hr).mpr (r' y).2⟩)
    have hρ : ρ ≫ W.ι = r ≫ (p ⁻¹ᵁ V i).ι := IsOpenImmersion.lift_fac _ _ _
    have e₁ : ρ ≫ a = r := by rw [← cancel_mono (p ⁻¹ᵁ V i).ι, Category.assoc, ha, hρ]
    have e₂ : ρ ≫ b = r' := by rw [← cancel_mono (p ⁻¹ᵁ V j).ι, Category.assoc, hb, hρ, hr]
    have hval := normalized_values_eq hL hF q e heq ((hu i).pullGen fᵢ d a)
      ((hu j).pullGen fⱼ d b) (fun y J hJ => by
        rw [val_pull hJ, val_pull hJ, hn i _ _ D.ι y J hJ (by rw [Category.assoc, ha, he]),
          hn j _ _ D.ι y J hJ (by rw [Category.assoc, hb, he])]) ρ z K hK
    rw [val_pull hK, val_pull hK, e₁, e₂] at hval
    exact hval
  obtain ⟨v, hv, -⟩ := glue_gen hL f d (fun t => p ⁻¹ᵁ V t) (fun y => ⟨p y, hV (p y)⟩) u hu agree
  exact ⟨v, hv⟩

end GlobalTheory.AbLaw.Cube
