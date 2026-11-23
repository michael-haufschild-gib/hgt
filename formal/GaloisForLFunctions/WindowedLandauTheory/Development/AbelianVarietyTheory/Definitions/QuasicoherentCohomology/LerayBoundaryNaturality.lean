import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.LerayShortExact
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.LerayComparison

/-! Compatibility of the Leray comparison with the connecting maps
of a short exact sequence of sheaves. -/

noncomputable section

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite TopologicalSpace
  HTGeometry RHTower

namespace GlobalTheory.SchemeCohomology

private abbrev AbSheaf (X : TopCat.{0}) := TopCat.Sheaf AddCommGrpCat.{0} X

variable {X : TopCat.{0}} {ι : Type} [DecidableEq ι] [LinearOrder ι]
  {V : Opens X} {U : ι → Opens X}

local instance lerayBoundaryHasExt : HasExt.{0} (AbSheaf X) := hasExt_of_enoughInjectives _

private def mapIntoInjectiveEmbedding {S : ShortComplex (AbSheaf X)}
    (hS : S.ShortExact) : S ⟶ deningerInjectiveEmbedding S.X₁ := by
  let T := deningerInjectiveEmbedding S.X₁
  letI : Mono S.f := hS.mono_f
  letI : Epi S.g := hS.epi_g
  letI : Injective T.X₂ := CategoryTheory.Injective.injective_under S.X₁
  let b : S.X₂ ⟶ T.X₂ := Injective.factorThru T.f S.f
  have hb : S.f ≫ b = T.f := Injective.comp_factorThru T.f S.f
  let g := hS.exact.gIsCokernel
  let cg := CokernelCofork.ofπ (b ≫ T.g) (by rw [← Category.assoc, hb, T.zero])
  have hg : S.g ≫ g.desc cg = b ≫ T.g := Cofork.IsColimit.π_desc g
  exact { τ₁ := 𝟙 _, τ₂ := b, τ₃ := g.desc cg
          comm₁₂ := (Category.id_comp _).trans hb.symm
          comm₂₃ := hg.symm }

private abbrev C := abelianCechFunctor X V U

private abbrev Hmap {F G : AbSheaf X} (φ : F ⟶ G) (n : ℕ) :
    (sheafCechComplex V U F).homology n ⟶ (sheafCechComplex V U G).homology n :=
  HomologicalComplex.homologyMap (sheafCechComplexMap V U φ) n

private theorem cechBoundary_embed {S : ShortComplex (AbSheaf X)} (hS : S.ShortExact)
    (h₁ : CoverAcyclic V U S.X₁) (n : ℕ)
    (x : (sheafCechComplex V U S.X₃).homology n) :
    (coverCech_shortExact (deningerInjectiveEmbedding_shortExact S.X₁) h₁).δ n (n + 1) rfl
      (Hmap (V := V) (U := U) (mapIntoInjectiveEmbedding hS).τ₃ n x) =
    (coverCech_shortExact hS h₁).δ n (n + 1) rfl x := by
  let a := (C (V := V) (U := U)).mapShortComplex.map (mapIntoInjectiveEmbedding hS)
  have he := HomologicalComplex.HomologySequence.δ_naturality a
    (coverCech_shortExact hS h₁)
    (coverCech_shortExact (deningerInjectiveEmbedding_shortExact S.X₁) h₁) n (n + 1) rfl
  have ha : a.τ₁ = 𝟙 ((C (V := V) (U := U)).obj S.X₁) :=
    (C (V := V) (U := U)).map_id S.X₁
  have haH : HomologicalComplex.homologyMap a.τ₁ (n + 1) = 𝟙 _ :=
    (congrArg (fun g => HomologicalComplex.homologyMap g (n + 1)) ha).trans
      (HomologicalComplex.homologyMap_id _ _)
  rw [haH] at he
  exact (ConcreteCategory.congr_hom he x).symm

private theorem extBoundary_embed {S : ShortComplex (AbSheaf X)} (hS : S.ShortExact)
    (W : Opens X) (n : ℕ) (z : deningerSheafCohomology.{0} W S.X₃ n) :
    (z.comp (Ext.mk₀ (mapIntoInjectiveEmbedding hS).τ₃) (add_zero n)).comp
      (deningerInjectiveEmbedding_shortExact S.X₁).extClass rfl = z.comp hS.extClass rfl := by
  rw [Ext.comp_assoc_of_second_deg_zero,
    ← hS.extClass_naturality (deningerInjectiveEmbedding_shortExact S.X₁) (mapIntoInjectiveEmbedding hS)]
  change z.comp (hS.extClass.comp (Ext.mk₀ (𝟙 _)) (add_zero 1)) rfl = _
  rw [Ext.comp_mk₀_id]

private theorem lerayCechEquiv_injective_boundary (hcov : V ≤ ⨆ i, U i) {F : AbSheaf X}
    (hF : CoverAcyclic V U F) (n : ℕ)
    (x : (sheafCechComplex V U (deningerInjectiveEmbedding F).X₃).homology n) :
    let hT := deningerInjectiveEmbedding_shortExact F
    let hQ := hF.quotient (coverAcyclic_of_injective (deningerInjectiveEmbedding F).X₂) hT
    lerayCechEquiv hcov (n + 1) F hF ((coverCech_shortExact hT hF).δ n (n + 1) rfl x) =
      (lerayCechEquiv hcov n (deningerInjectiveEmbedding F).X₃ hQ x).comp hT.extClass rfl := by
  dsimp only
  let S := deningerGodementComplex F
  let T := deningerInjectiveEmbedding F
  let hS := deningerGodementShortExact F
  let hT := deningerInjectiveEmbedding_shortExact F
  let D := coverCech_shortExact hS hF
  let E := coverCech_shortExact hT hF
  let Q : CoverAcyclic V U S.X₃ := fun a ha => godementQuotient_acyclicOn (hF a ha)
  let Q' := hF.quotient (coverAcyclic_of_injective T.X₂) hT
  let a := mapIntoInjectiveEmbedding hS
  let δ := D.δ n (n + 1) rfl
  let δ' : (sheafCechComplex V U T.X₃).homology n ⟶ (sheafCechComplex V U F).homology (n + 1) :=
    E.δ n (n + 1) rfl
  have hzero : Hmap (V := V) (U := U) S.f (n + 1) = 0 :=
    (isZero_godementCech_homology (F := F) hcov n).eq_of_tgt _ _
  obtain ⟨y, hy⟩ := (ShortComplex.ab_exact_iff _).mp (D.homology_exact₁ n (n + 1) rfl)
    (δ' x) (ConcreteCategory.congr_hom hzero (δ' x))
  change δ y = δ' x at hy
  let y' : (sheafCechComplex V U T.X₃).homology n := Hmap (V := V) (U := U) a.τ₃ n y
  have hy' : δ' y' = δ y := cechBoundary_embed hS hF n y
  have hz : δ' (x - y') = 0 :=
    (δ'.hom.map_sub x y').trans (sub_eq_zero.mpr (hy'.trans hy).symm)
  obtain ⟨z, hz'⟩ := (ShortComplex.ab_exact_iff _).mp (E.homology_exact₃ n (n + 1) rfl) (x - y') hz
  change (sheafCechComplex V U T.X₂).homology n at z
  change Hmap (V := V) (U := U) T.g n z = x - y' at hz'
  have hx : x = Hmap (V := V) (U := U) T.g n z + y' := by
    rw [hz', sub_add_cancel]
  let W := coverInter V U ∅
  let β := hT.extClass.postcomp (deningerOpenFree W) (rfl : n + 1 = n + 1)
  have he : β (lerayCechEquiv hcov n T.X₃ Q' x) =
      β (lerayCechEquiv hcov n T.X₃ Q' y') := by
    conv_lhs => rw [hx]
    rw [map_add, map_add, lerayCechEquiv_natural hcov n (coverAcyclic_of_injective T.X₂) Q' T.g]
    change ((lerayCechEquiv hcov n T.X₂ _ z).comp (Ext.mk₀ T.g) (add_zero n)).comp
      hT.extClass rfl + _ = _
    rw [Ext.comp_assoc_of_second_deg_zero, hT.comp_extClass, Ext.comp_zero, zero_add]
  change lerayCechEquiv hcov (n + 1) F hF (δ' x) = β (lerayCechEquiv hcov n T.X₃ Q' x)
  rw [he, ← show δ y = δ' x from hy]
  rw [show lerayCechEquiv hcov (n + 1) F hF (δ y) =
    (lerayCechEquiv hcov n S.X₃ Q y).comp hS.extClass rfl from
      lerayCechEquiv_godement_boundary hcov hF n y]
  change _ = (lerayCechEquiv hcov n T.X₃ Q'
    (HomologicalComplex.homologyMap (sheafCechComplexMap V U a.τ₃) n y)).comp hT.extClass rfl
  rw [lerayCechEquiv_natural hcov n Q Q' a.τ₃]
  exact (extBoundary_embed hS W n (lerayCechEquiv hcov n S.X₃ Q y)).symm

/-- The Leray comparison carries the Čech connecting map to the extension-class map. -/
theorem lerayCechEquiv_boundary (hcov : V ≤ ⨆ i, U i) {S : ShortComplex (AbSheaf X)}
    (hS : S.ShortExact) (h₁ : CoverAcyclic V U S.X₁) (h₃ : CoverAcyclic V U S.X₃)
    (n : ℕ) (x : (sheafCechComplex V U S.X₃).homology n) :
    lerayCechEquiv hcov (n + 1) S.X₁ h₁ ((coverCech_shortExact hS h₁).δ n (n + 1) rfl x) =
      (lerayCechEquiv hcov n S.X₃ h₃ x).comp hS.extClass rfl := by
  let T := deningerInjectiveEmbedding S.X₁
  let hT := deningerInjectiveEmbedding_shortExact S.X₁
  let hQ := CoverAcyclic.quotient (S := T) h₁ (coverAcyclic_of_injective T.X₂) hT
  let a := mapIntoInjectiveEmbedding hS
  rw [← cechBoundary_embed hS h₁ n x, lerayCechEquiv_injective_boundary hcov h₁]
  change (lerayCechEquiv hcov n T.X₃ hQ
    (HomologicalComplex.homologyMap (sheafCechComplexMap V U a.τ₃) n x)).comp hT.extClass rfl = _
  rw [lerayCechEquiv_natural hcov n h₃ hQ a.τ₃]
  exact extBoundary_embed hS (coverInter V U ∅) n (lerayCechEquiv hcov n S.X₃ h₃ x)

end GlobalTheory.SchemeCohomology
