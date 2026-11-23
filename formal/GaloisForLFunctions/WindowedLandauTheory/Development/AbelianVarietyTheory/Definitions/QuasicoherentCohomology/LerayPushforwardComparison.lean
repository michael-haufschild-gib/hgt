import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.LerayOpenFreeComparison
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.PushforwardCechComplex
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.PushforwardComparison

/-! The Leray comparison commutes with inverse-image covers and direct image. -/

noncomputable section

open CategoryTheory CategoryTheory.Abelian Opposite TopologicalSpace HTGeometry RHTower

namespace GlobalTheory.SchemeCohomology

private abbrev AbSheaf (X : TopCat.{0}) := TopCat.Sheaf AddCommGrpCat.{0} X

variable {X Y : TopCat.{0}} (f : Y ⟶ X) {ι : Type} [DecidableEq ι] [LinearOrder ι]
  {V : Opens X} {U : ι → Opens X} {B : Set (Opens X)}

local instance lerayPushHasExt (Z : TopCat.{0}) : HasExt.{0} (AbSheaf Z) :=
  hasExt_of_enoughInjectives _

private abbrev Push := TopCat.Sheaf.pushforward AddCommGrpCat.{0} f
private abbrev pre (W : Opens X) := (Opens.map f).obj W
private abbrev UV := pre f ∘ U

local instance lerayPushAdditive : (Push f).Additive where
  map_add := rfl

variable (hB : Opens.IsBasis B)
  (hU : ∀ (I : Finset ι), I.Nonempty → coverInter V U I ∈ B)

include hU in
omit [DecidableEq ι] [LinearOrder ι] in
private theorem coverAcyclic_inverseImages {G : AbSheaf Y} (hG : AcyclicOnPreimages f B G) :
    CoverAcyclic (pre f V) (UV (U := U) f) G := by
  intro I hI n x
  let W := coverInter (pre f V) (UV (U := U) f) I
  have hvan : ∀ z : Ext (openFree W) G (n + 1), z = 0 :=
    Eq.ndrec (motive := fun W : Opens Y => ∀ z : Ext (openFree W) G (n + 1), z = 0)
      (hG _ (hU I hI) n) (preimage_coverInter f V U I)
  apply (deningerToOpenFreeExt W G (n + 1)).injective
  rw [map_zero]
  exact hvan _

include hB hU in
omit [DecidableEq ι] [LinearOrder ι] in
private theorem coverAcyclic_directImage {G : AbSheaf Y} (hG : AcyclicOnPreimages f B G) :
    CoverAcyclic V U ((Push f).obj G) := by
  intro I hI n x
  let W := coverInter V U I
  apply (deningerToOpenFreeExt W ((Push f).obj G) (n + 1)).injective
  rw [map_zero]
  apply (abelianPushforwardComparison_bijective f hB G hG W (n + 1)).injective
  rw [map_zero]
  exact hG W (hU I hI) n _

variable (hcov : V ≤ ⨆ i, U i)

private abbrev W := coverInter V U (∅ : Finset ι)

private abbrev pushCechH (G : AbSheaf Y) (n : ℕ) :=
  HomologicalComplex.homologyMap (pushforwardCechIso f V U G).hom n

/-- Čech comparison with Ext intertwines the direct-image comparison. -/
theorem lerayOpenFreeEquiv_pushforward (G : AbSheaf Y) (hG : AcyclicOnPreimages f B G) (n : ℕ)
    (x : (sheafCechComplex V U ((Push f).obj G)).homology n) :
    abelianPushforwardComparison f G (W (V := V) (U := U)) n
      (lerayOpenFreeEquiv hcov rfl ((Push f).obj G)
        (coverAcyclic_directImage f hB hU hG) n x) =
    lerayOpenFreeEquiv (preimage_cover_le f V U hcov) (preimage_coverInter f V U ∅).symm G
        (coverAcyclic_inverseImages f hU hG) n (pushCechH (V := V) (U := U) f G n x) := by
  let preCov := preimage_cover_le f V U hcov
  let W₀ := W (V := V) (U := U)
  let eW := preimage_coverInter f V U (∅ : Finset ι)
  induction n generalizing G with
  | zero =>
    obtain ⟨z, rfl⟩ := (sectionsToCechH0 ((Push f).obj G) hcov).surjective x
    let a := pushforwardCechDatumMap f V U G
    have hz := sectionsToCechH0_natural_datum ((Push f).obj G) G hcov preCov a z
    rw [show pushCechH (V := V) (U := U) f G 0
      (sectionsToCechH0 ((Push f).obj G) hcov z) =
      sectionsToCechH0 G preCov (a.app ∅ z) from hz]
    rw [lerayOpenFreeEquiv_zero, lerayOpenFreeEquiv_zero]
    simp only [eqToHom_refl, op_id]
    let left (w : ((Push f).obj G).1.obj (op W₀)) :=
      abelianPushforwardComparison f G W₀ 0 (Ext.mk₀ ((openFreeHomEquiv W₀ ((Push f).obj G)).symm w))
    let right (w : G.1.obj (op (pre f W₀))) := Ext.mk₀ ((openFreeHomEquiv (pre f W₀) G).symm w)
    have hleft := ConcreteCategory.congr_hom (((Push f).obj G).1.map_id (op W₀)) z
    let p := (eqToHom eW.symm).op
    let q := (eqToHom eW).op
    have hpq : p ≫ q = 𝟙 (op (pre f W₀)) := Subsingleton.elim _ _
    have hright : G.1.map q (G.1.map p z) = z :=
      (ConcreteCategory.congr_hom (G.1.map_comp p q) z).symm.trans
        ((ConcreteCategory.congr_hom (congrArg G.1.map hpq) z).trans
          (ConcreteCategory.congr_hom (G.1.map_id (op (pre f W₀))) z))
    exact (congrArg left hleft).trans
      ((abelianPushforwardComparison_zero_section f G W₀ z).trans (congrArg right hright).symm)
  | succ n ih =>
    let S := deningerInjectiveEmbedding G
    let hS := deningerInjectiveEmbedding_shortExact G
    let T := S.map (Push f)
    let hT := abelianPushforward_shortExact_of_acyclic f hB hS hG
    letI : Injective S.X₂ := CategoryTheory.Injective.injective_under G
    letI : Injective T.X₂ := injective_abelianPushforward f S.X₂
    let hQ := AcyclicOnPreimages.quotient_injective f hG hS
    let hC := coverCech_shortExact hT (coverAcyclic_directImage f hB hU hG)
    let hD := coverCech_shortExact hS (coverAcyclic_inverseImages f hU hG)
    have hz : HomologicalComplex.homologyMap (sheafCechComplexMap V U T.f) (n + 1) x = 0 := by
      let e := lerayOpenFreeEquiv hcov rfl T.X₂ (coverAcyclic_of_injective T.X₂) (n + 1)
      apply e.injective
      rw [map_zero]
      exact Ext.eq_zero_of_injective _
    obtain ⟨z, hz'⟩ := (ShortComplex.ab_exact_iff _).mp (hC.homology_exact₁ n (n + 1) rfl) x hz
    change (sheafCechComplex V U T.X₃).homology n at z
    change hC.δ n (n + 1) rfl z = x at hz'
    rw [← hz']
    let a := S.mapNatTrans (pushforwardCechFunctorIso f V U).hom
    have hδ : pushCechH (V := V) (U := U) f G (n + 1) (hC.δ n (n + 1) rfl z) =
        hD.δ n (n + 1) rfl (pushCechH (V := V) (U := U) f S.X₃ n z) :=
      ConcreteCategory.congr_hom (HomologicalComplex.HomologySequence.δ_naturality
        a hC hD n (n + 1) rfl) z
    let y := pushCechH (V := V) (U := U) f S.X₃ n z
    let w := lerayOpenFreeEquiv hcov rfl T.X₃ (coverAcyclic_directImage f hB hU hQ) n z
    have hleft := lerayOpenFreeEquiv_boundary hcov rfl hT (coverAcyclic_directImage f hB hU hG)
      (coverAcyclic_directImage f hB hU hQ) n z
    have hright := lerayOpenFreeEquiv_boundary preCov eW.symm hS
      (coverAcyclic_inverseImages f hU hG) (coverAcyclic_inverseImages f hU hQ) n y
    calc
      _ = abelianPushforwardComparison f S.X₁ W₀ (n + 1) (w.comp hT.extClass rfl) :=
        congrArg (abelianPushforwardComparison f S.X₁ W₀ (n + 1)) hleft
      _ = (abelianPushforwardComparison f S.X₃ W₀ n w).comp hS.extClass rfl :=
        abelianPushforwardComparison_boundary f hS hT W₀ n w
      _ = (lerayOpenFreeEquiv preCov eW.symm S.X₃
          (coverAcyclic_inverseImages f hU hQ) n y).comp hS.extClass rfl :=
        congrArg (fun a : Ext (openFree (pre f W₀)) S.X₃ n => a.comp hS.extClass rfl) (ih S.X₃ hQ z)
      _ = lerayOpenFreeEquiv preCov eW.symm S.X₁
          (coverAcyclic_inverseImages f hU hG) (n + 1) (hD.δ n (n + 1) rfl y) :=
        hright.symm
      _ = _ := congrArg (lerayOpenFreeEquiv preCov eW.symm S.X₁
        (coverAcyclic_inverseImages f hU hG) (n + 1)) hδ.symm

end GlobalTheory.SchemeCohomology
