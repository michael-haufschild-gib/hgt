import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.ModuleLerayFunctoriality
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.AffineModulePushforward
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.HodgeTrace

/-! Hodge pullback and trace on the relative-forms Čech complexes of
affine covers. -/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian Opposite TopologicalSpace HTGeometry

namespace GlobalTheory.SchemeCohomology

variable {k : Type} [CommRing k] {X Y : Scheme.{0}} {ι : Type} [DecidableEq ι] [LinearOrder ι]
  {s : X ⟶ Spec (CommRingCat.of k)} {t : Y ⟶ Spec (CommRingCat.of k)} {f : Y ⟶ X}

private abbrev sheafOf {X : Scheme.{0}} := SheafOfModules.toSheaf X.ringCatSheaf

local instance formsHasExt (X : Scheme.{0}) :
    HasExt.{0} (TopCat.Sheaf AddCommGrpCat.{0} X.carrier) := hasExt_of_enoughInjectives _

omit [DecidableEq ι] [LinearOrder ι] in
private theorem formsCoverAcyclic (s : X ⟶ Spec (CommRingCat.of k)) (p : ℕ)
    {U : ι → X.Opens} (hU : ∀ I : Finset ι, I.Nonempty → IsAffineOpen (coverInter ⊤ U I)) :
    CoverAcyclic ⊤ U (sheafOf.obj (relativeForms s p)) :=
  fun I hI => relativeForms_acyclicOn s p (hU I hI)

/-- Comparison of affine Čech cohomology of relative forms with Hodge cohomology. -/
def affineFormsLeray (s : X ⟶ Spec (CommRingCat.of k)) (p q : ℕ) {U : ι → X.Opens}
    (hcov : ⊤ ≤ ⨆ i, U i) (hU : ∀ I : Finset ι, I.Nonempty → IsAffineOpen (coverInter ⊤ U I)) :
    ModuleCechCohomology ⊤ U (relativeForms s p) q ≃+ HodgeCohomology s p q :=
  (moduleLerayLinearEquivAt (relativeForms s p) q hcov (coverInter_empty ⊤ U)
    (formsCoverAcyclic s p hU)).toAddEquiv

private abbrev preCov (f : Y ⟶ X) (U : ι → X.Opens) : ι → Y.Opens := fun i => f ⁻¹ᵁ U i

omit [DecidableEq ι] [LinearOrder ι] in
private theorem affine_preCov [IsAffineHom f] {U : ι → X.Opens}
    (hU : ∀ I : Finset ι, I.Nonempty → IsAffineOpen (coverInter ⊤ U I)) :
    ∀ I : Finset ι, I.Nonempty → IsAffineOpen (coverInter ⊤ (preCov f U) I) := by
  intro I hI
  exact Eq.ndrec (motive := fun O : Y.Opens => IsAffineOpen O)
    ((hU I hI).preimage f) (preimage_coverInter f.base ⊤ U I)

private abbrev FormsComplex (s : X ⟶ Spec (CommRingCat.of k)) (U : ι → X.Opens) (p : ℕ) :=
  sheafCechComplex ⊤ U (sheafOf.obj (relativeForms s p))

/-- Pullback of relative forms on the sections over each inverse-image intersection. -/
def relativeFormsCechPullback (hf : f ≫ s = t) (U : ι → X.Opens) (p : ℕ) :
    FormsComplex s U p ⟶ FormsComplex t (preCov f U) p :=
  sheafCechComplexMap ⊤ U (sheafOf.map (relativeFormsPullback hf p)) ≫
    (pushforwardCechIso f.base ⊤ U (sheafOf.obj (relativeForms t p))).hom

theorem relativeFormsCechPullback_component (hf : f ≫ s = t) (U : ι → X.Opens)
    (p q : ℕ) (x : (FormsComplex s U p).X q) (I : Finset ι) :
    ((relativeFormsCechPullback hf U p).f q x).val I =
      (pushforwardCechDatumMap f.base ⊤ U (sheafOf.obj (relativeForms t p))).app I
        ((relativeFormsPullback hf p).app (coverInter ⊤ U I) (x.val I)) :=
  rfl

/-- Trace of relative forms on the sections over each inverse-image intersection. -/
def relativeFormsCechTrace [IsFinite f] [Etale f] (hf : f ≫ s = t) (U : ι → X.Opens) (p : ℕ) :
    FormsComplex t (preCov f U) p ⟶ FormsComplex s U p :=
  (pushforwardCechIso f.base ⊤ U (sheafOf.obj (relativeForms t p))).inv ≫
    sheafCechComplexMap ⊤ U (sheafOf.map (relativeFormsTrace hf p))

theorem relativeFormsCechTrace_component [IsFinite f] [Etale f] (hf : f ≫ s = t)
    (U : ι → X.Opens) (p q : ℕ)
    (z : (sheafCechComplex ⊤ U (sheafOf.obj ((Scheme.Modules.pushforward f).obj (relativeForms t p)))).X q)
    (I : Finset ι) :
    ((relativeFormsCechTrace hf U p).f q
      ((pushforwardCechIso f.base ⊤ U (sheafOf.obj (relativeForms t p))).hom.f q z)).val I =
      (relativeFormsTrace hf p).app (coverInter ⊤ U I) (z.val I) := by
  let E := pushforwardCechIso f.base ⊤ U (sheafOf.obj (relativeForms t p))
  let Q := sheafCechComplexMap ⊤ U (sheafOf.map (relativeFormsTrace hf p))
  have hz : E.inv.f q (E.hom.f q z) = z :=
    ConcreteCategory.congr_hom (congrArg (fun ψ => ψ.f q) E.hom_inv_id) z
  exact congrArg (fun y => (Q.f q y).val I) hz

omit [DecidableEq ι] [LinearOrder ι] in
private theorem affineFormsPushforwardAcyclic [IsAffineHom f] (t : Y ⟶ Spec (CommRingCat.of k))
    (p : ℕ) {U : ι → X.Opens}
    (hU : ∀ I : Finset ι, I.Nonempty → IsAffineOpen (coverInter ⊤ U I)) :
    CoverAcyclic ⊤ U (sheafOf.obj ((Scheme.Modules.pushforward f).obj (relativeForms t p))) := by
  letI := relativeForms_isQuasicoherent t p
  letI := pushforward_isQuasicoherent f (relativeForms t p)
  exact fun I hI => quasicoherent_acyclicOn ((Scheme.Modules.pushforward f).obj (relativeForms t p)) (hU I hI)

private theorem affineFormsLeray_pushforward [IsAffineHom f] (t : Y ⟶ Spec (CommRingCat.of k))
    (p q : ℕ) {U : ι → X.Opens} (hcov : ⊤ ≤ ⨆ i, U i)
    (hU : ∀ I : Finset ι, I.Nonempty → IsAffineOpen (coverInter ⊤ U I))
    (z : ModuleCechCohomology ⊤ U ((Scheme.Modules.pushforward f).obj (relativeForms t p)) q) :
    CohomologyOn.pushforwardComparison f (relativeForms t p) ⊤ q
      (moduleLerayLinearEquivAt _ q hcov (coverInter_empty ⊤ U) (affineFormsPushforwardAcyclic t p hU) z) =
    affineFormsLeray t p q (preimage_cover_le f.base ⊤ U hcov) (affine_preCov hU)
      (HomologicalComplex.homologyMap
        (pushforwardCechIso f.base ⊤ U (sheafOf.obj (relativeForms t p))).hom q z) := by
  have hv : AcyclicOnPreimages f.base {W | IsAffineOpen W} (sheafOf.obj (relativeForms t p)) := by
    intro W hW n a
    obtain ⟨b, rfl⟩ := (deningerToOpenFreeExt (f ⁻¹ᵁ W) _ (n + 1)).surjective a
    exact (congrArg (deningerToOpenFreeExt (f ⁻¹ᵁ W) _ (n + 1))
      (relativeForms_acyclicOn t p (IsAffineOpen.preimage hW f) n b)).trans (map_zero _)
  exact moduleLerayLinearEquivAt_pushforward f X.isBasis_affineOpens hU hcov _ hv
    (affineFormsPushforwardAcyclic t p hU) (formsCoverAcyclic t p (affine_preCov hU)) q z

/-- The affine Leray comparison intertwines cochain and Hodge pullback. -/
theorem affineFormsLeray_pullback [IsAffineHom f] (hf : f ≫ s = t) (p q : ℕ)
    {U : ι → X.Opens} (hcov : ⊤ ≤ ⨆ i, U i)
    (hU : ∀ I : Finset ι, I.Nonempty → IsAffineOpen (coverInter ⊤ U I))
    (x : ModuleCechCohomology ⊤ U (relativeForms s p) q) :
    affineFormsLeray t p q (preimage_cover_le f.base ⊤ U hcov) (affine_preCov hU)
      (HomologicalComplex.homologyMap (relativeFormsCechPullback hf U p) q x) =
      hodgePullback hf p q (affineFormsLeray s p q hcov hU x) := by
  let φ := relativeFormsPullback hf p
  let P := CohomologyOn.pushforwardComparison f (relativeForms t p) ⊤ q
  let C := sheafCechComplexMap ⊤ U (sheafOf.map φ)
  let E := pushforwardCechIso f.base ⊤ U (sheafOf.obj (relativeForms t p))
  have hm := ConcreteCategory.congr_hom (HomologicalComplex.homologyMap_comp C E.hom q) x
  have hp := affineFormsLeray_pushforward t p q hcov hU (HomologicalComplex.homologyMap C q x)
  have hn := moduleLerayLinearEquivAt_natural φ q hcov (coverInter_empty ⊤ U)
    (formsCoverAcyclic s p hU) (affineFormsPushforwardAcyclic t p hU) x
  exact (congrArg (affineFormsLeray t p q (preimage_cover_le f.base ⊤ U hcov) (affine_preCov hU)) hm).trans
    (hp.symm.trans (congrArg P hn))

/-- The affine Leray comparison intertwines cochain and Hodge trace. -/
theorem affineFormsLeray_trace [IsFinite f] [Etale f] (hf : f ≫ s = t) (p q : ℕ)
    {U : ι → X.Opens} (hcov : ⊤ ≤ ⨆ i, U i)
    (hU : ∀ I : Finset ι, I.Nonempty → IsAffineOpen (coverInter ⊤ U I))
    (x : ModuleCechCohomology ⊤ (preCov f U) (relativeForms t p) q) :
    affineFormsLeray s p q hcov hU
      (HomologicalComplex.homologyMap (relativeFormsCechTrace hf U p) q x) =
      hodgeTrace hf p q (affineFormsLeray t p q (preimage_cover_le f.base ⊤ U hcov) (affine_preCov hU) x) := by
  let φ := relativeFormsTrace hf p
  let C := sheafCechComplexMap ⊤ U (sheafOf.map φ)
  let E := pushforwardCechIso f.base ⊤ U (sheafOf.obj (relativeForms t p))
  let y := HomologicalComplex.homologyMap E.inv q x
  have hm := ConcreteCategory.congr_hom (HomologicalComplex.homologyMap_comp E.inv C q) x
  have hi : HomologicalComplex.homologyMap E.hom q y = x := by
    have hh : HomologicalComplex.homologyMap (E.inv ≫ E.hom) q = 𝟙 _ := by
      rw [E.inv_hom_id, HomologicalComplex.homologyMap_id]
    exact (ConcreteCategory.congr_hom (HomologicalComplex.homologyMap_comp E.inv E.hom q) x).symm.trans
      (ConcreteCategory.congr_hom hh x)
  have hp := affineFormsLeray_pushforward t p q hcov hU y
  let e := formsPushforwardEquiv hf p q
  have h := hp.trans (congrArg
    (affineFormsLeray t p q (preimage_cover_le f.base ⊤ U hcov) (affine_preCov hU)) hi)
  have h' := (congrArg e.symm h).symm.trans (e.symm_apply_apply _)
  have hn := moduleLerayLinearEquivAt_natural φ q hcov (coverInter_empty ⊤ U)
    (affineFormsPushforwardAcyclic t p hU) (formsCoverAcyclic s p hU) y
  exact (congrArg (affineFormsLeray s p q hcov hU) hm).trans
    (hn.trans (congrArg (CohomologyOn.map φ ⊤ q) h'.symm))

end GlobalTheory.SchemeCohomology
