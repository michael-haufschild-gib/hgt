import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.FlatLineBundleCech
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.CechGlobalSections

/-! Degree-zero cocycles of the scalar-linear Čech complex are global sections. -/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace HTGeometry
open GaloisForLFunctions.HTGeometry.BorelWeil

namespace GlobalTheory.LineBundleSections

variable {R : Type} [CommRing R] {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of R))
  (F : X.Modules) {ι : Type} [DecidableEq ι] [LinearOrder ι] (U : ι → X.Opens)

private abbrev D := sectionDatum F U
private abbrev C := cech f F U

private def augment (a : (D F U).obj ∅) : (D F U).Cochain :=
  fun s => if e : s = ∅ then e.symm ▸ a else 0

private theorem augment_isBot (a : (D F U).obj ∅) :
    (D F U).IsBot (augment F U a) :=
  fun _ hs => dif_neg hs.ne_empty

private def restrictToCocycle (a : (D F U).obj ∅) :
    LinearMap.ker ((C f F U).d 0 1).hom :=
  ⟨⟨(D F U).d (augment F U a), (D F U).d_isDeg_of_isBot (augment_isBot F U a)⟩, by
    change ((C f F U).d 0 1).hom _ = 0
    simp only [C, cech, FinsetCechDatum.linearComplex]
    exact Subtype.ext ((D F U).d_d (augment F U a))⟩

private theorem restrictToCocycle_bijective (hc : ⊤ ≤ ⨆ i, U i) :
    Function.Bijective (restrictToCocycle f F U) := by
  let G := (SheafOfModules.toSheaf X.ringCatSheaf).obj F
  constructor
  · intro a b h
    have e : (D F U).d (augment F U a) = (D F U).d (augment F U b) :=
      congrArg (fun z : LinearMap.ker ((C f F U).d 0 1).hom => z.1.1) h
    have hz : augment F U a - augment F U b = 0 := by
      apply sheafCech_exactBot G hc
      · intro s hs
        change augment F U a s - augment F U b s = 0
        rw [augment_isBot F U a s hs, augment_isBot F U b s hs, sub_self]
      · rw [FinsetCechDatum.d_sub, e, sub_self]
    have he := congrFun hz ∅
    change augment F U a ∅ - augment F U b ∅ = 0 at he
    have h₀ (x : (D F U).obj ∅) : augment F U x ∅ = x := dif_pos rfl
    rwa [h₀, h₀, sub_eq_zero] at he
  · intro y
    have hy : (D F U).d y.1.1 = 0 := by
      have h : ((C f F U).d 0 1).hom y.1 = 0 := y.2
      simp only [C, cech, FinsetCechDatum.linearComplex] at h
      exact congrArg Subtype.val h
    obtain ⟨b, hb, hby⟩ := GlobalTheory.SchemeCohomology.sheafCech_exactAt_zero G hc
      y.1.1 y.1.2 hy
    have he : augment F U (b ∅) = b := by
      funext s
      by_cases hs : s = ∅
      · subst s
        exact dif_pos rfl
      · rw [augment, dif_neg hs, hb s (Finset.card_ne_zero.mpr (Finset.nonempty_iff_ne_empty.mpr hs))]
    refine ⟨b ∅, Subtype.ext (Subtype.ext ?_)⟩
    exact (congrArg (D F U).d he).trans hby

/-- Each cocycle in degree zero is the family of restrictions of a unique global section. -/
def sectionsEquivKernel (hc : ⊤ ≤ ⨆ i, U i) :
    (D F U).obj ∅ ≃ LinearMap.ker ((C f F U).d 0 1).hom :=
  Equiv.ofBijective (restrictToCocycle f F U) (restrictToCocycle_bijective f F U hc)

theorem sectionsEquivKernel_singleton (hc : ⊤ ≤ ⨆ i, U i) (a : (D F U).obj ∅) (i : ι) :
    (sectionsEquivKernel f F U hc a).1.1 {i} =
      (D F U).res (Finset.empty_subset {i}) a := by
  change (D F U).d (augment F U a) {i} = _
  rw [FinsetCechDatum.d, Finset.sum_singleton,
    (D F U).res_cochain_congr (augment F U a) (Finset.erase_singleton i) _
      (Finset.empty_subset {i}), augment, dif_pos rfl]
  have hsign : (cechSign ({i} : Finset ι) i : ℤ) = 1 := by
    simp [cechSign, belowCard, Finset.filter_singleton]
  rw [hsign, one_smul]

/-- Use global sections as the augmentation of a covering of the whole scheme. -/
def globalSectionsEquivKernel (hc : ⊤ ≤ ⨆ i, U i) :
    Γ(F, ⊤) ≃ LinearMap.ker ((C f F U).d 0 1).hom := by
  let E := coverInter ⊤ U ∅
  let e : E ⟶ (⊤ : X.Opens) := homOfLE le_top
  haveI : IsIso e :=
    ⟨⟨homOfLE (coverInter_empty ⊤ U).ge, Subsingleton.elim _ _, Subsingleton.elim _ _⟩⟩
  exact (Equiv.ofBijective (F.presheaf.map e.op)
    (ConcreteCategory.bijective_of_isIso (F.presheaf.map e.op))).trans
    (sectionsEquivKernel f F U hc)

theorem globalSectionsEquivKernel_singleton (hc : ⊤ ≤ ⨆ i, U i) (a : Γ(F, ⊤)) (i : ι) :
    (globalSectionsEquivKernel f F U hc a).1.1 {i} =
      F.presheaf.map (homOfLE (le_top : coverInter ⊤ U {i} ≤ ⊤)).op a := by
  change (sectionsEquivKernel f F U hc (F.presheaf.map (homOfLE le_top).op a)).1.1 {i} = _
  rw [sectionsEquivKernel_singleton]
  let k : coverInter ⊤ U {i} ⟶ coverInter ⊤ U ∅ := homOfLE (coverInter_anti (Finset.empty_subset {i}))
  change F.presheaf.map k.op (F.presheaf.map (homOfLE le_top).op a) = _
  rw [← ConcreteCategory.comp_apply, ← F.presheaf.map_comp]
  rfl

end GlobalTheory.LineBundleSections
