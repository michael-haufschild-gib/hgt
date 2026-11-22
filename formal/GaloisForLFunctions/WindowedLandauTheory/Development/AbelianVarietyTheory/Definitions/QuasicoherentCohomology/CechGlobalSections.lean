import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.FiniteCechComplex
import GaloisForLFunctions.HTGeometry.SheafFinsetCech

/-! Degree-zero alternating Čech cocycles are the sections on the covered open. -/

noncomputable section

open CategoryTheory TopologicalSpace Opposite HTGeometry RHTower
open GaloisForLFunctions.HTGeometry.BorelWeil

namespace GlobalTheory.SchemeCohomology

universe u

variable {X : TopCat.{u}} {ι : Type u} [DecidableEq ι] [LinearOrder ι]
  {V : Opens X} {U : ι → Opens X} (F : TopCat.Sheaf AddCommGrpCat.{u} X)

omit [LinearOrder ι] in
private theorem pairIntersection (i j : ι) :
    coverInter V U {i, j} = coverInter V U {i} ⊓ coverInter V U {j} := by
  simp [coverInter, inf_left_comm, inf_comm]

/-- Compatible local sections glue, expressed as exactness of the augmented complex in degree zero. -/
theorem sheafCech_exactAt_zero (hcov : V ≤ ⨆ i, U i) : (sheafCech F V U).ExactAt 0 := by
  let D := sheafCech F V U
  intro c hc hdc
  let W (i : ι) := coverInter V U {i}
  have hWV (i : ι) : W i ≤ coverInter V U ∅ := coverInter_anti (Finset.empty_subset _)
  have hcover : coverInter V U ∅ ≤ ⨆ i, W i := by
    intro x hx
    have hxV := (mem_coverInter.mp hx).1
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (hcov hxV)
    refine Opens.mem_iSup.mpr ⟨i, mem_coverInter.mpr ⟨hxV, fun j hj => ?_⟩⟩
    rwa [Finset.mem_singleton.mp hj]
  have hpair (i j : ι) (hij : i < j) :
      deningerRes F (inf_le_left : W i ⊓ W j ≤ W i) (c {i}) =
        deningerRes F (inf_le_right : W i ⊓ W j ≤ W j) (c {j}) := by
    have e₁ : ({i, j} : Finset ι).erase i = {j} := by simp [hij.ne]
    have e₂ : ({i, j} : Finset ι).erase j = {i} := by
      ext x
      simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨hne, rfl | rfl⟩
        · rfl
        · exact (hne rfl).elim
      · rintro rfl
        exact ⟨hij.ne, Or.inl rfl⟩
    have h₁ : ({j} : Finset ι) ⊆ {i, j} := by simp
    have h₂ : ({i} : Finset ι) ⊆ {i, j} := by simp
    have f₁ : ({i, j} : Finset ι).filter (· < i) = ∅ := by
      ext t
      simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty, iff_false]
      rintro ⟨rfl | rfl, he⟩
      · exact lt_irrefl _ he
      · exact not_lt_of_ge hij.le he
    have f₂ : ({i, j} : Finset ι).filter (· < j) = {i} := by
      ext t
      simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
      exact ⟨fun ⟨ht, hlt⟩ => ht.resolve_right (fun e => (lt_irrefl j) (e ▸ hlt)),
        fun ht => ⟨Or.inl ht, ht.symm ▸ hij⟩⟩
    have hs₁ : (cechSign ({i, j} : Finset ι) i : ℤ) = 1 := by simp [cechSign, belowCard, f₁]
    have hs₂ : (cechSign ({i, j} : Finset ι) j : ℤ) = -1 := by simp [cechSign, belowCard, f₂]
    have h := congrFun hdc {i, j}
    change D.d c {i, j} = 0 at h
    rw [FinsetCechDatum.d, Finset.sum_pair hij.ne,
      FinsetCechDatum.res_cochain_congr c e₁ _ h₁, FinsetCechDatum.res_cochain_congr c e₂ _ h₂,
      hs₁, hs₂, one_zsmul, neg_one_zsmul, ← sub_eq_add_neg, sub_eq_zero] at h
    have he : W i ⊓ W j ≤ coverInter V U {i, j} := (pairIntersection i j).ge
    have hh := congrArg (deningerRes F he) h.symm
    change deningerRes F he (deningerRes F (coverInter_anti h₂) (c {i})) =
      deningerRes F he (deningerRes F (coverInter_anti h₁) (c {j})) at hh
    simpa only [deningerRes_res] using hh
  have hcompatible (i j : ι) :
      deningerRes F (inf_le_left : W i ⊓ W j ≤ W i) (c {i}) =
        deningerRes F (inf_le_right : W i ⊓ W j ≤ W j) (c {j}) := by
    rcases lt_trichotomy i j with h | rfl | h
    · exact hpair i j h
    · rfl
    · have e : W i ⊓ W j ≤ W j ⊓ W i := (inf_comm _ _).le
      have hh := congrArg (deningerRes F e) (hpair j i h).symm
      simpa only [deningerRes_res] using hh
  obtain ⟨z, hz⟩ := deningerGlue (F := F) hWV hcover (fun i => c {i}) hcompatible
  let b : D.Cochain := fun a => if e : a = ∅ then e.symm ▸ z else 0
  have hb : D.IsBot b := fun a ha => dif_neg ha.ne_empty
  refine ⟨b, fun a ha => hb a (Finset.card_pos.mp (Nat.pos_of_ne_zero ha)), funext fun a => ?_⟩
  by_cases ha : a.card = 1
  · obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp ha
    change D.d b {i} = c {i}
    rw [FinsetCechDatum.d, Finset.sum_singleton,
      FinsetCechDatum.res_cochain_congr b (Finset.erase_singleton i) _ (Finset.empty_subset _)]
    have hs : (cechSign ({i} : Finset ι) i : ℤ) = 1 := by
      simp [cechSign, belowCard, Finset.filter_singleton]
    rw [hs, one_zsmul]
    exact hz i
  · exact ((D.d_isDeg_of_isBot hb) a ha).trans (hc a ha).symm

private def augment {ι : Type u} [DecidableEq ι] [LinearOrder ι]
    (D : FinsetCechDatum.{u} ι) (z : D.obj ∅) : D.Cochain :=
  fun a => if e : a = ∅ then e.symm ▸ z else 0

private theorem augment_isBot {ι : Type u} [DecidableEq ι] [LinearOrder ι]
    (D : FinsetCechDatum.{u} ι) (z : D.obj ∅) : D.IsBot (augment D z) :=
  fun _ ha => dif_neg ha.ne_empty

private theorem augment_at_empty {ι : Type u} [DecidableEq ι] [LinearOrder ι]
    (D : FinsetCechDatum.{u} ι) (z : D.obj ∅) : augment D z ∅ = z := dif_pos rfl

private def augDiff {ι : Type u} [DecidableEq ι] [LinearOrder ι] (D : FinsetCechDatum.{u} ι) :
    AddCommGrpCat.of (D.obj ∅) ⟶ D.cochainComplex.X 0 :=
  AddCommGrpCat.ofHom
    { toFun := fun z => ⟨D.d (augment D z), D.d_isDeg_of_isBot (augment_isBot D z)⟩
      map_zero' := by
        apply Subtype.ext
        have h : augment D 0 = 0 := by
          funext a
          by_cases ha : a = ∅
          · subst a
            exact augment_at_empty D 0
          · exact dif_neg ha
        exact (congrArg D.d h).trans D.d_zero
      map_add' := fun z z' => by
        apply Subtype.ext
        have h : augment D (z + z') = augment D z + augment D z' := by
          funext a
          by_cases ha : a = ∅
          · subst a
            simp only [Pi.add_apply, augment_at_empty]
          · simp [augment, ha]
        exact (congrArg D.d h).trans (D.d_add _ _) }

private def augCycles {ι : Type u} [DecidableEq ι] [LinearOrder ι] (D : FinsetCechDatum.{u} ι) :
    AddCommGrpCat.of (D.obj ∅) ⟶ D.cochainComplex.cycles 0 :=
  D.cochainComplex.liftCycles' (augDiff D) 1 rfl (by
    apply AddCommGrpCat.ext
    intro z
    change D.cochainComplex.d 0 1 ⟨D.d (augment D z), _⟩ = 0
    rw [FinsetCechDatum.cochainComplex_d_apply]
    exact Subtype.ext (D.d_d (augment D z)))

private theorem augCycles_i {ι : Type u} [DecidableEq ι] [LinearOrder ι] (D : FinsetCechDatum.{u} ι) :
    augCycles D ≫ D.cochainComplex.iCycles 0 = augDiff D := by
  rw [augCycles, HomologicalComplex.liftCycles_i]

private theorem augCycles_bijective (hcov : V ≤ ⨆ i, U i) :
    Function.Bijective (augCycles (sheafCech F V U)) := by
  let D := sheafCech F V U
  let K := D.cochainComplex
  have haug (z : D.obj ∅) :
      K.iCycles 0 (augCycles D z) = (⟨D.d (augment D z), _⟩ : D.degreeCochains 0) :=
    ConcreteCategory.congr_hom (augCycles_i D) z
  constructor
  · intro z z' h
    have hh := congrArg (fun y => K.iCycles 0 y) h
    rw [haug, haug] at hh
    have hd : D.d (augment D z) = D.d (augment D z') := congrArg Subtype.val hh
    have he : augment D z - augment D z' = 0 := by
      apply sheafCech_exactBot F hcov
      · intro a ha
        change augment D z a - augment D z' a = 0
        rw [augment_isBot D z a ha, augment_isBot D z' a ha, sub_zero]
      · change D.d (augment D z - augment D z') = 0
        rw [D.d_sub, hd, sub_self]
    have hz := congrFun he ∅
    change augment D z ∅ - augment D z' ∅ = 0 at hz
    rwa [augment_at_empty, augment_at_empty, sub_eq_zero] at hz
  · intro y
    let c : D.degreeCochains 0 := K.iCycles 0 y
    have hd : D.d c.1 = 0 := by
      have h := ConcreteCategory.congr_hom (K.iCycles_d 0 1) y
      change K.d 0 1 c = 0 at h
      rw [FinsetCechDatum.cochainComplex_d_apply] at h
      exact congrArg Subtype.val h
    obtain ⟨b, hb, e⟩ := sheafCech_exactAt_zero F hcov c.1 c.2 hd
    have hb' : augment D (b ∅) = b := by
      funext a
      by_cases ha : a = ∅
      · subst a
        exact augment_at_empty D (b ∅)
      · rw [augment, dif_neg ha, hb a (Finset.card_ne_zero.mpr (Finset.nonempty_iff_ne_empty.mpr ha))]
    refine ⟨b ∅, (AddCommGrpCat.mono_iff_injective (K.iCycles 0)).mp inferInstance ?_⟩
    rw [haug]
    exact Subtype.ext ((congrArg D.d hb').trans e)

/-- A section represents its family of restrictions in degree-zero Čech cohomology. -/
def sectionsToCechH0 (hcov : V ≤ ⨆ i, U i) :
    (sheafCech F V U).obj ∅ ≃+ (sheafCech F V U).cochainComplex.homology 0 :=
  (AddEquiv.ofBijective (augCycles (sheafCech F V U)).hom (augCycles_bijective F hcov)).trans
    ((sheafCech F V U).cochainComplex.isoHomologyπ₀.addCommGroupIsoToAddEquiv)

private theorem augDiff_natural {ι : Type u} [DecidableEq ι] [LinearOrder ι]
    {D E : FinsetCechDatum.{u} ι} (φ : D.Hom E) :
    augDiff D ≫ φ.cochainMap.f 0 = AddCommGrpCat.ofHom (φ.app ∅) ≫ augDiff E := by
  apply AddCommGrpCat.ext
  intro z
  apply Subtype.ext
  change φ.onCochain (D.d (augment D z)) = E.d (augment E (φ.app ∅ z))
  rw [← φ.d_onCochain]
  congr 1
  funext a
  by_cases ha : a = ∅
  · subst a
    exact congrArg (φ.app ∅) (augment_at_empty D z) |>.trans (augment_at_empty E _).symm
  · simp [FinsetCechDatum.Hom.onCochain, augment, ha]

private theorem augCycles_natural {ι : Type u} [DecidableEq ι] [LinearOrder ι]
    {D E : FinsetCechDatum.{u} ι} (φ : D.Hom E) :
    augCycles D ≫ HomologicalComplex.cyclesMap φ.cochainMap 0 =
      AddCommGrpCat.ofHom (φ.app ∅) ≫ augCycles E := by
  apply (cancel_mono (E.cochainComplex.iCycles 0)).mp
  calc
    _ = (augCycles D ≫ D.cochainComplex.iCycles 0) ≫ φ.cochainMap.f 0 := by
      rw [Category.assoc, HomologicalComplex.cyclesMap_i, Category.assoc]
    _ = AddCommGrpCat.ofHom (φ.app ∅) ≫ augDiff E := by
      rw [augCycles_i, augDiff_natural]
    _ = _ := by rw [Category.assoc, augCycles_i]

theorem sectionsToCechH0_natural {G : TopCat.Sheaf AddCommGrpCat.{u} X}
    (φ : F ⟶ G) (hcov : V ≤ ⨆ i, U i) (z : (sheafCech F V U).obj ∅) :
    HomologicalComplex.homologyMap (sheafCechMap φ V U).cochainMap 0 (sectionsToCechH0 F hcov z) =
      sectionsToCechH0 G hcov ((sheafCechMap φ V U).app ∅ z) := by
  let D := sheafCech F V U
  let E := sheafCech G V U
  let a := sheafCechMap φ V U
  have h : augCycles D ≫ D.cochainComplex.homologyπ 0 ≫ HomologicalComplex.homologyMap a.cochainMap 0 =
      AddCommGrpCat.ofHom (a.app ∅) ≫ augCycles E ≫ E.cochainComplex.homologyπ 0 := by
    rw [HomologicalComplex.homologyπ_naturality, ← Category.assoc, augCycles_natural, Category.assoc]
  exact ConcreteCategory.congr_hom h z

end GlobalTheory.SchemeCohomology
