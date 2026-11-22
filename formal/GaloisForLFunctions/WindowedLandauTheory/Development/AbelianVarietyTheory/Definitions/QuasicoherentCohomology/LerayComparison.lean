import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.GodementCechComparison
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.CechGlobalSections

/-! The Čech and sheaf cohomology connecting maps compare the two cohomologies on a Leray cover. -/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite TopologicalSpace
  HTGeometry RHTower

namespace GlobalTheory.SchemeCohomology

universe u w

variable {X : TopCat.{u}} [HasExt.{w} (TopCat.Sheaf AddCommGrpCat.{u} X)]
  {ι : Type u} [LinearOrder ι] [DecidableEq ι] {V : Opens X} {U : ι → Opens X}

private def sectionEquiv (W : Opens X) (F : TopCat.Sheaf AddCommGrpCat.{u} X) :
    (deningerOpenFree W ⟶ F) ≃+ F.1.obj (op W) :=
  { deningerOpenFreeHomEquiv W F with
    map_add' := fun f g => by
      let z := deningerOpenFreeHomEquiv W (deningerOpenFree W) (𝟙 _)
      have e (h : deningerOpenFree W ⟶ F) :
          deningerOpenFreeHomEquiv W F h = h.1.app (op W) z := by
        simpa only [Category.id_comp] using
          deningerOpenFreeHomEquiv_naturality_right W h (𝟙 _)
      change deningerOpenFreeHomEquiv W F (f + g) =
        deningerOpenFreeHomEquiv W F f + deningerOpenFreeHomEquiv W F g
      rw [e, e, e]
      rfl }

private def extZeroSections (W : Opens X) (F : TopCat.Sheaf AddCommGrpCat.{u} X) :
    deningerSheafCohomology.{w} W F 0 ≃+ F.1.obj (op W) :=
  Ext.addEquiv₀.trans (sectionEquiv W F)

private theorem extZeroSections_natural (W : Opens X) {F G : TopCat.Sheaf AddCommGrpCat.{u} X}
    (φ : F ⟶ G) (x : deningerSheafCohomology.{w} W F 0) :
    extZeroSections W G (x.comp (Ext.mk₀ φ) rfl) = φ.1.app (op W) (extZeroSections W F x) := by
  obtain ⟨f, rfl⟩ := Ext.addEquiv₀.symm.surjective x
  change sectionEquiv W G (Ext.addEquiv₀ ((Ext.mk₀ f).comp (Ext.mk₀ φ) rfl)) =
    φ.1.app (op W) (sectionEquiv W F (Ext.addEquiv₀ (Ext.mk₀ f)))
  rw [Ext.mk₀_comp_mk₀, deningerExt_addEquiv₀_mk₀, deningerExt_addEquiv₀_mk₀]
  exact deningerOpenFreeHomEquiv_naturality_right W φ f

private theorem toExtZero_natural (W : Opens X) {F G : TopCat.Sheaf AddCommGrpCat.{u} X}
    (φ : F ⟶ G) (s : F.1.obj (op W)) :
    (extZeroSections W G).symm (φ.1.app (op W) s) =
      ((extZeroSections W F).symm s).comp (Ext.mk₀ φ) rfl := by
  apply (extZeroSections W G).injective
  rw [AddEquiv.apply_symm_apply, extZeroSections_natural, AddEquiv.apply_symm_apply]

section FirstDegree

variable {F : TopCat.Sheaf AddCommGrpCat.{u} X} (hcov : V ≤ ⨆ i, U i)
  (hF : ∀ a : Finset ι, a.Nonempty → DeningerAcyclicOn.{w} F (coverInter V U a))

local notation "W₀" => coverInter V U ∅
local notation "S" => deningerGodementComplex F
local notation "SČ" => godementCechSequence V U F

private def cechOneProj :
    (sheafCech (S).X₃ V U).obj ∅ →+ (sheafCechComplex V U F).homology 1 :=
  ((godementCech_shortExact hF).δ 0 1 rfl).hom.comp
    (sectionsToCechH0 (S).X₃ hcov).toAddMonoidHom

private theorem cechOneProj_surjective : Function.Surjective (cechOneProj hcov hF) := by
  have hC := godementCech_shortExact hF
  have hmono : HomologicalComplex.homologyMap (SČ).f 1 = 0 :=
    (isZero_godementCech_homology (F := F) hcov 0).eq_of_tgt _ _
  intro x
  have h : HomologicalComplex.homologyMap (SČ).f 1 x = 0 := by rw [hmono]; rfl
  obtain ⟨y, hy⟩ := (ShortComplex.ab_exact_iff _).mp (hC.homology_exact₁ 0 1 rfl) x h
  refine ⟨(sectionsToCechH0 (S).X₃ hcov).symm y, ?_⟩
  change hC.δ 0 1 rfl ((sectionsToCechH0 (S).X₃ hcov)
    ((sectionsToCechH0 (S).X₃ hcov).symm y)) = x
  rw [AddEquiv.apply_symm_apply]
  exact hy

private theorem cechOneProj_eq_zero_iff (s : (sheafCech (S).X₃ V U).obj ∅) :
    cechOneProj hcov hF s = 0 ↔
      ∃ t : (sheafCech (S).X₂ V U).obj ∅, (sheafCechMap (S).g V U).app ∅ t = s := by
  have hC := godementCech_shortExact hF
  have h := ((ShortComplex.ab_exact_iff_function_exact _).mp (hC.homology_exact₃ 0 1 rfl))
    (sectionsToCechH0 (S).X₃ hcov s)
  change hC.δ 0 1 rfl (sectionsToCechH0 (S).X₃ hcov s) = 0 ↔ _
  rw [h]
  constructor
  · rintro ⟨y, hy⟩
    let t := (sectionsToCechH0 (S).X₂ hcov).symm y
    refine ⟨t, (sectionsToCechH0 (S).X₃ hcov).injective ?_⟩
    rw [← sectionsToCechH0_natural (S).X₂ (S).g hcov, AddEquiv.apply_symm_apply]
    exact hy
  · rintro ⟨t, rfl⟩
    refine ⟨sectionsToCechH0 (S).X₂ hcov t, ?_⟩
    exact sectionsToCechH0_natural (S).X₂ (S).g hcov t

private def extOneProj (F : TopCat.Sheaf AddCommGrpCat.{u} X) :
    (sheafCech (deningerGodementComplex F).X₃ V U).obj ∅ →+
      deningerSheafCohomology.{w} W₀ F 1 :=
  ((deningerGodementShortExact F).extClass.postcomp (deningerOpenFree W₀) (rfl : 0 + 1 = 1)).comp
    (extZeroSections W₀ (deningerGodementComplex F).X₃).symm.toAddMonoidHom

private theorem extOneProj_surjective : Function.Surjective (extOneProj (V := V) (U := U) F) := by
  intro x
  obtain ⟨y, hy⟩ := Ext.covariant_sequence_exact₁ (deningerOpenFree W₀)
    (deningerGodementShortExact F) x (godement_acyclicOn F W₀ 0 _) (n₀ := 0) rfl
  refine ⟨extZeroSections W₀ (S).X₃ y, ?_⟩
  change ((extZeroSections W₀ (S).X₃).symm (extZeroSections W₀ (S).X₃ y)).comp
    (deningerGodementShortExact F).extClass rfl = x
  rw [AddEquiv.symm_apply_apply]
  exact hy

omit [LinearOrder ι] [DecidableEq ι] in
private theorem extOneProj_eq_zero_iff (s : (sheafCech (S).X₃ V U).obj ∅) :
    extOneProj F s = 0 ↔
      ∃ t : (sheafCech (S).X₂ V U).obj ∅, (sheafCechMap (S).g V U).app ∅ t = s := by
  let hS := deningerGodementShortExact F
  change ((extZeroSections W₀ (S).X₃).symm s).comp hS.extClass rfl = 0 ↔ _
  constructor
  · intro h
    obtain ⟨x, hx⟩ := Ext.covariant_sequence_exact₃ (deningerOpenFree W₀) hS _ rfl h
    refine ⟨extZeroSections W₀ (S).X₂ x, ?_⟩
    change (S).g.1.app (op W₀) (extZeroSections W₀ (S).X₂ x) = s
    rw [← extZeroSections_natural, hx, AddEquiv.apply_symm_apply]
  · rintro ⟨t, rfl⟩
    change ((extZeroSections W₀ (S).X₃).symm ((S).g.1.app (op W₀) t)).comp hS.extClass rfl = 0
    rw [toExtZero_natural, Ext.comp_assoc_of_second_deg_zero, hS.comp_extClass, Ext.comp_zero]

private theorem ker_oneProj :
    (cechOneProj hcov hF).ker = (extOneProj (V := V) (U := U) F).ker := by
  ext s
  rw [AddMonoidHom.mem_ker, AddMonoidHom.mem_ker, cechOneProj_eq_zero_iff, extOneProj_eq_zero_iff]

/-- In degree one both cohomologies are the same quotient of the sections of the Godement quotient. -/
def cechH1ToExt :
    (sheafCechComplex V U F).homology 1 ≃+ deningerSheafCohomology.{w} W₀ F 1 :=
  (QuotientAddGroup.quotientKerEquivOfSurjective _ (cechOneProj_surjective hcov hF)).symm.trans
    ((QuotientAddGroup.quotientAddEquivOfEq (ker_oneProj hcov hF)).trans
      (QuotientAddGroup.quotientKerEquivOfSurjective _ (extOneProj_surjective (V := V) (U := U) (F := F))))

private theorem cechH1ToExt_apply_proj (s : (sheafCech (S).X₃ V U).obj ∅) :
    cechH1ToExt hcov hF (cechOneProj hcov hF s) = extOneProj F s := by
  have h : (QuotientAddGroup.quotientKerEquivOfSurjective _
      (cechOneProj_surjective hcov hF)).symm (cechOneProj hcov hF s) = QuotientAddGroup.mk s := by
    rw [AddEquiv.symm_apply_eq]
    rfl
  simp only [cechH1ToExt, AddEquiv.trans_apply, h]
  rfl

private theorem cechH1ToExt_natural {G : TopCat.Sheaf AddCommGrpCat.{u} X}
    (hG : ∀ a : Finset ι, a.Nonempty → DeningerAcyclicOn.{w} G (coverInter V U a))
    (φ : F ⟶ G) (x : (sheafCechComplex V U F).homology 1) :
    cechH1ToExt hcov hG (HomologicalComplex.homologyMap (sheafCechComplexMap V U φ) 1 x) =
      (cechH1ToExt hcov hF x).comp (Ext.mk₀ φ) rfl := by
  obtain ⟨s, rfl⟩ := cechOneProj_surjective hcov hF x
  let a := godementSequenceMap φ
  let t := (sheafCechMap a.τ₃ V U).app ∅ s
  have hc : HomologicalComplex.homologyMap (sheafCechComplexMap V U φ) 1 (cechOneProj hcov hF s) =
      cechOneProj hcov hG t := by
    have hδ := HomologicalComplex.HomologySequence.δ_naturality (godementCechSequenceMap V U φ)
      (godementCech_shortExact hF) (godementCech_shortExact hG) 0 1 rfl
    have h := ConcreteCategory.congr_hom hδ (sectionsToCechH0 (S).X₃ hcov s)
    change _ = (godementCech_shortExact hG).δ 0 1 rfl
      (HomologicalComplex.homologyMap (sheafCechComplexMap V U a.τ₃) 0
        (sectionsToCechH0 (S).X₃ hcov s)) at h
    rw [sectionsToCechH0_natural] at h
    exact h
  rw [hc, cechH1ToExt_apply_proj, cechH1ToExt_apply_proj]
  change ((extZeroSections W₀ (deningerGodementComplex G).X₃).symm (a.τ₃.1.app (op W₀) s)).comp
      (deningerGodementShortExact G).extClass rfl =
    (((extZeroSections W₀ (S).X₃).symm s).comp (deningerGodementShortExact F).extClass rfl).comp
      (Ext.mk₀ φ) rfl
  rw [toExtZero_natural, Ext.comp_assoc_of_second_deg_zero, Ext.comp_assoc_of_third_deg_zero,
    ← (deningerGodementShortExact F).extClass_naturality (deningerGodementShortExact G) a]
  rfl

end FirstDegree

/-- Čech cohomology on a finite cover with acyclic intersections computes sheaf cohomology. -/
def lerayCechEquiv (hcov : V ≤ ⨆ i, U i) :
    ∀ (n : ℕ) (F : TopCat.Sheaf AddCommGrpCat.{u} X),
      (∀ a : Finset ι, a.Nonempty → DeningerAcyclicOn.{w} F (coverInter V U a)) →
      (sheafCechComplex V U F).homology n ≃+ deningerSheafCohomology.{w} (coverInter V U ∅) F n
  | 0, F, _ => (sectionsToCechH0 F hcov).symm.trans
      (extZeroSections (coverInter V U ∅) F).symm
  | 1, _, hF => cechH1ToExt hcov hF
  | n + 2, F, hF =>
      ((godementCechShift hcov hF n).addCommGroupIsoToAddEquiv.symm.trans
        (lerayCechEquiv hcov (n + 1) (deningerGodementComplex F).X₃
          (fun a ha => godementQuotient_acyclicOn (hF a ha)))).trans
        (godementExtShift F (coverInter V U ∅) n)

/-- The comparison commutes with maps of sheaves, including scalar multiplication. -/
theorem lerayCechEquiv_natural (hcov : V ≤ ⨆ i, U i) :
    ∀ (n : ℕ) {F G : TopCat.Sheaf AddCommGrpCat.{u} X}
      (hF : ∀ a : Finset ι, a.Nonempty → DeningerAcyclicOn.{w} F (coverInter V U a))
      (hG : ∀ a : Finset ι, a.Nonempty → DeningerAcyclicOn.{w} G (coverInter V U a))
      (φ : F ⟶ G) (x : (sheafCechComplex V U F).homology n),
      lerayCechEquiv hcov n G hG (HomologicalComplex.homologyMap (sheafCechComplexMap V U φ) n x) =
        (lerayCechEquiv hcov n F hF x).comp (Ext.mk₀ φ) (add_zero n)
  | 0, F, G, hF, hG, φ, x => by
      obtain ⟨z, rfl⟩ := (sectionsToCechH0 F hcov).surjective x
      rw [sectionsToCechH0_natural]
      simp only [lerayCechEquiv, AddEquiv.trans_apply, AddEquiv.symm_apply_apply]
      exact toExtZero_natural (coverInter V U ∅) φ z
  | 1, F, G, hF, hG, φ, x => cechH1ToExt_natural hcov hF hG φ x
  | n + 2, F, G, hF, hG, φ, x => by
      let e := (godementCechShift hcov hF n).addCommGroupIsoToAddEquiv
      let e' := (godementCechShift hcov hG n).addCommGroupIsoToAddEquiv
      let a := godementSequenceMap φ
      obtain ⟨y, rfl⟩ := e.surjective x
      have h : HomologicalComplex.homologyMap (sheafCechComplexMap V U φ) (n + 2) (e y) =
          e' (HomologicalComplex.homologyMap (sheafCechComplexMap V U a.τ₃) (n + 1) y) :=
        ConcreteCategory.congr_hom (godementCechShift_natural hcov hF hG φ n) y
      rw [h]
      change godementExtShift G (coverInter V U ∅) n
          (lerayCechEquiv hcov (n + 1) (deningerGodementComplex G).X₃ _
            (e'.symm (e' (HomologicalComplex.homologyMap
              (sheafCechComplexMap V U a.τ₃) (n + 1) y)))) =
        (godementExtShift F (coverInter V U ∅) n
          (lerayCechEquiv hcov (n + 1) (deningerGodementComplex F).X₃ _ (e.symm (e y)))).comp
            (Ext.mk₀ φ) (add_zero (n + 2))
      rw [AddEquiv.symm_apply_apply, AddEquiv.symm_apply_apply,
        lerayCechEquiv_natural hcov (n + 1) _ _ a.τ₃, godementExtShift_natural]

end GlobalTheory.SchemeCohomology
