import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.AffineCoverFormCochains
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.AffineFormsAcyclic
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.HodgeCohomology

/-! Hodge cohomology computed by Čech cochains of regular rational forms. -/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian TopologicalSpace HTGeometry RHTower
open GlobalTheory.CechDR GlobalTheory.SchemeCohomology
open scoped GlobalTheory.CechDR

namespace GlobalTheory.PD

variable {K : Type} [Field K] {X : Scheme.{0}} [IsIntegral X]
  {s : X ⟶ Spec (CommRingCat.of K)} [Algebra K X.functionField] [Smooth s]
  {ι : Type} [LinearOrder ι]
  {U : ι → X.Opens} {B : Finset ι → Subalgebra K X.functionField}
  (h : IsAffCover s U B) (p q : ℕ)

private abbrev C := (h.formCechDatum p).cochainComplex
private abbrev R := cech (fun I => omB K X.functionField (B I) p)

private theorem formCochainsEquiv_cycles (x : (C h p).X q) :
    ((C h p).sc q).g x = 0 ↔ (R (K := K) (X := X) (B := B) p).D
      (h.formCochainsEquiv p q x) = 0 := by
  have hn := (ComplexShape.up ℕ).next_eq' (show (ComplexShape.up ℕ).Rel q (q + 1) from rfl)
  change (C h p).d q ((ComplexShape.up ℕ).next q) x = 0 ↔ _
  rw [hn, ← h.formCochainsEquiv_d]
  constructor
  · intro hx
    rw [hx, map_zero]
    rfl
  · intro hx
    apply (h.formCochainsEquiv p (q + 1)).injective
    rw [map_zero]
    exact Subtype.ext hx

private theorem formCochainsEquiv_boundaries (x : (R (K := K) (X := X) (B := B) p).C q) :
    x.val ∈ (R (K := K) (X := X) (B := B) p).B q ↔
      ∃ y, h.formCochainsEquiv p q (((C h p).sc q).f y) = x := by
  cases q with
  | zero =>
    have hneg : cechC (fun I => omB K X.functionField (B I) p) (-1) = ⊥ := by
      apply bot_unique
      intro a ha
      rw [Submodule.mem_bot]
      funext I
      have hz : ¬ (I.Nonempty ∧ (I.card : ℤ) = -1 + 1) := by
        rintro ⟨hI, hc⟩
        have hp := Finset.card_pos.mpr hI
        omega
      have hI := Submodule.mem_pi.mp ha I (Set.mem_univ I)
      rw [if_neg hz, Submodule.mem_bot] at hI
      exact hI
    have hf : ((C h p).sc 0).f = 0 :=
      (C h p).shape _ _ (by simp [ComplexShape.up])
    change x.val ∈ (cechC (fun I => omB K X.functionField (B I) p) (0 - 1)).map _ ↔ _
    rw [show (0 : ℤ) - 1 = -1 by omega, hneg, Submodule.map_bot, hf]
    change x.val = 0 ↔ ∃ _ : ((C h p).sc 0).X₁, h.formCochainsEquiv p 0 0 = x
    rw [map_zero]
    exact ⟨fun e => ⟨0, Subtype.ext e.symm⟩, fun ⟨_, e⟩ => congrArg Subtype.val e.symm⟩
  | succ l =>
    have hl := (ComplexShape.up ℕ).prev_eq'
      (show (ComplexShape.up ℕ).Rel l (l + 1) from rfl)
    change x.val ∈ (cechC (fun I => omB K X.functionField (B I) p) ((l + 1 : ℕ) - (1 : ℤ))).map
      (deltaL K ι (DR K X.functionField)) ↔
      ∃ y : (C h p).X ((ComplexShape.up ℕ).prev (l + 1)),
        h.formCochainsEquiv p (l + 1)
          ((C h p).d ((ComplexShape.up ℕ).prev (l + 1)) (l + 1) y) = x
    rw [hl, show ((l + 1 : ℕ) : ℤ) - 1 = l by omega, Submodule.mem_map]
    constructor
    · rintro ⟨a, ha, hax⟩
      obtain ⟨y, hy⟩ := (h.formCochainsEquiv p l).surjective ⟨a, ha⟩
      refine ⟨y, Subtype.ext ?_⟩
      rw [h.formCochainsEquiv_d, hy]
      exact hax
    · rintro ⟨y, rfl⟩
      exact ⟨_, (h.formCochainsEquiv p l y).2, (h.formCochainsEquiv_d p l y).symm⟩

private abbrev cohomologyAddEquiv :
    (C h p).homology q ≃+ (R (K := K) (X := X) (B := B) p).H q :=
  Cx.homologyAddEquiv (h.formCochainsEquiv p q)
    (formCochainsEquiv_cycles h p q) (formCochainsEquiv_boundaries h p q)

private def scalarMap (r : K) : C h p ⟶ C h p :=
  letI := sectionAlgebra s ⊤
  sheafCechComplexMap ⊤ U ((SheafOfModules.toSheaf X.ringCatSheaf).map
    (globalSectionEnd (relativeForms s p) (algebraMap K Γ(X, ⊤) r)))

private theorem formCochainsEquiv_scale (r : K) (x : (C h p).X q) :
    h.formCochainsEquiv p q ((scalarMap h p r).f q x) = r • h.formCochainsEquiv p q x := by
  apply Subtype.ext
  funext I
  change (h.formCochainsEquiv p q ((scalarMap h p r).f q x)).val I =
    r • (h.formCochainsEquiv p q x).val I
  letI := sectionAlgebra s ⊤
  by_cases hi : I.Nonempty
  · rw [h.formCochainsEquiv_apply p q _ hi, h.formCochainsEquiv_apply p q _ hi]
    exact congrArg Subtype.val (h.sectionRationalForms_scale hi p r (x.val I))
  · have hI := Finset.not_nonempty_iff_eq_empty.mp hi
    subst I
    rw [h.formCochainsEquiv_apply_empty, h.formCochainsEquiv_apply_empty, smul_zero]

private abbrev FormCechCohomology := ModuleCechCohomology ⊤ U (relativeForms s p) q

local instance moduleCechBase : Module K (FormCechCohomology (s := s) (U := U) p q) :=
  letI := sectionAlgebra s ⊤
  Module.compHom _ (algebraMap K Γ(X, ⊤))

/-- The Čech realization is linear over the base field. -/
def IsAffCover.formCechLinearEquiv :
    FormCechCohomology (s := s) (U := U) p q ≃ₗ[K] (R (K := K) (X := X) (B := B) p).H q :=
  { cohomologyAddEquiv h p q with
    map_smul' r x := by
      let S := (C h p).sc q
      let m := (HomologicalComplex.shortComplexFunctor AddCommGrpCat (ComplexShape.up ℕ) q).map
        (scalarMap h p r)
      let e := h.formCochainsEquiv p q
      let η := cohomologyAddEquiv h p q
      change η (ShortComplex.homologyMap m x) = r • η x
      obtain ⟨z, rfl⟩ := (AddCommGrpCat.epi_iff_surjective S.homologyπ).mp inferInstance x
      have hn : ShortComplex.homologyMap m (S.homologyπ z) =
          S.homologyπ (ShortComplex.cyclesMap m z) :=
        ConcreteCategory.congr_hom (ShortComplex.homologyπ_naturality m) z
      rw [hn]
      have hz : (R (K := K) (X := X) (B := B) p).D (e (S.iCycles z)) = 0 :=
        (formCochainsEquiv_cycles h p q _).mp (ConcreteCategory.congr_hom S.iCycles_g z)
      let a : (R (K := K) (X := X) (B := B) p).Z q :=
        ⟨(e (S.iCycles z)).val, (e (S.iCycles z)).2, LinearMap.mem_ker.mpr hz⟩
      have ha : (r • a).val = (e (S.iCycles (ShortComplex.cyclesMap m z))).val := by
        have hc : S.iCycles (ShortComplex.cyclesMap m z) = (scalarMap h p r).f q (S.iCycles z) :=
          ConcreteCategory.congr_hom (ShortComplex.cyclesMap_i m) z
        rw [hc, formCochainsEquiv_scale h p q r]
        rfl
      rw [show η (S.homologyπ (ShortComplex.cyclesMap m z)) = Submodule.Quotient.mk (r • a) from
        Cx.homologyAddEquiv_π_val _ _ _ _ _ ha,
        show η (S.homologyπ z) = Submodule.Quotient.mk a from
          Cx.homologyAddEquiv_π_val _ _ _ _ _ rfl]
      rfl }

local instance affineHodgeHasExt : HasExt.{0} (TopCat.Sheaf AddCommGrpCat.{0} X) :=
  hasExt_of_enoughInjectives _

/-- On a smooth integral scheme, the regular rational forms of an affine cover
compute the Hodge cohomology in every bidegree. -/
def IsAffCover.hodgeCechEquiv :
    HodgeCohomology s p q ≃ₗ[K] (R (K := K) (X := X) (B := B) p).H q := by
  letI := sectionAlgebra s ⊤
  have e := moduleLerayLinearEquiv ⊤ U (relativeForms s p) q h.cover.ge fun I hi => by
    apply relativeForms_acyclicOn
    simpa only [coverInter, top_inf_eq] using h.affine I hi
  rw [coverInter_empty] at e
  let eK : FormCechCohomology (s := s) (U := U) p q ≃ₗ[K] HodgeCohomology s p q :=
    { e.toAddEquiv with map_smul' := fun r x => e.map_smul (algebraMap K Γ(X, ⊤) r) x }
  exact eK.symm.trans (h.formCechLinearEquiv p q)

end GlobalTheory.PD
