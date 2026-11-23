import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.AffineCoverSectionTrace
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.AffineCoverHodgeCohomology
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.CechCoefficientMap

/-! Finite étale trace on affine Čech cochains acts by the rational
trace on each intersection. -/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace HTGeometry
open GlobalTheory.CechDR GlobalTheory.SchemeCohomology
open scoped GlobalTheory.CechDR

namespace GlobalTheory.PD

variable {k : Type} [Field k] [CharZero k] {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]
  {s : X ⟶ Spec (CommRingCat.of k)} {t : Y ⟶ Spec (CommRingCat.of k)} [Smooth s] [Smooth t]
  {f : Y ⟶ X} [IsFinite f] [Etale f] [IsDominant f] {ι : Type} [LinearOrder ι] {U : ι → X.Opens}

theorem IsAffCover.formCochainsEquiv_trace (hf : f ≫ s = t) :
    letI := sectionFunctionFieldAlgebra s
    letI := sectionFunctionFieldAlgebra t
    letI := f.functionFieldPullback.hom.toAlgebra
    letI := functionFieldPullback_scalarTower hf
    letI := finiteDimensional_functionFieldPullback f
    letI := functionFieldPullback_etale (f := f) s
    ∀ {A : Finset ι → Subalgebra k X.functionField} {B : Finset ι → Subalgebra k Y.functionField}
      (hX : IsAffCover s U A) (hY : IsAffCover t (fun i => f ⁻¹ᵁ U i) B)
      (p q : ℕ) (x : (hY.formCechDatum p).cochainComplex.X q),
    (hX.formCochainsEquiv p q ((relativeFormsCechTrace hf U p).f q x)).val =
      mapCochain (traceDR k X.functionField Y.functionField) (hY.formCochainsEquiv p q x).val := by
  letI := sectionFunctionFieldAlgebra s
  letI := sectionFunctionFieldAlgebra t
  letI := f.functionFieldPullback.hom.toAlgebra
  letI := functionFieldPullback_scalarTower hf
  letI := finiteDimensional_functionFieldPullback f
  letI := functionFieldPullback_etale (f := f) s
  intro A B hX hY p q x
  let G := (SheafOfModules.toSheaf Y.ringCatSheaf).obj (relativeForms t p)
  let E := pushforwardCechIso f.base ⊤ U G
  let z := E.inv.f q x
  have hz : E.hom.f q z = x :=
    ConcreteCategory.congr_hom (congrArg (fun ψ => ψ.f q) E.inv_hom_id) x
  rw [← hz]
  funext I
  rw [mapCochain_apply]
  by_cases hI : I.Nonempty
  · rw [hX.formCochainsEquiv_apply p q _ hI, hY.formCochainsEquiv_apply p q _ hI,
      relativeFormsCechTrace_component]
    let e := preimage_coverInter f.base ⊤ U I
    exact (IsAffCover.sectionRationalForms_trace hf hX hY hI hI e p (z.val I)).symm
  · have hi := Finset.not_nonempty_iff_eq_empty.mp hI
    subst I
    rw [hX.formCochainsEquiv_apply_empty, hY.formCochainsEquiv_apply_empty, map_zero]


/-- Under the affine Čech comparison, Hodge trace is the map on the
cohomology of regular rational forms induced by field trace. -/
theorem IsAffCover.hodgeCechEquiv_trace (hf : f ≫ s = t) :
    letI := sectionFunctionFieldAlgebra s
    letI := sectionFunctionFieldAlgebra t
    letI := f.functionFieldPullback.hom.toAlgebra
    letI := functionFieldPullback_scalarTower hf
    letI := finiteDimensional_functionFieldPullback f
    letI := functionFieldPullback_etale (f := f) s
    ∀ {A : Finset ι → Subalgebra k X.functionField} {B : Finset ι → Subalgebra k Y.functionField}
      (hX : IsAffCover s U A) (hY : IsAffCover t (fun i => f ⁻¹ᵁ U i) B)
      (p q : ℕ) (x : HodgeCohomology t p q),
    let C := cech (fun I => omB k Y.functionField (B I) p)
    let D := cech (fun I => omB k X.functionField (A I) p)
    let P := mapCochain (traceDR k X.functionField Y.functionField)
    let hP : IsMap C D P := isMap_mapCochain _ _ _ fun I hi =>
      IsAffCover.traceDR_mem_regularForms hf hX hY hi hi (preimage_coverInter f.base ⊤ U I) p
    hX.hodgeCechEquiv p q (hodgeTrace hf p q x) =
      C.hmap D P hP q (hY.hodgeCechEquiv p q x) := by
  letI := sectionFunctionFieldAlgebra s
  letI := sectionFunctionFieldAlgebra t
  letI := f.functionFieldPullback.hom.toAlgebra
  letI := functionFieldPullback_scalarTower hf
  letI := finiteDimensional_functionFieldPullback f
  letI := functionFieldPullback_etale (f := f) s
  intro A B hX hY p q x C D P hP
  have ha (I : Finset ι) (hi : I.Nonempty) : IsAffineOpen (coverInter ⊤ U I) := by
    simpa only [coverInter, top_inf_eq] using hX.affine I hi
  have hb (I : Finset ι) (hi : I.Nonempty) :
      IsAffineOpen (coverInter ⊤ (fun i => f ⁻¹ᵁ U i) I) := by
    simpa only [coverInter, top_inf_eq] using hY.affine I hi
  let H := affineFormsLeray t p q hY.cover.ge hb
  let G := affineFormsLeray s p q hX.cover.ge ha
  obtain ⟨a, rfl⟩ := H.surjective x
  let φ := relativeFormsCechTrace hf U p
  let b := HomologicalComplex.homologyMap φ q a
  have hp : G b = hodgeTrace hf p q (H a) :=
    affineFormsLeray_trace hf p q hX.cover.ge ha a
  calc
    _ = hX.hodgeCechEquiv p q (G b) := congrArg (hX.hodgeCechEquiv p q) hp.symm
    _ = hX.formCechLinearEquiv p q b := hX.hodgeCechEquiv_affineFormsLeray p q ha b
    _ = C.hmap D P hP q (hY.formCechLinearEquiv p q a) :=
      hY.formCechLinearEquiv_natural p q hX φ P hP (IsAffCover.formCochainsEquiv_trace hf hX hY p q) a
    _ = _ := congrArg (C.hmap D P hP q) (hY.hodgeCechEquiv_affineFormsLeray p q hb a).symm

end GlobalTheory.PD
