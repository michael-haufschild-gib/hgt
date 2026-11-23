import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.AffineCoverSectionPullback
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.AffineCoverHodgeCohomology
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.CechCoefficientMap
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.AffineFormsCechComparison

/-! The Čech pullback for an inverse-image cover is the componentwise
pullback on regular rational forms. -/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace HTGeometry
open GlobalTheory.CechDR GlobalTheory.SchemeCohomology
open scoped GlobalTheory.CechDR

namespace GlobalTheory.PD

variable {K : Type} [Field K] {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]
  {s : X ⟶ Spec (CommRingCat.of K)} {t : Y ⟶ Spec (CommRingCat.of K)}
  [Algebra K X.functionField] [Algebra K Y.functionField] [Smooth s] [Smooth t]
  {ι : Type} [LinearOrder ι] {U : ι → X.Opens}
  {A : Finset ι → Subalgebra K X.functionField} {B : Finset ι → Subalgebra K Y.functionField}
  {f : Y ⟶ X}

theorem IsAffCover.formCochainsEquiv_pullback
    (hX : IsAffCover s U A) (hY : IsAffCover t (fun i => f ⁻¹ᵁ U i) B)
    (hf : f ≫ s = t) (ψ : X.functionField →ₐ[K] Y.functionField)
    (hψ : ∀ (W : X.Opens) (hW : genericPoint X ∈ W)
      (hW' : genericPoint Y ∈ f ⁻¹ᵁ W) (a : Γ(X, W)),
      ψ ((X.presheaf.germ W _ hW).hom a) = (Y.presheaf.germ (f ⁻¹ᵁ W) _ hW').hom ((f.app W).hom a))
    (p q : ℕ) (x : (hX.formCechDatum p).cochainComplex.X q) :
    (hY.formCochainsEquiv p q ((relativeFormsCechPullback hf U p).f q x)).val =
      mapCochain (pullbackDR ψ).toLinearMap (hX.formCochainsEquiv p q x).val := by
  funext I
  rw [mapCochain_apply]
  by_cases hI : I.Nonempty
  · rw [hY.formCochainsEquiv_apply p q _ hI, hX.formCochainsEquiv_apply p q x hI,
      relativeFormsCechPullback_component]
    let e := preimage_coverInter f.base ⊤ U I
    exact hX.sectionRationalForms_pullback hY hf ψ hψ hI hI (leOfHom (eqToHom e.symm)) p (x.val I)
  · have h₀ := Finset.not_nonempty_iff_eq_empty.mp hI
    subst I
    rw [hY.formCochainsEquiv_apply_empty, hX.formCochainsEquiv_apply_empty, map_zero]


/-- Under the affine Čech comparison, Hodge pullback is the map on the
cohomology of regular rational forms induced by field pullback. -/
theorem IsAffCover.hodgeCechEquiv_pullback [IsAffineHom f]
    (hX : IsAffCover s U A) (hY : IsAffCover t (fun i => f ⁻¹ᵁ U i) B)
    (hf : f ≫ s = t) (ψ : X.functionField →ₐ[K] Y.functionField)
    (hψ : ∀ (W : X.Opens) (hW : genericPoint X ∈ W)
      (hW' : genericPoint Y ∈ f ⁻¹ᵁ W) (a : Γ(X, W)),
      ψ ((X.presheaf.germ W _ hW).hom a) = (Y.presheaf.germ (f ⁻¹ᵁ W) _ hW').hom ((f.app W).hom a))
    (hB : ∀ I, I.Nonempty → (A I).map ψ ≤ B I) (p q : ℕ) (x : HodgeCohomology s p q) :
    let C := cech (fun I => omB K X.functionField (A I) p)
    let D := cech (fun I => omB K Y.functionField (B I) p)
    let P := mapCochain (pullbackDR ψ).toLinearMap
    let hP : IsMap C D P := isMap_mapCochain
      (fun I => omB K X.functionField (A I) p) (fun I => omB K Y.functionField (B I) p)
      (pullbackDR ψ).toLinearMap fun I hi =>
        IsDRMap.regularForms K (isDRMap_pullbackDR K ψ) (hB I hi) p
    hY.hodgeCechEquiv p q (hodgePullback hf p q x) =
      C.hmap D P hP q (hX.hodgeCechEquiv p q x) := by
  intro C D P hP
  have ha (I : Finset ι) (hi : I.Nonempty) : IsAffineOpen (coverInter ⊤ U I) := by
    simpa only [coverInter, top_inf_eq] using hX.affine I hi
  have hb (I : Finset ι) (hi : I.Nonempty) :
      IsAffineOpen (coverInter ⊤ (fun i => f ⁻¹ᵁ U i) I) := by
    simpa only [coverInter, top_inf_eq] using hY.affine I hi
  let H := affineFormsLeray s p q hX.cover.ge ha
  let G := affineFormsLeray t p q hY.cover.ge hb
  obtain ⟨a, rfl⟩ := H.surjective x
  let φ := relativeFormsCechPullback hf U p
  let b := HomologicalComplex.homologyMap φ q a
  have hp : G b = hodgePullback hf p q (H a) :=
    affineFormsLeray_pullback hf p q hX.cover.ge ha a
  calc
    _ = hY.hodgeCechEquiv p q (G b) := congrArg (hY.hodgeCechEquiv p q) hp.symm
    _ = hY.formCechLinearEquiv p q b := hY.hodgeCechEquiv_affineFormsLeray p q hb b
    _ = C.hmap D P hP q (hX.formCechLinearEquiv p q a) :=
      hX.formCechLinearEquiv_natural p q hY φ P hP (hX.formCochainsEquiv_pullback hY hf ψ hψ p q) a
    _ = _ := congrArg (C.hmap D P hP q) (hX.hodgeCechEquiv_affineFormsLeray p q ha a).symm

end GlobalTheory.PD
