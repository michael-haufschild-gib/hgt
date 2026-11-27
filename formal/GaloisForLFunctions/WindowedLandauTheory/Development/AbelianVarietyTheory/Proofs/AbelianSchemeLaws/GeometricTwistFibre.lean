import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.AbelianSchemeLaws.TwistedPowerFieldCohomology
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.AbelianSchemeLaws.PrincipalPolarizationBaseChange
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.PELModuli.PELRelativeAmplePullback

/-! Geometric fibres of a power with one translated factor have the section
dimension of the full power and vanishing positive cohomology. -/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
open TopologicalSpace HTGeometry
open GlobalTheory.LineBundleSections GlobalTheory.ProjectiveSections GlobalTheory.SchemeCohomology
open GlobalTheory.TwistTranslate
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Pdiv.PullbackComparison
open UpperTheory.Cb
open scoped CategoryTheory.Obj

namespace GlobalTheory.PrincipalSections

attribute [local instance] Over.cartesianMonoidalCategory

private theorem translate_projection {K : Type} [Field K] {S : Scheme.{0}} {A : Over S} [GrpObj A]
    (t : Spec (.of K) ⟶ S) (x : 𝟙_ (Over S) ⟶ A) :
    let B := (Over.pullback t).obj A
    let τ : A ⟶ A := (toUnit A ≫ x) * 𝟙 A
    ∃ y : 𝟙_ (Over (Spec (.of K))) ⟶ B,
      (translate B y).left ≫ pφ t A = pφ t A ≫ τ.left := by
  let B := (Over.pullback t).obj A
  let π := pφ t A
  let H := isGrpPullback t A
  let τ : A ⟶ A := (toUnit A ≫ x) * 𝟙 A
  have h : (t ≫ x.left) ≫ A.hom = (𝟙 (Spec (.of K))) ≫ t := by
    have hx : x.left ≫ A.hom = 𝟙 S := Over.w x
    exact (Category.assoc t x.left A.hom).trans
      ((congrArg (fun k : (𝟙_ (Over S)).left ⟶ S => t ≫ k) hx).trans
        ((Category.comp_id t).trans (Category.id_comp t).symm))
  let y : 𝟙_ (Over (Spec (.of K))) ⟶ B :=
    Over.homMk (H.1.lift (t ≫ x.left) (𝟙 _) h) (H.1.lift_snd _ _ _)
  have hy : y.left ≫ π = t ≫ x.left := H.1.lift_fst _ _ _
  let B₀ := Over.mk (B.hom ≫ t)
  let π₀ : B₀ ⟶ A := Over.homMk π H.1.w
  let x₀ : B₀ ⟶ A := toUnit B₀ ≫ x
  have hx₀ : x₀.left = (toUnit B ≫ y).left ≫ π :=
    (Category.assoc _ _ _).trans ((congrArg (B.hom ≫ ·) hy.symm).trans (Category.assoc _ _ _).symm)
  have hπ₀ : π₀.left = (𝟙 B : B ⟶ B).left ≫ π := (Category.id_comp π).symm
  have he : π₀ ≫ τ = x₀ * π₀ := by
    change π₀ ≫ ((toUnit A ≫ x) * 𝟙 A) = _
    rw [MonObj.comp_mul, Category.comp_id, comp_toUnit_assoc]
  refine ⟨y, ?_⟩
  exact (H.2 B (toUnit B ≫ y) (𝟙 B) x₀ π₀ hx₀ hπ₀).symm.trans
    (congrArg Over.Hom.left he.symm)

/-- The geometric fibre of a translated power has the same cohomology
as the corresponding untwisted power on that fibre. -/
theorem geometric_twist_finrank_and_vanishing {K : Type} [Field K] [IsAlgClosed K]
    {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left}
    (hA : IsAbelianScheme A) (hL : L.IsLB) (hAmp : RelAmple A L) (hK : KTriv A L)
    (hrig : ∃ t : (L.pull η[A].left).Gen, t.IsGen)
    (hsym : ∀ s : S, ∃ U : S.Opens, s ∈ U ∧ ∃ t : (LB.LinComb L (K := Fin 2)
      ![(A.hom ⁻¹ᵁ U).ι ≫ (GrpObj.inv : A ⟶ A).left, (A.hom ⁻¹ᵁ U).ι] ![1, -1]).Gen, t.IsGen)
    (d : ℕ) [SmoothOfRelativeDimension d A.hom]
    (t : Spec (.of K) ⟶ S) (x : 𝟙_ (Over S) ⟶ A) (j : ℕ) (hj : 1 ≤ j) :
    let B := (Over.pullback t).obj A
    let τ : A ⟶ A := (toUnit A ≫ x) * 𝟙 A
    let M := LB.LinComb L ![𝟙 A.left, τ.left] ![(j : ℤ) - 1, 1]
    let F := toMod (M.pull (pφ t A))
    letI := sectionBaseModule B.hom F ⊤
    Module.finrank K Γ(F, ⊤) = j ^ d ∧ ∀ n : ℕ, Subsingleton (CohomologyOn F ⊤ (n + 1)) := by
  let B := (Over.pullback t).obj A
  let π := pφ t A
  let L' := L.pull π
  let H := isGrpPullback t A
  have hL' : L'.IsLB := hL.pull π
  let hB := hA.pullback t
  letI := hB.proper
  letI : SmoothOfRelativeDimension d B.hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange d).of_isPullback H.1 inferInstance
  obtain ⟨w, hw⟩ := hL'.gen_refl
  have hAmp' : RelAmple B L' := PolPull.relAmple_baseChange H.1 hL hL' ⟨w, hw⟩
    inferInstance inferInstance hAmp
  have hK' : KTriv B L' := PolPull.kTriv_baseChange H hL hL' hw hK
  have hrig' := PolPull.rigid_generator_pullback t hL hrig
  have hsym' := PolPull.symmetric_generators_pullback t hL hsym
  obtain ⟨y, hy⟩ := translate_projection t x
  let τ : A ⟶ A := (toUnit A ≫ x) * 𝟙 A
  let a : Fin 2 → (A.left ⟶ A.left) := ![𝟙 A.left, τ.left]
  let b : Fin 2 → (B.left ⟶ B.left) := ![𝟙 B.left, (translate B y).left]
  let e : Fin 2 → ℤ := ![(j : ℤ) - 1, 1]
  let M := LB.LinComb L a e
  let N := LB.LinComb L' b e
  have hN : N.IsLB := hL'.linComb b e
  have hM : (M.pull π).IsLB := (hL.linComb a e).pull π
  have hfac (k : Fin 2) : b k ≫ π = π ≫ a k := by
    fin_cases k
    · exact (Category.id_comp π).trans (Category.comp_id π).symm
    · exact hy
  obtain ⟨v, hv⟩ := iso_linComb_pull hw a b e π hfac
  have he := field_twist_finrank_and_vanishing hB hL' hAmp' hK' hrig' hsym' d y j hj
  letI := sectionBaseModule B.hom (toMod N) ⊤
  letI := sectionBaseModule B.hom (toMod (M.pull π)) ⊤
  obtain ⟨k, i, hi, hif⟩ := isProjOver_of_relAmple hL' hAmp'
  letI := hi
  let U (a : Fin (k + 1)) := i ⁻¹ᵁ PSpace.coordinateOpen K k a
  have hU : ⨆ a, U a = ⊤ := i.iSup_preimage_eq_top (PSpace.iSup_coordinateOpen K k)
  have ha (I : Finset (Fin (k + 1))) (hI : I.Nonempty) : IsAffineOpen (coverInter ⊤ U I) :=
    (coverInter_pull (π := i) (PSpace.coordinateOpen K k) I).symm ▸
      (PSpace.isAffineOpen_coordinateInter K k hI).preimage i
  let D := cechIsoOfIsGen B.hom U hN hM hv
  constructor
  · let u := (cechHomologyZeroEquiv B.hom (toMod N) U hU).symm.trans
      ((HomologicalComplex.homologyMapIso D 0).toLinearEquiv.trans
        (cechHomologyZeroEquiv B.hom (toMod (M.pull π)) U hU))
    exact u.finrank_eq.symm.trans he.1
  · intro n
    have h := (exactAt_cech_iff_subsingleton_cohomology B.hom hN U hU.ge ha (n + 1)).mpr (he.2 n)
    exact (exactAt_cech_iff_subsingleton_cohomology B.hom hM U hU.ge ha (n + 1)).mp (h.of_iso D)

end GlobalTheory.PrincipalSections
