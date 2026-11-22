import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.ProjectivePolynomialCech
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.ProjectiveTopCechCoefficients
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.CechCoefficientDescent
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.ModuleCechComparison

/-! Top cohomology of a negative projective twist is detected by the finitely
many Laurent monomials with all exponents negative. -/

noncomputable section

open AlgebraicGeometry CategoryTheory HTGeometry Opposite TopologicalSpace

namespace GlobalTheory.SchemeCohomology

open UpperTheory.Cb

variable (K : Type) [Field K] (p m : ℕ)

private abbrev X := PSpace K (p + 1)
private abbrev F := pspaceTwist K (p + 1) (-(m : ℤ))
private abbrev U := PSpace.coordinateOpen K (p + 1)
private abbrev D := polyTwCech K (Fin (p + 2)) PEmpty m
private abbrev sheafOf := SheafOfModules.toSheaf (X K p).ringCatSheaf
private abbrev E := sheafCech ((sheafOf K p).obj (F K p m)) ⊤ (U K p)
private abbrev comparison := pspaceTwistCechMap K (p + 1) m

private def degreeEquiv (q : ℕ) :
    (D K p m).degreeCochains q ≃+ (E K p m).degreeCochains q :=
  AddEquiv.ofBijective ((comparison K p m).cochainMap.f q).hom
    (cochainMap_bijective_of_nonempty _ (fun a => pspaceTwistCechMap_bijective K (p + 1) m) q)

private abbrev topShortComplex :=
  (E K p m).cochainComplex.sc' p (p + 1) (p + 2)

private abbrev coeffSpace := AddCommGrpCat.of (TopLaurentExponents (Fin (p + 2)) m → K)

private def chartCoefficients : (topShortComplex K p m).X₂ ⟶ coeffSpace K p m :=
  AddCommGrpCat.ofHom ((topLaurentCoefficients m (p + 1)).comp
    (degreeEquiv K p m (p + 1)).symm.toAddMonoidHom)

private theorem degreeEquiv_d (b : (D K p m).degreeCochains p) :
    (E K p m).cochainComplex.d p (p + 1) (degreeEquiv K p m p b) =
      degreeEquiv K p m (p + 1) ((D K p m).cochainComplex.d p (p + 1) b) :=
  ConcreteCategory.congr_hom ((comparison K p m).cochainMap.comm p (p + 1)) b

private theorem chartCoefficients_exact : Function.Exact (topShortComplex K p m).f
    (chartCoefficients K p m) := by
  have hpoly := exact_topLaurentCoefficients (K := K) (ι := Fin (p + 2)) m p (Fintype.card_fin _)
  intro x
  obtain ⟨z, rfl⟩ := (degreeEquiv K p m (p + 1)).surjective x
  change topLaurentCoefficients m (p + 1)
    ((degreeEquiv K p m (p + 1)).symm (degreeEquiv K p m (p + 1) z)) = 0 ↔ _
  rw [AddEquiv.symm_apply_apply, hpoly]
  constructor
  · rintro ⟨b, hb⟩
    refine ⟨degreeEquiv K p m p b, ?_⟩
    exact (degreeEquiv_d K p m b).trans (congrArg (degreeEquiv K p m (p + 1)) hb)
  · rintro ⟨b, hb⟩
    obtain ⟨c, rfl⟩ := (degreeEquiv K p m p).surjective b
    refine ⟨c, (degreeEquiv K p m (p + 1)).injective ?_⟩
    exact (degreeEquiv_d K p m c).symm.trans hb

private def scalarComplexMap (r : K) : (E K p m).cochainComplex ⟶ (E K p m).cochainComplex :=
  letI := sectionAlgebra (PSpace.str K (p + 1)) ⊤
  sheafCechComplexMap ⊤ (U K p) ((sheafOf K p).map
    (globalSectionEnd (F K p m) (algebraMap K Γ(X K p, ⊤) r)))

private theorem degreeEquiv_scale (r : K) (b : (D K p m).degreeCochains (p + 1)) :
    (scalarComplexMap K p m r).f (p + 1) (degreeEquiv K p m (p + 1) b) =
      degreeEquiv K p m (p + 1)
        ⟨(polynomialTwistScale m r).onCochain b.1, (polynomialTwistScale m r).onCochain_isDeg b.2⟩ := by
  letI := sectionAlgebra (PSpace.str K (p + 1)) ⊤
  apply Subtype.ext
  funext a
  let W := coverInter ⊤ (U K p) a
  change (globalSectionEnd (F K p m) (algebraMap K Γ(X K p, ⊤) r)).app W
      ((comparison K p m).app a (b.1 a)) =
    (comparison K p m).app a ((polynomialTwistScale m r).app a (b.1 a))
  rw [globalSectionEnd_app]
  by_cases ha : a.Nonempty
  · exact (pspaceTwistCechMap_scale K (p + 1) m r ha (b.1 a)).symm
  · have hc : a.card ≠ p + 2 := by
      rw [Finset.not_nonempty_iff_eq_empty.mp ha]
      simp
    rw [b.2 a hc, map_zero, map_zero, map_zero, smul_zero]

private abbrev scFunctor :=
  HomologicalComplex.shortComplexFunctor' AddCommGrpCat.{0} (ComplexShape.up ℕ) p (p + 1) (p + 2)

private def scalarCoefficients (r : K) : coeffSpace K p m ⟶ coeffSpace K p m :=
  AddCommGrpCat.ofHom
    { toFun := fun x => r • x
      map_zero' := smul_zero _
      map_add' := smul_add _ }

private theorem chartCoefficients_scale (r : K) :
    ((scFunctor p).map (scalarComplexMap K p m r)).τ₂ ≫ chartCoefficients K p m =
      chartCoefficients K p m ≫ scalarCoefficients K p m r := by
  apply AddCommGrpCat.ext
  intro x
  obtain ⟨b, rfl⟩ := (degreeEquiv K p m (p + 1)).surjective x
  change topLaurentCoefficients m (p + 1) ((degreeEquiv K p m (p + 1)).symm
      ((scalarComplexMap K p m r).f (p + 1) (degreeEquiv K p m (p + 1) b))) =
    r • topLaurentCoefficients m (p + 1) ((degreeEquiv K p m (p + 1)).symm (degreeEquiv K p m (p + 1) b))
  rw [degreeEquiv_scale, AddEquiv.symm_apply_apply, AddEquiv.symm_apply_apply]
  exact topLaurentCoefficients_scale m (p + 1) r b

private abbrev homologyIso :=
  HomologicalComplex.homologyFunctorIso' AddCommGrpCat.{0} (ComplexShape.up ℕ)
    p (p + 1) (p + 2) (by simp) (by simp)

private def homologyCoefficients : (E K p m).cochainComplex.homology (p + 1) ⟶ coeffSpace K p m :=
  ((homologyIso p).app (E K p m).cochainComplex).hom ≫
    descHomologyOfExact _ (chartCoefficients K p m) (chartCoefficients_exact K p m)

/-- Top Čech cohomology of a negative twist is a finite module over the base field. -/
theorem pspaceTwist_topCech_finite :
    letI := sectionAlgebra (PSpace.str K (p + 1)) ⊤
    let H := ModuleCechCohomology (X := X K p) ⊤ (U K p) (F K p m) (p + 1)
    letI := Module.compHom H (algebraMap K Γ(X K p, ⊤))
    Module.Finite K H := by
  letI := sectionAlgebra (PSpace.str K (p + 1)) ⊤
  let H := ModuleCechCohomology (X := X K p) ⊤ (U K p) (F K p m) (p + 1)
  letI := Module.compHom H (algebraMap K Γ(X K p, ⊤))
  let f := homologyCoefficients K p m
  let L : H →ₗ[K] (TopLaurentExponents (Fin (p + 2)) m → K) :=
    { f.hom with map_smul' := fun r x => by
        let g := scalarComplexMap K p m r
        let e := (homologyIso p).app (E K p m).cochainComplex
        let a := descHomologyOfExact _ (chartCoefficients K p m) (chartCoefficients_exact K p m)
        let b := scalarCoefficients K p m r
        have h₁ : HomologicalComplex.homologyMap g (p + 1) ≫ e.hom =
            e.hom ≫ ShortComplex.homologyMap ((scFunctor p).map g) :=
          (homologyIso p).hom.naturality g
        have h₂ : ShortComplex.homologyMap ((scFunctor p).map g) ≫ a = a ≫ b :=
          descHomologyOfExact_natural _ _ _ _ _ (chartCoefficients_scale K p m r)
        have hh : HomologicalComplex.homologyMap g (p + 1) ≫ f = f ≫ b := by
          change HomologicalComplex.homologyMap g (p + 1) ≫ e.hom ≫ a = (e.hom ≫ a) ≫ b
          rw [← Category.assoc, h₁, Category.assoc, h₂, Category.assoc]
        exact ConcreteCategory.congr_hom hh x }
  apply Module.Finite.of_injective L
  exact (descHomologyOfExact_injective _ _ (chartCoefficients_exact K p m)).comp
    ((AddCommGrpCat.mono_iff_injective _).mp inferInstance)

end GlobalTheory.SchemeCohomology
