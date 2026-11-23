import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.GodementCechComparison
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.CechCoefficientDescent

/-! Čech cochains of a direct image are the cochains of the inverse-image cover. -/

noncomputable section

open CategoryTheory Opposite TopologicalSpace HTGeometry

namespace GlobalTheory.SchemeCohomology

variable {X Y : TopCat.{0}} (f : Y ⟶ X) {ι : Type}
  (V : Opens X) (U : ι → Opens X)

private abbrev preimage (W : Opens X) : Opens Y := (Opens.map f).obj W

private def preimageInfHom : InfTopHom (Opens X) (Opens Y) :=
  ⟨⟨preimage f, fun _ _ => rfl⟩, rfl⟩

theorem preimage_coverInter (I : Finset ι) :
    preimage f (coverInter V U I) = coverInter (preimage f V) (preimage f ∘ U) I := by
  change preimageInfHom f (V ⊓ I.inf U) = preimageInfHom f V ⊓ I.inf (preimageInfHom f ∘ U)
  rw [map_inf, map_finset_inf]

theorem preimage_cover_le (h : V ≤ ⨆ i, U i) :
    preimage f V ≤ ⨆ i, preimage f (U i) := by
  intro y hy
  have hx : f y ∈ ⨆ i, U i := h hy
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx
  exact Opens.mem_iSup.mpr ⟨i, hi⟩

private abbrev Push := TopCat.Sheaf.pushforward AddCommGrpCat.{0} f

variable [DecidableEq ι] [LinearOrder ι]

/-- The section maps identifying the Čech data on the two covers. -/
def pushforwardCechDatumMap (G : TopCat.Sheaf AddCommGrpCat.{0} Y) :
    (sheafCech ((Push f).obj G) V U).Hom
      (sheafCech G (preimage f V) (preimage f ∘ U)) where
  app I := ConcreteCategory.hom (G.1.map (eqToHom (preimage_coverInter f V U I).symm).op)
  comm {I J} hij z := by
    let r := homOfLE (coverInter_anti (V := V) (U := U) hij)
    let r' := homOfLE (coverInter_anti (V := preimage f V) (U := preimage f ∘ U) hij)
    let eI := eqToHom (preimage_coverInter f V U I).symm
    let eJ := eqToHom (preimage_coverInter f V U J).symm
    change G.1.map r'.op (G.1.map eI.op z) =
      G.1.map eJ.op (G.1.map ((Opens.map f).map r).op z)
    have hc : eI.op ≫ r'.op = ((Opens.map f).map r).op ≫ eJ.op := Subsingleton.elim _ _
    exact (ConcreteCategory.congr_hom (G.1.map_comp eI.op r'.op) z).symm.trans
      ((ConcreteCategory.congr_hom (congrArg G.1.map hc) z).trans
        (ConcreteCategory.congr_hom (G.1.map_comp ((Opens.map f).map r).op eJ.op) z))

omit [DecidableEq ι] [LinearOrder ι] in
theorem pushforwardCechDatumMap_bijective (G : TopCat.Sheaf AddCommGrpCat.{0} Y) (I : Finset ι) :
    Function.Bijective ((pushforwardCechDatumMap f V U G).app I) :=
  ConcreteCategory.bijective_of_isIso (G.1.map (eqToHom (preimage_coverInter f V U I).symm).op)

/-- The direct-image Čech complex is canonically isomorphic to the preimage Čech complex. -/
def pushforwardCechIso (G : TopCat.Sheaf AddCommGrpCat.{0} Y) :
    sheafCechComplex V U ((Push f).obj G) ≅
      sheafCechComplex (preimage f V) (preimage f ∘ U) G := by
  let a := pushforwardCechDatumMap f V U G
  letI (n : ℕ) : IsIso (a.cochainMap.f n) :=
    (ConcreteCategory.isIso_iff_bijective (f := a.cochainMap.f n)).mpr
      (cochainMap_bijective_of_nonempty a (fun I _ => pushforwardCechDatumMap_bijective f V U G I) n)
  letI : IsIso a.cochainMap := HomologicalComplex.Hom.isIso_of_components _
  exact asIso a.cochainMap

theorem pushforwardCechIso_natural {F G : TopCat.Sheaf AddCommGrpCat.{0} Y} (φ : F ⟶ G) :
    sheafCechComplexMap V U ((Push f).map φ) ≫ (pushforwardCechIso f V U G).hom =
      (pushforwardCechIso f V U F).hom ≫ sheafCechComplexMap (preimage f V) (preimage f ∘ U) φ := by
  apply HomologicalComplex.hom_ext
  intro n
  apply AddCommGrpCat.ext
  intro z
  apply Subtype.ext
  funext I
  let e := eqToHom (preimage_coverInter f V U I).symm
  exact ConcreteCategory.congr_hom (φ.1.naturality e.op).symm (z.val I)

/-- The inverse-image comparison is natural in the coefficient sheaf. -/
def pushforwardCechFunctorIso :
    Push f ⋙ abelianCechFunctor X V U ≅
      abelianCechFunctor Y (preimage f V) (preimage f ∘ U) :=
  NatIso.ofComponents (pushforwardCechIso f V U)
    (fun {_ _} φ => pushforwardCechIso_natural f V U φ)

end GlobalTheory.SchemeCohomology
