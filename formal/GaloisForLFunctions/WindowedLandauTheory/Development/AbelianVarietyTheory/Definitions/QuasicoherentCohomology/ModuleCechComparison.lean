import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.LerayComparison
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.CohomologyPullback

/-! The natural Leray comparison is linear for the global scalars of a scheme module. -/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian Opposite TopologicalSpace
  HTGeometry RHTower

namespace GlobalTheory.SchemeCohomology

private def sheafCechFunctor (X : TopCat.{0}) (V : Opens X) {ι : Type}
    [DecidableEq ι] [LinearOrder ι] (U : ι → Opens X) :
    TopCat.Sheaf AddCommGrpCat.{0} X ⥤ CochainComplex AddCommGrpCat.{0} ℕ where
  obj := sheafCechComplex V U
  map := sheafCechComplexMap V U
  map_id _ := by ext n c; rfl
  map_comp _ _ := by ext n c; rfl

private instance sheafCechFunctor_additive (X : TopCat.{0}) (V : Opens X) {ι : Type}
    [DecidableEq ι] [LinearOrder ι] (U : ι → Opens X) :
    (sheafCechFunctor X V U).Additive where
  map_add := by intros; ext n c; rfl

variable {X : Scheme.{0}} {ι : Type} [DecidableEq ι] [LinearOrder ι]
  (V : X.Opens) (U : ι → X.Opens)

private abbrev moduleCechFunctor (n : ℕ) : X.Modules ⥤ AddCommGrpCat.{0} :=
  SheafOfModules.toSheaf X.ringCatSheaf ⋙ sheafCechFunctor X V U ⋙
    HomologicalComplex.homologyFunctor _ (ComplexShape.up ℕ) n

private instance moduleCechFunctor_additive (n : ℕ) : (moduleCechFunctor V U n).Additive where
  map_add {M N} f g := by
    let A := SheafOfModules.toSheaf X.ringCatSheaf
    let B := sheafCechFunctor X V U
    haveI : A.Additive := inferInstanceAs (SheafOfModules.toSheaf X.ringCatSheaf).Additive
    haveI : B.Additive := sheafCechFunctor_additive X V U
    change HomologicalComplex.homologyMap (B.map (A.map (f + g))) n =
      HomologicalComplex.homologyMap (B.map (A.map f)) n + HomologicalComplex.homologyMap (B.map (A.map g)) n
    have hA : A.map (f + g) = A.map f + A.map g := A.map_add
    have hB : B.map (A.map f + A.map g) = B.map (A.map f) + B.map (A.map g) := B.map_add
    exact (congrArg (fun k => HomologicalComplex.homologyMap (B.map k) n) hA).trans
      ((congrArg (fun k => HomologicalComplex.homologyMap k n) hB).trans
        (HomologicalComplex.homologyMap_add _ _ _))

/-- Čech cohomology of a scheme module for the given family of opens. -/
def ModuleCechCohomology (M : X.Modules) (n : ℕ) : Type := (moduleCechFunctor V U n).obj M

instance (M : X.Modules) (n : ℕ) : AddCommGroup (ModuleCechCohomology V U M n) :=
  inferInstanceAs (AddCommGroup ((moduleCechFunctor V U n).obj M))

private def moduleCechAction (M : X.Modules) (n : ℕ) :
    Γ(X, ⊤) →+* AddMonoid.End (ModuleCechCohomology V U M n) where
  toFun r := ((moduleCechFunctor V U n).map (globalSectionEnd M r)).hom
  map_one' := by
    rw [map_one]
    exact congrArg AddCommGrpCat.Hom.hom ((moduleCechFunctor V U n).map_id M)
  map_mul' r s := by
    rw [map_mul]
    change ((moduleCechFunctor V U n).map (globalSectionEnd M s ≫ globalSectionEnd M r)).hom = _
    rw [Functor.map_comp]
    rfl
  map_zero' := by
    rw [map_zero]
    exact congrArg AddCommGrpCat.Hom.hom ((moduleCechFunctor V U n).map_zero M M)
  map_add' r s := by
    rw [map_add]
    exact congrArg AddCommGrpCat.Hom.hom ((moduleCechFunctor V U n).map_add
      (f := (globalSectionEnd M r : M ⟶ M)) (g := (globalSectionEnd M s : M ⟶ M)))

instance (M : X.Modules) (n : ℕ) : Module Γ(X, ⊤) (ModuleCechCohomology V U M n) :=
  Module.compHom _ (moduleCechAction V U M n)

local instance moduleCechHasExt (Y : TopCat.{0}) : HasExt.{0} (TopCat.Sheaf AddCommGrpCat.{0} Y) :=
  hasExt_of_enoughInjectives _

private def freeSheafComparison {Y : TopCat.{0}} (W : Opens Y) :
    deningerOpenFree W ⟶ openFree W :=
  (deningerOpenFreeHomEquiv W (openFree W)).symm (openFreeHomEquiv W _ (𝟙 _))

private theorem freeSheafComparison_apply {Y : TopCat.{0}} (W : Opens Y)
    {G : TopCat.Sheaf AddCommGrpCat.{0} Y} (g : openFree W ⟶ G) :
    deningerOpenFreeHomEquiv W G (freeSheafComparison W ≫ g) = openFreeHomEquiv W G g := by
  rw [deningerOpenFreeHomEquiv_naturality_right, freeSheafComparison, Equiv.apply_symm_apply,
    ← openFreeHomEquiv_natural, Category.id_comp]

private instance {Y : TopCat.{0}} (W : Opens Y) : IsIso (freeSheafComparison W) := by
  apply isIso_of_coyoneda_map_bijective
  intro G
  convert ((openFreeHomEquiv W G).trans (deningerOpenFreeHomEquiv W G).symm).bijective using 1
  funext g
  exact (deningerOpenFreeHomEquiv W G).injective ((freeSheafComparison_apply W g).trans
    (Equiv.apply_symm_apply _ _).symm)

private def changeFreeSource {Y : TopCat.{0}} (W : Opens Y) (G : TopCat.Sheaf AddCommGrpCat.{0} Y)
    (n : ℕ) : deningerSheafCohomology.{0} W G n ≃+ Ext (openFree W) G n :=
  let e := asIso (freeSheafComparison W)
  { (Ext.mk₀ e.inv).precomp G (zero_add n) with
    invFun := (Ext.mk₀ e.hom).precomp G (zero_add n)
    left_inv := fun y => by
      change (Ext.mk₀ e.hom).comp ((Ext.mk₀ e.inv).comp y (zero_add n)) (zero_add n) = y
      rw [← Ext.comp_assoc_of_second_deg_zero, Ext.mk₀_comp_mk₀, e.hom_inv_id, Ext.mk₀_id_comp]
    right_inv := fun y => by
      change (Ext.mk₀ e.inv).comp ((Ext.mk₀ e.hom).comp y (zero_add n)) (zero_add n) = y
      rw [← Ext.comp_assoc_of_second_deg_zero, Ext.mk₀_comp_mk₀, e.inv_hom_id, Ext.mk₀_id_comp] }

/-- The comparison on a cover with acyclic intersections preserves global scalar multiplication. -/
def moduleLerayLinearEquiv (M : X.Modules) (n : ℕ) (hcov : V ≤ ⨆ i, U i)
    (hM : ∀ a : Finset ι, a.Nonempty →
      DeningerAcyclicOn.{0} ((SheafOfModules.toSheaf X.ringCatSheaf).obj M) (coverInter V U a)) :
    ModuleCechCohomology V U M n ≃ₗ[Γ(X, ⊤)] CohomologyOn M (coverInter V U ∅) n :=
  let W := coverInter V U ∅
  let A := SheafOfModules.toSheaf X.ringCatSheaf
  let e := lerayCechEquiv hcov n (A.obj M) hM
  { e.trans (changeFreeSource W (A.obj M) n) with
    map_smul' r y := by
      let g := A.map (globalSectionEnd M r)
      let φ := Ext.mk₀ (asIso (freeSheafComparison W)).inv
      have h := lerayCechEquiv_natural hcov n hM hM g y
      change e (r • y) = (e y).comp (Ext.mk₀ g) (add_zero n) at h
      change φ.comp (e (r • y)) (zero_add n) =
        (φ.comp (e y) (zero_add n)).comp (Ext.mk₀ g) (add_zero n)
      rw [h, Ext.comp_assoc_of_third_deg_zero] }

end GlobalTheory.SchemeCohomology
