import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.LinearCechMaps
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.FlatLineBundleCech
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.AffineLineBundleBaseChange
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.AffineBaseChangeSectionRings
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.LineBundleSectionScalarChange

/-! A Čech complex over the image of an open immersion can be computed on
the inverse-image cover with the pulled-back bundle. -/

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace HTGeometry Opposite
open GlobalTheory.SchemeCohomology ReciprocityTheory.ChartRestriction.G.Semi TensorProduct

namespace GlobalTheory.LineBundleSections

variable {R : Type} [CommRing R] {X : Scheme.{0}} (f : X ⟶ Spec (.of R)) (F : X.Modules)
  {κ : Type} [LinearOrder κ] (W : X.Opens) (U : κ → X.Opens)

abbrev openSectionDatum : FinsetCechDatum.{0} κ :=
  sheafCech ((SheafOfModules.toSheaf X.ringCatSheaf).obj F) W U

abbrev openSectionDatumModule (s : Finset κ) : Module R ((openSectionDatum F W U).obj s) :=
  sectionBaseModule f F (coverInter W U s)

theorem open_res_base_smul {s t : Finset κ} (h : s ⊆ t) (r : R)
    (x : (openSectionDatum F W U).obj s) :
    letI (a : Finset κ) := openSectionDatumModule f F W U a
    (openSectionDatum F W U).res h (r • x) = r • (openSectionDatum F W U).res h x := by
  let A := coverInter W U s
  let B := coverInter W U t
  let i : B ⟶ A := homOfLE (coverInter_anti h)
  letI := sectionAlgebra f A
  letI := sectionAlgebra f B
  let y : Γ(F, A) := x
  change F.presheaf.map i.op ((algebraMap R Γ(X, A) r) • y) =
    (algebraMap R Γ(X, B) r) • F.presheaf.map i.op y
  rw [F.map_smul]
  exact congrArg (fun a : Γ(X, B) => a • F.presheaf.map i.op y) ((sectionRes f i).commutes r)

/-- Count Čech cochains on intersections inside the given open. -/
def cechOverOpen : CochainComplex (ModuleCat.{0} R) ℕ :=
  letI (s : Finset κ) := openSectionDatumModule f F W U s
  (openSectionDatum F W U).linearComplex (open_res_base_smul f F W U)

private theorem bijective_pullSection_of_openImmersion {X Y : Scheme.{0}} {π : Y ⟶ X}
    [IsOpenImmersion π] {L : LB X} (hL : L.IsLB) {A : X.Opens} (hA : IsAffineOpen A)
    (hAr : A ≤ π.opensRange) {B : Y.Opens} (hB : B = π ⁻¹ᵁ A) :
    Function.Bijective (pullSection (ChartPull.pull L π) hB.le) := by
  subst B
  let σ := pullSection (ChartPull.pull L π) (le_rfl : π ⁻¹ᵁ A ≤ π ⁻¹ᵁ A)
  let S := Γ(X, A)
  let T := Γ(Y, π ⁻¹ᵁ A)
  let M := Γ(toMod L, A)
  let N := Γ(toMod (L.pull π), π ⁻¹ᵁ A)
  let ρ := (π.appLE A (π ⁻¹ᵁ A) le_rfl).hom
  letI : Algebra S T := ρ.toAlgebra
  letI : Module S N := Module.compHom _ ρ
  letI : IsScalarTower S T N := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  haveI : IsIso (π.app A) := π.isIso_app A hAr
  have hρ : Function.Bijective (algebraMap S T) := by
    change Function.Bijective (π.appLE A (π ⁻¹ᵁ A) le_rfl)
    rw [← Scheme.Hom.app_eq_appLE]
    exact ConcreteCategory.bijective_of_isIso (π.app A)
  let u : S ≃ₗ[S] T := LinearEquiv.ofBijective (Algebra.linearMap S T) hρ
  let e := (TensorProduct.lid S M).symm.trans (TensorProduct.congr u (LinearEquiv.refl S M))
  have hc := isBaseChange_pullSection hL hA (hA.preimage_of_isOpenImmersion π hAr) le_rfl
  have he (x : M) : e x = (1 : T) ⊗ₜ[S] x := by simp [e, u]
  have hσ : (hc.equiv ∘ e : M → N) = σ := funext fun x => by
    change hc.equiv (e x) = _
    rw [he, hc.equiv_tmul, one_smul]
    rfl
  exact hσ ▸ hc.equiv.bijective.comp e.bijective

/-- Restricting along an open immersion identifies the section complexes on
affine intersections contained in its image. -/
def openCechPullbackIso {Y : Scheme.{0}} (π : Y ⟶ X) [IsOpenImmersion π] {L : LB X}
    (hL : L.IsLB) (hU : ∀ s : Finset κ, s.Nonempty → IsAffineOpen (coverInter π.opensRange U s)) :
    cechOverOpen f (toMod L) π.opensRange U ≅
      cech (π ≫ f) (toMod (L.pull π)) (fun i => π ⁻¹ᵁ U i) := by
  let F := toMod L
  let G := toMod (L.pull π)
  let V (i : κ) := π ⁻¹ᵁ U i
  let W := π.opensRange
  let B := openSectionDatum F W U
  let D := sectionDatum G V
  letI (s : Finset κ) := openSectionDatumModule f F W U s
  letI (s : Finset κ) := sectionDatumModule (π ≫ f) G V s
  have h (s : Finset κ) : coverInter ⊤ V s = π ⁻¹ᵁ coverInter W U s := by
    ext y
    change y ∈ coverInter ⊤ V s ↔ π y ∈ coverInter W U s
    rw [mem_coverInter, mem_coverInter]
    have hy : π y ∈ W := by
      change π y ∈ (π.opensRange : Set X)
      rw [Scheme.Hom.coe_opensRange]
      exact ⟨y, rfl⟩
    exact ⟨fun h => ⟨hy, h.2⟩, fun h => ⟨trivial, h.2⟩⟩
  let P := ChartPull.pull L π
  let φ : B.Hom D :=
    { app := fun s => pullSection P (h s).le
      comm := fun i x => (pullSection_restrict P _ _ (coverInter_anti i) (coverInter_anti i) x).symm }
  have hφ (s : Finset κ) (r : R) (x : B.obj s) : φ.app s (r • x) = r • φ.app s x := by
    let A := coverInter W U s
    let V₀ := coverInter ⊤ V s
    letI := sectionAlgebra f A
    letI := sectionAlgebra (π ≫ f) V₀
    letI : Algebra R R := Algebra.id R
    let y : Γ(F, A) := x
    have hbase : π ≫ f = (π ≫ f) ≫ Spec.map (CommRingCat.ofHom (algebraMap R R)) := by
      change π ≫ f = (π ≫ f) ≫ Spec.map (𝟙 (CommRingCat.of R))
      rw [Spec.map_id, Category.comp_id]
    change pullSection P (h s).le (algebraMap R Γ(X, A) r • y) =
      algebraMap R Γ(Y, V₀) r • pullSection P (h s).le y
    rw [pullSection_smul]
    exact congrArg (fun a : Γ(Y, V₀) => a • pullSection P (h s).le y)
      (appLE_base_algebraMap hbase (h s).le r)
  let b : cechOverOpen f F W U ⟶ cech (π ≫ f) G V :=
    FinsetCechDatum.linearCochainMap (open_res_base_smul f F W U) (res_base_smul (π ≫ f) G V) φ hφ
  letI : IsIso b := FinsetCechDatum.isIso_linearCochainMap _ _ φ hφ fun s hs =>
    bijective_pullSection_of_openImmersion hL (hU s hs) inf_le_left (h s)
  exact asIso b

end GlobalTheory.LineBundleSections
