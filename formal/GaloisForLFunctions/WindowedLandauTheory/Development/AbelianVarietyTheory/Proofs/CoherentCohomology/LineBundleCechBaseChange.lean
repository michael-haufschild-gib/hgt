import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.LinearCechBaseChange
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.FlatLineBundleCech
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.LineBundleSectionScalarChange

/-! Change of affine base commutes with the Čech complex of a line bundle. -/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace HTGeometry
open GlobalTheory.SchemeCohomology ReciprocityTheory.ChartRestriction.G.Semi
open scoped ChangeOfRings

namespace GlobalTheory.LineBundleSections

variable {R S : Type} [CommRing R] [CommRing S] [Algebra R S]
  {X Y : Scheme.{0}} {f : X ⟶ Spec (CommRingCat.of R)} {g : Y ⟶ Spec (CommRingCat.of S)}
  {π : Y ⟶ X} (L : LB X) {ι : Type} [DecidableEq ι] [LinearOrder ι] (U : ι → X.Opens)

theorem coverInter_pull (s : Finset ι) :
    coverInter ⊤ (fun i => π ⁻¹ᵁ U i) s = π ⁻¹ᵁ coverInter ⊤ U s := by
  ext y
  change y ∈ coverInter ⊤ (fun i => π ⁻¹ᵁ U i) s ↔ π y ∈ coverInter ⊤ U s
  rw [mem_coverInter, mem_coverInter]
  exact ⟨fun hy => ⟨trivial, hy.2⟩, fun hy => ⟨trivial, hy.2⟩⟩

private abbrev F := toMod L
private abbrev G := toMod (L.pull π)
private abbrev D := sectionDatum (F L) U
private abbrev E := sectionDatum (G L (π := π)) (fun i => π ⁻¹ᵁ U i)

private def sectionPullDatum : (D L U).Hom (E (π := π) L U) where
  app s := pullSection (ChartPull.pull L π) (coverInter_pull (π := π) U s).le
  comm h x := (pullSection_restrict (ChartPull.pull L π) (coverInter_pull (π := π) U _).le
    (coverInter_pull (π := π) U _).le (coverInter_anti h) (coverInter_anti h) x).symm

private theorem sectionPullDatum_smul
    (w : π ≫ f = g ≫ Spec.map (CommRingCat.ofHom (algebraMap R S)))
    (s : Finset ι) (r : R) (x : (D L U).obj s) :
    letI := sectionDatumModule f (F L) U s
    letI := sectionDatumModule g (G L (π := π)) (fun i => π ⁻¹ᵁ U i) s
    (sectionPullDatum (π := π) L U).app s (r • x) =
      algebraMap R S r • (sectionPullDatum (π := π) L U).app s x := by
  let W := coverInter ⊤ U s
  let W' := coverInter ⊤ (fun i => π ⁻¹ᵁ U i) s
  letI := sectionAlgebra f W
  letI := sectionAlgebra g W'
  let x' : Γ(F L, W) := x
  let P := ChartPull.pull L π
  let h : W' ≤ π ⁻¹ᵁ W := (coverInter_pull (π := π) U s).le
  change pullSection P h (algebraMap R Γ(X, W) r • x') =
    algebraMap S Γ(Y, W') (algebraMap R S r) • pullSection P h x'
  rw [pullSection_smul, appLE_base_algebraMap w]

/-- The scalar extension of the affine Čech complex is the complex on the inverse-image cover. -/
def cechBaseChangeIso [Fintype ι] (hL : L.IsLB) (α : R →+* S)
    (H : IsPullback π g f (Spec.map (CommRingCat.ofHom α)))
    (hU : ∀ s : Finset ι, s.Nonempty → IsAffineOpen (coverInter ⊤ U s)) :
    (((ModuleCat.extendScalars α).mapHomologicalComplex (ComplexShape.up ℕ)).obj
      (cech f (F L) U)) ≅ cech g (G L (π := π)) (fun i => π ⁻¹ᵁ U i) := by
  letI : Algebra R S := α.toAlgebra
  letI (s : Finset ι) := sectionDatumModule f (F L) U s
  letI (s : Finset ι) := sectionDatumModule g (G L (π := π)) (fun i => π ⁻¹ᵁ U i) s
  let φ := sectionPullDatum (π := π) L U
  let hφ := sectionPullDatum_smul L U H.w
  let hD {s t : Finset ι} (h : s ⊆ t) (r : R) (x : (D L U).obj s) :=
    res_base_smul f (F L) U h r x
  let hE {s t : Finset ι} (h : s ⊆ t) (r : S) (x : (E (π := π) L U).obj s) :=
    res_base_smul g (G L (π := π)) (fun i => π ⁻¹ᵁ U i) h r x
  let β := FinsetCechDatum.linearBaseChange α φ hφ hD hE
  have hi : IsIso β := FinsetCechDatum.isIso_linearBaseChange α φ hφ hD hE fun s hs =>
    isBaseChange_scalarPullSection L hL H (hU s hs) (coverInter_pull (π := π) U s)
  exact @asIso _ _ _ _ β hi

theorem cechBaseChangeIso_hom_f_tmul [Fintype ι] (hL : L.IsLB) (α : R →+* S)
    (H : IsPullback π g f (Spec.map (CommRingCat.ofHom α)))
    (hU : ∀ s : Finset ι, s.Nonempty → IsAffineOpen (coverInter ⊤ U s))
    (n : ℕ) (r : S) (x : (cech f (F L) U).X n) (s : Finset ι) :
    letI := sectionDatumModule g (G L (π := π)) (fun i => π ⁻¹ᵁ U i) s
    ((cechBaseChangeIso L U hL α H hU).hom.f n (r ⊗ₜ[R,α] x)).1 s =
      r • (sectionPullDatum (π := π) L U).app s (x.1 s) := rfl

end GlobalTheory.LineBundleSections
