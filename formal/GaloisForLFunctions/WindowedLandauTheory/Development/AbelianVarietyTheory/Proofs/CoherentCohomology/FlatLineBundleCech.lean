import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.LineBundleAffineSections
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.LinearCechComplex
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.RelativeForms
import GaloisForLFunctions.HTGeometry.SheafFinsetCech
import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-! On a flat scheme the affine Čech complex of a line bundle is bounded and flat. -/

noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace HTGeometry
open GlobalTheory.SchemeCohomology ReciprocityTheory.ChartRestriction.G.Semi

namespace GlobalTheory.LineBundleSections

variable {R : Type} [CommRing R] {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of R))
  (F : X.Modules) {ι : Type} [DecidableEq ι] [LinearOrder ι] (U : ι → X.Opens)

abbrev sectionDatum : FinsetCechDatum.{0} ι :=
  sheafCech ((SheafOfModules.toSheaf X.ringCatSheaf).obj F) ⊤ U

abbrev sectionDatumModule (s : Finset ι) : Module R ((sectionDatum F U).obj s) :=
  letI := sectionAlgebra f (coverInter ⊤ U s)
  Module.compHom Γ(F, coverInter ⊤ U s) (algebraMap R Γ(X, coverInter ⊤ U s))

theorem res_base_smul {s t : Finset ι} (h : s ⊆ t) (r : R)
    (x : (sectionDatum F U).obj s) :
    letI (a : Finset ι) := sectionDatumModule f F U a
    (sectionDatum F U).res h (r • x) = r • (sectionDatum F U).res h x := by
  let S := coverInter ⊤ U s
  let T := coverInter ⊤ U t
  let i : T ⟶ S := homOfLE (coverInter_anti h)
  letI := sectionAlgebra f S
  letI := sectionAlgebra f T
  let x' : Γ(F, S) := x
  change F.presheaf.map i.op ((algebraMap R Γ(X, S) r) • x') =
    (algebraMap R Γ(X, T) r) • F.presheaf.map i.op x'
  rw [F.map_smul]
  exact congrArg (fun a : Γ(X, T) => a • F.presheaf.map i.op x') ((sectionRes f i).commutes r)

/-- The Čech complex of sections, with the scalar action restricted to the affine base. -/
def cech : CochainComplex (ModuleCat.{0} R) ℕ :=
  letI (s : Finset ι) := sectionDatumModule f F U s
  (sectionDatum F U).linearComplex (res_base_smul f F U)

theorem cech_isZero [Fintype ι] (n : ℕ) (hn : Fintype.card ι ≤ n) :
    Limits.IsZero ((cech f F U).X n) := by
  letI (s : Finset ι) := sectionDatumModule f F U s
  exact (sectionDatum F U).linearComplex_X_isZero (res_base_smul f F U) n hn

theorem cech_flat [Flat f] [Fintype ι] {L : LB X} (hL : L.IsLB)
    (haff : ∀ s : Finset ι, s.Nonempty → IsAffineOpen (coverInter ⊤ U s)) (n : ℕ) :
    Module.Flat R ((cech f (toMod L) U).X n) := by
  letI (s : Finset ι) := sectionDatumModule f (toMod L) U s
  apply (sectionDatum (toMod L) U).linearComplex_X_flat (res_base_smul f (toMod L) U) n
  intro s hs
  let V := coverInter ⊤ U s
  letI := sectionAlgebra f V
  have hbase : (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom.Flat :=
    RingHom.Flat.of_bijective (ConcreteCategory.bijective_of_isIso _)
  haveI : Module.Flat R Γ(X, V) := RingHom.flat_algebraMap_iff.mp
    (hbase.comp (f.flat_appLE (isAffineOpen_top _) (haff s hs) (by simp)))
  haveI : Module.Projective Γ(X, V) Γ(toMod L, V) :=
    (finite_projective_sections hL (haff s hs)).2
  letI : Module R Γ(toMod L, V) := sectionDatumModule f (toMod L) U s
  letI : IsScalarTower R Γ(X, V) Γ(toMod L, V) :=
    IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  exact Module.Flat.trans R Γ(X, V) Γ(toMod L, V)

end GlobalTheory.LineBundleSections
