import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.LinearCechHomologyComparison
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.PerfectCochainModel
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.ProjectiveLineBundleCohomology
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.AffineQuasicoherentAcyclic

/-! A line bundle on a flat projective scheme has a finite projective Čech model. -/

noncomputable section

open AlgebraicGeometry CategoryTheory HTGeometry
open GlobalTheory.SchemeCohomology ReciprocityTheory.ChartRestriction.G.Semi UpperTheory.Cb

namespace GlobalTheory.LineBundleSections

variable {R : Type} [CommRing R] [IsNoetherianRing R] {X : Scheme.{0}}
  (f : X ⟶ Spec (CommRingCat.of R)) {L : LB X} (hL : L.IsLB)
  {ι : Type} [Fintype ι] [DecidableEq ι] [LinearOrder ι] (U : ι → X.Opens)
  (hcov : ⊤ ≤ ⨆ i, U i) (hU : ∀ s : Finset ι, s.Nonempty → IsAffineOpen (coverInter ⊤ U s))

include hL hcov hU

/-- Finiteness of line-bundle cohomology carries to the scalar-linear affine Čech complex. -/
theorem cech_homology_finite (hf : IsProjOver f) (q : ℕ) :
    Module.Finite R ((cech f (toMod L) U).homology q) := by
  let F := toMod L
  letI : F.IsQuasicoherent := isQuasicoherent_toMod hL
  letI := sectionAlgebra f ⊤
  let A := ModuleCechCohomology ⊤ U F q
  let B := CohomologyOn F ⊤ q
  letI : Module R A := Module.compHom A (algebraMap R Γ(X, ⊤))
  letI : Module R B := Module.compHom B (algebraMap R Γ(X, ⊤))
  letI : Module.Finite R B := cohomology_finite_of_projective f hf hL q
  let e := cechCohomologyEquiv f F U q
  have a : A ≃ₗ[Γ(X, ⊤)] B := by
    have b := moduleLerayLinearEquiv ⊤ U F q hcov
      (fun s hs => quasicoherent_acyclicOn F (hU s hs))
    rwa [coverInter_empty] at b
  let b : A →ₗ[R] B :=
    { a.toAddMonoidHom with
      map_smul' r x := a.map_smul (algebraMap R Γ(X, ⊤) r) x }
  exact Module.Finite.of_injective (b.comp e.toLinearMap) (a.injective.comp e.injective)

/-- A finite projective model computes the affine Čech complex after every scalar extension. -/
theorem exists_perfect_cech [Flat f] (hf : IsProjOver f) :
    ∃ (K : CochainComplex (ModuleCat.{0} R) ℕ) (φ : K ⟶ cech f (toMod L) U),
      (∀ q, Fintype.card ι < q → Limits.IsZero (K.X q)) ∧
      (∀ q, Module.Finite R (K.X q) ∧ Module.Projective R (K.X q)) ∧
      QuasiIso φ ∧ ∀ (R' : Type) [CommRing R'] [Algebra R R'],
        QuasiIso (((ModuleCat.extendScalars.{0, 0, 0} (algebraMap R R')).mapHomologicalComplex _).map φ) := by
  obtain ⟨K, φ, hk, hfin, _, hproj, hφ, _, hbc⟩ :=
    GlobalTheory.exists_finite_projective_complex_quasiIso
      (cech f (toMod L) U) (Fintype.card ι) (fun q hq => cech_isZero f (toMod L) U q hq.le)
      (cech_flat f U hL hU) (cech_homology_finite f hL U hcov hU hf)
  exact ⟨K, φ, hk, fun q => ⟨hfin q, hproj q⟩, hφ, hbc⟩

end GlobalTheory.LineBundleSections
