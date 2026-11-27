import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.PerfectCochainModel
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.ResidueFibreExactness
import Mathlib.RingTheory.Support

/-! A bounded flat complex with finite homology is supported away from
points where its derived field fibre is acyclic. -/

open CategoryTheory CategoryTheory.Limits

namespace GlobalTheory

/-- If the field fibre is acyclic, each homology module is annihilated by
some scalar nonvanishing at that fibre. -/
theorem exists_smul_homology_eq_zero_of_acyclic_fibre {R K : Type} [CommRing R]
    [IsNoetherianRing R] [Field K] (χ : R →+* K)
    (C : CochainComplex (ModuleCat.{0} R) ℕ) (N : ℕ)
    (hN : ∀ n, N < n → IsZero (C.X n)) (hflat : ∀ n, Module.Flat R (C.X n))
    (hfin : ∀ n, Module.Finite R (C.homology n))
    (hac : (((ModuleCat.extendScalars χ).mapHomologicalComplex (ComplexShape.up ℕ)).obj C).Acyclic)
    (n : ℕ) : ∃ r : R, χ r ≠ 0 ∧ ∀ z : C.homology n, r • z = 0 := by
  letI : Algebra R K := χ.toAlgebra
  let F := (ModuleCat.extendScalars χ).mapHomologicalComplex (ComplexShape.up ℕ)
  obtain ⟨P, φ, -, hpfin, -, hproj, hφ, -, hφK⟩ :=
    exists_finite_projective_complex_quasiIso C N hN hflat hfin
  letI : QuasiIso φ := hφ
  letI : QuasiIso (F.map φ) := hφK K
  have he : (F.obj P).ExactAt n := (exactAt_iff_of_quasiIsoAt (F.map φ) n).mpr (hac n)
  let D := P.sc n
  have hD : Function.Exact (D.f.hom.lTensor K) (D.g.hom.lTensor K) :=
    (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp he
  have hpt (z : P.homology n) : ∃ r : R, χ r ≠ 0 ∧ r • z = 0 := by
    let e := D.moduleCatHomologyIso.toLinearEquiv
    obtain ⟨b, hb⟩ := Submodule.Quotient.mk_surjective _ (e z)
    letI : Module.Finite R D.X₂ := hpfin _
    letI : Module.Finite R D.X₃ := hpfin _
    letI : Module.Projective R D.X₃ := hproj _
    have hz : D.g.hom ∘ₗ D.f.hom = 0 := congrArg ModuleCat.Hom.hom D.zero
    obtain ⟨r, hr, a, ha⟩ := exists_smul_mem_range_of_exact_fibre K hz hD b.1 b.2
    have hb' : r • e z = Submodule.Quotient.mk (r • b) :=
      congrArg (fun u : D.moduleCatLeftHomologyData.H => r • u) hb.symm
    have hz' : Submodule.Quotient.mk (r • b) = (0 : D.moduleCatLeftHomologyData.H) :=
      (Submodule.Quotient.mk_eq_zero _).mpr ⟨a, Subtype.ext ha⟩
    exact ⟨r, hr, e.injective ((e.map_smul r (show D.homology from z)).trans
      (hb'.trans (hz'.trans e.map_zero.symm)))⟩
  let e := (isoOfQuasiIsoAt φ n).toLinearEquiv
  let p : PrimeSpectrum R := ⟨RingHom.ker χ, RingHom.ker_isPrime χ⟩
  have hp : p ∉ Module.support R (C.homology n) := by
    rw [Module.notMem_support_iff']
    intro z
    obtain ⟨r, hr, hz⟩ := hpt (e.symm z)
    refine ⟨r, hr, ?_⟩
    rw [← e.apply_symm_apply z, ← map_smul, hz, map_zero]
  letI := hfin n
  rw [Module.mem_support_iff_of_finite, SetLike.not_le_iff_exists] at hp
  obtain ⟨r, hr, hr'⟩ := hp
  exact ⟨r, hr', Module.mem_annihilator.mp hr⟩

end GlobalTheory
