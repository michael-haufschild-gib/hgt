import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.FiniteLengthFreeComplex
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.PerfectCochainModel
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.PointSupportedModule
import Mathlib.Algebra.Category.ModuleCat.Descent
import Mathlib.RingTheory.LocalRing.Module

/-! The cohomology dimensions of a perfect complex supported at one rational
point are computed over its regular local ring. -/

noncomputable section

open CategoryTheory CategoryTheory.Limits TensorProduct

namespace GlobalTheory.FiniteLengthComplex

/-- A flat cochain complex bounded by the local dimension has a single
one-dimensional cohomology group if its localized first dual cokernel is the
residue field. The presentation is tested on finite free models. -/
theorem finrank_homology_of_local_dual_cokernel
    {K R O : Type} [Field K] [IsAlgClosed K] [CommRing R] [Algebra K R]
    [Algebra.FiniteType K R] [CommRing O] [algRO : Algebra R O]
    (χ₀ : R →ₐ[K] K) [(RingHom.ker χ₀).IsPrime]
    [IsLocalization.AtPrime O (RingHom.ker χ₀)] [IsRegularLocalRing O]
    (g : ℕ) (hg : ringKrullDim O = g)
    (C : CochainComplex (ModuleCat.{0} R) ℕ)
    (hz : ∀ p, g < p → IsZero (C.X p)) (hflat : ∀ p, Module.Flat R (C.X p))
    (hfin : ∀ p, Module.Finite R (C.homology p))
    (hsupp : ∀ χ : R →ₐ[K] K, χ ≠ χ₀ →
      ∀ p, ∃ r : R, χ r ≠ 0 ∧ ∀ z : C.homology p, r • z = 0)
    (D : CochainComplex (ModuleCat.{0} O) ℕ)
    (e : ((ModuleCat.extendScalars.{0, 0, 0} (algebraMap R O)).mapHomologicalComplex _).obj C ≅ D)
    (hq : ∀ (P : CochainComplex (ModuleCat.{0} O) ℕ) (φ : P ⟶ D),
      (∀ p, Module.Free O (P.X p) ∧ Module.Finite O (P.X p)) →
      (∀ (S : Type) [CommRing S] [Algebra O S], QuasiIso
        (((ModuleCat.extendScalars.{0, 0, 0} (algebraMap O S)).mapHomologicalComplex _).map φ)) →
      Nonempty ((Module.Dual O (P.X 0) ⧸ LinearMap.range (P.d 0 1).hom.dualMap) ≃ₗ[O]
        IsLocalRing.ResidueField O)) (n : ℕ) :
    Module.Finite K ((ModuleCat.restrictScalars (algebraMap K R)).obj (C.homology n)) ∧
      Module.finrank K ((ModuleCat.restrictScalars (algebraMap K R)).obj (C.homology n)) =
        if n = g then 1 else 0 := by
  letI : Module.Flat R O := IsLocalization.flat O (RingHom.ker χ₀).primeCompl
  let F := ModuleCat.extendScalars.{0, 0, 0} (algebraMap R O)
  letI : PreservesFiniteLimits F := ModuleCat.preservesFiniteLimits_extendScalars_of_flat
    (RingHom.flat_algebraMap_iff.mpr inferInstance)
  letI : F.IsLeftAdjoint := (ModuleCat.extendRestrictScalarsAdj (algebraMap R O)).isLeftAdjoint
  have tensorEquiv (M : ModuleCat.{0} R) : Nonempty (F.obj M ≃ₗ[O] O ⊗[R] M) := by
    obtain ⟨α, rfl⟩ : ∃ α : R →+* O, algRO = α.toAlgebra :=
      ⟨algebraMap R O, Algebra.algebra_ext _ _ fun _ => rfl⟩
    exact ⟨LinearEquiv.refl _ _⟩
  have termEquiv (p : ℕ) : Nonempty (D.X p ≃ₗ[O] O ⊗[R] C.X p) := by
    obtain ⟨u⟩ := tensorEquiv (C.X p)
    exact ⟨((HomologicalComplex.eval _ _ p).mapIso e.symm).toLinearEquiv.trans u⟩
  have homologyEquiv (p : ℕ) : Nonempty (D.homology p ≃ₗ[O] O ⊗[R] C.homology p) := by
    obtain ⟨u⟩ := tensorEquiv (C.homology p)
    exact ⟨(HomologicalComplex.homologyMapIso e.symm p).toLinearEquiv.trans
      (((C.sc p).mapHomologyIso F).toLinearEquiv.trans u)⟩
  obtain ⟨P, φ, hPz, hPfin, -, hPproj, hφ, -, hφS⟩ :=
    exists_finite_projective_complex_quasiIso D g
      (fun p hp => by
        obtain ⟨u⟩ := termEquiv p
        letI : Subsingleton (C.X p) := ModuleCat.isZero_iff_subsingleton.mp (hz p hp)
        exact ModuleCat.isZero_iff_subsingleton.mpr u.toEquiv.subsingleton)
      (fun p => by
        obtain ⟨u⟩ := termEquiv p
        letI := hflat p
        exact Module.Flat.of_linearEquiv u)
      (fun p => by
        obtain ⟨u⟩ := homologyEquiv p
        letI := hfin p
        exact Module.Finite.equiv u.symm)
  letI := hφ
  have hfree (p : ℕ) : Module.Free O (P.X p) ∧ Module.Finite O (P.X p) := by
    letI := hPfin p
    letI := hPproj p
    exact ⟨Module.free_of_flat_of_isLocalRing, inferInstance⟩
  have EH (p : ℕ) : Nonempty (P.homology p ≃ₗ[O] O ⊗[R] C.homology p) := by
    obtain ⟨u⟩ := homologyEquiv p
    exact ⟨(asIso (HomologicalComplex.homologyMap φ p)).toLinearEquiv.trans u⟩
  have lengthComparison (p : ℕ) :=
    letI : Module K (C.homology p) := Module.compHom _ (algebraMap K R)
    letI : IsScalarTower K R (C.homology p) := ⟨fun a r z => by
      change (a • r) • z = (algebraMap K R a) • (r • z)
      rw [Algebra.smul_def, mul_smul]⟩
    letI := hfin p
    GlobalTheory.PointSupport.finiteLength_and_finrank_eq_length (O := O) χ₀ (H := C.homology p)
      (fun χ hχ => hsupp χ hχ p)
  obtain ⟨hzero, hone⟩ := homology_of_free_complex_of_isFiniteLength O g hg P hfree hPz
    (fun p => by
      obtain ⟨u⟩ := EH p
      exact (lengthComparison p).1.of_injective (f := u.toLinearMap) u.injective)
    (hq P φ hfree hφS)
  obtain ⟨u⟩ := EH n
  obtain ⟨-, hfin', hlen⟩ := lengthComparison n
  refine ⟨hfin', ?_⟩
  rw [← u.length_eq] at hlen
  split_ifs with hn
  · subst n
    rw [hone] at hlen
    exact_mod_cast hlen
  · letI := ModuleCat.isZero_iff_subsingleton.mp (hzero n hn)
    rw [Module.length_eq_zero] at hlen
    exact_mod_cast hlen

end GlobalTheory.FiniteLengthComplex
