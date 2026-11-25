import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.FiniteGradedGenerators
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.FreeGradedCech
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CoherentCohomology.PolynomialCechZeroFiniteness
import Mathlib.Algebra.Homology.HomologySequence
import Mathlib.RingTheory.Polynomial.Basic

/-! Graded Čech cohomology of a finite module is finite over the Noetherian coefficient ring. -/

noncomputable section

open CategoryTheory DirectSum HTGeometry MvPolynomial

namespace GlobalTheory

variable {ι R : Type} [Fintype ι] [DecidableEq ι] [LinearOrder ι] [CommRing R]
  [IsNoetherianRing R]

private theorem finite_gradedCech_homology_of_bound {M : Type} [AddCommGroup M] [Module R M]
    [Module (MvPolynomial ι R) M] [IsScalarTower R (MvPolynomial ι R) M]
    (D : ℤ → Submodule R M) [PolyGradedSMul ι D] (q : ℕ) (m : ℤ)
    (h : Fintype.card ι ≤ q) : Module.Finite R ((gradedCech D m).homology q) := by
  let C := gradedCech D m
  have hz : Limits.IsZero (C.X q) :=
    (homLocDatum D m).linearComplex_X_isZero (fun k => homLocDatum_res_smul D k m) q h
  haveI := ModuleCat.subsingleton_of_isZero (HomologicalComplex.ExactAt.of_isZero hz).isZero_homology
  infer_instance

private theorem finite_freeGradedCech_homology [Nonempty ι] {a : ℕ} (d : Fin a → ℤ)
    (n : ℤ) (q : ℕ) : Module.Finite R ((gradedCech (grFree ι R d) n).homology q) := by
  let C := gradedCech (grFree ι R d) n
  let E (j : Fin a) := gradedCech (polyGrading ι R) (n - d j)
  let H := HomologicalComplex.homologyFunctor (ModuleCat R) (ComplexShape.up ℕ) q
  let p (j : Fin a) : H.obj C ⟶ H.obj (E j) := H.map (freeCechProj d n j)
  let i (j : Fin a) : H.obj (E j) ⟶ H.obj C := H.map (freeCechIncl d n j)
  have h : (∑ j, p j ≫ i j) = 𝟙 (H.obj C) := by
    simpa only [p, i, Functor.map_sum, Functor.map_comp, Functor.map_id] using
      congrArg H.map (sum_freeCechProj_comp_freeCechIncl (ι := ι) (R := R) d n)
  haveI (j : Fin a) : Module.Finite R (H.obj (E j)) :=
    finite_polynomialGradedCech_homology (n - d j) q
  let g : (∀ j, H.obj (E j)) →ₗ[R] H.obj C :=
    ∑ j, (i j).hom ∘ₗ LinearMap.proj j
  apply Module.Finite.of_surjective g
  intro z
  refine ⟨fun j => p j z, ?_⟩
  have e := congrArg (fun u : H.obj C ⟶ H.obj C => u.hom z) h
  simpa only [ModuleCat.hom_sum, LinearMap.sum_apply, ModuleCat.hom_comp, ModuleCat.hom_id,
    LinearMap.comp_apply, LinearMap.id_apply, g, LinearMap.proj_apply] using e

private theorem finite_of_exact_of_finite {A B C : Type} [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B] [AddCommGroup C] [Module R C]
    {f : A →ₗ[R] B} {g : B →ₗ[R] C} (h : Function.Exact f g)
    [Module.Finite R A] [Module.Finite R C] : Module.Finite R B := by
  letI := isNoetherian_of_range_eq_ker f g h.linearMap_ker_eq.symm
  infer_instance

/-- Descend from the length of the cover using finite homogeneous free covers and the
long exact cohomology sequence. -/
theorem finite_gradedCech_homology {M : Type} [AddCommGroup M] [Module R M]
    [Module (MvPolynomial ι R) M] [IsScalarTower R (MvPolynomial ι R) M]
    (D : ℤ → Submodule R M) [PolyGradedSMul ι D] [Decomposition D]
    [Module.Finite (MvPolynomial ι R) M] (n : ℤ) (q : ℕ) :
    Module.Finite R ((gradedCech D n).homology q) := by
  classical
  rcases isEmpty_or_nonempty ι with hι | hι
  · letI := hι
    exact finite_gradedCech_homology_of_bound D q n (by simp)
  letI := hι
  suffices aux : ∀ j p : ℕ, Fintype.card ι ≤ p + j →
      ∀ (N : Type) [AddCommGroup N] [Module R N] [Module (MvPolynomial ι R) N]
      [IsScalarTower R (MvPolynomial ι R) N] (E : ℤ → Submodule R N)
      [PolyGradedSMul ι E] [Decomposition E] [Module.Finite (MvPolynomial ι R) N],
      Module.Finite R ((gradedCech E n).homology p) from
    aux (Fintype.card ι) q (by omega) M D
  intro j
  induction j with
  | zero =>
    intro p hp N _ _ _ _ E _ _ _
    exact finite_gradedCech_homology_of_bound E p n (by omega)
  | succ j ih =>
    intro p hp N _ _ _ _ E _ _ _
    obtain ⟨a, d, g, hg, hs⟩ := exists_graded_surjection E
    let F := grFree ι R d
    let K := LinearMap.ker g
    let A := grSub F K
    letI : Decomposition A := grSubDecomposition hg.isHomogeneous_ker
    letI : Module.Finite (MvPolynomial ι R) K := inferInstance
    haveI := ih (p + 1) (by omega) K A
    haveI := finite_freeGradedCech_homology (ι := ι) (R := R) d n p
    have hi : IsGradedMap A F K.subtype := fun _ _ hz => hz
    have he : Function.Exact K.subtype g := by
      intro x
      exact ⟨fun hx => ⟨⟨x, hx⟩, rfl⟩, by rintro ⟨x, rfl⟩; exact x.2⟩
    have hseq := FinsetCechDatum.shortExact_linearCochainMap
      (fun h => homLocDatum_res_smul A h n) (fun h => homLocDatum_res_smul F h n)
      (homLocDatumMap hi n) (fun s r z => (homLocMap hi s n).map_smul r z)
      (fun h => homLocDatum_res_smul E h n)
      (homLocDatumMap hg n) (fun s r z => (homLocMap hg s n).map_smul r z)
      (fun s z => (homLocMap_exact hi hg he s n).apply_apply_eq_zero z)
      (fun _ _ => homLocMap_injective_of hi (fun x hx => ⟨0, by
        have e : x = 0 := K.injective_subtype (hx.trans (map_zero K.subtype).symm)
        rw [e, smul_zero]⟩) n)
      (fun s _ => homLocMap_exact hi hg he s n)
      (fun _ _ => homLocMap_surjective_of hg (fun y => ⟨0, by
        rw [pow_zero, one_smul]
        exact hs y⟩) n)
    have hex := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).1
      (hseq.homology_exact₃ p (p + 1) rfl)
    exact finite_of_exact_of_finite hex

end GlobalTheory
