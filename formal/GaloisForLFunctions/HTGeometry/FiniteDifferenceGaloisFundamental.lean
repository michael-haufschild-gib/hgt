import GaloisForLFunctions.HTGeometry.DifferenceAutomorphismFixedFieldFundamental
import GaloisForLFunctions.HTGeometry.FiniteDifferenceGaloisAlgebraicity

/-!
# Finite ordinary Galois branch from a fundamental solution

The finite-orbit contradiction now consumes only ordinary PV structure around an invertible
fundamental solution.  Comparison matrix, comparison algebra, basis, and fixed-field theorem are
all constructed internally.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

universe u

variable {K R C : Type u} [Field K] [CharZero K] [CommRing R] [Nontrivial R]
  [Algebra K R] [Field C] [IsAlgClosed C]
  [Algebra C K] [Algebra C R] [IsScalarTower C K R]

/-- Finite ordinary difference-Galois group plus an invertible fundamental solution forces every
PV carrier element to be algebraic over the base. -/
theorem isAlgebraic_of_finite_differenceAut_of_fundamental
    {σK : K ≃+* K} {σR : R ≃+* R}
    (hcompat : ∀ y : K, σR (algebraMap K R y) = algebraMap K R (σK y))
    (hconstC : ∀ y : C, σR (algebraMap C R y) = algebraMap C R y)
    (hsimple : IsSigmaSimple σR)
    (hnonew : ∀ r : R, σR r = r → ∃ c : C, r = algebraMap C R c)
    (B : Matrix (Fin 2) (Fin 2) K) (Y : Matrix (Fin 2) (Fin 2) R) [Invertible Y]
    (hY : Y.map (σR : R → R) = (B.map (algebraMap K R)) * Y)
    (u : R) (hu : Y.det * u = 1)
    (htop : Algebra.adjoin K
      (Set.range (fun p : Fin 2 × Fin 2 => Y p.1 p.2) ∪ {u}) = ⊤)
    [Finite (differenceAut (K := K) σR)] {x : R} :
    IsAlgebraic K x := by
  apply isAlgebraic_of_finite_differenceAut (K := K) (L := R) (σL := σR)
  intro y hy
  obtain ⟨k, hk⟩ := exists_eq_algebraMap_of_forall_differenceAut_of_fundamental
    hcompat hconstC hsimple hnonew B Y hY u hu htop hy
  exact ⟨k, hk.symm⟩

/-- A transcendental carrier rules out the finite ordinary difference-Galois branch from the same
fundamental-solution data. -/
theorem not_finite_differenceAut_of_transcendental_of_fundamental
    {σK : K ≃+* K} {σR : R ≃+* R}
    (hcompat : ∀ y : K, σR (algebraMap K R y) = algebraMap K R (σK y))
    (hconstC : ∀ y : C, σR (algebraMap C R y) = algebraMap C R y)
    (hsimple : IsSigmaSimple σR)
    (hnonew : ∀ r : R, σR r = r → ∃ c : C, r = algebraMap C R c)
    (B : Matrix (Fin 2) (Fin 2) K) (Y : Matrix (Fin 2) (Fin 2) R) [Invertible Y]
    (hY : Y.map (σR : R → R) = (B.map (algebraMap K R)) * Y)
    (u : R) (hu : Y.det * u = 1)
    (htop : Algebra.adjoin K
      (Set.range (fun p : Fin 2 × Fin 2 => Y p.1 p.2) ∪ {u}) = ⊤)
    {x : R} (hx : Transcendental K x) :
    ¬ Finite (differenceAut (K := K) σR) := by
  intro hfinite
  letI : Finite (differenceAut (K := K) σR) := hfinite
  exact hx (isAlgebraic_of_finite_differenceAut_of_fundamental
    hcompat hconstC hsimple hnonew B Y hY u hu htop)

end

end GaloisForLFunctions.HTGeometry
