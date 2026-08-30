import GaloisForLFunctions.HTGeometry.DifferenceAutomorphismFixedField
import GaloisForLFunctions.HTGeometry.FiniteDifferenceGaloisAlgebraicity

/-!
# Finite ordinary PV groups force algebraicity from torsor data

This module composes ordinary Picard--Vessiot fixed-field descent with the finite-orbit product.
The resulting boundary has no free invariant-field hypothesis.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open scoped TensorProduct

universe u

variable {K R C : Type u} [Field K] [CharZero K] [CommRing R] [Nontrivial R]
  [Algebra K R] [Field C] [IsAlgClosed C]
  [Algebra C K] [Algebra C R] [IsScalarTower C K R]

/-- A finite ordinary difference-Galois group forces algebraicity once the displayed PV torsor
data and its inverse comparison determinant are constructed. -/
theorem isAlgebraic_of_finite_differenceAut_of_pvTorsor
    (E : Subalgebra C (R ⊗[K] R)) [Algebra.FiniteType C E]
    {ι : Type*} (b : Module.Basis ι C E)
    (hgen : Algebra.adjoin C
      (Set.range (algebraMap R (R ⊗[K] R)) ∪ (E : Set (R ⊗[K] R))) = ⊤)
    (hindep : LinearIndependent R (fun i => ((b i : E) : R ⊗[K] R)))
    {σK : K ≃+* K} {σR : R ≃+* R}
    (hcompat : ∀ y : K, σR (algebraMap K R y) = algebraMap K R (σK y))
    (hconstC : ∀ y : C, σR (algebraMap C R y) = algebraMap C R y)
    (hEσ : ∀ e ∈ E, differenceTensorEquiv σK σR hcompat e = e)
    (hsimple : IsSigmaSimple σR)
    (Y : Matrix (Fin 2) (Fin 2) R)
    (Z : Matrix (Fin 2) (Fin 2) (R ⊗[K] R)) (hZE : ∀ i j, Z i j ∈ E)
    (hZ : leftFundamental K Y * Z = rightFundamental K Y)
    (w : R ⊗[K] R) (hwE : w ∈ E) (hw : Z.det * w = 1)
    (u : R) (hu : Y.det * u = 1)
    (htop : Algebra.adjoin K
      (Set.range (fun p : Fin 2 × Fin 2 => Y p.1 p.2) ∪ {u}) = ⊤)
    [Finite (differenceAut (K := K) σR)] {x : R} :
    IsAlgebraic K x := by
  apply isAlgebraic_of_finite_differenceAut (K := K) (L := R) (σL := σR)
  intro y hy
  obtain ⟨k, hk⟩ := exists_eq_algebraMap_of_forall_differenceAut
    (K := K) (R := R) (C := C) E b hgen hindep hcompat hconstC hEσ hsimple
      Y Z hZE hZ w hwE hw u hu htop hy
  exact ⟨k, hk.symm⟩

/-- A transcendental PV carrier rules out the finite ordinary difference-Galois branch after the
fixed-field producer has been instantiated. -/
theorem not_finite_differenceAut_of_transcendental_of_pvTorsor
    (E : Subalgebra C (R ⊗[K] R)) [Algebra.FiniteType C E]
    {ι : Type*} (b : Module.Basis ι C E)
    (hgen : Algebra.adjoin C
      (Set.range (algebraMap R (R ⊗[K] R)) ∪ (E : Set (R ⊗[K] R))) = ⊤)
    (hindep : LinearIndependent R (fun i => ((b i : E) : R ⊗[K] R)))
    {σK : K ≃+* K} {σR : R ≃+* R}
    (hcompat : ∀ y : K, σR (algebraMap K R y) = algebraMap K R (σK y))
    (hconstC : ∀ y : C, σR (algebraMap C R y) = algebraMap C R y)
    (hEσ : ∀ e ∈ E, differenceTensorEquiv σK σR hcompat e = e)
    (hsimple : IsSigmaSimple σR)
    (Y : Matrix (Fin 2) (Fin 2) R)
    (Z : Matrix (Fin 2) (Fin 2) (R ⊗[K] R)) (hZE : ∀ i j, Z i j ∈ E)
    (hZ : leftFundamental K Y * Z = rightFundamental K Y)
    (w : R ⊗[K] R) (hwE : w ∈ E) (hw : Z.det * w = 1)
    (u : R) (hu : Y.det * u = 1)
    (htop : Algebra.adjoin K
      (Set.range (fun p : Fin 2 × Fin 2 => Y p.1 p.2) ∪ {u}) = ⊤)
    {x : R} (hx : Transcendental K x) :
    ¬ Finite (differenceAut (K := K) σR) := by
  intro hfinite
  letI : Finite (differenceAut (K := K) σR) := hfinite
  exact hx (isAlgebraic_of_finite_differenceAut_of_pvTorsor
    (K := K) (R := R) (C := C) E b hgen hindep hcompat hconstC hEσ hsimple
      Y Z hZE hZ w hwE hw u hu htop)

end

end GaloisForLFunctions.HTGeometry
