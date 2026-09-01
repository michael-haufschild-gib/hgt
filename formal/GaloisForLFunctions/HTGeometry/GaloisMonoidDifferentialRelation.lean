import GaloisForLFunctions.HTGeometry.GaloisDifferentialPointGroup
import GaloisForLFunctions.HTGeometry.DifferentialEvalTransfer

/-!
# Differential relations transported by a comparison Galois monoid

Once a constants basis of the comparison algebra is independent over the Picard--Vessiot ring,
every differential comparison point specializes the torsor to a base-fixing differential
endomorphism.  Closure under multiplication then realizes every matrix in the generated Galois
monoid, so every scalar differential relation of a fundamental entry propagates along its orbit.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open scoped TensorProduct Differential

universe u

variable {K R C : Type u} [Field K] [CommRing R] [Nontrivial R] [Algebra K R]
  [Field C] [Algebra C K] [Algebra C R] [IsScalarTower C K R]
  [Differential K] [Differential R] [DifferentialAlgebra K R]
  [Differential C] [DifferentialAlgebra C R]

/-- A differential base endomorphism realizing right multiplication of a fundamental matrix. -/
def HasDifferentialGaloisAction
    (K : Type u) [Field K] [Algebra K R]
    (Y : Matrix (Fin 2) (Fin 2) R) (g : Matrix (Fin 2) (Fin 2) C) : Prop :=
  ∃ φ : R →ₐ[K] R,
    (∀ x : R, φ (Differential.deriv x) = Differential.deriv (φ x)) ∧
    ∀ i j, φ (Y i j) =
      ∑ l : Fin 2, Y i l * algebraMap C R (g l j)

theorem hasDifferentialGaloisAction_one
    (Y : Matrix (Fin 2) (Fin 2) R) :
    HasDifferentialGaloisAction K Y (1 : Matrix (Fin 2) (Fin 2) C) := by
  refine ⟨AlgHom.id K R, fun _ => rfl, ?_⟩
  intro i j
  simp [Fin.sum_univ_two, Matrix.one_apply]

theorem HasDifferentialGaloisAction.mul
    (Y : Matrix (Fin 2) (Fin 2) R)
    {g h : Matrix (Fin 2) (Fin 2) C}
    (hg : HasDifferentialGaloisAction K Y g)
    (hh : HasDifferentialGaloisAction K Y h) :
    HasDifferentialGaloisAction K Y (g * h) := by
  obtain ⟨φ, hφδ, hφY⟩ := hg
  obtain ⟨ψ, hψδ, hψY⟩ := hh
  have hφC : ∀ c : C, φ (algebraMap C R c) = algebraMap C R c := by
    intro c
    calc
      φ (algebraMap C R c) = φ (algebraMap K R (algebraMap C K c)) := by
        rw [IsScalarTower.algebraMap_apply C K R]
      _ = algebraMap K R (algebraMap C K c) := φ.commutes _
      _ = algebraMap C R c := (IsScalarTower.algebraMap_apply C K R c).symm
  refine ⟨φ.comp ψ, fun x => by rw [AlgHom.comp_apply, hψδ, hφδ, AlgHom.comp_apply], ?_⟩
  intro i j
  rw [AlgHom.comp_apply, hψY, map_sum]
  calc
    ∑ l : Fin 2, φ (Y i l * algebraMap C R (h l j)) =
        ∑ l : Fin 2, (∑ k : Fin 2, Y i k * algebraMap C R (g k l)) *
          algebraMap C R (h l j) := by
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [map_mul, hφY, hφC]
    _ = ∑ k : Fin 2, Y i k * algebraMap C R ((g * h) k j) := by
      simp [Matrix.mul_apply, Fin.sum_univ_two]
      ring

/-- Every matrix in the multiplicative comparison monoid acts through a differential base
endomorphism of the Picard--Vessiot ring. -/
theorem hasDifferentialGaloisAction_of_mem_galoisMonoid
    (E : Subalgebra C (R ⊗[K] R)) {ι : Type*}
    (b : Module.Basis ι C E)
    (hgen : Algebra.adjoin C
      (Set.range (algebraMap R (R ⊗[K] R)) ∪ (E : Set (R ⊗[K] R))) = ⊤)
    (hindep : LinearIndependent R (fun i => ((b i : E) : R ⊗[K] R)))
    (hEδ : ∀ e ∈ E, tensorSquareDerivation (K := K) e ∈ E)
    (Y : Matrix (Fin 2) (Fin 2) R)
    (Z : Matrix (Fin 2) (Fin 2) (R ⊗[K] R)) (hZE : ∀ i j, Z i j ∈ E)
    (hZ : leftFundamental K Y * Z = rightFundamental K Y)
    {g : Matrix (Fin 2) (Fin 2) C}
    (hg : g ∈ galoisMonoid E Z hZE (tensorDifferentialPoints E hEδ)) :
    HasDifferentialGaloisAction K Y g := by
  change g ∈ Submonoid.closure {g : Matrix (Fin 2) (Fin 2) C |
    ∃ χ ∈ tensorDifferentialPoints E hEδ, galoisMatrixAt E Z hZE χ = g} at hg
  induction hg using Submonoid.closure_induction with
  | mem g hg =>
      obtain ⟨χ, hχ, rfl⟩ := hg
      refine ⟨galoisAutAtK E b hgen hindep χ,
        fun x => galoisAutAt_deriv E b hgen hindep hEδ χ hχ x, ?_⟩
      intro i j
      rw [galoisAutAtK_apply,
        galoisAutAt_fundamental E b hgen hindep χ Y Z hZE hZ]
      rfl
  | one => exact hasDifferentialGaloisAction_one Y
  | mul g h _ _ hg hh => exact hg.mul Y hh

/-- A scalar differential relation of one fundamental entry propagates through the entire
comparison Galois monoid. -/
theorem differentialRelation_fundamental_mul_of_mem_galoisMonoid
    (E : Subalgebra C (R ⊗[K] R)) {ι : Type*}
    (b : Module.Basis ι C E)
    (hgen : Algebra.adjoin C
      (Set.range (algebraMap R (R ⊗[K] R)) ∪ (E : Set (R ⊗[K] R))) = ⊤)
    (hindep : LinearIndependent R (fun i => ((b i : E) : R ⊗[K] R)))
    (hEδ : ∀ e ∈ E, tensorSquareDerivation (K := K) e ∈ E)
    (Y : Matrix (Fin 2) (Fin 2) R)
    (Z : Matrix (Fin 2) (Fin 2) (R ⊗[K] R)) (hZE : ∀ i j, Z i j ∈ E)
    (hZ : leftFundamental K Y * Z = rightFundamental K Y)
    (P : DifferentialPolynomial Unit K)
    (hP : differentialPolynomialEvalOver (K := K) (fun _ : Unit => Y 0 0) P = 0)
    {g : Matrix (Fin 2) (Fin 2) C}
    (hg : g ∈ galoisMonoid E Z hZE (tensorDifferentialPoints E hEδ)) :
    differentialPolynomialEvalOver (K := K)
      (fun _ : Unit => ∑ l : Fin 2, Y 0 l * algebraMap C R (g l 0)) P = 0 := by
  obtain ⟨φ, hφδ, hφY⟩ :=
    hasDifferentialGaloisAction_of_mem_galoisMonoid E b hgen hindep hEδ Y Z hZE hZ hg
  have hmap := evalOver_algHom (C := K) φ hφδ (fun _ : Unit => Y 0 0) P
  rw [hP, map_zero] at hmap
  simpa [hφY] using hmap.symm

end

end GaloisForLFunctions.HTGeometry
