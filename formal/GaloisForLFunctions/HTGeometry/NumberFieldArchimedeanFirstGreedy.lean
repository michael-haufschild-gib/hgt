import GaloisForLFunctions.HTGeometry.NumberFieldArchimedeanPrimitiveNormalization
import GaloisForLFunctions.HTGeometry.NumberFieldArchimedeanSiegelData
import GaloisForLFunctions.HTGeometry.ComplexSiegelLovasz

/-!
# First greedy rung for number-field archimedean reduction

Primitive normalization chooses the first integral coordinate internally.  This file identifies
its total archimedean energy with the summed real/Hermitian Jacobi head and proves the resulting
first-rung minimality simultaneously across all infinite places.
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix NumberField
open scoped Classical ComplexOrder Matrix NumberField

noncomputable section

variable {K : Type*} [Field K] [NumberField K]
variable {n : ℕ}

/-- Sum of one Jacobi weight over all real and complex infinite places. -/
def numberFieldArchimedeanJacobiMass
    {A : numberFieldArchimedeanPositiveForms K n}
    (J : NumberFieldArchimedeanJacobiData A) (i : Fin n) : ℝ :=
  (∑ w : {w : InfinitePlace K // w.IsReal}, J.realD w i) +
    ∑ w : {w : InfinitePlace K // w.IsComplex}, (J.complexD w i).re

/-- Sum of one diagonal entry of the real/Hermitian forms represented by simultaneous Jacobi
data. -/
def numberFieldArchimedeanJacobiFormDiagonalMass
    {A : numberFieldArchimedeanPositiveForms K n}
    (J : NumberFieldArchimedeanJacobiData A) (j : Fin n) : ℝ :=
  (∑ w : {w : InfinitePlace K // w.IsReal},
      (J.realJacobiData w).form j j) +
    ∑ w : {w : InfinitePlace K // w.IsComplex},
      ((J.complexJacobiData w).form j j).re

/-- Coordinate energy is exactly the sum of the corresponding local form diagonals. -/
theorem numberFieldArchimedeanEnergy_coordinateBasis
    (A : numberFieldArchimedeanPositiveForms K n) (j : Fin n) :
    numberFieldArchimedeanEnergy A
        (numberFieldIntegerVectorEmbedding K
          (numberFieldCoordinateBasis (K := K) j)) =
      (∑ w : {w : InfinitePlace K // w.IsReal},
          (A.1.1 w : Matrix (Fin n) (Fin n) ℝ) j j) +
        ∑ w : {w : InfinitePlace K // w.IsComplex},
          ((A.1.2 w : Matrix (Fin n) (Fin n) ℂ) j j).re := by
  classical
  unfold numberFieldArchimedeanEnergy
  congr 1
  · apply Finset.sum_congr rfl
    intro w hw
    have hz : (fun i =>
        (numberFieldIntegerVectorEmbedding K
          (numberFieldCoordinateBasis (K := K) j) i).1 w) =
        Pi.single j (1 : ℝ) := by
      funext i
      by_cases hij : i = j
      · subst i
        simp [numberFieldCoordinateBasis]
      · simp [numberFieldCoordinateBasis, hij]
    rw [hz]
    simp only [dotProduct, Matrix.mulVec_single]
    rw [Finset.sum_eq_single j]
    · simp
    · intro b hb hbj
      simp [hbj]
    · simp
  · apply Finset.sum_congr rfl
    intro w hw
    have hz : (fun i =>
        (numberFieldIntegerVectorEmbedding K
          (numberFieldCoordinateBasis (K := K) j) i).2 w) =
        Pi.single j (1 : ℂ) := by
      funext i
      by_cases hij : i = j
      · subst i
        simp [numberFieldCoordinateBasis]
      · simp [numberFieldCoordinateBasis, hij]
    rw [hz]
    have hstar :
        star (Pi.single j (1 : ℂ) : Fin n → ℂ) =
          (Pi.single j (1 : ℂ) : Fin n → ℂ) := by
      funext i
      by_cases hij : i = j <;> simp [hij]
    have hdiag := congrArg Complex.re
      (star_single_dot_mulVec_single
        (A.1.2 w : Matrix (Fin n) (Fin n) ℂ) j)
    rw [hstar] at hdiag
    rw [hstar]
    exact hdiag

/-- Jacobi form-diagonal mass is the corresponding coordinate energy. -/
theorem NumberFieldArchimedeanJacobiData.formDiagonalMass_eq_energy
    {A : numberFieldArchimedeanPositiveForms K n}
    (J : NumberFieldArchimedeanJacobiData A) (j : Fin n) :
    numberFieldArchimedeanJacobiFormDiagonalMass J j =
      numberFieldArchimedeanEnergy A
        (numberFieldIntegerVectorEmbedding K
          (numberFieldCoordinateBasis (K := K) j)) := by
  rw [numberFieldArchimedeanEnergy_coordinateBasis]
  unfold numberFieldArchimedeanJacobiFormDiagonalMass
  congr 1
  · apply Finset.sum_congr rfl
    intro w hw
    rw [J.realJacobiData_form]
  · apply Finset.sum_congr rfl
    intro w hw
    rw [J.complexJacobiData_form]

/-- At the first coordinate, form-diagonal mass is exactly Jacobi-weight mass. -/
theorem NumberFieldArchimedeanJacobiData.formDiagonalMass_zero
    {A : numberFieldArchimedeanPositiveForms K n}
    (J : NumberFieldArchimedeanJacobiData A)
    {i : Fin n} (hi : (i : ℕ) = 0) :
    numberFieldArchimedeanJacobiFormDiagonalMass J i =
      numberFieldArchimedeanJacobiMass J i := by
  unfold numberFieldArchimedeanJacobiFormDiagonalMass
    numberFieldArchimedeanJacobiMass
  congr 1
  · apply Finset.sum_congr rfl
    intro w hw
    exact (J.realJacobiData w).form_diag_zero hi
  · apply Finset.sum_congr rfl
    intro w hw
    exact (J.complexJacobiData w).form_diag_zero hi

/-- First rung of the simultaneous greedy flag.  For every corrected archimedean cone point, an
internally constructed special-linear action and Jacobi decomposition make the summed first
Jacobi weight no larger than every coordinate's total local diagonal energy. -/
theorem exists_numberFieldArchimedean_firstGreedyJacobi
    (K : Type*) [Field K] [NumberField K]
    (n : ℕ) (hn : 2 ≤ n)
    (A : numberFieldArchimedeanPositiveForms K n) :
    ∃ (G : Matrix.SpecialLinearGroup (Fin n) (𝓞 K))
        (J : NumberFieldArchimedeanJacobiData (G • A)),
      ∀ j : Fin n,
        numberFieldArchimedeanJacobiMass J
            ⟨0, lt_of_lt_of_le (Nat.succ_pos 1) hn⟩ ≤
          numberFieldArchimedeanJacobiFormDiagonalMass J j := by
  obtain ⟨a, β, hβ, hprim, hcol, hmin⟩ :=
    exists_numberFieldArchimedean_primitiveNormalization K n hn A
  let G : Matrix.SpecialLinearGroup (Fin n) (𝓞 K) :=
    transposeSpecialLinearOfDetOne β hβ
  let J : NumberFieldArchimedeanJacobiData (G • A) :=
    Classical.choice (exists_numberFieldArchimedeanJacobiData (G • A))
  refine ⟨G, J, ?_⟩
  intro j
  rw [← J.formDiagonalMass_zero
      (i := ⟨0, lt_of_lt_of_le (Nat.succ_pos 1) hn⟩) rfl,
    J.formDiagonalMass_eq_energy, J.formDiagonalMass_eq_energy]
  exact hmin j

end

end GaloisForLFunctions.HTGeometry
