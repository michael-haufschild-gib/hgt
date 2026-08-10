import GaloisForLFunctions.QuantumAlg.Util.HilbertSchmidt

/-!
# Static Gaussian crossing memory

A matrix pencil with ordinary classical Gaussian coefficients and its free-Fock semicircular
surrogate have different Wick combinatorics.  At fourth order the classical moment retains one
crossing pairing that the free/noncrossing moment omits.  This file identifies that missing term
exactly.

For a Hermitian coefficient family `A`, the crossing memory is

`square fourth energy - (1/2) * commutator energy`.

Thus Hall fullness or atomlessness of the free pencil does not by itself transfer spectral decay
to a quenched static Hamiltonian.  Any valid transfer must control this crossing memory and its
higher-order analogues.  For a commuting family the commutator correction vanishes and the
crossing term is the entire square fourth energy, so the classical and noncrossing fourth moments
are provably different whenever that energy is nonzero.
-/

open scoped BigOperators Matrix
open Matrix

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Ordinary matrix commutator, kept explicit because the theorem compares associative Wick
words rather than Lie-algebra elements. -/
def matrixCommutator {N : Type*} [Fintype N]
    (A B : Matrix N N ℂ) : Matrix N N ℂ :=
  A * B - B * A

/-- The commutator of two Hermitian matrices is skew-Hermitian. -/
theorem matrixCommutator_conjTranspose_of_hermitian
    {N : Type*} [Fintype N]
    {A B : Matrix N N ℂ} (hA : Aᴴ = A) (hB : Bᴴ = B) :
    (matrixCommutator A B)ᴴ = -matrixCommutator A B := by
  simp [matrixCommutator, Matrix.conjTranspose_mul, hA, hB, sub_eq_add_neg]

/-- Cyclic trace expansion of the squared commutator. -/
theorem trace_matrixCommutator_sq
    {N : Type*} [Fintype N] [DecidableEq N]
    (A B : Matrix N N ℂ) :
    Matrix.trace (matrixCommutator A B * matrixCommutator A B) =
      2 * Matrix.trace (A * B * A * B) -
        2 * Matrix.trace (A * A * B * B) := by
  have hABBA : Matrix.trace (A * B * (B * A)) = Matrix.trace (A * A * B * B) := by
    calc
      Matrix.trace (A * B * (B * A)) = Matrix.trace ((A * B * B) * A) := by
        simp only [Matrix.mul_assoc]
      _ = Matrix.trace (A * (A * B * B)) := Matrix.trace_mul_comm _ _
      _ = Matrix.trace (A * A * B * B) := by simp only [Matrix.mul_assoc]
  have hBAAB : Matrix.trace (B * A * (A * B)) = Matrix.trace (A * A * B * B) := by
    calc
      Matrix.trace (B * A * (A * B)) = Matrix.trace (B * (A * A * B)) := by
        simp only [Matrix.mul_assoc]
      _ = Matrix.trace ((A * A * B) * B) := Matrix.trace_mul_comm _ _
      _ = Matrix.trace (A * A * B * B) := by simp only [Matrix.mul_assoc]
  have hBABA : Matrix.trace (B * A * (B * A)) = Matrix.trace (A * B * A * B) := by
    calc
      Matrix.trace (B * A * (B * A)) = Matrix.trace ((B * A * B) * A) := by
        simp only [Matrix.mul_assoc]
      _ = Matrix.trace (A * (B * A * B)) := Matrix.trace_mul_comm _ _
      _ = Matrix.trace (A * B * A * B) := by simp only [Matrix.mul_assoc]
  have hABAB : Matrix.trace (A * B * (A * B)) = Matrix.trace (A * B * A * B) := by
    simp only [Matrix.mul_assoc]
  simp only [matrixCommutator, Matrix.sub_mul, Matrix.mul_sub, Matrix.trace_sub]
  rw [hABAB, hABBA, hBAAB, hBABA]
  ring

/-- For Hermitian coefficients, Hilbert--Schmidt commutator energy is the negative trace of the
squared commutator. -/
theorem hsInner_matrixCommutator_self
    {N : Type*} [Fintype N] [DecidableEq N]
    {A B : Matrix N N ℂ} (hA : Aᴴ = A) (hB : Bᴴ = B) :
    QuantumAlg.hsInner (matrixCommutator A B) (matrixCommutator A B) =
      2 * Matrix.trace (A * A * B * B) -
        2 * Matrix.trace (A * B * A * B) := by
  rw [QuantumAlg.hsInner_def,
    matrixCommutator_conjTranspose_of_hermitian hA hB,
    Matrix.neg_mul, Matrix.trace_neg, trace_matrixCommutator_sq]
  ring

/-- Pairwise crossing law: a crossing word equals square energy minus half the
Hilbert--Schmidt commutator energy. -/
theorem trace_crossing_eq_square_sub_half_commutatorEnergy
    {N : Type*} [Fintype N] [DecidableEq N]
    {A B : Matrix N N ℂ} (hA : Aᴴ = A) (hB : Bᴴ = B) :
    Matrix.trace (A * B * A * B) =
      Matrix.trace (A * A * B * B) -
        (2 : ℂ)⁻¹ * QuantumAlg.hsInner
          (matrixCommutator A B) (matrixCommutator A B) := by
  rw [hsInner_matrixCommutator_self hA hB]
  norm_num
  ring

/-- Total square-energy contraction of a finite coefficient family. -/
def matrixFamilySquareFourthEnergy
    {K N : Type*} [Fintype K] [Fintype N]
    (A : K → Matrix N N ℂ) : ℂ :=
  ∑ i, ∑ j, Matrix.trace (A i * A i * A j * A j)

/-- Total Hilbert--Schmidt energy of all coefficient commutators. -/
def matrixFamilyCommutatorEnergy
    {K N : Type*} [Fintype K] [Fintype N]
    (A : K → Matrix N N ℂ) : ℂ :=
  ∑ i, ∑ j, QuantumAlg.hsInner
    (matrixCommutator (A i) (A j)) (matrixCommutator (A i) (A j))

/-- The fourth-order crossing contraction retained by classical Wick calculus and omitted by
free/noncrossing Wick calculus. -/
def matrixFamilyCrossingMemory
    {K N : Type*} [Fintype K] [Fintype N]
    (A : K → Matrix N N ℂ) : ℂ :=
  ∑ i, ∑ j, Matrix.trace (A i * A j * A i * A j)

/-- Sum of the two noncrossing fourth-order pair contractions. -/
def matrixFamilyNoncrossingWickFourth
    {K N : Type*} [Fintype K] [Fintype N]
    (A : K → Matrix N N ℂ) : ℂ :=
  ∑ i, ∑ j,
    (Matrix.trace (A i * A i * A j * A j) +
      Matrix.trace (A i * A j * A j * A i))

/-- Sum of all three classical fourth-order Wick pair contractions. -/
def matrixFamilyClassicalWickFourth
    {K N : Type*} [Fintype K] [Fintype N]
    (A : K → Matrix N N ℂ) : ℂ :=
  matrixFamilyNoncrossingWickFourth A + matrixFamilyCrossingMemory A

/-- Exact static/free separation: classical fourth order minus noncrossing fourth order is the
crossing memory. -/
theorem matrixFamilyClassicalWickFourth_sub_noncrossing
    {K N : Type*} [Fintype K] [Fintype N]
    (A : K → Matrix N N ℂ) :
    matrixFamilyClassicalWickFourth A - matrixFamilyNoncrossingWickFourth A =
      matrixFamilyCrossingMemory A := by
  simp [matrixFamilyClassicalWickFourth]

/-- Cyclicity makes the two noncrossing contractions equal. -/
theorem matrixFamilyNoncrossingWickFourth_eq_two_mul_squareEnergy
    {K N : Type*} [Fintype K] [Fintype N] [DecidableEq K] [DecidableEq N]
    (A : K → Matrix N N ℂ) :
    matrixFamilyNoncrossingWickFourth A =
      2 * matrixFamilySquareFourthEnergy A := by
  have hcycle : ∀ i j,
      Matrix.trace (A i * A j * A j * A i) =
        Matrix.trace (A i * A i * A j * A j) := by
    intro i j
    calc
      Matrix.trace (A i * A j * A j * A i) =
          Matrix.trace ((A i * A j * A j) * A i) := by
            simp only [Matrix.mul_assoc]
      _ = Matrix.trace (A i * (A i * A j * A j)) := Matrix.trace_mul_comm _ _
      _ = Matrix.trace (A i * A i * A j * A j) := by
        simp only [Matrix.mul_assoc]
  simp only [matrixFamilyNoncrossingWickFourth, matrixFamilySquareFourthEnergy]
  simp_rw [hcycle]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- **Fourth-order crossing-memory law.** For a Hermitian matrix pencil, the exact defect between
classical and noncrossing Wick calculus is square fourth energy minus half the total commutator
energy. -/
theorem matrixFamilyCrossingMemory_eq_square_sub_half_commutatorEnergy
    {K N : Type*} [Fintype K] [Fintype N] [DecidableEq K] [DecidableEq N]
    (A : K → Matrix N N ℂ) (hA : ∀ i, (A i)ᴴ = A i) :
    matrixFamilyCrossingMemory A =
      matrixFamilySquareFourthEnergy A -
        (2 : ℂ)⁻¹ * matrixFamilyCommutatorEnergy A := by
  simp only [matrixFamilyCrossingMemory, matrixFamilySquareFourthEnergy,
    matrixFamilyCommutatorEnergy]
  simp_rw [trace_crossing_eq_square_sub_half_commutatorEnergy (hA _) (hA _),
    Finset.sum_sub_distrib]
  simp only [← Finset.mul_sum]

/-- Equivalent closed formula for the full classical fourth Wick contraction. -/
theorem matrixFamilyClassicalWickFourth_eq_three_square_sub_half_commutatorEnergy
    {K N : Type*} [Fintype K] [Fintype N] [DecidableEq K] [DecidableEq N]
    (A : K → Matrix N N ℂ) (hA : ∀ i, (A i)ᴴ = A i) :
    matrixFamilyClassicalWickFourth A =
      3 * matrixFamilySquareFourthEnergy A -
        (2 : ℂ)⁻¹ * matrixFamilyCommutatorEnergy A := by
  rw [matrixFamilyClassicalWickFourth,
    matrixFamilyNoncrossingWickFourth_eq_two_mul_squareEnergy,
    matrixFamilyCrossingMemory_eq_square_sub_half_commutatorEnergy A hA]
  ring

/-- Exact fourth-order transfer criterion: classical and free/noncrossing fourth moments agree
precisely when commutator energy is twice square energy. -/
theorem matrixFamilyClassicalWickFourth_eq_noncrossing_iff_energy_balance
    {K N : Type*} [Fintype K] [Fintype N] [DecidableEq K] [DecidableEq N]
    (A : K → Matrix N N ℂ) (hA : ∀ i, (A i)ᴴ = A i) :
    matrixFamilyClassicalWickFourth A = matrixFamilyNoncrossingWickFourth A ↔
      matrixFamilySquareFourthEnergy A =
        (2 : ℂ)⁻¹ * matrixFamilyCommutatorEnergy A := by
  constructor
  · intro h
    have hzero : matrixFamilyClassicalWickFourth A -
        matrixFamilyNoncrossingWickFourth A = 0 := sub_eq_zero.mpr h
    rw [matrixFamilyClassicalWickFourth_sub_noncrossing,
      matrixFamilyCrossingMemory_eq_square_sub_half_commutatorEnergy A hA] at hzero
    exact sub_eq_zero.mp hzero
  · intro h
    apply sub_eq_zero.mp
    rw [matrixFamilyClassicalWickFourth_sub_noncrossing,
      matrixFamilyCrossingMemory_eq_square_sub_half_commutatorEnergy A hA, h, sub_self]

/-- Commuting coefficients retain the full square-energy crossing contraction. -/
theorem matrixFamilyCrossingMemory_eq_squareEnergy_of_commute
    {K N : Type*} [Fintype K] [Fintype N] [DecidableEq K] [DecidableEq N]
    (A : K → Matrix N N ℂ) (hcomm : ∀ i j, A i * A j = A j * A i) :
    matrixFamilyCrossingMemory A = matrixFamilySquareFourthEnergy A := by
  simp only [matrixFamilyCrossingMemory, matrixFamilySquareFourthEnergy]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [show A i * A j * A i * A j = A i * (A j * A i) * A j by
    simp only [Matrix.mul_assoc]]
  rw [hcomm j i]
  simp only [Matrix.mul_assoc]

/-- A commuting classical pencil has coefficient `3`, rather than the free/noncrossing
coefficient `2`, on its square fourth energy. -/
theorem matrixFamilyClassicalWickFourth_eq_three_squareEnergy_of_commute
    {K N : Type*} [Fintype K] [Fintype N] [DecidableEq K] [DecidableEq N]
    (A : K → Matrix N N ℂ) (hcomm : ∀ i j, A i * A j = A j * A i) :
    matrixFamilyClassicalWickFourth A = 3 * matrixFamilySquareFourthEnergy A := by
  rw [matrixFamilyClassicalWickFourth,
    matrixFamilyNoncrossingWickFourth_eq_two_mul_squareEnergy,
    matrixFamilyCrossingMemory_eq_squareEnergy_of_commute A hcomm]
  ring

/-- On a commuting pencil the static/free fourth-order defect is exactly square energy. -/
theorem matrixFamilyClassicalWickFourth_sub_noncrossing_eq_squareEnergy_of_commute
    {K N : Type*} [Fintype K] [Fintype N] [DecidableEq K] [DecidableEq N]
    (A : K → Matrix N N ℂ) (hcomm : ∀ i j, A i * A j = A j * A i) :
    matrixFamilyClassicalWickFourth A - matrixFamilyNoncrossingWickFourth A =
      matrixFamilySquareFourthEnergy A := by
  rw [matrixFamilyClassicalWickFourth_sub_noncrossing,
    matrixFamilyCrossingMemory_eq_squareEnergy_of_commute A hcomm]

/-- Therefore a commuting pencil with nonzero square energy cannot share the free/noncrossing
fourth moment. -/
theorem matrixFamilyClassicalWickFourth_ne_noncrossing_of_commute
    {K N : Type*} [Fintype K] [Fintype N] [DecidableEq K] [DecidableEq N]
    (A : K → Matrix N N ℂ) (hcomm : ∀ i j, A i * A j = A j * A i)
    (henergy : matrixFamilySquareFourthEnergy A ≠ 0) :
    matrixFamilyClassicalWickFourth A ≠ matrixFamilyNoncrossingWickFourth A := by
  exact sub_ne_zero.mp (by
    rw [matrixFamilyClassicalWickFourth_sub_noncrossing_eq_squareEnergy_of_commute
      A hcomm]
    exact henergy)

end

end GaloisForLFunctions.HTGeometry
