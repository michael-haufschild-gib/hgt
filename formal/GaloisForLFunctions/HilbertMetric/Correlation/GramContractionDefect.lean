import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheDeficitOfThePrimeFormIsADirichletEnergy

/-!
# Exact Gram-contraction deficit

For two finite real arrays with a common column window, the product of their
squared Frobenius norms minus their Gram contraction is half the sum of all
squared mixed minors. Equality holds precisely when every mixed minor vanishes.

This sharpens the positive-matrix step in Slonim's induction-norm bound,
arXiv:2611.11593, Proposition 3.4. Its scalar engine is the Lagrange identity
already used by the corpus's prime-ladder Dirichlet energy.
-/

noncomputable section

open Finset Matrix
open GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

namespace HilbertMetric.Correlation

/-- Squared Frobenius mass of an array on a finite rectangle. -/
def arrayMass (rows cols : Finset ℕ) (A : ℕ → ℕ → ℝ) : ℝ :=
  ∑ a ∈ rows, ∑ i ∈ cols, A a i ^ 2

/-- The contraction of two Gram matrices, written as squared row inner products. -/
def gramContraction (rows₁ rows₂ cols : Finset ℕ) (A B : ℕ → ℕ → ℝ) : ℝ :=
  ∑ a ∈ rows₁, ∑ b ∈ rows₂, (∑ i ∈ cols, A a i * B b i) ^ 2

/-- Twice the Gram-contraction deficit is exactly the total squared mixed-minor mass. -/
theorem gramContraction_defect (rows₁ rows₂ cols : Finset ℕ) (A B : ℕ → ℕ → ℝ) :
    2 * (arrayMass rows₁ cols A * arrayMass rows₂ cols B -
      gramContraction rows₁ rows₂ cols A B) =
      ∑ a ∈ rows₁, ∑ b ∈ rows₂, ∑ i ∈ cols, ∑ j ∈ cols,
        (A a i * B b j - A a j * B b i) ^ 2 := by
  simp_rw [sum_sum_minor_sq]
  simp only [arrayMass, gramContraction, sum_sub_distrib, ← mul_sum]
  simp only [← sum_mul]
  ring

/-- The positive-matrix trace bound holds without assumptions on array entries. -/
theorem gramContraction_le (rows₁ rows₂ cols : Finset ℕ) (A B : ℕ → ℕ → ℝ) :
    gramContraction rows₁ rows₂ cols A B ≤
      arrayMass rows₁ cols A * arrayMass rows₂ cols B := by
  have hn : 0 ≤ ∑ a ∈ rows₁, ∑ b ∈ rows₂, ∑ i ∈ cols, ∑ j ∈ cols,
      (A a i * B b j - A a j * B b i) ^ 2 :=
    sum_nonneg fun _ _ => sum_nonneg fun _ _ =>
      sum_nonneg fun _ _ => sum_nonneg fun _ _ => sq_nonneg _
  rw [← gramContraction_defect] at hn
  linarith only [hn]

/-- Equality is exactly simultaneous vanishing of all mixed row minors. -/
theorem gramContraction_eq_iff (rows₁ rows₂ cols : Finset ℕ) (A B : ℕ → ℕ → ℝ) :
    gramContraction rows₁ rows₂ cols A B = arrayMass rows₁ cols A * arrayMass rows₂ cols B ↔
      ∀ a ∈ rows₁, ∀ b ∈ rows₂, ∀ i ∈ cols, ∀ j ∈ cols,
        A a i * B b j = A a j * B b i := by
  have hz : (∑ a ∈ rows₁, ∑ b ∈ rows₂, ∑ i ∈ cols, ∑ j ∈ cols,
      (A a i * B b j - A a j * B b i) ^ 2) = 0 ↔
      ∀ a ∈ rows₁, ∀ b ∈ rows₂, ∀ i ∈ cols, ∀ j ∈ cols,
        A a i * B b j = A a j * B b i := by
    simp only [sum_eq_zero_iff_of_nonneg (fun a _ => sum_nonneg fun b _ =>
        sum_nonneg fun i _ => sum_nonneg fun j _ => sq_nonneg _),
      sum_eq_zero_iff_of_nonneg (fun b _ =>
        sum_nonneg fun i _ => sum_nonneg fun j _ => sq_nonneg _),
      sum_eq_zero_iff_of_nonneg (fun i _ => sum_nonneg fun j _ => sq_nonneg _),
      sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg _), sq_eq_zero_iff, sub_eq_zero]
  rw [← hz, ← gramContraction_defect]
  constructor <;> intro h <;> linarith only [h]

/-- A single nonzero mixed minor certifies strict contraction. -/
theorem gramContraction_lt_iff (rows₁ rows₂ cols : Finset ℕ) (A B : ℕ → ℕ → ℝ) :
    gramContraction rows₁ rows₂ cols A B < arrayMass rows₁ cols A * arrayMass rows₂ cols B ↔
      ∃ a ∈ rows₁, ∃ b ∈ rows₂, ∃ i ∈ cols, ∃ j ∈ cols,
        A a i * B b j ≠ A a j * B b i := by
  rw [lt_iff_le_and_ne, and_iff_right (gramContraction_le rows₁ rows₂ cols A B),
    ne_eq, gramContraction_eq_iff]
  push Not
  rfl

/-- The Gram matrix on a finite column window. -/
def arrayGram (rows cols : Finset ℕ) (A : ℕ → ℕ → ℝ) : Matrix cols cols ℝ :=
  fun i j => ∑ a ∈ rows, A a i * A a j

theorem arrayGram_trace (rows cols : Finset ℕ) (A : ℕ → ℕ → ℝ) :
    (arrayGram rows cols A).trace = arrayMass rows cols A := by
  change (∑ i : cols, ∑ a ∈ rows, A a i * A a i) = _
  rw [Finset.sum_coe_sort cols (fun i => ∑ a ∈ rows, A a i * A a i), sum_comm]
  simp only [arrayMass, pow_two]

/-- The row contraction is literally the trace of the product of the two Gram matrices. -/
theorem arrayGram_trace_mul (rows₁ rows₂ cols : Finset ℕ) (A B : ℕ → ℕ → ℝ) :
    (arrayGram rows₁ cols A * arrayGram rows₂ cols B).trace =
      gramContraction rows₁ rows₂ cols A B := by
  change (∑ i : cols, ∑ j : cols,
    (∑ a ∈ rows₁, A a i * A a j) * (∑ b ∈ rows₂, B b j * B b i)) = _
  have hj (i : cols) : (∑ j : cols,
      (∑ a ∈ rows₁, A a i * A a j) * (∑ b ∈ rows₂, B b j * B b i)) =
      ∑ j ∈ cols, (∑ a ∈ rows₁, A a i * A a j) * (∑ b ∈ rows₂, B b j * B b i) :=
    Finset.sum_coe_sort cols (fun j =>
      (∑ a ∈ rows₁, A a i * A a j) * (∑ b ∈ rows₂, B b j * B b i))
  simp_rw [hj]
  rw [Finset.sum_coe_sort cols (fun i =>
    ∑ j ∈ cols, (∑ a ∈ rows₁, A a i * A a j) * (∑ b ∈ rows₂, B b j * B b i))]
  simp only [sum_mul, mul_sum, gramContraction, pow_two]
  calc
    _ = ∑ i ∈ cols, ∑ j ∈ cols, ∑ a ∈ rows₁, ∑ b ∈ rows₂,
        A a i * A a j * (B b j * B b i) := by
      exact sum_congr rfl fun i _ => sum_congr rfl fun j _ => sum_comm
    _ = ∑ i ∈ cols, ∑ a ∈ rows₁, ∑ j ∈ cols, ∑ b ∈ rows₂,
        A a i * A a j * (B b j * B b i) := by
      exact sum_congr rfl fun i _ => sum_comm
    _ = ∑ a ∈ rows₁, ∑ i ∈ cols, ∑ j ∈ cols, ∑ b ∈ rows₂,
        A a i * A a j * (B b j * B b i) := sum_comm
    _ = ∑ a ∈ rows₁, ∑ i ∈ cols, ∑ b ∈ rows₂, ∑ j ∈ cols,
        A a i * A a j * (B b j * B b i) := by
      exact sum_congr rfl fun a _ => sum_congr rfl fun i _ => sum_comm
    _ = ∑ a ∈ rows₁, ∑ b ∈ rows₂, ∑ i ∈ cols, ∑ j ∈ cols,
        A a i * A a j * (B b j * B b i) := by
      exact sum_congr rfl fun a _ => sum_comm
    _ = _ := by
      apply sum_congr rfl
      intro a ha
      apply sum_congr rfl
      intro b hb
      apply sum_congr rfl
      intro i hi
      apply sum_congr rfl
      intro j hj
      ring

/-- The induction-norm matrix inequality, with positivity supplied by the Gram construction. -/
theorem arrayGram_trace_mul_le (rows₁ rows₂ cols : Finset ℕ) (A B : ℕ → ℕ → ℝ) :
    (arrayGram rows₁ cols A * arrayGram rows₂ cols B).trace ≤
      (arrayGram rows₁ cols A).trace * (arrayGram rows₂ cols B).trace := by
  rw [arrayGram_trace_mul, arrayGram_trace, arrayGram_trace]
  exact gramContraction_le rows₁ rows₂ cols A B

end HilbertMetric.Correlation
