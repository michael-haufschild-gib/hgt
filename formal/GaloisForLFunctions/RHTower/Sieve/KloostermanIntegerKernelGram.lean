import GaloisForLFunctions.RHTower.Sieve.KloostermanIntegerKernelOperator
import GaloisForLFunctions.RHTower.Sieve.LargeSieveDuality

/-!
# Gram expansion of the signed integer Kloosterman kernel

The transform output energy is expanded into its exact Hermitian Gram kernel.  Splitting the input
diagonal from the erased off-diagonal identifies the sole cancellation-bearing term a spectral
large sieve must control.
-/

open scoped BigOperators ComplexConjugate
open Complex Finset

namespace RHTower.Sieve

noncomputable section

/-- Source-side Gram kernel of the signed modulus transform over the output support `A`. -/
def kloostermanIntegerKernelGram
    (Q : Finset ℕ) (w : ℕ → ℂ) (A : Finset ℕ) (n k : ℕ) : ℂ :=
  ∑ m ∈ A, star (kloostermanIntegerModulusKernel Q w (m : ℤ) (n : ℤ)) *
    kloostermanIntegerModulusKernel Q w (m : ℤ) (k : ℤ)

/-- Gram kernel is Hermitian. -/
theorem star_kloostermanIntegerKernelGram
    (Q : Finset ℕ) (w : ℕ → ℂ) (A : Finset ℕ) (n k : ℕ) :
    star (kloostermanIntegerKernelGram Q w A n k) =
      kloostermanIntegerKernelGram Q w A k n := by
  unfold kloostermanIntegerKernelGram
  change (starRingEnd ℂ) (∑ m ∈ A,
    star (kloostermanIntegerModulusKernel Q w (m : ℤ) (n : ℤ)) *
      kloostermanIntegerModulusKernel Q w (m : ℤ) (k : ℤ)) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro m _hm
  rw [map_mul]
  simp
  ring

/-- Quadratic form of the source-side Gram kernel. -/
def kloostermanIntegerKernelGramQuadratic
    (Q : Finset ℕ) (w : ℕ → ℂ) (A B : Finset ℕ) (b : ℕ → ℂ) : ℂ :=
  ∑ n ∈ B, star (b n) * ∑ k ∈ B, b k * kloostermanIntegerKernelGram Q w A n k

/-- Exact Gram identity for transform output square energy. -/
theorem ofReal_sum_norm_kloostermanIntegerKernelTransform_sq_eq_gramQuadratic
    (Q : Finset ℕ) (w : ℕ → ℂ) (A B : Finset ℕ) (b : ℕ → ℂ) :
    ((∑ m ∈ A, ‖kloostermanIntegerKernelTransform Q w B b m‖ ^ (2 : ℕ) : ℝ) : ℂ) =
      kloostermanIntegerKernelGramQuadratic Q w A B b := by
  rw [Complex.ofReal_sum]
  simp_rw [← conj_mul_self]
  unfold kloostermanIntegerKernelGramQuadratic kloostermanIntegerKernelGram
    kloostermanIntegerKernelTransform
  simp_rw [map_sum, map_mul]
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n _hn
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _hk
  apply Finset.sum_congr rfl
  intro m _hm
  change (starRingEnd ℂ) (b n) *
      (starRingEnd ℂ) (kloostermanIntegerModulusKernel Q w (m : ℤ) (n : ℤ)) *
        (b k * kloostermanIntegerModulusKernel Q w (m : ℤ) (k : ℤ)) =
    (starRingEnd ℂ) (b n) *
      (b k * ((starRingEnd ℂ)
        (kloostermanIntegerModulusKernel Q w (m : ℤ) (n : ℤ)) *
          kloostermanIntegerModulusKernel Q w (m : ℤ) (k : ℤ)))
  ring

/-- Diagonal part of the Gram quadratic form. -/
def kloostermanIntegerKernelGramDiagonal
    (Q : Finset ℕ) (w : ℕ → ℂ) (A B : Finset ℕ) (b : ℕ → ℂ) : ℂ :=
  ∑ n ∈ B, star (b n) * (b n * kloostermanIntegerKernelGram Q w A n n)

/-- Off-diagonal part, with the diagonal index literally erased from every inner sum. -/
def kloostermanIntegerKernelGramOffDiagonal
    (Q : Finset ℕ) (w : ℕ → ℂ) (A B : Finset ℕ) (b : ℕ → ℂ) : ℂ :=
  ∑ n ∈ B, star (b n) *
    ∑ k ∈ B.erase n, b k * kloostermanIntegerKernelGram Q w A n k

/-- Exact diagonal/off-diagonal split. -/
theorem kloostermanIntegerKernelGramQuadratic_eq_diagonal_add_offDiagonal
    (Q : Finset ℕ) (w : ℕ → ℂ) (A B : Finset ℕ) (b : ℕ → ℂ) :
    kloostermanIntegerKernelGramQuadratic Q w A B b =
      kloostermanIntegerKernelGramDiagonal Q w A B b +
        kloostermanIntegerKernelGramOffDiagonal Q w A B b := by
  unfold kloostermanIntegerKernelGramQuadratic kloostermanIntegerKernelGramDiagonal
    kloostermanIntegerKernelGramOffDiagonal
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  rw [← mul_add]
  apply congrArg (star (b n) * ·)
  exact (Finset.add_sum_erase B
    (fun k => b k * kloostermanIntegerKernelGram Q w A n k) hn).symm

/-- Diagonal Gram entry is literal row square energy. -/
theorem kloostermanIntegerKernelGram_diagonal
    (Q : Finset ℕ) (w : ℕ → ℂ) (A : Finset ℕ) (n : ℕ) :
    kloostermanIntegerKernelGram Q w A n n =
      ((∑ m ∈ A,
        ‖kloostermanIntegerModulusKernel Q w (m : ℤ) (n : ℤ)‖ ^ (2 : ℕ) : ℝ) : ℂ) := by
  unfold kloostermanIntegerKernelGram
  rw [Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro m _hm
  exact conj_mul_self _

/-- Complete diagonal quadratic form as a manifestly nonnegative real square energy. -/
theorem kloostermanIntegerKernelGramDiagonal_eq
    (Q : Finset ℕ) (w : ℕ → ℂ) (A B : Finset ℕ) (b : ℕ → ℂ) :
    kloostermanIntegerKernelGramDiagonal Q w A B b =
      ((∑ n ∈ B, ‖b n‖ ^ (2 : ℕ) *
        ∑ m ∈ A,
          ‖kloostermanIntegerModulusKernel Q w (m : ℤ) (n : ℤ)‖ ^ (2 : ℕ) : ℝ) : ℂ) := by
  unfold kloostermanIntegerKernelGramDiagonal
  rw [Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro n _hn
  rw [kloostermanIntegerKernelGram_diagonal,
    show star (b n) * (b n *
      ((∑ m ∈ A,
        ‖kloostermanIntegerModulusKernel Q w (m : ℤ) (n : ℤ)‖ ^ (2 : ℕ) : ℝ) : ℂ)) =
      (star (b n) * b n) *
        ((∑ m ∈ A,
          ‖kloostermanIntegerModulusKernel Q w (m : ℤ) (n : ℤ)‖ ^ (2 : ℕ) : ℝ) : ℂ) by ring]
  change (starRingEnd ℂ) (b n) * b n *
      ((∑ m ∈ A,
        ‖kloostermanIntegerModulusKernel Q w (m : ℤ) (n : ℤ)‖ ^ (2 : ℕ) : ℝ) : ℂ) = _
  rw [conj_mul_self]
  push_cast
  ring

end

end RHTower.Sieve
