import GaloisForLFunctions.HeckeKreinToeplitz.KernelsOnGroupsAndTheirNegativeIndex
import GaloisForLFunctions.HTGeometry.SubexponentialIntegerGrowth

/-!
# Two-sided cyclic growth for Hermitian kernels

Hermitian symmetry identifies the norms at opposite integer times.
A subexponential bound at nonnegative times therefore controls the entire
integer kernel with the same constant.
-/

noncomputable section
set_option autoImplicit false
open Complex
open GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HeckeKreinToeplitz

/-- Hermitian symmetry extends every nonnegative-time exponential envelope to both directions. -/
theorem integerGrowth_of_hermitian_natural_bound {k : Multiplicative ℤ → ℂ}
    (hk : IsHermKernel k)
    (h : ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ n : ℕ,
      ‖k (Multiplicative.ofAdd (n : ℤ))‖ ≤ C * Real.exp (ε * n)) :
    HasSubexponentialIntegerGrowth (fun z => k (Multiplicative.ofAdd z)) := by
  intro ε hε
  obtain ⟨C, hC⟩ := h ε hε
  have hC0 : 0 ≤ C := (norm_nonneg (k (Multiplicative.ofAdd (0 : ℤ)))).trans
    (by simpa using hC 0)
  refine ⟨C, hC0, fun z => ?_⟩
  change ‖k (Multiplicative.ofAdd z)‖ ≤ C * Real.exp (ε * |(z : ℝ)|)
  have hz : ∃ n : ℕ, z = (n : ℤ) ∨ z = -(n : ℤ) := by
    cases z with
    | ofNat n => exact ⟨n, Or.inl rfl⟩
    | negSucc n => exact ⟨n + 1, Or.inr rfl⟩
  obtain ⟨n, hn | hn⟩ := hz
  · rw [hn]
    simpa only [Int.cast_natCast, abs_of_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n)] using hC n
  · rw [hn]
    have he : k (Multiplicative.ofAdd (-(n : ℤ))) =
        (starRingEnd ℂ) (k (Multiplicative.ofAdd (n : ℤ))) := hk (Multiplicative.ofAdd (n : ℤ))
    rw [he, Complex.norm_conj]
    simpa only [Int.cast_neg, Int.cast_natCast, abs_neg,
      abs_of_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n)] using hC n

#print axioms integerGrowth_of_hermitian_natural_bound

end GaloisForLFunctions.HeckeKreinToeplitz
