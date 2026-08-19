import GaloisForLFunctions.HTGeometry.CaratheodoryFejerAtomicKernelRoots
import Mathlib.Analysis.Matrix.Order
import Mathlib.Tactic

/-!
# Atomic PSD Gram factorization in the Carathéodory--Fejér theorem

For a specified finite collection of unit-circle atoms and positive weights,
this module supplies the literal rectangular Vandermonde factorization
`Bᴴ B`, its positive semidefiniteness, and the missing matrix-kernel to
weighted-energy step.  Thus the root conclusion is now derived from a genuine
PSD Gram kernel, rather than taking zero atomic energy as an external input.

The converse, which constructs the atoms and weights from an arbitrary
finite PSD Toeplitz matrix, remains the separate Carathéodory--Fejér existence
theorem; it is not asserted here.
-/

open scoped BigOperators ComplexOrder
open Matrix

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The square-root-weighted rectangular Vandermonde evaluation matrix. -/
def caratheodoryFejerAtomicFactor {n r : ℕ} (z : Fin r → ℂ) (weight : Fin r → ℝ) :
    Matrix (Fin r) (Fin (n + 1)) ℂ :=
  fun i j => (Real.sqrt (weight i) : ℂ) * z i ^ (j : ℕ)

/-- The finite atomic Carathéodory--Fejér Gram section. -/
def caratheodoryFejerAtomicGram {n r : ℕ} (z : Fin r → ℂ) (weight : Fin r → ℝ) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
  (caratheodoryFejerAtomicFactor (n := n) z weight)ᴴ *
    caratheodoryFejerAtomicFactor (n := n) z weight

/-- Literal rectangular factorization of the atomic Gram matrix. -/
theorem caratheodoryFejerAtomicGram_factorization {n r : ℕ}
    (z : Fin r → ℂ) (weight : Fin r → ℝ) :
    caratheodoryFejerAtomicGram (n := n) z weight =
      (caratheodoryFejerAtomicFactor (n := n) z weight)ᴴ *
        caratheodoryFejerAtomicFactor (n := n) z weight := rfl

/-- Every atomic Carathéodory--Fejér Gram section is positive semidefinite. -/
theorem caratheodoryFejerAtomicGram_posSemidef {n r : ℕ}
    (z : Fin r → ℂ) (weight : Fin r → ℝ) :
    (caratheodoryFejerAtomicGram (n := n) z weight).PosSemidef := by
  exact Matrix.posSemidef_conjTranspose_mul_self _

/-- A kernel vector of the actual atomic Gram matrix annihilates every
positive-weighted Vandermonde atom. -/
theorem caratheodoryFejerAtomicGram_kernel_eval_eq_zero
    {n r : ℕ} (xi : Fin (n + 1) → ℂ) (z : Fin r → ℂ) (weight : Fin r → ℝ)
    (hweight : ∀ i, 0 < weight i)
    (hker : caratheodoryFejerAtomicGram (n := n) z weight *ᵥ xi = 0)
    (i : Fin r) :
    (finiteToeplitzKernelPolynomial xi).eval (z i) = 0 := by
  let B := caratheodoryFejerAtomicFactor (n := n) z weight
  have hker' : (Bᴴ * B) *ᵥ xi = 0 := by
    simpa [B, caratheodoryFejerAtomicGram] using hker
  have hBzero : B *ᵥ xi = 0 :=
    (Matrix.conjTranspose_mul_self_mulVec_eq_zero B xi).mp hker'
  have hi := congrFun hBzero i
  change (∑ j : Fin (n + 1),
    ((Real.sqrt (weight i) : ℂ) * z i ^ (j : ℕ)) * xi j) = 0 at hi
  have hi' : (Real.sqrt (weight i) : ℂ) *
      (∑ j : Fin (n + 1), xi j * z i ^ (j : ℕ)) = 0 := by
    calc
      (Real.sqrt (weight i) : ℂ) *
          (∑ j : Fin (n + 1), xi j * z i ^ (j : ℕ)) =
          ∑ j : Fin (n + 1),
            ((Real.sqrt (weight i) : ℂ) * z i ^ (j : ℕ)) * xi j := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro j _
              ring
      _ = 0 := hi
  have hsum : ∑ j : Fin (n + 1), xi j * z i ^ (j : ℕ) = 0 :=
    (mul_eq_zero.mp hi').resolve_left
      (by exact_mod_cast (Real.sqrt_pos.2 (hweight i)).ne')
  rw [finiteToeplitzKernelPolynomial_eval]
  exact hsum

/-- The finite Carathéodory--Fejér unit-circle root conclusion, derived from
the actual atomic PSD Gram kernel. -/
theorem caratheodoryFejerAtomicGram_kernel_polynomial_roots_on_unitCircle
    {n : ℕ} (xi : Fin (n + 1) → ℂ) (z : Fin n → ℂ) (weight : Fin n → ℝ)
    (hInjective : Function.Injective z)
    (hCircle : ∀ i, ‖z i‖ = 1)
    (hweight : ∀ i, 0 < weight i)
    (hker : caratheodoryFejerAtomicGram (n := n) z weight *ᵥ xi = 0)
    (hxi : finiteToeplitzKernelPolynomial xi ≠ 0)
    {u : ℂ} (hu : u ∈ (finiteToeplitzKernelPolynomial xi).roots) :
    ‖u‖ = 1 := by
  apply atomic_kernel_polynomial_roots_on_unitCircle xi z hInjective hCircle ?_ hxi hu
  intro i
  rw [← finiteToeplitzKernelPolynomial_eval]
  exact caratheodoryFejerAtomicGram_kernel_eval_eq_zero xi z weight hweight hker i

end

end GaloisForLFunctions.HTGeometry
