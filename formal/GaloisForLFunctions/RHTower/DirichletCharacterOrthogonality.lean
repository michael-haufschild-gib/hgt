import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-!
# Closed finite-family orthogonality for Dirichlet characters

This is the finite algebraic first layer required by the Bondarenko--Heap
prime-modulus character-family argument.  It works for every positive modulus, represented as
`n + 1`, and gives the exact character average before any zero-density or analytic input enters.
-/

open scoped BigOperators

noncomputable section

namespace RHTower

/-- Complete orthogonality for the complex Dirichlet-character family modulo `n + 1`.
The statement has no analytic assumption, density input, or unproved arithmetic premise. -/
theorem dirichletCharacterFamily_orthogonality
    (n : ℕ) (a b : (ZMod (n + 1))ˣ) :
    ∑ χ : DirichletCharacter ℂ (n + 1),
      χ ((a : ZMod (n + 1))⁻¹) * χ b =
        if (a : ZMod (n + 1)) = b then ((n + 1).totient : ℂ) else 0 := by
  exact DirichletCharacter.sum_char_inv_mul_char_eq ℂ a.isUnit b

/-- The same orthogonality kernel with the inverse on its second factor.
This is the form used to diagonalize a family second moment. -/
theorem dirichletCharacterFamily_kernel
    (n : ℕ) (u v : (ZMod (n + 1))ˣ) :
    ∑ χ : DirichletCharacter ℂ (n + 1),
      χ u * χ ((v : ZMod (n + 1))⁻¹) =
        if u = v then ((n + 1).totient : ℂ) else 0 := by
  simpa only [Units.ext_iff, mul_comm, eq_comm] using
    dirichletCharacterFamily_orthogonality n v u

/-- Exact finite-family diagonalization of two Dirichlet-character sums.
No zero-density estimate, character hypothesis, or unproved analytic input enters this identity. -/
theorem dirichletCharacterFamily_bilinear
    (n : ℕ) (f g : (ZMod (n + 1))ˣ → ℂ) :
    ∑ χ : DirichletCharacter ℂ (n + 1),
      (∑ u, f u * χ u) * (∑ v, g v * χ ((v : ZMod (n + 1))⁻¹)) =
        ((n + 1).totient : ℂ) * ∑ u, f u * g u := by
  classical
  calc
    _ = ∑ u, ∑ v, ∑ χ : DirichletCharacter ℂ (n + 1),
        (f u * χ u) * (g v * χ ((v : ZMod (n + 1))⁻¹)) := by
      simp_rw [Finset.sum_mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro u hu
      rw [Finset.sum_comm]
    _ = ∑ u, ∑ v, f u * g v *
        (∑ χ : DirichletCharacter ℂ (n + 1),
          χ u * χ ((v : ZMod (n + 1))⁻¹)) := by
      apply Finset.sum_congr rfl
      intro u hu
      apply Finset.sum_congr rfl
      intro v hv
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro χ hχ
      ring
    _ = ∑ u, ∑ v, f u * g v *
        (if u = v then ((n + 1).totient : ℂ) else 0) := by
      simp_rw [dirichletCharacterFamily_kernel]
    _ = ∑ u, f u * g u * ((n + 1).totient : ℂ) := by
      apply Finset.sum_congr rfl
      intro u hu
      symm
      simpa only [mul_ite, mul_zero, eq_comm, Finset.mem_univ, if_true] using
        (Finset.sum_ite_eq' Finset.univ u
          (fun v => f u * g v * ((n + 1).totient : ℂ)))
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro u hu
      ring

end RHTower
