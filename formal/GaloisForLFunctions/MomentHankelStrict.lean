import GaloisForLFunctions.MomentFunctionalPositivity
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Algebra.Polynomial.OfFn

/-!
# Strict finite Hankel matrices from an infinite-support representing measure

`MomentFunctionalPositivity` proves nonnegativity and nondegeneracy of the polynomial square
functional supplied by an infinitely supported representing measure.  This module packages that
statement as strict positive definiteness, and hence positive determinant, of every finite Hankel
matrix.  It is the common finite-dimensional consumer for measure-producing RH detours.
-/

open scoped BigOperators
open MeasureTheory Polynomial

namespace HTGeometry

/-- The finite Hankel matrix of a real sequence. -/
noncomputable def momentHankelMatrix (s : ℕ → ℝ) (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => s ((i : ℕ) + (j : ℕ))

theorem momentHankelMatrix_isHermitian (s : ℕ → ℝ) (n : ℕ) :
    (momentHankelMatrix s n).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  simp [momentHankelMatrix, add_comm]

@[simp] theorem momentFunctional_monomial (s : ℕ → ℝ) (n : ℕ) (c : ℝ) :
    momentFunctional s (Polynomial.monomial n c) = c * s n := by
  simp [momentFunctional]

theorem momentFunctional_finset_sum {ι : Type*} [DecidableEq ι]
    (s : ℕ → ℝ) (S : Finset ι) (f : ι → Polynomial ℝ) :
    momentFunctional s (∑ i ∈ S, f i) = ∑ i ∈ S, momentFunctional s (f i) := by
  induction S using Finset.induction with
  | empty => simp
  | @insert i S hi ih => simp [Finset.sum_insert, hi, momentFunctional_add, ih]

/-- The coefficient-vector quadratic form of the finite Hankel matrix is literally the moment
functional evaluated on the square of the corresponding polynomial. -/
theorem dotProduct_mulVec_momentHankelMatrix (s : ℕ → ℝ) (n : ℕ) (a : Fin n → ℝ) :
    a ⬝ᵥ (momentHankelMatrix s n).mulVec a =
      momentFunctional s ((Polynomial.ofFn n a) ^ 2) := by
  rw [Polynomial.ofFn_eq_sum_monomial, pow_two, Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  rw [momentFunctional_finset_sum]
  simp_rw [momentFunctional_finset_sum]
  simp only [dotProduct, Matrix.mulVec, momentHankelMatrix, Finset.mul_sum,
    Polynomial.monomial_mul_monomial, momentFunctional_monomial]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- A representing measure which charges the complement of every finite set makes every finite
Hankel matrix strictly positive definite. -/
theorem momentHankelMatrix_posDef_of_infiniteSupport {μ : Measure ℝ} (s : ℕ → ℝ)
    (hs : ∀ k, s k = ∫ x, (x : ℝ) ^ k ∂μ)
    (hint : ∀ k, Integrable (fun x : ℝ => (x : ℝ) ^ k) μ)
    (hμinf : ∀ F : Finset ℝ, 0 < μ {x : ℝ | x ∉ F}) (n : ℕ) :
    (momentHankelMatrix s n).PosDef := by
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  refine ⟨momentHankelMatrix_isHermitian s n, ?_⟩
  intro a ha
  rw [star_trivial, dotProduct_mulVec_momentHankelMatrix]
  have hnonneg := momentFunctional_pow_two_nonneg s hs hint (Polynomial.ofFn n a)
  have hne : momentFunctional s ((Polynomial.ofFn n a) ^ 2) ≠ 0 := by
    intro hzero
    have hp := momentFunctional_pow_two_eq_zero s hs hint hμinf (Polynomial.ofFn n a) hzero
    apply ha
    apply Polynomial.injective_ofFn n
    rw [hp, Polynomial.ofFn_zero]
  exact lt_of_le_of_ne hnonneg (Ne.symm hne)

/-- Infinite-support moment representations make every finite Hankel determinant strictly
positive. -/
theorem det_momentHankelMatrix_pos_of_infiniteSupport {μ : Measure ℝ} (s : ℕ → ℝ)
    (hs : ∀ k, s k = ∫ x, (x : ℝ) ^ k ∂μ)
    (hint : ∀ k, Integrable (fun x : ℝ => (x : ℝ) ^ k) μ)
    (hμinf : ∀ F : Finset ℝ, 0 < μ {x : ℝ | x ∉ F}) (n : ℕ) :
    0 < (momentHankelMatrix s n).det :=
  (momentHankelMatrix_posDef_of_infiniteSupport s hs hint hμinf n).det_pos

end HTGeometry
