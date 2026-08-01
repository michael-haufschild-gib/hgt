import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.StdBasis
import Mathlib.RingTheory.Adjoin.Polynomial.Basic
import Mathlib.Data.Real.Basic

/-!
# Simple-clock rank-one algebra saturation

A diagonal clock with distinct labels and one rank-one kernel whose generating vector has no zero
coordinate generate the full finite matrix algebra.  The proof is constructive: Lagrange
polynomials in the clock isolate diagonal matrix units, and sandwiching the rank-one kernel between
two such projectors isolates every matrix unit.
-/

open scoped BigOperators
open Polynomial

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Lagrange polynomial selecting one label from a finite simple-spectrum clock. -/
def simpleClockLagrangePolynomial
    {I : Type*} [Fintype I] [DecidableEq I]
    (label : I → ℝ) (i : I) : ℝ[X] :=
  ∏ j ∈ Finset.univ.erase i,
    Polynomial.C (label i - label j)⁻¹ *
      (Polynomial.X - Polynomial.C (label j))

theorem simpleClockLagrangePolynomial_eval
    {I : Type*} [Fintype I] [DecidableEq I]
    (label : I → ℝ) (hlabel : Function.Injective label) (i j : I) :
    (simpleClockLagrangePolynomial label i).eval (label j) =
      if j = i then 1 else 0 := by
  by_cases hji : j = i
  · subst j
    rw [if_pos rfl]
    rw [simpleClockLagrangePolynomial, Polynomial.eval_prod]
    apply Finset.prod_eq_one
    intro k hk
    rw [Finset.mem_erase] at hk
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_sub,
      Polynomial.eval_X]
    have hne : label i - label k ≠ 0 := sub_ne_zero.mpr (hlabel.ne hk.1.symm)
    field_simp
  · rw [if_neg hji]
    rw [simpleClockLagrangePolynomial, Polynomial.eval_prod]
    apply Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hji, Finset.mem_univ j⟩)
    simp

/-- Polynomial evaluation on a real diagonal matrix is coordinatewise scalar evaluation. -/
theorem aeval_diagonal_real
    {I : Type*} [Fintype I] [DecidableEq I]
    (p : ℝ[X]) (label : I → ℝ) :
    aeval (Matrix.diagonal label) p =
      Matrix.diagonal (fun i => p.eval (label i)) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      rw [map_add, hp, hq]
      ext i j
      by_cases hij : i = j
      · subst j
        simp
      · simp [hij]
  | monomial n a =>
      simp only [aeval_def, Polynomial.eval₂_monomial]
      rw [Matrix.algebraMap_eq_diagonal, Matrix.diagonal_pow,
        Matrix.diagonal_mul_diagonal]
      ext i j
      by_cases hij : i = j
      · subst j
        simp
      · simp [hij]

/-- Lagrange functional calculus of the clock gives the corresponding diagonal matrix unit. -/
theorem aeval_simpleClockLagrangePolynomial
    {I : Type*} [Fintype I] [DecidableEq I]
    (label : I → ℝ) (hlabel : Function.Injective label) (i : I) :
    aeval (Matrix.diagonal label) (simpleClockLagrangePolynomial label i) =
      Matrix.single i i 1 := by
  rw [aeval_diagonal_real]
  have hselector :
      (fun j => (simpleClockLagrangePolynomial label i).eval (label j)) =
        Pi.single i 1 := by
    funext j
    rw [simpleClockLagrangePolynomial_eval label hlabel]
    simp [Pi.single_apply, eq_comm]
  rw [hselector, Matrix.diagonal_single]

/-- A diagonal simple clock and one full-support rank-one kernel generate the full matrix algebra. -/
theorem simpleClock_rankOne_generatedSubalgebra_eq_top
    {I : Type*} [Fintype I] [DecidableEq I]
    (label vector : I → ℝ)
    (hlabel : Function.Injective label)
    (hvector : ∀ i, vector i ≠ 0) :
    Algebra.adjoin ℝ
        ({Matrix.diagonal label, fun i j => vector i * vector j} :
          Set (Matrix I I ℝ)) = ⊤ := by
  let clock : Matrix I I ℝ := Matrix.diagonal label
  let boundary : Matrix I I ℝ := fun i j => vector i * vector j
  let generators : Set (Matrix I I ℝ) := {clock, boundary}
  let A : Subalgebra ℝ (Matrix I I ℝ) := Algebra.adjoin ℝ generators
  have hclock : clock ∈ A := by
    apply Algebra.subset_adjoin
    simp [generators]
  have hboundary : boundary ∈ A := by
    apply Algebra.subset_adjoin
    simp [generators]
  have hprojector : ∀ i : I, Matrix.single i i 1 ∈ A := by
    intro i
    have hpoly :
        aeval clock (simpleClockLagrangePolynomial label i) ∈ A := by
      have hsingleton : Algebra.adjoin ℝ {clock} ≤ A := by
        apply Algebra.adjoin_le
        intro x hx
        rw [Set.mem_singleton_iff] at hx
        subst x
        exact hclock
      exact hsingleton (Polynomial.aeval_mem_adjoin_singleton ℝ clock)
    rw [show clock = Matrix.diagonal label by rfl,
      aeval_simpleClockLagrangePolynomial label hlabel i] at hpoly
    exact hpoly
  have hsingle : ∀ i j : I, Matrix.single i j 1 ∈ A := by
    intro i j
    have hprod :
        Matrix.single i i 1 * boundary * Matrix.single j j 1 ∈ A :=
      A.mul_mem (A.mul_mem (hprojector i) hboundary) (hprojector j)
    have hprodEq :
        Matrix.single i i 1 * boundary * Matrix.single j j 1 =
          (vector i * vector j) • Matrix.single i j 1 := by
      simp [boundary]
    rw [hprodEq] at hprod
    have hne : vector i * vector j ≠ 0 := mul_ne_zero (hvector i) (hvector j)
    have hscaled := A.smul_mem hprod (vector i * vector j)⁻¹
    have hrescale :
        (vector i * vector j)⁻¹ •
            ((vector i * vector j) •
              (Matrix.single i j (1 : ℝ) : Matrix I I ℝ)) =
          Matrix.single i j 1 := by
      rw [smul_smul, inv_mul_cancel₀ hne, one_smul]
    rw [hrescale] at hscaled
    exact hscaled
  have hA : A = ⊤ := by
    apply Algebra.eq_top_iff.mpr
    intro M
    have hdecomp :
        M = ∑ i : I, ∑ j : I, Matrix.single i j (M i j) :=
      Matrix.matrix_eq_sum_single M
    rw [hdecomp]
    apply Subalgebra.sum_mem
    intro i hi
    apply Subalgebra.sum_mem
    intro j hj
    simpa only [Matrix.smul_single, smul_eq_mul, mul_one] using
      A.smul_mem (hsingle i j) (M i j)
  dsimp only [A, generators, clock, boundary] at hA
  exact hA

end

end GaloisForLFunctions.HTGeometry
