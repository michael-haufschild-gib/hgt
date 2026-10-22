import GaloisForLFunctions.HTGeometry.PolynomialODE.JetRankThreeSourcePositiveSl2
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# No finite graded module for the source-positive theta sl₂ action

The exact nonlinear source-positive theta `sl₂` action cannot close on a nonconstant
finite-dimensional polynomial carrier with nonnegative Cartan weights. The obstruction is
structural: `[E,F]=H` makes the finite Cartan trace vanish, while any nonconstant polynomial
grading contributes a strictly positive Cartan weight.

Thus a contravariant-form attack on theta rank-three D1 cannot truncate the exact polynomial
action to a finite graded Shapovalov module. A surviving representation-theoretic proof must use
an infinite graded carrier or a cross-scale congruence outside this finite-module ansatz.
-/

open Complex Real

namespace HTGeometry

noncomputable section

theorem modularThetaSourcePositiveFieldLie_add
    (X : ModularThetaSourcePositiveState → ModularThetaSourcePositivePolynomial)
    (P Q : ModularThetaSourcePositivePolynomial) :
    modularThetaSourcePositiveFieldLie X (P + Q) =
      modularThetaSourcePositiveFieldLie X P +
        modularThetaSourcePositiveFieldLie X Q := by
  simp [modularThetaSourcePositiveFieldLie, add_mul]
  ring

theorem modularThetaSourcePositiveFieldLie_sub
    (X : ModularThetaSourcePositiveState → ModularThetaSourcePositivePolynomial)
    (P Q : ModularThetaSourcePositivePolynomial) :
    modularThetaSourcePositiveFieldLie X (P - Q) =
      modularThetaSourcePositiveFieldLie X P -
        modularThetaSourcePositiveFieldLie X Q := by
  simp [modularThetaSourcePositiveFieldLie, sub_mul]
  ring

theorem modularThetaSourcePositiveFieldLie_mul
    (X : ModularThetaSourcePositiveState → ModularThetaSourcePositivePolynomial)
    (P Q : ModularThetaSourcePositivePolynomial) :
    modularThetaSourcePositiveFieldLie X (P * Q) =
      modularThetaSourcePositiveFieldLie X P * Q +
        P * modularThetaSourcePositiveFieldLie X Q := by
  unfold modularThetaSourcePositiveFieldLie
  simp only [MvPolynomial.pderiv_mul, add_mul]
  ring

theorem modularThetaSourcePositiveFieldLie_C
    (X : ModularThetaSourcePositiveState → ModularThetaSourcePositivePolynomial)
    (c : ℂ) :
    modularThetaSourcePositiveFieldLie X (MvPolynomial.C c) = 0 := by
  simp [modularThetaSourcePositiveFieldLie]

theorem modularThetaSourcePositiveFieldLie_X
    (X : ModularThetaSourcePositiveState → ModularThetaSourcePositivePolynomial)
    (i : ModularThetaSourcePositiveState) :
    modularThetaSourcePositiveFieldLie X (MvPolynomial.X i) = X i := by
  cases i <;> simp [modularThetaSourcePositiveFieldLie, MvPolynomial.pderiv_X]

theorem modularThetaSourcePositiveFieldLie_smul
    (X : ModularThetaSourcePositiveState → ModularThetaSourcePositivePolynomial)
    (c : ℂ) (P : ModularThetaSourcePositivePolynomial) :
    modularThetaSourcePositiveFieldLie X (c • P) =
      c • modularThetaSourcePositiveFieldLie X P := by
  simp only [MvPolynomial.smul_eq_C_mul]
  rw [modularThetaSourcePositiveFieldLie_mul,
    modularThetaSourcePositiveFieldLie_C]
  simp

theorem modularThetaSourcePositiveFieldLie_finset_sum
    {ι : Type*}
    (X : ModularThetaSourcePositiveState → ModularThetaSourcePositivePolynomial)
    (s : Finset ι) (P : ι → ModularThetaSourcePositivePolynomial) :
    modularThetaSourcePositiveFieldLie X (∑ i ∈ s, P i) =
      ∑ i ∈ s, modularThetaSourcePositiveFieldLie X (P i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [modularThetaSourcePositiveFieldLie]
  | @insert i s hi ih =>
      simp [hi, modularThetaSourcePositiveFieldLie_add, ih]

theorem modularThetaSourcePositiveFieldLie_sum
    {ι : Type*} [Fintype ι]
    (X : ModularThetaSourcePositiveState → ModularThetaSourcePositivePolynomial)
    (P : ι → ModularThetaSourcePositivePolynomial) :
    modularThetaSourcePositiveFieldLie X (∑ i, P i) =
      ∑ i, modularThetaSourcePositiveFieldLie X (P i) := by
  exact modularThetaSourcePositiveFieldLie_finset_sum X Finset.univ P

/-- Polynomial Lie derivatives represent the bracket of the source-positive vector fields. -/
theorem modularThetaSourcePositiveFieldLie_comm
    (X Y : ModularThetaSourcePositiveState → ModularThetaSourcePositivePolynomial)
    (P : ModularThetaSourcePositivePolynomial) :
    modularThetaSourcePositiveFieldLie X
        (modularThetaSourcePositiveFieldLie Y P) -
      modularThetaSourcePositiveFieldLie Y
        (modularThetaSourcePositiveFieldLie X P) =
      modularThetaSourcePositiveFieldLie
        (modularThetaSourcePositiveVectorFieldBracket X Y) P := by
  induction P using MvPolynomial.induction_on with
  | C c =>
      simp [modularThetaSourcePositiveFieldLie]
  | add P Q hP hQ =>
      simp only [modularThetaSourcePositiveFieldLie_add]
      linear_combination hP + hQ
  | mul_X P i hP =>
      simp only [modularThetaSourcePositiveFieldLie_mul,
        modularThetaSourcePositiveFieldLie_X,
        modularThetaSourcePositiveFieldLie_add]
      have hi :
          modularThetaSourcePositiveFieldLie X (Y i) -
            modularThetaSourcePositiveFieldLie Y (X i) =
          modularThetaSourcePositiveVectorFieldBracket X Y i := by
        unfold modularThetaSourcePositiveFieldLie
          modularThetaSourcePositiveVectorFieldBracket
        ring
      linear_combination hP * MvPolynomial.X i + P * hi

/-- The vector-field `[E,F]=H` identity acts on every source-positive polynomial. -/
theorem modularThetaSourcePositiveFieldLie_sl2_ef
    (P : ModularThetaSourcePositivePolynomial) :
    modularThetaSourcePositiveFieldLie modularThetaSourcePositiveSl2E
        (modularThetaSourcePositiveFieldLie modularThetaSourcePositiveSl2F P) -
      modularThetaSourcePositiveFieldLie modularThetaSourcePositiveSl2F
        (modularThetaSourcePositiveFieldLie modularThetaSourcePositiveSl2E P) =
      modularThetaSourcePositiveFieldLie modularThetaSourcePositiveSl2H P := by
  rw [modularThetaSourcePositiveFieldLie_comm,
    modularThetaSourcePositive_sl2_bracket_ef]

/-- A finite `sl₂` carrier cannot have only nonnegative Cartan weights and at least one
strictly positive weight. Trace of `[E,F]` vanishes, whereas trace of its Cartan diagonal is
strictly positive. -/
theorem not_exists_nonnegativeWeight_sl2Matrices :
    ¬ ∃ (n : ℕ) (w : Fin n → ℝ) (E F : Matrix (Fin n) (Fin n) ℂ),
      (∀ i, 0 ≤ w i) ∧ (∃ i, 0 < w i) ∧
        E * F - F * E = Matrix.diagonal (fun i => (w i : ℂ)) := by
  rintro ⟨n, w, E, F, hw, ⟨i, hi⟩, hbracket⟩
  have hsum : 0 < ∑ j, w j := by
    apply Finset.sum_pos'
    · intro j hj
      exact hw j
    · exact ⟨i, Finset.mem_univ i, hi⟩
  have htrace : Matrix.trace (E * F - F * E) = 0 := by
    rw [Matrix.trace_sub, Matrix.trace_mul_comm]
    exact sub_self _
  rw [hbracket, Matrix.trace_diagonal] at htrace
  have hsumzero : (∑ j, w j : ℝ) = 0 := by
    have hre := congrArg Complex.re htrace
    simpa using hre
  linarith

/-- **Finite graded source-`sl₂` no-go.** No linearly independent nonconstant finite polynomial
carrier can be closed under the exact source-positive raising and lowering Lie derivatives while
diagonalizing the Cartan action with nonnegative weights.

This rules out the finite Shapovalov/contravariant-form ansatz proposed for the remaining
theta rank-three D1 cone. It does not rule out an infinite graded form or a direct cross-scale
congruence. -/
theorem modularThetaSourcePositive_no_finite_nonconstant_graded_sl2Carrier
    {n : ℕ}
    (p : Fin n → ModularThetaSourcePositivePolynomial)
    (w : Fin n → ℝ) (E F : Matrix (Fin n) (Fin n) ℂ)
    (hp : LinearIndependent ℂ p)
    (hw : ∀ i, 0 ≤ w i) (hpositive : ∃ i, 0 < w i)
    (hE : ∀ j,
      modularThetaSourcePositiveFieldLie modularThetaSourcePositiveSl2E (p j) =
        ∑ i, E i j • p i)
    (hF : ∀ j,
      modularThetaSourcePositiveFieldLie modularThetaSourcePositiveSl2F (p j) =
        ∑ i, F i j • p i)
    (hH : ∀ j,
      modularThetaSourcePositiveFieldLie modularThetaSourcePositiveSl2H (p j) =
        (w j : ℂ) • p j) :
    False := by
  apply not_exists_nonnegativeWeight_sl2Matrices
  refine ⟨n, w, E, F, hw, hpositive, ?_⟩
  apply Matrix.ext
  intro k j
  have hj := modularThetaSourcePositiveFieldLie_sl2_ef (p j)
  rw [hF j, hE j,
    modularThetaSourcePositiveFieldLie_sum,
    modularThetaSourcePositiveFieldLie_sum] at hj
  simp_rw [modularThetaSourcePositiveFieldLie_smul, hE, hF] at hj
  rw [hH j] at hj
  have hcoeff := (Fintype.linearIndependent_iff.mp hp)
    (fun k => (E * F - F * E - Matrix.diagonal (fun i => (w i : ℂ))) k j)
  have hEF :
      ∑ x, (∑ t, E x t * F t j) • p x =
        ∑ t, F t j • ∑ x, E x t • p x := by
    simp only [Finset.smul_sum, Finset.sum_smul, smul_smul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x hx
    apply Finset.sum_congr rfl
    intro t ht
    rw [mul_comm]
  have hFE :
      ∑ x, (∑ t, F x t * E t j) • p x =
        ∑ t, E t j • ∑ x, F x t • p x := by
    simp only [Finset.smul_sum, Finset.sum_smul, smul_smul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x hx
    apply Finset.sum_congr rfl
    intro t ht
    rw [mul_comm]
  have hdiag :
      ∑ x, (if x = j then (w x : ℂ) else 0) • p x =
        (w j : ℂ) • p j := by
    simp
  have hzero :
      ∑ k, ((E * F - F * E - Matrix.diagonal (fun i => (w i : ℂ))) k j) • p k = 0 := by
    simp only [Matrix.sub_apply, Matrix.mul_apply,
      Matrix.diagonal_apply, sub_smul, Finset.sum_sub_distrib]
    rw [hEF, hFE, hdiag]
    linear_combination hj
  have hk := hcoeff hzero k
  simpa only [Matrix.sub_apply, sub_eq_zero] using hk

end

end HTGeometry
