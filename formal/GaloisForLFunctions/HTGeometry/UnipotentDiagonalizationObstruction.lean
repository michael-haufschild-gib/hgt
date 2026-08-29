import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Data.Complex.Basic

/-!
# Unipotent obstructions to diagonalisation and to positive-metric unitarity

Two elementary but reusable finite-dimensional facts.

* A matrix similar to a diagonal matrix and satisfying `(M - 1)² = 0` is the identity.  Hence a
  nontrivial unipotent matrix is not diagonalisable, and neither is any matrix one of whose powers
  is nontrivially unipotent.
* If `M * M = 1 + K` with `K * K = 0` and `K ≠ 0`, then no positive-definite metric `Q` satisfies
  `Mᴴ Q M = Q`.  The proof compares the invariance identity for `M²` and `M⁴`; the quadratic terms
  force `Kᴴ Q K = 0`, which contradicts positive definiteness.  No spectral theorem is used.
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A square matrix is diagonalisable when it is similar to a diagonal matrix. -/
def IsDiagonalizableMatrix (M : Matrix n n ℂ) : Prop :=
  ∃ (U : Matrix n n ℂ) (d : n → ℂ), IsUnit U.det ∧ M * U = U * Matrix.diagonal d

/-- Diagonalisability passes to the square. -/
theorem IsDiagonalizableMatrix.mul_self {M : Matrix n n ℂ}
    (h : IsDiagonalizableMatrix M) : IsDiagonalizableMatrix (M * M) := by
  obtain ⟨U, d, hU, hMU⟩ := h
  refine ⟨U, fun i => d i * d i, hU, ?_⟩
  calc M * M * U = M * (M * U) := by rw [Matrix.mul_assoc]
    _ = M * (U * Matrix.diagonal d) := by rw [hMU]
    _ = (M * U) * Matrix.diagonal d := by rw [Matrix.mul_assoc]
    _ = U * Matrix.diagonal d * Matrix.diagonal d := by rw [hMU]
    _ = U * (Matrix.diagonal d * Matrix.diagonal d) := by rw [Matrix.mul_assoc]
    _ = U * Matrix.diagonal fun i => d i * d i := by
        rw [Matrix.diagonal_mul_diagonal]

/-- A diagonalisable unipotent matrix of index at most two is the identity. -/
theorem eq_one_of_isDiagonalizableMatrix_of_sub_one_sq
    {M : Matrix n n ℂ} (h : IsDiagonalizableMatrix M)
    (hnil : (M - 1) * (M - 1) = 0) : M = 1 := by
  obtain ⟨U, d, hU, hMU⟩ := h
  have hUunit : IsUnit U := (Matrix.isUnit_iff_isUnit_det U).mpr hU
  have hdiagsub : Matrix.diagonal d - 1 = Matrix.diagonal fun i => d i - 1 := by
    ext i j
    by_cases hij : i = j <;> simp [hij]
  have hstep : (M - 1) * U = U * Matrix.diagonal fun i => d i - 1 := by
    rw [← hdiagsub, Matrix.mul_sub, Matrix.mul_one, ← hMU, Matrix.sub_mul,
      Matrix.one_mul]
  have hzero : U * Matrix.diagonal (fun i => (d i - 1) * (d i - 1)) = 0 := by
    calc U * Matrix.diagonal (fun i => (d i - 1) * (d i - 1))
        = U * (Matrix.diagonal (fun i => d i - 1) *
            Matrix.diagonal fun i => d i - 1) := by
          rw [Matrix.diagonal_mul_diagonal]
      _ = ((M - 1) * U) * Matrix.diagonal fun i => d i - 1 := by
          rw [hstep, Matrix.mul_assoc]
      _ = (M - 1) * ((M - 1) * U) := by rw [Matrix.mul_assoc, hstep]
      _ = ((M - 1) * (M - 1)) * U := by rw [Matrix.mul_assoc]
      _ = 0 := by rw [hnil, Matrix.zero_mul]
  have hdiag : Matrix.diagonal (fun i => (d i - 1) * (d i - 1)) = 0 := by
    have := hUunit.mul_left_cancel (b := Matrix.diagonal fun i => (d i - 1) * (d i - 1))
      (c := (0 : Matrix n n ℂ))
    exact this (by rw [hzero, Matrix.mul_zero])
  have hd : ∀ i, d i = 1 := by
    intro i
    have := congrArg (fun A => A i i) hdiag
    simp only [Matrix.diagonal_apply_eq, Matrix.zero_apply] at this
    have hsq : d i - 1 = 0 := by
      rcases mul_eq_zero.1 this with h | h <;> exact h
    exact sub_eq_zero.1 hsq
  have hdiagone : Matrix.diagonal d = (1 : Matrix n n ℂ) := by
    ext i j
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij, hd]
  have : M * U = 1 * U := by rw [hMU, hdiagone, Matrix.mul_one, Matrix.one_mul]
  exact hUunit.mul_right_cancel this

/-- A nontrivial unipotent square obstructs diagonalisability. -/
theorem not_isDiagonalizableMatrix_of_mul_self_unipotent
    {M K : Matrix n n ℂ} (hK : K * K = 0) (hK0 : K ≠ 0)
    (hM : M * M = 1 + K) : ¬ IsDiagonalizableMatrix M := by
  intro hdiag
  have hsq : IsDiagonalizableMatrix (M * M) := hdiag.mul_self
  have hnil : (M * M - 1) * (M * M - 1) = 0 := by
    rw [hM]; simpa using hK
  have := eq_one_of_isDiagonalizableMatrix_of_sub_one_sq hsq hnil
  rw [hM] at this
  exact hK0 (by simpa using this)

/-- Positive definiteness of a one-particle metric, written without an order instance on `ℂ`:
the metric is Hermitian and its quadratic form is real-positive off zero.  This is `Matrix.PosDef`
unfolded. -/
def IsPositiveDefiniteMetric (Q : Matrix n n ℂ) : Prop :=
  Q.IsHermitian ∧ ∀ x : n → ℂ, x ≠ 0 → 0 < (star x ⬝ᵥ Q *ᵥ x).re

/-- **No positive-metric unitarity.**  If `M * M = 1 + K` with `K` a nonzero square-zero matrix,
then no positive-definite metric `Q` makes `M` an isometry.  Comparing the invariance identity at
`M²` and `M⁴` cancels the linear term and forces `Kᴴ Q K = 0`, which the metric forbids.  No
spectral theorem is used. -/
theorem not_conjTranspose_mul_mul_eq_of_mul_self_unipotent
    {M K Q : Matrix n n ℂ} (hK : K * K = 0) (hK0 : K ≠ 0)
    (hM : M * M = 1 + K) (hQ : IsPositiveDefiniteMetric Q) :
    Mᴴ * Q * M ≠ Q := by
  intro hiso
  have hpow : ∀ k : ℕ, (M ^ k)ᴴ * Q * M ^ k = Q := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        have hstep : M ^ (k + 1) = M ^ k * M := by rw [pow_succ]
        rw [hstep, Matrix.conjTranspose_mul]
        calc Mᴴ * (M ^ k)ᴴ * Q * (M ^ k * M)
            = Mᴴ * ((M ^ k)ᴴ * Q * M ^ k) * M := by
              simp [Matrix.mul_assoc]
          _ = Mᴴ * Q * M := by rw [ih]
          _ = Q := hiso
  have hsq2 : M ^ 2 = 1 + K := by rw [pow_two]; exact hM
  have hsq4 : M ^ 4 = 1 + (2 : ℂ) • K := by
    have h4 : M ^ 4 = M ^ 2 * M ^ 2 := by rw [← pow_add]
    rw [h4, hsq2]
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, hK]
    module
  have e2 := hpow 2
  have e4 := hpow 4
  rw [hsq2] at e2
  rw [hsq4] at e4
  have h2 : Kᴴ * Q + Q * K + Kᴴ * Q * K = 0 := by
    simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_one] at e2
    have hexp : (1 + Kᴴ) * Q * (1 + K)
        = Q + (Kᴴ * Q + Q * K + Kᴴ * Q * K) := by
      simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one]
      abel
    rw [hexp] at e2
    have := congrArg (fun A => A - Q) e2
    simpa using this
  have h4 : (2 : ℂ) • (Kᴴ * Q + Q * K) + (4 : ℂ) • (Kᴴ * Q * K) = 0 := by
    simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_one,
      Matrix.conjTranspose_smul, star_ofNat] at e4
    have hexp : (1 + (2 : ℂ) • Kᴴ) * Q * (1 + (2 : ℂ) • K)
        = Q + ((2 : ℂ) • (Kᴴ * Q + Q * K) + (4 : ℂ) • (Kᴴ * Q * K)) := by
      simp only [Matrix.add_mul, Matrix.mul_add, Matrix.smul_mul, Matrix.mul_smul,
        Matrix.one_mul, Matrix.mul_one]
      module
    rw [hexp] at e4
    have := congrArg (fun A => A - Q) e4
    simpa using this
  have hzero : Kᴴ * Q * K = 0 := by
    have hcomb : (2 : ℂ) • (Kᴴ * Q + Q * K + Kᴴ * Q * K) -
        ((2 : ℂ) • (Kᴴ * Q + Q * K) + (4 : ℂ) • (Kᴴ * Q * K)) =
        (-2 : ℂ) • (Kᴴ * Q * K) := by module
    rw [h2, h4] at hcomb
    have hneg : (-2 : ℂ) • (Kᴴ * Q * K) = 0 := by simpa using hcomb.symm
    have h2ne : (-2 : ℂ) ≠ 0 := by norm_num
    exact (smul_eq_zero.1 hneg).resolve_left h2ne
  obtain ⟨i, j, hij⟩ : ∃ i j, K i j ≠ 0 := by
    by_contra hcon
    simp only [not_exists, ne_eq, not_not] at hcon
    exact hK0 (by ext i j; simpa using hcon i j)
  have hKx : K *ᵥ Pi.single j (1 : ℂ) ≠ 0 := by
    intro h
    have hi := congrFun h i
    rw [Matrix.mulVec_single] at hi
    simp at hi
    exact hij hi
  have hpos := hQ.2 _ hKx
  have hquad : ∀ (A B : Matrix n n ℂ) (x : n → ℂ),
      star (A *ᵥ x) ⬝ᵥ B *ᵥ (A *ᵥ x) = star x ⬝ᵥ (Aᴴ * B * A) *ᵥ x := by
    intro A B x
    simp only [Matrix.star_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul,
      Matrix.mul_assoc]
  rw [hquad K Q (Pi.single j (1 : ℂ)), hzero] at hpos
  simp at hpos

end GaloisForLFunctions.HTGeometry
