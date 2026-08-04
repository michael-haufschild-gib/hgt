import GaloisForLFunctions.HTGeometry.ColumnPencilDeterminant
import GaloisForLFunctions.HTGeometry.PolynomialCascadeModel
import Mathlib.Algebra.MvPolynomial.PDeriv

/-!
# Jets of an affinely driven variable

If a model derivation acts on one variable by `δ X = A·X + B` with `A` and `B` free of that variable,
then every jet of `X` is again affine in it:

`δ^i X = A_i·X + B_i`,  `A_0 = 1`, `B_0 = 0`, `A_{i+1} = δA_i + A_i·A`, `B_{i+1} = δB_i + A_i·B`.

Consequently the variable's own partial derivative sees only `A_i`, and every other partial derivative
is affine in the variable.  The output-jet Jacobian is therefore a column pencil whose constant column
is `(A_i)` — the shape whose top coefficient the pencil calculus extracts.

This is the general form of the reduction the exponential cascades run: there `A` is a monomial and
`B = 0`, but nothing in the decomposition uses that.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

variable (δ : Derivation ℂ (MvPolynomial ℕ ℂ) (MvPolynomial ℕ ℂ))

/-- The homogeneous coefficient of the `i`-th jet of an affinely driven variable. -/
noncomputable def affineJetA (A : MvPolynomial ℕ ℂ) : ℕ → MvPolynomial ℕ ℂ
  | 0 => 1
  | (i + 1) => δ (affineJetA A i) + affineJetA A i * A

/-- The inhomogeneous coefficient of the `i`-th jet of an affinely driven variable. -/
noncomputable def affineJetB (A B : MvPolynomial ℕ ℂ) : ℕ → MvPolynomial ℕ ℂ
  | 0 => 0
  | (i + 1) => δ (affineJetB A B i) + affineJetA δ A i * B

@[simp] theorem affineJetA_zero (A : MvPolynomial ℕ ℂ) : affineJetA δ A 0 = 1 := rfl

@[simp] theorem affineJetB_zero (A B : MvPolynomial ℕ ℂ) : affineJetB δ A B 0 = 0 := rfl

theorem affineJetA_succ (A : MvPolynomial ℕ ℂ) (i : ℕ) :
    affineJetA δ A (i + 1) = δ (affineJetA δ A i) + affineJetA δ A i * A := rfl

theorem affineJetB_succ (A B : MvPolynomial ℕ ℂ) (i : ℕ) :
    affineJetB δ A B (i + 1) = δ (affineJetB δ A B i) + affineJetA δ A i * B := rfl

/-- **The jets of an affinely driven variable.** -/
theorem iterate_of_affine_law {N : ℕ} {A B : MvPolynomial ℕ ℂ}
    (hlaw : δ (MvPolynomial.X N) = A * MvPolynomial.X N + B) (i : ℕ) :
    ((δ : MvPolynomial ℕ ℂ → MvPolynomial ℕ ℂ)^[i]) (MvPolynomial.X N)
      = affineJetA δ A i * MvPolynomial.X N + affineJetB δ A B i := by
  induction i with
  | zero => simp
  | succ i ih =>
      rw [Function.iterate_succ_apply', ih, map_add, Derivation.leibniz, hlaw,
        affineJetA_succ, affineJetB_succ]
      simp only [smul_eq_mul]
      ring

/-! ## The Jacobian is a column pencil -/

variable {δ}

/-- The variable's own partial derivative sees only the homogeneous coefficient. -/
theorem pderiv_top_iterate_of_affine {N : ℕ} {A B : MvPolynomial ℕ ℂ}
    (hlaw : δ (MvPolynomial.X N) = A * MvPolynomial.X N + B)
    (hA : ∀ i, (MvPolynomial.pderiv N) (affineJetA δ A i) = 0)
    (hB : ∀ i, (MvPolynomial.pderiv N) (affineJetB δ A B i) = 0) (i : ℕ) :
    (MvPolynomial.pderiv N)
        (((δ : MvPolynomial ℕ ℂ → MvPolynomial ℕ ℂ)^[i]) (MvPolynomial.X N))
      = affineJetA δ A i := by
  rw [iterate_of_affine_law δ hlaw i, map_add, hB i, add_zero, Derivation.leibniz,
    MvPolynomial.pderiv_X_self, hA i]
  simp

/-- Every other partial derivative is affine in the variable. -/
theorem pderiv_low_iterate_of_affine {N j : ℕ} (hj : j ≠ N) {A B : MvPolynomial ℕ ℂ}
    (hlaw : δ (MvPolynomial.X N) = A * MvPolynomial.X N + B) (i : ℕ) :
    (MvPolynomial.pderiv j)
        (((δ : MvPolynomial ℕ ℂ → MvPolynomial ℕ ℂ)^[i]) (MvPolynomial.X N))
      = (MvPolynomial.pderiv j) (affineJetB δ A B i)
        + MvPolynomial.X N * (MvPolynomial.pderiv j) (affineJetA δ A i) := by
  rw [iterate_of_affine_law δ hlaw i, map_add, Derivation.leibniz,
    MvPolynomial.pderiv_X_of_ne (fun h => hj h.symm)]
  simp only [smul_eq_mul, mul_zero]
  ring

/-! ## Stability of the coefficients -/

/-- If a derivation-stable subalgebra contains the two coefficients, it contains every jet
coefficient. -/
theorem affineJetA_mem {S : Subalgebra ℂ (MvPolynomial ℕ ℂ)}
    (hS : ∀ P ∈ S, δ P ∈ S) {A : MvPolynomial ℕ ℂ} (hA : A ∈ S) (i : ℕ) :
    affineJetA δ A i ∈ S := by
  induction i with
  | zero => simp
  | succ i ih =>
      rw [affineJetA_succ]
      exact Subalgebra.add_mem _ (hS _ ih) (Subalgebra.mul_mem _ ih hA)

theorem affineJetB_mem {S : Subalgebra ℂ (MvPolynomial ℕ ℂ)}
    (hS : ∀ P ∈ S, δ P ∈ S) {A B : MvPolynomial ℕ ℂ} (hA : A ∈ S) (hB : B ∈ S) (i : ℕ) :
    affineJetB δ A B i ∈ S := by
  induction i with
  | zero => simp
  | succ i ih =>
      rw [affineJetB_succ]
      exact Subalgebra.add_mem _ (hS _ ih)
        (Subalgebra.mul_mem _ (affineJetA_mem hS hA i) hB)

end GaloisForLFunctions.HTGeometry
