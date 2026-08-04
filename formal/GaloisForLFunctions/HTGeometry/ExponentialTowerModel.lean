import GaloisForLFunctions.HTGeometry.CascadeStateIndependence
import Mathlib.Algebra.MvPolynomial.Derivation

/-!
# The exponential tower and its polynomial model

The iterated exponential `exp ∘ ⋯ ∘ exp` is the explicit instance of a first-order entire cascade: its
states satisfy

`(Y_k)' = Y_1 · Y_2 ⋯ Y_k`,

so the derivation acts on the states by *polynomials* in the states.  The whole differential structure
therefore lives in a polynomial ring, where the coordinate derivations needed for an observability
determinant are the partial derivatives.

This file builds both sides of that correspondence: the derivative law for the analytic tower, and the
derivation on `MvPolynomial ℕ ℂ` prescribing the same law on the variables.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

/-! ## The analytic tower -/

/-- The `k`-fold exponential, as a state of the constant cascade. -/
noncomputable def expTower (k : ℕ) : ℂ → ℂ := entireCascade (fun _ => Complex.exp) k

@[simp] theorem expTower_zero (z : ℂ) : expTower 0 z = z := rfl

@[simp] theorem expTower_succ (k : ℕ) (z : ℂ) :
    expTower (k + 1) z = Complex.exp (expTower k z) := rfl

theorem expTower_succ_eq (k : ℕ) : expTower (k + 1) = fun z => Complex.exp (expTower k z) := rfl

theorem differentiable_expTower (k : ℕ) : Differentiable ℂ (expTower k) := by
  induction k with
  | zero => simp [expTower]
  | succ k ih =>
      rw [expTower_succ_eq]
      exact Complex.differentiable_exp.comp ih

/-- **The derivative law of the tower.**  Each state's derivative is the product of all the states
below and including it. -/
theorem deriv_expTower (k : ℕ) (z : ℂ) :
    deriv (expTower k) z = ∏ i ∈ Finset.Icc 1 k, expTower i z := by
  induction k with
  | zero => simp [expTower]
  | succ k ih =>
      have hd : HasDerivAt (expTower k) (deriv (expTower k) z) z :=
        ((differentiable_expTower k) z).hasDerivAt
      have hc : HasDerivAt (fun w => Complex.exp (expTower k w))
          (Complex.exp (expTower k z) * deriv (expTower k) z) z := hd.cexp
      have hval : deriv (expTower (k + 1)) z
          = Complex.exp (expTower k z) * deriv (expTower k) z := by
        rw [expTower_succ_eq]
        exact hc.deriv
      rw [hval, ih, Finset.prod_Icc_succ_top (by omega : 1 ≤ k + 1)]
      rw [expTower_succ]
      ring

/-! ## The polynomial model -/

/-- The product of the model variables from `1` to `k`; the empty product at `k = 0`. -/
noncomputable def towerMonomial (k : ℕ) : MvPolynomial ℕ ℂ :=
  ∏ i ∈ Finset.Icc 1 k, MvPolynomial.X i

@[simp] theorem towerMonomial_zero : towerMonomial 0 = 1 := by
  simp [towerMonomial]

theorem towerMonomial_succ (k : ℕ) :
    towerMonomial (k + 1) = towerMonomial k * MvPolynomial.X (k + 1) := by
  rw [towerMonomial, towerMonomial, Finset.prod_Icc_succ_top (by omega : 1 ≤ k + 1)]

/-- **The model derivation.**  It sends each variable to the product of the variables below it, which
is the tower's derivative law. -/
noncomputable def towerDerivation : Derivation ℂ (MvPolynomial ℕ ℂ) (MvPolynomial ℕ ℂ) :=
  MvPolynomial.mkDerivation ℂ towerMonomial

@[simp] theorem towerDerivation_X (k : ℕ) :
    towerDerivation (MvPolynomial.X k) = towerMonomial k :=
  MvPolynomial.mkDerivation_X ℂ towerMonomial k

/-- The model derivation is determined by the derivative law. -/
theorem towerDerivation_unique
    (D : Derivation ℂ (MvPolynomial ℕ ℂ) (MvPolynomial ℕ ℂ))
    (hD : ∀ k, D (MvPolynomial.X k) = towerMonomial k) :
    D = towerDerivation :=
  MvPolynomial.derivation_ext (fun k => by rw [hD k, towerDerivation_X])

end GaloisForLFunctions.HTGeometry
