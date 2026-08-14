import GaloisForLFunctions.HTGeometry.FormalEulerOperator
import GaloisForLFunctions.HTGeometry.MvPolynomialFirstOrderTaylor

/-!
# Linearizing an algebraic differential equation along a formal series

Written in the Euler basis, an algebraic differential equation of order `m` is a polynomial in the
jets `θ^j F`.  Perturbing the argument decomposes it into three pieces:

```text
P(jets (Y + H)) = P(jets Y) + L_Y(H) + defect ,     L_Y = ∑_j (∂_j P)(jets Y) θ^j .
```

The middle term is a linear differential operator whose coefficients are the partial derivatives of
`P` evaluated along `Y`; the defect is quadratic in the perturbation.

When `Y` is a truncation of a formal solution the coefficients of `L_Y` are polynomials in the
coefficients of the equation, hence convergent, and the perturbation is divisible by a high power of
`t`, which makes the defect divisible by its square.  That is the reduction of the nonlinear
equation to the linear theory.
-/

open PowerSeries MvPolynomial

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The `θ`-jet vector of a formal series. -/
def eulerJetVector {m : ℕ} (F : PowerSeries ℂ) : Fin (m + 1) → PowerSeries ℂ :=
  fun j => eulerOp^[(j : ℕ)] F

/-- The Euler operator is additive. -/
theorem eulerOp_add (F G : PowerSeries ℂ) : eulerOp (F + G) = eulerOp F + eulerOp G := by
  ext n
  simp only [coeff_eulerOp, map_add]
  ring

theorem eulerOp_iterate_add (j : ℕ) (F G : PowerSeries ℂ) :
    eulerOp^[j] (F + G) = eulerOp^[j] F + eulerOp^[j] G := by
  induction j generalizing F G with
  | zero => simp
  | succ j ih =>
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply, Function.iterate_succ_apply,
        eulerOp_add, ih]

theorem eulerJetVector_add {m : ℕ} (Y H : PowerSeries ℂ) :
    eulerJetVector (m := m) (Y + H) = eulerJetVector (m := m) Y + eulerJetVector (m := m) H := by
  funext j
  exact eulerOp_iterate_add (j : ℕ) Y H

/-- `F` is a formal solution of the algebraic differential equation `P = 0` written in the Euler
basis. -/
def IsFormalEulerADESolution {m : ℕ} (P : MvPolynomial (Fin (m + 1)) (PowerSeries ℂ))
    (F : PowerSeries ℂ) : Prop :=
  MvPolynomial.aeval (eulerJetVector (m := m) F) P = 0

/-- The coefficients of the linearization of `P` along `Y`. -/
def linearizationCoeff {m : ℕ} (P : MvPolynomial (Fin (m + 1)) (PowerSeries ℂ))
    (Y : PowerSeries ℂ) (j : Fin (m + 1)) : PowerSeries ℂ :=
  MvPolynomial.aeval (eulerJetVector (m := m) Y) (MvPolynomial.pderiv j P)

/-- **The linearization decomposition.**  Perturbing the argument of a differential polynomial
produces its value, the linearized operator applied to the perturbation, and a defect. -/
theorem aeval_eulerJetVector_add {m : ℕ} (P : MvPolynomial (Fin (m + 1)) (PowerSeries ℂ))
    (Y H : PowerSeries ℂ) :
    MvPolynomial.aeval (eulerJetVector (m := m) (Y + H)) P
      = MvPolynomial.aeval (eulerJetVector (m := m) Y) P
        + eulerLinearOp (linearizationCoeff P Y) H
        + taylorDefect (eulerJetVector (m := m) Y) (eulerJetVector (m := m) H) P := by
  rw [eulerJetVector_add,
    aeval_add_eq_add_sum_pderiv_mod_sq (eulerJetVector (m := m) Y) (eulerJetVector (m := m) H) P]
  congr 1

/-! ### The perturbation is divisible by a power of the variable -/

/-- The Euler operator preserves divisibility by a power of the variable. -/
theorem X_pow_dvd_eulerOp {k : ℕ} {H : PowerSeries ℂ} (h : (PowerSeries.X : PowerSeries ℂ) ^ k ∣ H) :
    (PowerSeries.X : PowerSeries ℂ) ^ k ∣ eulerOp H := by
  rw [PowerSeries.X_pow_dvd_iff] at h ⊢
  intro n hn
  rw [coeff_eulerOp, h n hn, mul_zero]

theorem X_pow_dvd_eulerOp_iterate {k : ℕ} {H : PowerSeries ℂ} (j : ℕ)
    (h : (PowerSeries.X : PowerSeries ℂ) ^ k ∣ H) :
    (PowerSeries.X : PowerSeries ℂ) ^ k ∣ eulerOp^[j] H := by
  induction j generalizing H with
  | zero => simpa using h
  | succ j ih =>
      rw [Function.iterate_succ_apply]
      exact ih (X_pow_dvd_eulerOp h)

/-- **The defect of a perturbation divisible by `t^k` is divisible by `t^{2k}`.** -/
theorem taylorDefect_mem_sq_X_pow {m k : ℕ} (P : MvPolynomial (Fin (m + 1)) (PowerSeries ℂ))
    (Y H : PowerSeries ℂ) (hH : (PowerSeries.X : PowerSeries ℂ) ^ k ∣ H) :
    taylorDefect (eulerJetVector (m := m) Y) (eulerJetVector (m := m) H) P
      ∈ (Ideal.span {(PowerSeries.X : PowerSeries ℂ) ^ k}) ^ 2 := by
  refine taylorDefect_mem_sq _ _ _ (fun j => ?_) P
  rw [Ideal.mem_span_singleton]
  exact X_pow_dvd_eulerOp_iterate (j : ℕ) hH

/-- **The nonlinear equation, rewritten around a base point.**  If `Y + H` is a formal solution then
the linearized operator applied to the perturbation is the value at the base point plus the defect,
both of which are controlled: the value is what the base point fails by, and the defect is quadratic
in the perturbation. -/
theorem eulerLinearOp_linearization_eq {m : ℕ} (P : MvPolynomial (Fin (m + 1)) (PowerSeries ℂ))
    (Y H : PowerSeries ℂ) (hsol : IsFormalEulerADESolution P (Y + H)) :
    eulerLinearOp (linearizationCoeff P Y) H
      = -(MvPolynomial.aeval (eulerJetVector (m := m) Y) P)
        - taylorDefect (eulerJetVector (m := m) Y) (eulerJetVector (m := m) H) P := by
  have h := aeval_eulerJetVector_add P Y H
  rw [IsFormalEulerADESolution] at hsol
  rw [hsol] at h
  linear_combination -h

end

end GaloisForLFunctions.HTGeometry
