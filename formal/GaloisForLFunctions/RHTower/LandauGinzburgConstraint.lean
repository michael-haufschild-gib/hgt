import Mathlib

/-!
# Lagrange-multiplier Landau--Ginzburg constraint

For a one-variable polynomial `F`, consider the two-field potential

`W_F(s,u) = u F(s)`.

The multiplier coordinate turns the zero equation for `F` into one of the critical equations for
`W_F`.  Above a simple zero `rho`, the other critical equation forces `u = 0`, and the Hessian has
determinant `-(F'(rho))^(2 : ℕ)`.  Thus every simple zero becomes a nondegenerate critical point, while
all such critical points have the same critical value zero.

The results below isolate the algebraic core of this constraint construction.  They do not assert
anything about the location of the zeros of `F`.
-/

noncomputable section

namespace RHTower

open Polynomial

/-- The two-field Lagrange-multiplier potential `W_F(s,u) = u F(s)`. -/
def lagrangePotential (F : Polynomial ℂ) (s u : ℂ) : ℂ :=
  u * F.eval s

/-- The ordered pair `(partial_s W_F, partial_u W_F)`. -/
def lagrangeGradient (F : Polynomial ℂ) (s u : ℂ) : ℂ × ℂ :=
  (u * F.derivative.eval s, F.eval s)

/-- The critical equations are exactly the multiplier equation and the original zero equation. -/
theorem lagrangeGradient_eq_zero_iff (F : Polynomial ℂ) (s u : ℂ) :
    lagrangeGradient F s u = (0, 0) ↔
      u * F.derivative.eval s = 0 ∧ F.eval s = 0 := by
  simp [lagrangeGradient]

/-- If `F'` is nonzero at `s`, the critical locus over `s` is exactly `(F(s)=0, u=0)`. -/
theorem lagrangeGradient_eq_zero_iff_of_derivative_ne
    (F : Polynomial ℂ) (s u : ℂ) (hsimple : F.derivative.eval s ≠ 0) :
    lagrangeGradient F s u = (0, 0) ↔ F.eval s = 0 ∧ u = 0 := by
  rw [lagrangeGradient_eq_zero_iff]
  simp [hsimple, and_comm]

/-- Above a simple zero of `F`, the multiplier coordinate of a critical point is forced to vanish. -/
theorem lagrangeGradient_at_simpleRoot_eq_zero_iff
    (F : Polynomial ℂ) (rho u : ℂ)
    (hroot : F.eval rho = 0) (hsimple : F.derivative.eval rho ≠ 0) :
    lagrangeGradient F rho u = (0, 0) ↔ u = 0 := by
  rw [lagrangeGradient_eq_zero_iff]
  simp [hroot, hsimple]

/-- Every critical point of the Lagrange-multiplier potential has critical value zero. -/
theorem lagrangePotential_eq_zero_of_gradient_eq_zero
    (F : Polynomial ℂ) (s u : ℂ)
    (hcrit : lagrangeGradient F s u = (0, 0)) :
    lagrangePotential F s u = 0 := by
  have hroot := (lagrangeGradient_eq_zero_iff F s u).mp hcrit |>.2
  simp [lagrangePotential, hroot]

/-- Any two critical points of `W_F` have the same critical value. -/
theorem lagrangePotential_eq_of_gradient_eq_zero
    (F : Polynomial ℂ) (s₁ u₁ s₂ u₂ : ℂ)
    (hcrit₁ : lagrangeGradient F s₁ u₁ = (0, 0))
    (hcrit₂ : lagrangeGradient F s₂ u₂ = (0, 0)) :
    lagrangePotential F s₁ u₁ = lagrangePotential F s₂ u₂ := by
  rw [lagrangePotential_eq_zero_of_gradient_eq_zero F s₁ u₁ hcrit₁,
    lagrangePotential_eq_zero_of_gradient_eq_zero F s₂ u₂ hcrit₂]

/-- The determinant of the Hessian of `W_F` in coordinates `(s,u)`. -/
def lagrangeHessianDet (F : Polynomial ℂ) (s u : ℂ) : ℂ :=
  (u * F.derivative.derivative.eval s) * 0 -
    F.derivative.eval s * F.derivative.eval s

/-- The Hessian determinant is the negative square of the derivative of `F`. -/
theorem lagrangeHessianDet_eq (F : Polynomial ℂ) (s u : ℂ) :
    lagrangeHessianDet F s u = -(F.derivative.eval s) ^ (2 : ℕ) := by
  simp [lagrangeHessianDet, pow_two]

/-- A simple zero of `F` gives a nondegenerate critical point of `W_F`. -/
theorem lagrangeHessianDet_ne_zero_at_simpleRoot
    (F : Polynomial ℂ) (rho u : ℂ)
    (hsimple : F.derivative.eval rho ≠ 0) :
    lagrangeHessianDet F rho u ≠ 0 := by
  rw [lagrangeHessianDet_eq]
  exact neg_ne_zero.mpr (pow_ne_zero 2 hsimple)

/-- If `F = (X - rho) G`, the multiplier potential is exactly the node `x*y` in the
coordinates `x = s - rho` and `y = u G(s)`. -/
theorem lagrangePotential_linearFactor_eq_node
    (G : Polynomial ℂ) (rho s u : ℂ) :
    lagrangePotential ((X - C rho) * G) s u =
      (s - rho) * (u * G.eval s) := by
  simp [lagrangePotential]
  ring

/-- The fiber of the multiplier potential over a value `t`. -/
def lagrangeFiber (F : Polynomial ℂ) (t : ℂ) :=
  {p : ℂ × ℂ // lagrangePotential F p.1 p.2 = t}

/-- The complement of the zero set of `F`. -/
def polynomialZeroComplement (F : Polynomial ℂ) :=
  {s : ℂ // F.eval s ≠ 0}

/-- Every nonzero fiber of `W_F` is canonically the complement of the zero set of `F`. -/
def lagrangeFiberEquivZeroComplement
    (F : Polynomial ℂ) (t : ℂ) (ht : t ≠ 0) :
    lagrangeFiber F t ≃ polynomialZeroComplement F where
  toFun p := by
    refine ⟨p.1.1, ?_⟩
    intro hzero
    apply ht
    rw [← p.2]
    simp [lagrangePotential, hzero]
  invFun s := by
    refine ⟨(s.1, t / F.eval s.1), ?_⟩
    simp [lagrangePotential, s.2]
  left_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · dsimp
      have hF : F.eval p.1.1 ≠ 0 := by
        intro hzero
        apply ht
        rw [← p.2]
        simp [lagrangePotential, hzero]
      exact (div_eq_iff hF).2 p.2.symm
  right_inv s := by
    apply Subtype.ext
    rfl

end RHTower
