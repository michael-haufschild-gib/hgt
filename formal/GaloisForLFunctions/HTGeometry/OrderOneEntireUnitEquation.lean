import GaloisForLFunctions.HTGeometry.OrderOneEntireQuotient

/-!
# Finite-order units in a three-term entire identity

Differentiation eliminates one exponential unit. A simple zero of the
right-hand side certifies that the elimination denominator is nonzero.
The remaining unit inherits the order-one coefficient envelope.
-/

noncomputable section

open Complex Set

namespace GaloisForLFunctions.HTGeometry

/-- Finite-order zero-free factors in `g A + h B = C` inherit order-one
growth when `C` has a simple zero at which `B` does not vanish. -/
theorem orderOneEnvelope_of_finiteOrder_unit_equation
    {A B C g h : ℂ → ℂ}
    (hA : Differentiable ℂ A) (hB : Differentiable ℂ B)
    (hC : Differentiable ℂ C) (hg : Differentiable ℂ g) (hh : Differentiable ℂ h)
    (hAg : OrderOneEnvelope A) (hBg : OrderOneEnvelope B) (hCg : OrderOneEnvelope C)
    (hg0 : ∀ z, g z ≠ 0) (hh0 : ∀ z, h z ≠ 0)
    (hgf : FiniteOrderEnvelope g) (hhf : FiniteOrderEnvelope h)
    (heq : ∀ z, g z * A z + h z * B z = C z)
    {z₀ : ℂ} (hC0 : C z₀ = 0) (hC1 : deriv C z₀ ≠ 0) (hB0 : B z₀ ≠ 0) :
    OrderOneEnvelope g := by
  obtain ⟨P, hP⟩ := exists_polynomial_exp_of_ne_zero hg hg0 hgf
  obtain ⟨Q, hQ⟩ := exists_polynomial_exp_of_ne_zero hh hh0 hhf
  let U := fun z => P.derivative.eval z * A z + deriv A z
  let V := fun z => Q.derivative.eval z * B z + deriv B z
  let W := fun z => U z * B z - A z * V z
  let N := fun z => deriv C z * B z - C z * V z
  have hUd : Differentiable ℂ U := (P.derivative.differentiable.mul hA).add hA.deriv
  have hVd : Differentiable ℂ V := (Q.derivative.differentiable.mul hB).add hB.deriv
  have hWd : Differentiable ℂ W := (hUd.mul hB).sub (hA.mul hVd)
  have hNd : Differentiable ℂ N := (hC.deriv.mul hB).sub (hC.mul hVd)
  have hUg : OrderOneEnvelope U :=
    ((orderOneEnvelope_polynomial P.derivative).mul hAg).add (hAg.deriv hA)
  have hVg : OrderOneEnvelope V :=
    ((orderOneEnvelope_polynomial Q.derivative).mul hBg).add (hBg.deriv hB)
  have hWg : OrderOneEnvelope W := (hUg.mul hBg).sub (hAg.mul hVg)
  have hNg : OrderOneEnvelope N := ((hCg.deriv hC).mul hBg).sub (hCg.mul hVg)
  have hderiv (z : ℂ) : g z * U z + h z * V z = deriv C z := by
    have hd := (((P.hasDerivAt z).cexp.mul (hA z).hasDerivAt).add
      ((Q.hasDerivAt z).cexp.mul (hB z).hasDerivAt)).deriv
    have he : (fun w => Complex.exp (P.eval w)) * A +
        (fun w => Complex.exp (Q.eval w)) * B = C := by
      funext w
      change Complex.exp (P.eval w) * A w + Complex.exp (Q.eval w) * B w = C w
      rw [← hP w, ← hQ w]
      exact heq w
    rw [he, ← hP z, ← hQ z] at hd
    dsimp [U, V]
    linear_combination -hd
  have hfac (z : ℂ) : N z = g z * W z := by
    dsimp only [N, W]
    rw [← hderiv z, ← heq z]
    ring
  have hN0 : N z₀ ≠ 0 := by
    simpa only [N, hC0, zero_mul, sub_zero] using mul_ne_zero hC1 hB0
  have hW0 : W z₀ ≠ 0 := by
    intro hw
    apply hN0
    rw [hfac, hw, mul_zero]
  exact OrderOneEnvelope.of_entire_quotient
    (Complex.analyticOnNhd_univ_iff_differentiable.mpr hWd)
    (Complex.analyticOnNhd_univ_iff_differentiable.mpr hNd)
    (Complex.analyticOnNhd_univ_iff_differentiable.mpr hg)
    ⟨z₀, hW0⟩ ⟨z₀, hN0⟩ hg0 hfac hWg hNg

end GaloisForLFunctions.HTGeometry
