import GaloisForLFunctions.RHTower.ThetaCuspWignerPairSignLaw

/-!
# The theta Wigner pair kernel as a shifted second derivative

The exact center integral of an ordered theta-cusp source pair factors into a Dirichlet weight and
one universal kernel in the hyperbolic separation.  That kernel is, up to a positive constant,
`((σ-1)^2 - d^2/dy^2)` applied to the hyperbolic-secant power `(cosh y)^{-(σ+2)}`.

The spectral shift is exactly `(σ-1)^2`: the two competing terms of the radial Mellin weight
recombine into the second-order operator of the secant power, and the leftover constant
`(σ+2)^2 - (6σ+3)` is a perfect square.  It degenerates only at `σ = 1`, the abscissa of the zeta
pole.
-/

open Real MeasureTheory Set

namespace RHTower

noncomputable section

/-- Negative power of the hyperbolic cosine carrying the universal pair kernel. -/
def thetaCuspWignerCoshPower (σ y : ℝ) : ℝ := Real.cosh y ^ (-(σ + 2))

theorem hasDerivAt_thetaCuspWignerCoshPower (σ y : ℝ) :
    HasDerivAt (thetaCuspWignerCoshPower σ)
      (-(σ + 2) * (Real.cosh y ^ (-(σ + 3)) * Real.sinh y)) y := by
  have hc : (0 : ℝ) < Real.cosh y := Real.cosh_pos y
  have h := (Real.hasDerivAt_cosh y).rpow_const (p := -(σ + 2)) (Or.inl hc.ne')
  refine h.congr_deriv ?_
  rw [show -(σ + 2) - 1 = -(σ + 3) by ring]
  ring

theorem hasDerivAt_deriv_thetaCuspWignerCoshPower (σ y : ℝ) :
    HasDerivAt (fun z : ℝ => -(σ + 2) * (Real.cosh z ^ (-(σ + 3)) * Real.sinh z))
      ((σ + 2) ^ 2 * Real.cosh y ^ (-(σ + 2)) -
        (σ + 2) * (σ + 3) * Real.cosh y ^ (-(σ + 4))) y := by
  have hc : (0 : ℝ) < Real.cosh y := Real.cosh_pos y
  have hp := (Real.hasDerivAt_cosh y).rpow_const (p := -(σ + 3)) (Or.inl hc.ne')
  have h := ((hp.mul (Real.hasDerivAt_sinh y)).const_mul (-(σ + 2)))
  refine h.congr_deriv ?_
  have hsq : Real.sinh y ^ (2 : ℕ) = Real.cosh y ^ (2 : ℕ) - 1 := by
    have := Real.cosh_sq_sub_sinh_sq y
    linarith
  have e3 : Real.cosh y ^ (-(σ + 3) - 1) = Real.cosh y ^ (-(σ + 4)) := by
    rw [show -(σ + 3) - 1 = -(σ + 4) by ring]
  have e2 : Real.cosh y ^ (-(σ + 4)) * Real.cosh y ^ (2 : ℕ) =
      Real.cosh y ^ (-(σ + 2)) := by
    rw [← Real.rpow_natCast (Real.cosh y) 2, ← Real.rpow_add hc]
    norm_num
    ring_nf
  have e4 : Real.cosh y ^ (-(σ + 3)) * Real.cosh y = Real.cosh y ^ (-(σ + 2)) := by
    have h1 := Real.rpow_add hc (-(σ + 3)) 1
    rw [Real.rpow_one] at h1
    rw [← h1]; congr 1; ring
  rw [e3]
  linear_combination ((σ + 2) * (σ + 3) * Real.cosh y ^ (-(σ + 4))) * hsq +
    ((σ + 2) * (σ + 3)) * e2 + (-(σ + 2)) * e4

theorem deriv_thetaCuspWignerCoshPower (σ : ℝ) :
    deriv (thetaCuspWignerCoshPower σ) =
      fun z : ℝ => -(σ + 2) * (Real.cosh z ^ (-(σ + 3)) * Real.sinh z) :=
  funext fun y => (hasDerivAt_thetaCuspWignerCoshPower σ y).deriv

theorem deriv_deriv_thetaCuspWignerCoshPower (σ y : ℝ) :
    deriv (deriv (thetaCuspWignerCoshPower σ)) y =
      (σ + 2) ^ 2 * Real.cosh y ^ (-(σ + 2)) -
        (σ + 2) * (σ + 3) * Real.cosh y ^ (-(σ + 4)) := by
  rw [deriv_thetaCuspWignerCoshPower]
  exact (hasDerivAt_deriv_thetaCuspWignerCoshPower σ y).deriv

/-- **The universal pair kernel is a shifted second derivative.**  Up to the positive constant
`(2π)^{-σ} Γ(σ+2)/2`, the universal theta Wigner pair kernel is `((σ-1)^2 - d^2/dy^2)` applied to
the hyperbolic-secant power `(cosh y)^{-(σ+2)}`.  The shift is exactly `(σ-1)^2`, which vanishes
only at `σ = 1`. -/
theorem thetaCuspWignerPairKernel_eq_shifted_second_deriv (σ y : ℝ) :
    thetaCuspWignerPairKernel σ y =
      (2 * Real.pi) ^ (-σ) * Real.Gamma (σ + 2) / 2 *
        ((σ - 1) ^ 2 * thetaCuspWignerCoshPower σ y -
          deriv (deriv (thetaCuspWignerCoshPower σ)) y) := by
  have hc : (0 : ℝ) < Real.cosh y := Real.cosh_pos y
  have hinv : (1 / Real.cosh y) ^ (σ + 2) = Real.cosh y ^ (-(σ + 2)) := by
    rw [one_div, Real.inv_rpow hc.le, ← Real.rpow_neg hc.le]
  have hC2 : Real.cosh y ^ (-(σ + 4)) =
      Real.cosh y ^ (-(σ + 2)) / Real.cosh y ^ (2 : ℕ) := by
    rw [← Real.rpow_natCast (Real.cosh y) 2, ← Real.rpow_sub hc]
    congr 1
    push_cast
    ring
  rw [thetaCuspWignerPairKernel, thetaCuspWignerRadialQ, thetaCuspWignerCoshPower,
    deriv_deriv_thetaCuspWignerCoshPower, hinv, hC2]
  field_simp
  ring

end

end RHTower
