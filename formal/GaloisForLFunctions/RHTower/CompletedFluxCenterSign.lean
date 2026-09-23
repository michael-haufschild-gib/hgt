import GaloisForLFunctions.RHTower.CompletedFluxLaguerreReader
import GaloisForLFunctions.RHTower.PrimeArchThetaFirstMoment

/-!
# The quadratic completed-flux coefficient is negative at the center

The theta-cusp representation proves unconditionally that `Xi(0) > 0`, `Xi'(0) = 0`, and
`Xi''(0) < 0`.  The exact completed-flux Laguerre reader therefore gives a strictly negative
quadratic coefficient at the functional-equation fixed point.  Thus the center cannot be the
positive source witness needed to refute RH through the quadratic completed-flux port.
-/

open Complex

namespace RHTower

noncomputable section

/-- The quadratic coefficient of the completed-flux germ is strictly negative at the center. -/
theorem completedFluxTaylorCoeff_two_center_re_neg :
    (completedFluxTaylorCoeff (linePt 0) 2).re < 0 := by
  have hreaderC :=
    xi_laguerre_margin_eq_neg_sq_mul_completedFluxTaylorCoeff_two
      0 Xi_zero_pos.ne'
  have hscale : -((Xi 0 : ℂ) ^ (2 : ℕ)) = ((-(Xi 0) ^ (2 : ℕ) : ℝ) : ℂ) := by
    push_cast
    ring
  rw [hscale] at hreaderC
  have hreader := congrArg Complex.re hreaderC
  simp only [Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, zero_mul,
    sub_zero] at hreader
  rw [Xi_deriv_zero] at hreader
  nlinarith [sq_pos_of_ne_zero Xi_zero_pos.ne',
    mul_neg_of_pos_of_neg Xi_zero_pos Xi_secondDeriv_zero_neg]

/-- The fixed continued-prime plus archimedean quadratic coefficient is likewise negative at the
center. -/
theorem prime_archimedean_second_coeff_center_re_neg :
    (infinitePrimeFluxTaylorCoeff (linePt 0) 2 +
      archimedeanBoundaryFluxTaylorCoeff (linePt 0) 2).re < 0 := by
  rw [← completedFluxTaylorCoeff_two_line_eq_prime_add_archimedean]
  exact completedFluxTaylorCoeff_two_center_re_neg

end

end RHTower
