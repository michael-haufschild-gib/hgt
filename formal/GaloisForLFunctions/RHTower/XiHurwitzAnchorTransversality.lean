import GaloisForLFunctions.Hurwitz.AnchorTransversality
import GaloisForLFunctions.RHTower.RiemannTower

/-!
# Every Xi zero is a transverse Hurwitz anchor zero

At `a = 1`, the canonical continued Hurwitz function equals Riemann zeta.  Hence every Xi zero in
the positive-real strip is a zero of its corresponding frozen-exponent Hurwitz function.  The
anchor derivative theorem places the shifted zeta value in `Re > 1`, where it is nonzero, so this
common shift zero has analytic order exactly one irrespective of the Xi multiplicity.

This is an unconditional source/value relation.  It does not locate Xi zeros and is not an RH
criterion.
-/

open Complex HurwitzZetaContinuation

namespace RHTower

/-- Every positive-real Xi zero gives a zero of its frozen-exponent continued Hurwitz function at
the canonical shift. -/
theorem continuedHzeta_xiZero_at_one {rho : ℂ} (hrho : 0 < rho.re)
    (hrho1 : rho ≠ 1) (hzero : xi rho = 0) :
    continuedHzeta rho 1 = 0 := by
  rw [continuedHzeta_at_one]
  exact (xi_eq_zero_iff hrho hrho1).mp hzero

/-- The shift derivative at the canonical anchor is nonzero for every positive-real exponent. -/
theorem continuedHzeta_xiZero_deriv_at_one_ne_zero {rho : ℂ} (hrho : 0 < rho.re) :
    deriv (continuedHzeta rho) 1 ≠ 0 := by
  rw [(continuedHzeta_hasDerivAt_one hrho).deriv]
  have hrho0 : rho ≠ 0 := by
    intro h
    rw [h] at hrho
    simp at hrho
  exact mul_ne_zero (neg_ne_zero.mpr hrho0)
    (riemannZeta_ne_zero_of_one_lt_re (by
      rw [Complex.add_re, Complex.one_re]
      linarith))

/-- **Unconditional transverse-anchor law.**  The frozen-exponent Hurwitz function attached to
any positive-real Xi zero has a simple zero at `a = 1`, even when the Xi zero itself is multiple. -/
theorem analyticOrderAt_continuedHzeta_xiZero_at_one {rho : ℂ} (hrho : 0 < rho.re)
    (hrho1 : rho ≠ 1) (hzero : xi rho = 0) :
    analyticOrderAt (continuedHzeta rho) 1 = 1 := by
  have han : AnalyticAt ℂ (continuedHzeta rho) 1 :=
    continuedHzeta_analyticAt_one hrho
  exact han.analyticOrderAt_eq_one_of_zero_deriv_ne_zero
    (continuedHzeta_xiZero_at_one hrho hrho1 hzero)
    (continuedHzeta_xiZero_deriv_at_one_ne_zero hrho)

end RHTower
