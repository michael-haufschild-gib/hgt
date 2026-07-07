/-
The approximate-functional-equation transfer: bounding ζ on the strip by its Dirichlet polynomial.

The project's Euler–Maclaurin AFE (`EMCarrier.zeta_sub_emCarrier_norm_le`) is unconditional:

  ‖ζ(s) − (∑_{n≤N} n^{-s} + N^{1-s}/(s-1))‖ ≤ ‖s‖ · N^{-Re s} / Re s.

Reading the carrier as `dirichletPoly N s + emPole N s` and adding the two triangle inequalities gives
the pointwise transfer `zeta_norm_le_afe`:

  ‖ζ(s)‖ ≤ ‖∑_{n≤N} n^{-s}‖ + ‖N^{1-s}/(s-1)‖ + ‖s‖ · N^{-Re s} / Re s.

This is the bridge that carries the Dirichlet-polynomial mean-value bounds (`FourthMoment`,
`FourthMomentDiagonal`) up to ζ itself: choosing `N` with `Re s > 1/2` makes the pole term
`N^{1-s}/(s-1)` and the remainder both controllable, so a fourth-moment bound for `∑_{n≤N} n^{-s}`
transfers to `∫ |ζ|⁴`.  The `dirichletPoly` term is exactly the object whose fourth moment
`FourthMomentDiagonal.fourthMoment_bounded` controls (its square has divisor-function coefficients).
-/
import GaloisForLFunctions.RHTower.EMCarrier

open Complex

namespace RHTower

/-- **AFE transfer.**  On the strip `0 < Re s`, `s ≠ 1`, ζ is bounded by its length-`N` Dirichlet
polynomial plus the Euler–Maclaurin pole and remainder:
`‖ζ(s)‖ ≤ ‖dirichletPoly N s‖ + ‖emPole N s‖ + ‖s‖·N^{-Re s}/Re s`.  Direct from the unconditional
Euler–Maclaurin bound `zeta_sub_emCarrier_norm_le` and the triangle inequality. -/
theorem zeta_norm_le_afe {N : ℕ} (hN : 1 ≤ N) {s : ℂ} (hσ : 0 < s.re) (hs1 : s ≠ 1) :
    ‖riemannZeta s‖
      ≤ ‖dirichletPoly N s‖ + ‖emPole N s‖ + ‖s‖ * (N : ℝ) ^ (-s.re) / s.re := by
  have hAFE := zeta_sub_emCarrier_norm_le hN hσ hs1
  have hcar : ‖emCarrier N s‖ ≤ ‖dirichletPoly N s‖ + ‖emPole N s‖ := by
    rw [emCarrier]; exact norm_add_le _ _
  calc ‖riemannZeta s‖
      = ‖(riemannZeta s - emCarrier N s) + emCarrier N s‖ := by rw [sub_add_cancel]
    _ ≤ ‖riemannZeta s - emCarrier N s‖ + ‖emCarrier N s‖ := norm_add_le _ _
    _ ≤ ‖s‖ * (N : ℝ) ^ (-s.re) / s.re + (‖dirichletPoly N s‖ + ‖emPole N s‖) := by
        linarith [hAFE, hcar]
    _ = ‖dirichletPoly N s‖ + ‖emPole N s‖ + ‖s‖ * (N : ℝ) ^ (-s.re) / s.re := by ring

end RHTower
