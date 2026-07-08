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

/-- **AFE detection at a ζ-zero.**  At a zero `s` of ζ on the strip, the Euler–Maclaurin identity forces
`∑_{n≤N} n^{-s} = −(N^{1-s}/(s-1) − s·emTail)`, so for any mollifier value `M(s)` the detection value
`(∑_{n≤N} n^{-s})·M(s) − 1` has norm

  ‖D_N(s)·M(s) − 1‖ ≥ 1 − ‖N^{1-s}/(s-1) − s·emTail‖·‖M(s)‖  ≥ ½

whenever the Euler–Maclaurin correction times the mollifier is `≤ ½`.  Thus every ζ-zero is a *large
value* of the detection polynomial `D_N·M − 1` — the input the large-values inequality counts. -/
theorem afe_detection {N : ℕ} (hN : 1 ≤ N) {s : ℂ} (hσ : 0 < s.re) (hs1 : s ≠ 1)
    (hz : riemannZeta s = 0) (M : ℂ)
    (hsmall : ‖emPole N s - s * emTail N s‖ * ‖M‖ ≤ 1 / 2) :
    (1 : ℝ) / 2 ≤ ‖dirichletPoly N s * M - 1‖ := by
  have hdp : dirichletPoly N s = -(emPole N s - s * emTail N s) := by
    have h := zeta_eq_emCarrier_sub hN hσ hs1
    rw [hz, emCarrier] at h
    linear_combination -h
  set x : ℂ := emPole N s - s * emTail N s with hx
  rw [hdp]
  calc (1 : ℝ) / 2 ≤ 1 - ‖x‖ * ‖M‖ := by linarith [hsmall]
    _ = ‖(1 : ℂ)‖ - ‖-(x * M)‖ := by rw [norm_neg, norm_mul, norm_one]
    _ ≤ ‖(1 : ℂ) - (-(x * M))‖ := norm_sub_norm_le _ _
    _ = ‖-x * M - 1‖ := by
        rw [show (1 : ℂ) - (-(x * M)) = -(-x * M - 1) from by ring, norm_neg]

/-- The complex Möbius mollifier `M_y(s) = ∑_{m≤y} μ(m) m^{-s}`. -/
noncomputable def mollifierCx (y : ℕ) (s : ℂ) : ℂ :=
  ∑ m ∈ Finset.Icc 1 y, (ArithmeticFunction.moebius m : ℂ) * (m : ℂ) ^ (-s)

/-- **Mollifier norm bound.**  `‖M_y(s)‖ ≤ ∑_{m≤y} m^{-Re s}` — from `|μ(m)| ≤ 1` and
`‖m^{-s}‖ = m^{-Re s}`.  This bounds the mollifier value at a ζ-zero, the input `afe_detection`
needs to conclude `‖E(ρ)‖ ≥ ½`. -/
theorem norm_mollifierCx_le (y : ℕ) (s : ℂ) :
    ‖mollifierCx y s‖ ≤ ∑ m ∈ Finset.Icc 1 y, (m : ℝ) ^ (-s.re) := by
  refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun m hm => ?_)
  have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
  rw [norm_mul, Complex.norm_natCast_cpow_of_pos (by omega), Complex.neg_re]
  have hmu : ‖(ArithmeticFunction.moebius m : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_intCast]
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one
  calc ‖(ArithmeticFunction.moebius m : ℂ)‖ * (m : ℝ) ^ (-s.re)
      ≤ 1 * (m : ℝ) ^ (-s.re) := by
        apply mul_le_mul_of_nonneg_right hmu (Real.rpow_nonneg (by positivity) _)
    _ = (m : ℝ) ^ (-s.re) := one_mul _

end RHTower
