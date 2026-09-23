import GaloisForLFunctions.RHTower.Sieve.SmoothAFEZetaSquareLeftExpansion

noncomputable section

open Complex MeasureTheory

namespace RHTower.Sieve

theorem smoothAFEZetaSquareMellinAt_sub_eq_zeta_sq_add_residue
    {x : ℝ} (hx : 0 < x) (tau : ℝ) :
    smoothAFEZetaSquareRightMellinAt tau x -
        smoothAFEZetaSquareLeftMellinAt tau x =
      riemannZeta (linePt tau) ^ 2 +
        confluentResidueCoeff
          (smoothAFEZetaSquarePoleNumerator (linePt tau) x)
          (1 - linePt tau) := by
  let R : ℂ := ∫ v : ℝ,
    smoothAFEZetaSquareMellinIntegrand (linePt tau) x
      ((1 : ℂ) + (v : ℂ) * I)
  let L : ℂ := ∫ v : ℝ,
    smoothAFEZetaSquareMellinIntegrand (linePt tau) x
      ((-1 : ℂ) + (v : ℂ) * I)
  let Z : ℂ := riemannZeta (linePt tau) ^ 2 +
    confluentResidueCoeff
      (smoothAFEZetaSquarePoleNumerator (linePt tau) x)
      (1 - linePt tau)
  have hcontour := smoothAFEZetaSquareMellin_infinite_contour_shift_line hx tau
  have hraw : R - L = (((2 * Real.pi : ℝ) : ℂ)) * Z := by
    apply mul_left_cancel₀ Complex.I_ne_zero
    rw [show I * (R - L) = I • R - I • L by
      simp only [smul_eq_mul]
      ring]
    rw [show I * ((((2 * Real.pi : ℝ) : ℂ)) * Z) =
        2 * Real.pi * I * Z by
      push_cast
      ring]
    simpa only [R, L, Z, Complex.ofReal_one, Complex.ofReal_neg,
      Complex.ofReal_ofNat] using hcontour
  have hscalar : (((1 / (2 * Real.pi) : ℝ) : ℂ) *
      (((2 * Real.pi : ℝ) : ℂ))) = 1 := by
    norm_cast
    field_simp [Real.pi_ne_zero]
  unfold smoothAFEZetaSquareRightMellinAt
  unfold smoothAFEZetaSquareLeftMellinAt
  rw [Complex.real_smul, Complex.real_smul]
  change (((1 / (2 * Real.pi) : ℝ) : ℂ) * R -
      ((1 / (2 * Real.pi) : ℝ) : ℂ) * L) = Z
  calc
    ((1 / (2 * Real.pi) : ℝ) : ℂ) * R -
          ((1 / (2 * Real.pi) : ℝ) : ℂ) * L =
        ((1 / (2 * Real.pi) : ℝ) : ℂ) * (R - L) := by ring
    _ = ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ((((2 * Real.pi : ℝ) : ℂ)) * Z) := by rw [hraw]
    _ = Z := by rw [← mul_assoc, hscalar, one_mul]

theorem smoothAFEZetaSquare_exact_afe_confluent
    {x : ℝ} (hx : 0 < x) (tau : ℝ) :
    riemannZeta (linePt tau) ^ 2 =
      (∑' n : ℕ, ((n + 1).divisors.card : ℂ) *
        (n + 1 : ℂ) ^ (-linePt tau) *
        smoothAFECutoff ((n + 1 : ℝ) / x)) +
      (∑' n : ℕ, zetaChi (linePt tau) ^ 2 *
        ((n + 1).divisors.card : ℂ) *
        (n + 1 : ℂ) ^ (linePt tau - 1) *
        smoothAFEZetaSquareDualWeight tau ((n + 1 : ℝ) * x)) -
      confluentResidueCoeff
        (smoothAFEZetaSquarePoleNumerator (linePt tau) x)
        (1 - linePt tau) := by
  have hnorm := smoothAFEZetaSquareMellinAt_sub_eq_zeta_sq_add_residue hx tau
  rw [smoothAFEZetaSquareRightMellinAt_eq_tsum_smoothAFECutoff hx tau,
    smoothAFEZetaSquareLeftMellinAt_eq_neg_tsum_dualWeight hx tau] at hnorm
  linear_combination -hnorm

/-- Exact Gaussian approximate functional equation for `ζ(1/2+iτ)^(2 : ℕ)`,
including the closed confluent-pole correction. -/
theorem smoothAFEZetaSquare_exact_afe
    {x : ℝ} (hx : 0 < x) (tau : ℝ) :
    riemannZeta (linePt tau) ^ 2 =
      (∑' n : ℕ, ((n + 1).divisors.card : ℂ) *
        (n + 1 : ℂ) ^ (-linePt tau) *
        smoothAFECutoff ((n + 1 : ℝ) / x)) +
      (∑' n : ℕ, zetaChi (linePt tau) ^ 2 *
        ((n + 1).divisors.card : ℂ) *
        (n + 1 : ℂ) ^ (linePt tau - 1) *
        smoothAFEZetaSquareDualWeight tau ((n + 1 : ℝ) * x)) -
      (((x : ℂ) ^ (1 - linePt tau) *
          Complex.exp ((1 - linePt tau) ^ 2) /
          (1 - linePt tau)) *
        ((Real.log x : ℂ) + 2 * (1 - linePt tau) +
          2 * deriv regularizedRiemannZeta 1 -
          (1 - linePt tau)⁻¹)) := by
  have hs : linePt tau ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    rw [linePt_re, Complex.one_re] at hre
    norm_num at hre
  rw [smoothAFEZetaSquare_exact_afe_confluent hx tau,
    confluentResidueCoeff_smoothAFEZetaSquarePoleNumerator
      (linePt tau) hx hs]

end RHTower.Sieve
