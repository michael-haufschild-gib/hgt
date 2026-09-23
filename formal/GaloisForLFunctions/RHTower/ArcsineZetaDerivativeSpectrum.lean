import GaloisForLFunctions.HTGeometry.ArcsineEndpointSeries
import GaloisForLFunctions.RHTower.ArcsineZetaTransform
import GaloisForLFunctions.RHTower.ConstrainedProlateExteriorWeil

/-!
# The prolate arcsine charge as an even-zeta-derivative spectrum

This module closes the exact-value, positivity, absolute-convergence, and sharp-bound claims for
the prolate diagonal charge.  It upgrades the Tonelli transform in `ArcsineZetaTransform` by
identifying every inner logarithmic Dirichlet series with `-ζ'(2j+2)`.
-/

namespace GaloisForLFunctions

open Complex

theorem log_div_even_pow_le_sq (j k : ℕ) :
    Real.log k / (k : ℝ) ^ (2 * j + 2) ≤ Real.log k / (k : ℝ) ^ (2 : ℕ) := by
  rcases k.eq_zero_or_pos with rfl | hk
  · simp
  · have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
    have hlog : 0 ≤ Real.log k := Real.log_nonneg hk1
    have hpow : (k : ℝ) ^ (2 : ℕ) ≤ (k : ℝ) ^ (2 * j + 2) :=
      pow_le_pow_right₀ hk1 (by omega)
    exact div_le_div_of_nonneg_left hlog (pow_pos (by positivity) 2) hpow

theorem summable_log_div_even_pow (j : ℕ) :
    Summable (fun k : ℕ => Real.log k / (k : ℝ) ^ (2 * j + 2)) := by
  exact Summable.of_nonneg_of_le
    (fun k => div_nonneg (log_natCast_nonneg k) (by positivity))
    (log_div_even_pow_le_sq j) summable_log_div_sq

theorem tsum_log_div_even_pow_pos (j : ℕ) :
    0 < ∑' k : ℕ, Real.log k / (k : ℝ) ^ (2 * j + 2) := by
  refine (summable_log_div_even_pow j).tsum_pos
    (fun k => div_nonneg (log_natCast_nonneg k) (by positivity)) 2 ?_
  exact div_pos (Real.log_pos (by norm_num)) (by positivity)

/-- The logarithmic Dirichlet series at every even integer is exactly the negative zeta
derivative there. -/
theorem zeta_deriv_even_eq_neg_log_tsum (j : ℕ) :
    deriv riemannZeta (((2 * j + 2 : ℕ) : ℝ) : ℂ) =
      -((∑' k : ℕ, Real.log k / (k : ℝ) ^ (2 * j + 2) : ℝ) : ℂ) := by
  have hs : 1 < ((((2 * j + 2 : ℕ) : ℝ) : ℂ).re) := by
    simp only [ofReal_re]
    exact_mod_cast (show 1 < 2 * j + 2 by omega)
  rw [zeta_deriv_eq_neg_tsum hs]
  congr 1
  rw [Complex.ofReal_tsum]
  apply tsum_congr
  intro k
  rw [ofReal_div, ofReal_pow, ofReal_natCast]
  congr 1
  change (k : ℂ) ^ ((2 * j + 2 : ℕ) : ℂ) = (k : ℂ) ^ (2 * j + 2)
  exact Complex.cpow_natCast (k : ℂ) (2 * j + 2)

theorem zeta_deriv_even_re_neg (j : ℕ) :
    (deriv riemannZeta (((2 * j + 2 : ℕ) : ℝ) : ℂ)).re < 0 := by
  rw [zeta_deriv_even_eq_neg_log_tsum]
  simpa using (neg_neg_of_pos (tsum_log_div_even_pow_pos j))

theorem zeta_deriv_even_re_eq_neg_log_tsum (j : ℕ) :
    (deriv riemannZeta (((2 * j + 2 : ℕ) : ℝ) : ℂ)).re =
      -(∑' k : ℕ, Real.log k / (k : ℝ) ^ (2 * j + 2)) := by
  have h := congrArg Complex.re (zeta_deriv_even_eq_neg_log_tsum j)
  simpa using h

theorem summable_arcsin_even_log_spectrum :
    Summable (fun j : ℕ =>
      arcsinCoeff j * ∑' k : ℕ, Real.log k / (k : ℝ) ^ (2 * j + 2)) := by
  apply Summable.of_nonneg_of_le
    (fun j => mul_nonneg (arcsinCoeff_nonneg j)
      (le_of_lt (tsum_log_div_even_pow_pos j)))
    (fun j => ?_)
    (summable_arcsinCoeff.mul_right (∑' k : ℕ, Real.log k / (k : ℝ) ^ (2 : ℕ)))
  apply mul_le_mul_of_nonneg_left _ (arcsinCoeff_nonneg j)
  exact Summable.tsum_le_tsum (log_div_even_pow_le_sq j)
    (summable_log_div_even_pow j) summable_log_div_sq

/-- **Arcsine/zeta-derivative transform.** -/
theorem arcsine_zeta_derivative_transform :
    ((∑' k : ℕ, Real.log k / k * Real.arcsin (1 / (k : ℝ)) : ℝ) : ℂ) =
      -(∑' j : ℕ, (arcsinCoeff j : ℂ) *
        deriv riemannZeta (((2 * j + 2 : ℕ) : ℝ) : ℂ)) := by
  rw [← tsum_neg]
  have h := congrArg ((↑) : ℝ → ℂ) arcsine_dirichlet_transform
  rw [Complex.ofReal_tsum, Complex.ofReal_tsum] at h
  rw [Complex.ofReal_tsum, h]
  apply tsum_congr
  intro j
  rw [ofReal_mul, zeta_deriv_even_eq_neg_log_tsum]
  push_cast
  ring

/-- Absolute convergence of the even-zeta-derivative spectrum. -/
theorem summable_norm_arcsin_even_zeta_derivative_spectrum :
    Summable (fun j : ℕ => ‖(arcsinCoeff j : ℂ) *
      deriv riemannZeta (((2 * j + 2 : ℕ) : ℝ) : ℂ)‖) := by
  apply summable_arcsin_even_log_spectrum.congr
  intro j
  rw [zeta_deriv_even_eq_neg_log_tsum, norm_mul, norm_neg,
    norm_real, Real.norm_eq_abs, abs_of_pos (arcsinCoeff_pos j),
    norm_real, Real.norm_eq_abs,
    abs_of_pos (tsum_log_div_even_pow_pos j)]

theorem arcsine_zeta_derivative_transform_real :
    (∑' k : ℕ, Real.log k / k * Real.arcsin (1 / (k : ℝ))) =
      -(∑' j : ℕ, arcsinCoeff j *
        (deriv riemannZeta (((2 * j + 2 : ℕ) : ℝ) : ℂ)).re) := by
  rw [← tsum_neg, arcsine_dirichlet_transform]
  apply tsum_congr
  intro j
  rw [zeta_deriv_even_re_eq_neg_log_tsum]
  ring

noncomputable def prolateArcsineCharge : ℝ :=
  ∑' k : ℕ, Real.log k / k * Real.arcsin (1 / (k : ℝ))

theorem log_div_sq_le_arcsine_slice (k : ℕ) :
    Real.log k / (k : ℝ) ^ (2 : ℕ) ≤
      Real.log k / k * Real.arcsin (1 / (k : ℝ)) := by
  have hk0 : 0 ≤ (1 / (k : ℝ)) := by positivity
  have hk1 : 1 / (k : ℝ) ≤ 1 := by
    rcases k.eq_zero_or_pos with rfl | hk
    · simp
    · rw [div_le_one (by positivity)]
      exact_mod_cast hk
  have harc0 : 0 ≤ Real.arcsin (1 / (k : ℝ)) := Real.arcsin_nonneg.mpr hk0
  have harc : 1 / (k : ℝ) ≤ Real.arcsin (1 / (k : ℝ)) := by
    have h := Real.sin_le harc0
    rw [Real.sin_arcsin (by linarith) hk1] at h
    exact h
  have hlog : 0 ≤ Real.log k / k := div_nonneg (log_natCast_nonneg k) (Nat.cast_nonneg k)
  calc
    Real.log k / (k : ℝ) ^ (2 : ℕ) = Real.log k / k * (1 / (k : ℝ)) := by ring
    _ ≤ Real.log k / k * Real.arcsin (1 / (k : ℝ)) :=
      mul_le_mul_of_nonneg_left harc hlog

theorem arcsine_slice_le_pi_half_log_div_sq (k : ℕ) :
    Real.log k / k * Real.arcsin (1 / (k : ℝ)) ≤
      Real.pi / 2 * (Real.log k / (k : ℝ) ^ (2 : ℕ)) := by
  have hk1 : 1 / (k : ℝ) ≤ 1 := by
    rcases k.eq_zero_or_pos with rfl | hk
    · simp
    · rw [div_le_one (by positivity)]
      exact_mod_cast hk
  have harc := arcsin_le_pi_half_mul (1 / (k : ℝ)) (by positivity) hk1
  have hlog : 0 ≤ Real.log k / k := div_nonneg (log_natCast_nonneg k) (Nat.cast_nonneg k)
  calc
    Real.log k / k * Real.arcsin (1 / (k : ℝ)) ≤
        Real.log k / k * (Real.pi / 2 * (1 / (k : ℝ))) :=
      mul_le_mul_of_nonneg_left harc hlog
    _ = Real.pi / 2 * (Real.log k / (k : ℝ) ^ (2 : ℕ)) := by ring

theorem prolateArcsineCharge_pos : 0 < prolateArcsineCharge := by
  unfold prolateArcsineCharge
  refine arcsine_row_summable.tsum_pos arcsine_slice_nonneg 2 ?_
  exact mul_pos (div_pos (Real.log_pos (by norm_num)) (by norm_num))
    (Real.arcsin_pos.mpr (by norm_num))

theorem prolateArcsineCharge_bounds_dirichlet :
    (∑' k : ℕ, Real.log k / (k : ℝ) ^ (2 : ℕ)) ≤ prolateArcsineCharge ∧
      prolateArcsineCharge ≤
        Real.pi / 2 * (∑' k : ℕ, Real.log k / (k : ℝ) ^ (2 : ℕ)) := by
  constructor
  · exact Summable.tsum_le_tsum log_div_sq_le_arcsine_slice
      summable_log_div_sq arcsine_row_summable
  · have hscaled : Summable (fun k : ℕ =>
        Real.pi / 2 * (Real.log k / (k : ℝ) ^ (2 : ℕ))) := summable_log_div_sq.mul_left _
    rw [← tsum_mul_left]
    exact Summable.tsum_le_tsum arcsine_slice_le_pi_half_log_div_sq
      arcsine_row_summable hscaled

theorem zeta_deriv_two_re_eq_neg_log_sq_tsum :
    (deriv riemannZeta (2 : ℂ)).re =
      -(∑' k : ℕ, Real.log k / (k : ℝ) ^ (2 : ℕ)) := by
  have h := congrArg Complex.re (zeta_deriv_even_eq_neg_log_tsum 0)
  norm_num at h ⊢
  exact h

/-- Sharp elementary bounds for the prolate charge in zeta-derivative coordinates. -/
theorem prolateArcsineCharge_bounds_zetaDerivative :
    -(deriv riemannZeta (2 : ℂ)).re ≤ prolateArcsineCharge ∧
      prolateArcsineCharge ≤ -(Real.pi / 2) * (deriv riemannZeta (2 : ℂ)).re := by
  rw [zeta_deriv_two_re_eq_neg_log_sq_tsum]
  simpa [prolateArcsineCharge] using prolateArcsineCharge_bounds_dirichlet

noncomputable def prolateArcsineDiagonalConstant : ℝ :=
  -(16 / (11 * Real.pi)) * prolateArcsineCharge

theorem prolateArcsineDiagonalConstant_neg : prolateArcsineDiagonalConstant < 0 := by
  unfold prolateArcsineDiagonalConstant
  exact mul_neg_of_neg_of_pos (neg_neg_of_pos (by positivity)) prolateArcsineCharge_pos

/-- The sharp elementary bounds for the signed diagonal constant. -/
theorem prolateArcsineDiagonalConstant_bounds :
    8 / 11 * (deriv riemannZeta (2 : ℂ)).re ≤ prolateArcsineDiagonalConstant ∧
      prolateArcsineDiagonalConstant ≤
        16 / (11 * Real.pi) * (deriv riemannZeta (2 : ℂ)).re := by
  let d : ℝ := (deriv riemannZeta (2 : ℂ)).re
  let a : ℝ := 16 / (11 * Real.pi)
  have ha : 0 < a := by dsimp only [a]; positivity
  have hb := prolateArcsineCharge_bounds_zetaDerivative
  change -d ≤ prolateArcsineCharge ∧ prolateArcsineCharge ≤ -(Real.pi / 2) * d at hb
  change 8 / 11 * d ≤ prolateArcsineDiagonalConstant ∧
    prolateArcsineDiagonalConstant ≤ a * d
  constructor
  · calc
      8 / 11 * d = (-a) * (-(Real.pi / 2) * d) := by
        dsimp only [a]
        field_simp [Real.pi_ne_zero]
        ring
      _ ≤ (-a) * prolateArcsineCharge :=
        mul_le_mul_of_nonpos_left hb.2 (neg_nonpos.mpr ha.le)
      _ = prolateArcsineDiagonalConstant := by
        rw [prolateArcsineDiagonalConstant]
  · calc
      prolateArcsineDiagonalConstant = (-a) * prolateArcsineCharge := by
        rw [prolateArcsineDiagonalConstant]
      _ ≤ (-a) * (-d) := mul_le_mul_of_nonpos_left hb.1 (neg_nonpos.mpr ha.le)
      _ = a * d := by ring

/-- The all-natural-index charge is the shifted prime series used by the constrained-prolate
module; the `k = 0,1` head vanishes. -/
theorem prolateArcsineCharge_eq_constrainedProlatePrimeSeries :
    prolateArcsineCharge = ∑' n : ℕ, constrainedProlatePrimeSeriesTerm n := by
  have hsplit := arcsine_row_summable.sum_add_tsum_nat_add 2
  have hhead : ∑ k ∈ Finset.range 2,
      Real.log k / k * Real.arcsin (1 / (k : ℝ)) = 0 := by
    norm_num [Finset.sum_range_succ]
  rw [hhead, zero_add] at hsplit
  simpa [prolateArcsineCharge, constrainedProlatePrimeSeriesTerm] using hsplit.symm

theorem prolateArcsineDiagonalConstant_eq_constrainedProlatePrimeConstant :
    prolateArcsineDiagonalConstant = constrainedProlatePrimeConstant := by
  rw [prolateArcsineDiagonalConstant, constrainedProlatePrimeConstant,
    prolateArcsineCharge_eq_constrainedProlatePrimeSeries]

/-- Exact even-zeta-derivative formula for the signed prolate diagonal constant. -/
theorem prolateArcsineDiagonalConstant_eq_zetaDerivativeSpectrum :
    prolateArcsineDiagonalConstant =
      16 / (11 * Real.pi) *
        (∑' j : ℕ, arcsinCoeff j *
          (deriv riemannZeta (((2 * j + 2 : ℕ) : ℝ) : ℂ)).re) := by
  rw [prolateArcsineDiagonalConstant, prolateArcsineCharge,
    arcsine_zeta_derivative_transform_real]
  ring

/-! ## Positive arithmetic spectrum -/

/-- The `k = n + 2` eigenvalue
`κ_k = 16 log(k) arcsin(1 / k) / (11 π k)` of the limiting arithmetic diagonal. -/
noncomputable def constrainedProlateArithmeticEigenvalue (n : ℕ) : ℝ :=
  (16 / (11 * Real.pi)) * constrainedProlatePrimeSeriesTerm n

theorem constrainedProlateArithmeticEigenvalue_eq (n : ℕ) :
    constrainedProlateArithmeticEigenvalue n =
      let k : ℝ := ((n + 2 : ℕ) : ℝ)
      (16 / (11 * Real.pi)) * (Real.log k / k * Real.arcsin (1 / k)) := by
  rfl

/-- Every eigenvalue of the limiting arithmetic diagonal is nonnegative. -/
theorem constrainedProlateArithmeticEigenvalue_nonneg (n : ℕ) :
    0 ≤ constrainedProlateArithmeticEigenvalue n := by
  exact mul_nonneg (by positivity) (constrainedProlatePrimeSeriesTerm_nonneg n)

/-- Every eigenvalue of the limiting arithmetic diagonal is in fact strictly positive. -/
theorem constrainedProlateArithmeticEigenvalue_pos (n : ℕ) :
    0 < constrainedProlateArithmeticEigenvalue n := by
  unfold constrainedProlateArithmeticEigenvalue constrainedProlatePrimeSeriesTerm
  have hk : (1 : ℝ) < ((n + 2 : ℕ) : ℝ) := by
    exact_mod_cast (show 1 < n + 2 by omega)
  exact mul_pos (by positivity)
    (mul_pos (div_pos (Real.log_pos hk) (by positivity))
      (Real.arcsin_pos.mpr (by positivity)))

/-- The positive arithmetic eigenvalue sequence is summable.  This is the scalar trace-class
criterion for the diagonal limit. -/
theorem summable_constrainedProlateArithmeticEigenvalue :
    Summable constrainedProlateArithmeticEigenvalue := by
  exact summable_constrainedProlatePrimeSeriesTerm.mul_left _

/-- The total mass of the positive arithmetic spectrum is exactly the negative of the signed
radial prime constant. -/
theorem tsum_constrainedProlateArithmeticEigenvalue :
    (∑' n : ℕ, constrainedProlateArithmeticEigenvalue n) =
      -constrainedProlatePrimeConstant := by
  rw [constrainedProlatePrimeConstant]
  change (∑' n : ℕ,
    (16 / (11 * Real.pi)) * constrainedProlatePrimeSeriesTerm n) = _
  rw [tsum_mul_left]
  ring

/-- The same total-mass identity in the arcsine diagonal normalization. -/
theorem tsum_constrainedProlateArithmeticEigenvalue_eq_neg_diagonalConstant :
    (∑' n : ℕ, constrainedProlateArithmeticEigenvalue n) =
      -prolateArcsineDiagonalConstant := by
  rw [tsum_constrainedProlateArithmeticEigenvalue,
    prolateArcsineDiagonalConstant_eq_constrainedProlatePrimeConstant]

end GaloisForLFunctions
