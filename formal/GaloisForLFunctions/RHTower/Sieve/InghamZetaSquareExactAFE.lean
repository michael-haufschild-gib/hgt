import GaloisForLFunctions.RHTower.Sieve.InghamZetaSquareInfiniteContour

/-!
# Exact exponential approximate functional equation for zeta square

Combining Mellin inversion on right line with completed infinite contour shift solves exactly for
`zeta(1/2+i tau)^(2 : ℕ)`: smoothed divisor carrier minus shifted residue minus reflected left contour.
-/

noncomputable section

open Complex MeasureTheory

namespace RHTower.Sieve

/-- Right vertical integral is exactly `2*pi` times exponentially smoothed critical divisor sum. -/
theorem integral_inghamZetaSquareMellinIntegrand_right_two_eq_smoothedDivisor
    {x : ℝ} (hx : 0 < x) (tau : ℝ) :
    (∫ v : ℝ,
      inghamZetaSquareMellinIntegrand (linePt tau) x
        (((2 : ℝ) : ℂ) + (v : ℂ) * I)) =
      (2 * Real.pi : ℂ) *
        ∑' n : ℕ, inghamCriticalDivisorCoeff tau n *
          Complex.exp (-((n : ℝ) * x : ℝ)) := by
  have h := ingham_exponential_mellin_identity tau hx
  unfold mellinInv at h
  simp only [smul_eq_mul, Complex.real_smul] at h
  have hshape :
      (∫ y : ℝ,
          (x : ℂ) ^ (-(((2 : ℝ) : ℂ) + (y : ℂ) * I)) *
            (Complex.Gamma (((2 : ℝ) : ℂ) + (y : ℂ) * I) *
              riemannZeta
                (linePt tau + (((2 : ℝ) : ℂ) + (y : ℂ) * I)) ^ 2)) =
        ∫ v : ℝ,
          inghamZetaSquareMellinIntegrand (linePt tau) x
            (((2 : ℝ) : ℂ) + (v : ℂ) * I) := by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun v => by
      simp only [inghamZetaSquareMellinIntegrand]
      ring
  rw [hshape] at h
  have hpi : (2 * Real.pi : ℂ) ≠ 0 := by
    exact mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
  have hcancel :
      (2 * Real.pi : ℂ) * (((1 / (2 * Real.pi) : ℝ) : ℂ)) = 1 := by
    push_cast
    field_simp
  calc
    (∫ v : ℝ,
        inghamZetaSquareMellinIntegrand (linePt tau) x
          (((2 : ℝ) : ℂ) + (v : ℂ) * I)) =
        1 * (∫ v : ℝ,
          inghamZetaSquareMellinIntegrand (linePt tau) x
            (((2 : ℝ) : ℂ) + (v : ℂ) * I)) := by ring
    _ = ((2 * Real.pi : ℂ) * (((1 / (2 * Real.pi) : ℝ) : ℂ))) *
        (∫ v : ℝ,
          inghamZetaSquareMellinIntegrand (linePt tau) x
            (((2 : ℝ) : ℂ) + (v : ℂ) * I)) := by rw [hcancel]
    _ = (2 * Real.pi : ℂ) *
        ((((1 / (2 * Real.pi) : ℝ) : ℂ)) *
          (∫ v : ℝ,
            inghamZetaSquareMellinIntegrand (linePt tau) x
              (((2 : ℝ) : ℂ) + (v : ℂ) * I))) := by ring
    _ = (2 * Real.pi : ℂ) *
        (∑' n : ℕ, inghamCriticalDivisorCoeff tau n *
          Complex.exp (-((n : ℝ) * x : ℝ))) := by rw [h]

/-- Exact Ramachandra exponential AFE on critical line, with no asymptotic remainder. -/
theorem inghamZetaSquare_exact_exponential_AFE
    {x : ℝ} (hx : 0 < x) (tau : ℝ) :
    riemannZeta (linePt tau) ^ 2 =
      (∑' n : ℕ, inghamCriticalDivisorCoeff tau n *
          Complex.exp (-((n : ℝ) * x : ℝ))) -
        confluentResidueCoeff (inghamZetaSquarePoleNumerator (linePt tau) x)
          (1 - linePt tau) -
        (1 / (2 * Real.pi) : ℂ) *
          (∫ v : ℝ,
            inghamZetaSquareMellinIntegrand (linePt tau) x
              (((-3 / 4 : ℝ) : ℂ) + (v : ℂ) * I)) := by
  have hcontour := inghamZetaSquareMellin_infinite_contour_shift_line hx tau
  rw [integral_inghamZetaSquareMellinIntegrand_right_two_eq_smoothedDivisor hx tau]
    at hcontour
  simp only [smul_eq_mul] at hcontour
  have hpi : (2 * Real.pi : ℂ) ≠ 0 := by
    exact mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
  have hI : I ≠ 0 := I_ne_zero
  have hbase :
      (2 * Real.pi : ℂ) *
          (∑' n : ℕ, inghamCriticalDivisorCoeff tau n *
            Complex.exp (-((n : ℝ) * x : ℝ))) -
        (∫ v : ℝ,
          inghamZetaSquareMellinIntegrand (linePt tau) x
            (((-3 / 4 : ℝ) : ℂ) + (v : ℂ) * I)) =
      (2 * Real.pi : ℂ) *
        (riemannZeta (linePt tau) ^ 2 +
          confluentResidueCoeff (inghamZetaSquarePoleNumerator (linePt tau) x)
            (1 - linePt tau)) := by
    apply mul_left_cancel₀ hI
    linear_combination hcontour
  have hcancel :
      (2 * Real.pi : ℂ) * (1 / (2 * Real.pi) : ℂ) = 1 := by
    field_simp
  apply mul_left_cancel₀ hpi
  rw [mul_sub, mul_sub, ← mul_assoc, hcancel, one_mul]
  linear_combination -hbase

end RHTower.Sieve
