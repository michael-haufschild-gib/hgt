import GaloisForLFunctions.RHTower.ThetaPrimeShiftNoetherArctan
import GaloisForLFunctions.RHTower.ThetaSourceDilation
import GaloisForLFunctions.RHTower.ThetaSourceStrictLogConcavityFluxNoGo

/-!
# Positive arithmetic action responses do not force Euler flux positivity

Dilating the explicit modulated Gaussian moves a negative source Bezoutian
to the line `re w = 1`. The dilated source retains strictly positive full
prime currents and strictly positive responses to every translated
arctangent. Thus those positive Noether data alone do not determine the
sign of the source spectral form, even in the Euler half-plane.

This is a counterexample among theta sources, not a counterexample to RH:
the constructed source is not the actual completed Riemann theta kernel
and is not asserted to satisfy its full Gamma/pole source equation.
-/

noncomputable section

open Complex MeasureTheory

namespace RHTower

open ThetaSourceWard

/-- Positive prime-current and local-action data coexist with negative Euler-line spectral flux. -/
theorem exists_thetaSource_positive_noether_negative_euler_flux :
    ∃ S : ThetaSource,
      (∀ x : ℝ, 0 < (fullPrimeShiftNoetherCurrent S S x).re) ∧
      (∀ r : ℝ, 0 < (thetaPrimeLocalResponse S S (thetaPrimeArctanProfile r)).re) ∧
      ∃ w : ℂ, w.re = 1 ∧ (sourceBezoutian S w w).re < 0 := by
  obtain ⟨a, ha, hneg⟩ := exists_modulatedGaussianSource_sourceBezoutian_diagonal_neg
  let S := thetaSourceDilation modulatedGaussianSource (Real.log a)
  let w₀ : ℂ := (a : ℂ) + (16 / 3 : ℝ) * I
  let w : ℂ := w₀ / (a : ℂ)
  have hw₀ : w₀.re = a := by simp [w₀]
  have hw : w.re = 1 := by
    change (w₀ / (a : ℂ)).re = 1
    rw [Complex.div_ofReal_re, hw₀, div_self (ne_of_gt ha.1)]
  have hscale : (Real.exp (Real.log a) : ℂ) * w = w₀ := by
    rw [Real.exp_log ha.1]
    dsimp only [w]
    have haC : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt ha.1)
    field_simp
  refine ⟨S, fun x => fullPrimeShiftNoetherCurrent_re_pos S S x,
    fun r => thetaPrimeLocalResponse_arctan_re_pos S S r, w, hw, ?_⟩
  change (sourceBezoutian (thetaSourceDilation modulatedGaussianSource (Real.log a)) w w).re < 0
  rw [sourceBezoutian_thetaSourceDilation, hscale, ← Complex.ofReal_pow, Complex.re_ofReal_mul]
  exact mul_neg_of_pos_of_neg (sq_pos_of_pos (Real.exp_pos _)) hneg

/-- No universal representation by nonnegative square weights of the positive current is possible. -/
theorem exists_thetaSource_no_positive_current_representation :
    ∃ (S : ThetaSource) (w : ℂ), w.re = 1 ∧
      (∀ x : ℝ, 0 < (fullPrimeShiftNoetherCurrent S S x).re) ∧
      (∀ r : ℝ, 0 < (thetaPrimeLocalResponse S S (thetaPrimeArctanProfile r)).re) ∧
      ∀ f : ℝ → ℝ,
        (sourceBezoutian S w w).re ≠
          ∫ x : ℝ, f x ^ 2 * (fullPrimeShiftNoetherCurrent S S x).re := by
  obtain ⟨S, hJ, hA, w, hw, hneg⟩ := exists_thetaSource_positive_noether_negative_euler_flux
  refine ⟨S, w, hw, hJ, hA, fun f => ?_⟩
  exact ne_of_lt (hneg.trans_le
    (integral_nonneg fun x => mul_nonneg (sq_nonneg (f x)) (hJ x).le))

end RHTower
