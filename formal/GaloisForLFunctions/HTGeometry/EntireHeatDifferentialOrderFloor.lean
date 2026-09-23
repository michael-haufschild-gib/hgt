import GaloisForLFunctions.HTGeometry.EntireHeatHolonomicFiniteSpectrum
import GaloisForLFunctions.HTGeometry.SuperGaussianCentralIndex
import GaloisForLFunctions.HTGeometry.EntireOrderZeroTranscendence
import GaloisForLFunctions.HTGeometry.WildCharacteristicCollapse
import GaloisForLFunctions.HTGeometry.LogSuperlacunaryDoubleExponentialFamily
import GaloisForLFunctions.HTGeometry.FirstOrderCoefficientDecomposition

/-!
# Entire-heat anchors: exact growth and order-zero floor

Pointwise convergence of the one-sided heat series at every complex time already supplies the
card's super-Gaussian coefficient bound.  This module connects that bound to the central-index
asymptotic consumed by Wiman--Valiron theory and proves the order-zero part of the differential
order floor for every infinite-spectrum anchor.
-/

noncomputable section

open Filter

namespace GaloisForLFunctions.HTGeometry

variable {a : ℕ → ℂ}

/-- The Taylor coefficient of the entire coefficient sum is its defining coefficient. -/
theorem taylorCoeff_coeffFun (ha : EntireCoeffs a) (n : ℕ) :
    taylorCoeff (coeffFun a) n = a n := by
  have h := taylorPS_ofScalarsSum_of_radius_eq_top a (ofScalars_radius_eq_top ha) n
  rw [coeff_taylorPS] at h
  change taylorCoeff (FormalMultilinearSeries.ofScalarsSum a) n = a n
  simpa [taylorCoeff, div_eq_inv_mul] using h

/-- Infinite coefficient support makes the entire coefficient sum nonpolynomial. -/
theorem not_exists_polynomial_coeffFun_of_infinite_support (ha : EntireCoeffs a)
    (htrans : ∀ M : ℕ, ∃ n, M ≤ n ∧ a n ≠ 0) :
    ¬ ∃ p : Polynomial ℂ, ∀ z : ℂ, coeffFun a z = p.eval z := by
  rintro ⟨p, hp⟩
  obtain ⟨M, hM⟩ := eventually_taylorCoeff_eq_zero_of_polynomial hp
  obtain ⟨n, hn, hne⟩ := htrans M
  exact hne (by rw [← taylorCoeff_coeffFun ha n, hM n hn])

/-- Entire complex-time heat evolution forces a sublogarithmic central index. -/
theorem tendsto_entireHeat_centralIndex_div_log_zero
    (ha : EntireCoeffs a)
    (hheat : ∀ t z : ℂ, Summable (fun n : ℕ =>
      a n * Complex.exp (-(4 * (Real.pi : ℂ) ^ (2 : ℕ)) * (n : ℂ) ^ (2 : ℕ) * t)
        * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * z)))
    {n₀ : ℕ} (hn₀ : a n₀ ≠ 0) :
    Tendsto (fun r : ℝ => (centralIndex a r : ℝ) / Real.log r) atTop (nhds 0) := by
  exact tendsto_centralIndex_div_log_zero ha
    (fun A hA => EntireHeatHolonomic.exists_superGaussian_bound hheat A hA) hn₀

/-- An infinite-spectrum entire-heat anchor satisfies no order-zero algebraic differential
equation. -/
theorem not_differentiallyAlgebraicOfOrder_zero_entireHeat
    (ha : EntireCoeffs a)
    (htrans : ∀ M : ℕ, ∃ n, M ≤ n ∧ a n ≠ 0) :
    ¬ GaloisForLFunctions.DifferentiallyAlgebraicOfOrder (coeffFun a) 0 := by
  exact not_differentiallyAlgebraicOfOrder_zero_of_transcendental
    (differentiable_coeffFun ha) (not_exists_polynomial_coeffFun_of_infinite_support ha htrans)

/-- An infinite-spectrum entire-heat anchor satisfies no first-order algebraic differential
equation. -/
theorem not_differentiallyAlgebraicOfOrder_one_entireHeat
    (ha : EntireCoeffs a)
    (hheat : ∀ t z : ℂ, Summable (fun n : ℕ =>
      a n * Complex.exp (-(4 * (Real.pi : ℂ) ^ (2 : ℕ)) * (n : ℂ) ^ (2 : ℕ) * t)
        * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * z)))
    (htrans : ∀ M : ℕ, ∃ n, M ≤ n ∧ a n ≠ 0) :
    ¬ GaloisForLFunctions.DifferentiallyAlgebraicOfOrder (coeffFun a) 1 := by
  obtain ⟨n₀, _, hn₀⟩ := htrans 0
  exact not_differentiallyAlgebraicOfOrder_one_of_centralIndex_div_log_zero
    ha hn₀ htrans (tendsto_entireHeat_centralIndex_div_log_zero ha hheat hn₀)

end GaloisForLFunctions.HTGeometry

end
