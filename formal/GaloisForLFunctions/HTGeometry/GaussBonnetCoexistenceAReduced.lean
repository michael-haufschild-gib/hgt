import GaloisForLFunctions.HTGeometry.GaussBonnetCoexistenceAWeights
import GaloisForLFunctions.HTGeometry.GaussBonnetCoexistenceALogarithm

/-!
# Exact reduced model-A coexistence balance

The constructed positive parameter weights satisfy both stationarity
conditions and the exact logarithmic equal-Gibbs equation. Factor the
actual radial derivative into the two proposed phase radii and a quadratic.
This prepares the global stability audit without numerical root finding.
-/
noncomputable section
open Real
namespace GaloisForLFunctions.HTGeometry
open CPV

def egbCoexistenceARadialPolynomial (τ θ v : ℝ) : ℝ :=
  egbCoexistenceAPressureWeight τ θ * v ^ 4 - egbCoexistenceATemperatureWeight τ θ * v ^ 3 + v ^ 2 -
    2 * egbCoexistenceACouplingWeight τ θ * egbCoexistenceATemperatureWeight τ θ * v - egbCoexistenceAChargeWeight τ θ

def egbCoexistenceAReducedGibbs (τ θ v : ℝ) : ℝ :=
  v / 2 + egbCoexistenceAChargeWeight τ θ / (2 * v) + egbCoexistenceAPressureWeight τ θ * v ^ 3 / 6 -
    egbCoexistenceATemperatureWeight τ θ * v ^ 2 / 4 -
      egbCoexistenceACouplingWeight τ θ * egbCoexistenceATemperatureWeight τ θ * log v

def egbCoexistenceAReducedLogGibbs (τ θ u : ℝ) : ℝ := egbCoexistenceAReducedGibbs τ θ (exp u)

theorem egbCoexistenceA_stationarity_difference (τ θ : ℝ) :
    egbCoexistenceAPressureWeight τ θ * (thermalRatio τ + 1) * (thermalRatio τ ^ 2 + 1) -
      egbCoexistenceATemperatureWeight τ θ * (thermalRatio τ ^ 2 + thermalRatio τ + 1 + 2 * egbCoexistenceACouplingWeight τ θ) +
        (thermalRatio τ + 1) = 0 := by
  have hz := thermalRatio_pos τ
  have hb := (egbCoexistenceACouplingWeight_bounds τ θ).1
  have hH := egbCoexistenceALogKernel_pos τ
  unfold egbCoexistenceAPressureWeight egbCoexistenceATemperatureWeight egbCoexistenceADenominator egbCoexistenceShape
  field_simp
  ring

theorem egbCoexistenceA_stationarity_large (τ θ : ℝ) : egbCoexistenceARadialPolynomial τ θ 1 = 0 := by
  have hz := thermalRatio_pos τ
  have hb := (egbCoexistenceACouplingWeight_bounds τ θ).1
  have hH := egbCoexistenceALogKernel_pos τ
  unfold egbCoexistenceARadialPolynomial egbCoexistenceAPressureWeight egbCoexistenceATemperatureWeight
    egbCoexistenceAChargeWeight egbCoexistenceADenominator egbCoexistenceShape
  field_simp
  ring

theorem egbCoexistenceA_stationarity_small (τ θ : ℝ) : egbCoexistenceARadialPolynomial τ θ (thermalRatio τ) = 0 := by
  have h₁ := egbCoexistenceA_stationarity_large τ θ
  have h₂ := egbCoexistenceA_stationarity_difference τ θ
  unfold egbCoexistenceARadialPolynomial at *
  norm_num only [one_pow, mul_one] at h₁
  linear_combination h₁ + (thermalRatio τ - 1) * h₂

/-- Only a quadratic remains after factoring out the two phase radii. -/
theorem egbCoexistenceARadialPolynomial_factorization (τ θ v : ℝ) :
    egbCoexistenceARadialPolynomial τ θ v = (v - thermalRatio τ) * (v - 1) *
      (egbCoexistenceAPressureWeight τ θ * v ^ 2 +
        (egbCoexistenceAPressureWeight τ θ * (thermalRatio τ + 1) - egbCoexistenceATemperatureWeight τ θ) * v -
          egbCoexistenceAChargeWeight τ θ / thermalRatio τ) := by
  have h₁ := egbCoexistenceA_stationarity_large τ θ
  have h₂ := egbCoexistenceA_stationarity_difference τ θ
  have hz := thermalRatio_pos τ
  unfold egbCoexistenceARadialPolynomial at *
  norm_num only [one_pow, mul_one] at h₁
  field_simp
  linear_combination v * (v - 1) * h₂ + v * (thermalRatio τ + 1 - v) * h₁

/-- Exact equality of free energies, including the logarithmic entropy term. -/
theorem egbCoexistenceAReducedGibbs_balance (τ θ : ℝ) :
    egbCoexistenceAReducedGibbs τ θ (thermalRatio τ) = egbCoexistenceAReducedGibbs τ θ 1 := by
  have hk : (thermalRatio τ - 1) ^ 3 * egbCoexistenceALogKernel τ -
      3 * (thermalRatio τ + 1) * (thermalRatio τ ^ 2 + 1) * log (thermalRatio τ) +
        4 * (thermalRatio τ ^ 2 + thermalRatio τ + 1) * (thermalRatio τ - 1) = 0 := by
    linarith [egbCoexistenceALogKernel_cubic_identity τ]
  have he : egbCoexistenceAReducedGibbs τ θ (thermalRatio τ) - egbCoexistenceAReducedGibbs τ θ 1 =
      4 * egbCoexistenceACouplingWeight τ θ / (3 * egbCoexistenceADenominator τ θ * (thermalRatio τ ^ 2 + 1)) *
        ((thermalRatio τ - 1) ^ 3 * egbCoexistenceALogKernel τ -
          3 * (thermalRatio τ + 1) * (thermalRatio τ ^ 2 + 1) * log (thermalRatio τ) +
            4 * (thermalRatio τ ^ 2 + thermalRatio τ + 1) * (thermalRatio τ - 1)) := by
    have hz := thermalRatio_pos τ
    have hb := (egbCoexistenceACouplingWeight_bounds τ θ).1
    have hH := egbCoexistenceALogKernel_pos τ
    unfold egbCoexistenceAReducedGibbs egbCoexistenceAPressureWeight egbCoexistenceATemperatureWeight
      egbCoexistenceAChargeWeight egbCoexistenceADenominator egbCoexistenceShape
    simp only [one_pow, mul_one, log_one, mul_zero, sub_zero]
    field_simp
    ring
  rw [hk, mul_zero] at he
  exact sub_eq_zero.mp he

theorem egbCoexistenceAReducedGibbs_hasDerivAt (τ θ u : ℝ) :
    HasDerivAt (egbCoexistenceAReducedGibbs τ θ)
      (egbCoexistenceARadialPolynomial τ θ (exp u) / (2 * exp u ^ 2)) (exp u) := by
  have hi := hasDerivAt_id (exp u)
  have hq := (hasDerivAt_const (exp u) (egbCoexistenceAChargeWeight τ θ)).div (hi.const_mul 2) (by simp only [id_eq]; positivity)
  have h := ((((hi.div_const 2).add hq).add
    (((hi.pow 3).const_mul (egbCoexistenceAPressureWeight τ θ)).div_const 6)).sub
    (((hi.pow 2).const_mul (egbCoexistenceATemperatureWeight τ θ)).div_const 4)).sub
    ((hasDerivAt_log (exp_ne_zero u)).const_mul (egbCoexistenceACouplingWeight τ θ * egbCoexistenceATemperatureWeight τ θ))
  apply h.congr_deriv
  unfold egbCoexistenceARadialPolynomial
  norm_num only [Nat.cast_ofNat, Pi.pow_apply, id_eq, pow_one]
  field_simp
  ring

theorem egbCoexistenceAReducedLogGibbs_hasDerivAt (τ θ u : ℝ) :
    HasDerivAt (egbCoexistenceAReducedLogGibbs τ θ)
      (egbCoexistenceARadialPolynomial τ θ (exp u) / (2 * exp u)) u := by
  have h := (egbCoexistenceAReducedGibbs_hasDerivAt τ θ u).comp u (hasDerivAt_exp u)
  apply h.congr_deriv
  field_simp

theorem egbCoexistenceAReducedLogGibbs_continuous (τ θ : ℝ) : Continuous (egbCoexistenceAReducedLogGibbs τ θ) :=
  continuous_iff_continuousAt.mpr fun u => (egbCoexistenceAReducedLogGibbs_hasDerivAt τ θ u).continuousAt

theorem egbCoexistenceAReducedLogGibbs_balance (τ θ : ℝ) :
    egbCoexistenceAReducedLogGibbs τ θ (log (thermalRatio τ)) = egbCoexistenceAReducedLogGibbs τ θ 0 := by
  unfold egbCoexistenceAReducedLogGibbs
  rw [exp_log (thermalRatio_pos τ), exp_zero]
  exact egbCoexistenceAReducedGibbs_balance τ θ

end GaloisForLFunctions.HTGeometry
