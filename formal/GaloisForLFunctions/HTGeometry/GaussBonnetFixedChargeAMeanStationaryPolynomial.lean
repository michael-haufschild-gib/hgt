import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAMiddleMeanQuadratic
import GaloisForLFunctions.HTGeometry.GaussBonnetGibbsAPolynomialForce

/-!
# Exact mean-coordinate factorization of the physical Gibbs force

Both phase roots factor out of the actual quartic. The remaining
quadratic is the one satisfied by the constructed unstable equilibrium.
-/
noncomputable section
open Real
namespace GaloisForLFunctions.HTGeometry

def egbFixedChargeAMeanStationaryPolynomial (τ φ v : ℝ) : ℝ :=
  egbFixedChargeAMeanPressureNumerator τ φ * v ^ (4 : ℕ) - 8 * (1 + egbCoexistenceASymmetricRatio τ ^ (2 : ℕ)) * v ^ (3 : ℕ) +
    egbFixedChargeAMeanDenominator τ φ * (1 + egbCoexistenceASymmetricRatio τ ^ (2 : ℕ)) * v ^ (2 : ℕ) -
    16 * egbFixedChargeAMeanCoupling τ φ * (1 + egbCoexistenceASymmetricRatio τ ^ (2 : ℕ)) * v -
    egbFixedChargeAMeanWeight τ φ * egbFixedChargeAMeanDenominator τ φ * (1 + egbCoexistenceASymmetricRatio τ ^ (2 : ℕ))

theorem egbFixedChargeAMiddleMeanConstant_cross (τ φ : ℝ) :
    egbFixedChargeAMiddleMeanConstant τ φ * (1 - egbCoexistenceASymmetricRatio τ ^ (2 : ℕ)) +
      egbFixedChargeAMeanWeight τ φ * egbFixedChargeAMeanDenominator τ φ * (1 + egbCoexistenceASymmetricRatio τ ^ (2 : ℕ)) = 0 := by
  have hd := egbCoexistenceASymmetricRatio_bounds τ
  have hx : 0 < 1 - egbCoexistenceASymmetricRatio τ ^ (2 : ℕ) := by nlinarith [hd.1, hd.2]
  unfold egbFixedChargeAMiddleMeanConstant
  field_simp <;> ring

theorem egbFixedChargeAMeanStationaryPolynomial_factorization (τ φ v : ℝ) :
    egbFixedChargeAMeanStationaryPolynomial τ φ v =
      (v ^ (2 : ℕ) - 2 * v + 1 - egbCoexistenceASymmetricRatio τ ^ (2 : ℕ)) *
        (egbFixedChargeAMeanPressureNumerator τ φ * v ^ (2 : ℕ) + egbFixedChargeAMiddleMeanLinear τ φ * v + egbFixedChargeAMiddleMeanConstant τ φ) := by
  have h := egbFixedChargeAMiddleMeanConstant_cross τ φ
  rw [egbFixedChargeAMiddleMeanConstant_formula] at h ⊢
  unfold egbFixedChargeAMeanStationaryPolynomial egbFixedChargeAMiddleMeanLinear egbFixedChargeAMeanPressureNumerator
  unfold egbFixedChargeAMeanDenominator at h ⊢
  linear_combination -h

theorem egbFixedChargeA_mean_charge_scale (w φ τ : ℝ) :
    (exp w * cos φ) ^ (2 : ℕ) + (exp w * sin φ) ^ (2 : ℕ) =
      egbFixedChargeAMeanRadius w φ τ ^ (2 : ℕ) * egbFixedChargeAMeanWeight τ φ := by
  rw [egbFixedChargeA_conserved_scale, egbFixedChargeA_mean_effective_scale]

theorem egbFixedChargeA_mean_gibbs_derivative (w φ τ l u : ℝ) :
    HasDerivAt (egbOffShellGibbsA (egbFixedChargeAPressure w φ τ) (egbFixedChargeATemperature w φ τ)
      (exp w * cos φ) (exp w * sin φ) l)
      (egbFixedChargeAMeanStationaryPolynomial τ φ (exp u) /
        (2 * egbFixedChargeAMeanDenominator τ φ * (1 + egbCoexistenceASymmetricRatio τ ^ (2 : ℕ)) * exp u ^ (2 : ℕ)))
      (egbFixedChargeAMeanRadius w φ τ * exp u) := by
  have hm := egbFixedChargeAMeanRadius_pos w φ τ
  have hu := exp_pos u
  have hD := egbFixedChargeAMeanDenominator_pos τ φ
  have hpi := Real.pi_pos
  have hx : 0 < 1 + egbCoexistenceASymmetricRatio τ ^ (2 : ℕ) := by positivity
  have h := egbOffShellGibbsA_polynomial_derivative (egbFixedChargeAPressure w φ τ) (egbFixedChargeATemperature w φ τ)
    (exp w * cos φ) (exp w * sin φ) l (log (egbFixedChargeAMeanRadius w φ τ * exp u))
  rw [exp_log (mul_pos hm hu)] at h
  apply h.congr_deriv
  unfold egbOffShellGibbsARadialNumerator egbFixedChargeAMeanStationaryPolynomial
  rw [egbFixedChargeA_mean_pressure, egbFixedChargeA_mean_temperature, egbFixedChargeA_mean_charge_scale,
    ← egbFixedChargeA_mean_coupling_scale]
  unfold egbFixedChargeAMeanPressureNumerator
  field_simp <;> ring

theorem egbFixedChargeAMeanStationaryPolynomial_scaled (τ φ t : ℝ) :
    egbFixedChargeAMeanStationaryPolynomial τ φ (1 + egbCoexistenceASymmetricRatio τ * t) /
      egbCoexistenceASymmetricRatio τ ^ (3 : ℕ) =
      (t ^ (2 : ℕ) - 1) * (egbFixedChargeAMeanPressureNumerator τ φ * egbCoexistenceASymmetricRatio τ * t ^ (2 : ℕ) +
        (2 * egbFixedChargeAMeanPressureNumerator τ φ + egbFixedChargeAMiddleMeanLinear τ φ) * t +
        (egbFixedChargeAMeanPressureNumerator τ φ + egbFixedChargeAMiddleMeanLinear τ φ + egbFixedChargeAMiddleMeanConstant τ φ) /
          egbCoexistenceASymmetricRatio τ) := by
  have hd := (egbCoexistenceASymmetricRatio_bounds τ).1
  rw [egbFixedChargeAMeanStationaryPolynomial_factorization]
  field_simp <;> ring

end GaloisForLFunctions.HTGeometry
