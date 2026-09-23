import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAMeanRadiusCorrection

/-!
# Critical mean displacement in the paper's dimensionless coupling

The first correction simplifies to a rational expression in b = α/r_c².
Its strict positivity follows from the closed equilibrium construction.
-/
noncomputable section
open Real
namespace GaloisForLFunctions.HTGeometry

def egbFixedChargeAMeanRelativeCorrection (φ : ℝ) : ℝ :=
  (25 + 28 * egbFixedChargeACriticalCouplingWeight φ - 252 * egbFixedChargeACriticalCouplingWeight φ ^ (2 : ℕ)) /
    (15 * (1 - 2 * egbFixedChargeACriticalCouplingWeight φ) * (1 + 6 * egbFixedChargeACriticalCouplingWeight φ))

theorem egbFixedChargeACritical_fraction_quotient (φ : ℝ) :
    egbFixedChargeAFraction φ = egbFixedChargeACriticalCouplingWeight φ / egbFixedChargeACriticalWeight φ := by
  apply (eq_div_iff (egbFixedChargeACriticalWeight_pos φ).ne').2
  rfl

theorem egbFixedChargeAMeanRelativeCorrection_formula (φ : ℝ) :
    -egbFixedChargeAMeanCriticalCorrection φ / egbFixedChargeACriticalWeight φ = egbFixedChargeAMeanRelativeCorrection φ := by
  have hb := (egbFixedChargeACriticalCouplingWeight_bounds φ).1
  have hb6 := egbFixedChargeACriticalCouplingWeight_lt_sixth φ
  have h1 : 0 < 1 - 6 * egbFixedChargeACriticalCouplingWeight φ := by linarith
  have h2 : 0 < 1 - 2 * egbFixedChargeACriticalCouplingWeight φ := by linarith
  have h3 : 0 < 1 + 2 * egbFixedChargeACriticalCouplingWeight φ := by positivity
  have h6 : 0 < 1 + 6 * egbFixedChargeACriticalCouplingWeight φ := by positivity
  have hs := egbFixedChargeACriticalWeight_pos φ
  have hden := egbFixedChargeAMeanCriticalCorrection_denominator_pos φ
  unfold egbFixedChargeAMeanCriticalCorrection egbFixedChargeAMeanRelativeCorrection
  rw [← neg_div, neg_neg, div_div]
  apply (div_eq_div_iff (mul_ne_zero hden.ne' hs.ne') (by positivity)).2
  rw [egbFixedChargeACritical_fraction_quotient, egbFixedChargeACriticalWeight_formula]
  have h1' : 1 - egbFixedChargeACriticalCouplingWeight φ * 6 ≠ 0 := by nlinarith
  field_simp [h1.ne', h1', h3.ne'] <;> ring

theorem egbFixedChargeAMeanRelativeCorrection_pos (φ : ℝ) : 0 < egbFixedChargeAMeanRelativeCorrection φ := by
  rw [← egbFixedChargeAMeanRelativeCorrection_formula]
  exact div_pos (neg_pos.mpr (egbFixedChargeAMeanCriticalCorrection_neg φ)) (egbFixedChargeACriticalWeight_pos φ)

theorem egbFixedChargeAMeanCriticalCorrection_relative (φ : ℝ) :
    egbFixedChargeAMeanCriticalCorrection φ = -egbFixedChargeACriticalWeight φ * egbFixedChargeAMeanRelativeCorrection φ := by
  have h := (eq_div_iff (egbFixedChargeACriticalWeight_pos φ).ne').1 (egbFixedChargeAMeanRelativeCorrection_formula φ).symm
  linarith

theorem egbFixedChargeAMeanRadiusCorrection_relative (w φ : ℝ) :
    egbFixedChargeAMeanRadiusCorrection w φ =
      egbFixedChargeACriticalRadius w φ * egbFixedChargeAMeanRelativeCorrection φ / 2 := by
  have hs := egbFixedChargeACriticalWeight_pos φ
  unfold egbFixedChargeAMeanRadiusCorrection
  rw [egbFixedChargeAMeanCriticalCorrection_relative]
  field_simp <;> ring

end GaloisForLFunctions.HTGeometry
