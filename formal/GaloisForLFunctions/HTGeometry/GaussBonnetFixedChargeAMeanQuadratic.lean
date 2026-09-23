import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAMeanParameters

/-!
# Exact even equilibrium equation for the mean radius

Recenter the fixed-charge quadratic using the actual mean-radius weight.
The coefficients contain only the squared radius asymmetry and the even
logarithmic kernel. Their positivity makes subtraction from the critical
quadratic a nonsingular route to higher-order critical limits.
-/
noncomputable section
open Real Filter
open scoped Topology
namespace GaloisForLFunctions.HTGeometry
open CPV

def egbFixedChargeAMeanQuadraticA (τ φ : ℝ) : ℝ :=
  4 * egbFixedChargeAFraction φ * egbCoexistenceALogKernel τ * (1 + egbCoexistenceASymmetricRatio τ ^ (2 : ℕ))
def egbFixedChargeAMeanQuadraticB (τ φ : ℝ) : ℝ :=
  2 * ((3 - egbCoexistenceASymmetricRatio τ ^ (2 : ℕ)) * (1 + egbCoexistenceASymmetricRatio τ ^ (2 : ℕ)) +
    egbFixedChargeAFraction φ * (1 - egbCoexistenceASymmetricRatio τ ^ (2 : ℕ)) *
      (2 * (3 + egbCoexistenceASymmetricRatio τ ^ (2 : ℕ)) - (1 - egbCoexistenceASymmetricRatio τ ^ (2 : ℕ)) * egbCoexistenceALogKernel τ))
def egbFixedChargeAMeanQuadraticC (τ : ℝ) : ℝ :=
  (1 - egbCoexistenceASymmetricRatio τ ^ (2 : ℕ)) ^ (2 : ℕ) * (1 + egbCoexistenceASymmetricRatio τ ^ (2 : ℕ))

theorem egbFixedChargeAMeanQuadraticA_transfer (τ φ : ℝ) :
    egbFixedChargeAMeanQuadraticA τ φ =
      egbFixedChargeAFraction φ * (1 + egbCoexistenceASymmetricRatio τ) ^ (2 : ℕ) * egbCoexistenceAQuadraticA τ / 2 := by
  have hd := (egbCoexistenceASymmetricRatio_bounds τ).1
  unfold egbFixedChargeAMeanQuadraticA egbCoexistenceAQuadraticA
  rw [egbCoexistenceASymmetricRatio_square_sum]
  field_simp

theorem egbFixedChargeAMeanQuadraticB_transfer (τ φ : ℝ) :
    egbFixedChargeAMeanQuadraticB τ φ =
      (1 + egbCoexistenceASymmetricRatio τ) ^ (4 : ℕ) * egbFixedChargeAQuadraticB τ φ / 2 := by
  have hd := (egbCoexistenceASymmetricRatio_bounds τ).1
  unfold egbFixedChargeAMeanQuadraticB egbFixedChargeAQuadraticB egbFixedChargeABase egbFixedChargeALinearCorrection
  rw [egbCoexistenceASymmetricRatio_shape, egbCoexistenceASymmetricRatio_square_sum,
    egbCoexistenceASymmetricRatio_quadratic_sum, egbCoexistenceASymmetricRatio_inversion]
  field_simp
  ring

theorem egbFixedChargeAMeanQuadraticC_transfer (τ : ℝ) :
    egbFixedChargeAMeanQuadraticC τ =
      (1 + egbCoexistenceASymmetricRatio τ) ^ (6 : ℕ) * egbCoexistenceAQuadraticC τ / 2 := by
  have hd := (egbCoexistenceASymmetricRatio_bounds τ).1
  unfold egbFixedChargeAMeanQuadraticC egbCoexistenceAQuadraticC
  rw [egbCoexistenceASymmetricRatio_square_sum, egbCoexistenceASymmetricRatio_inversion]
  field_simp
  ring

theorem egbFixedChargeAMeanQuadraticA_nonneg (τ φ : ℝ) : 0 ≤ egbFixedChargeAMeanQuadraticA τ φ := by
  have hr := (egbFixedChargeAFraction_bounds φ).1
  have hH := egbCoexistenceALogKernel_pos τ
  unfold egbFixedChargeAMeanQuadraticA
  positivity

theorem egbFixedChargeAMeanQuadraticB_pos (τ φ : ℝ) : 0 < egbFixedChargeAMeanQuadraticB τ φ := by
  have hd := (egbCoexistenceASymmetricRatio_bounds τ).1
  have hB := egbFixedChargeAQuadraticB_pos τ φ
  rw [egbFixedChargeAMeanQuadraticB_transfer]
  positivity

theorem egbFixedChargeAMeanQuadraticC_pos (τ : ℝ) : 0 < egbFixedChargeAMeanQuadraticC τ := by
  have hd := egbCoexistenceASymmetricRatio_bounds τ
  have h : 0 < 1 - egbCoexistenceASymmetricRatio τ ^ (2 : ℕ) := by nlinarith [hd.1, hd.2]
  unfold egbFixedChargeAMeanQuadraticC
  positivity

theorem egbFixedChargeAMeanWeight_quadratic (τ φ : ℝ) :
    egbFixedChargeAMeanQuadraticA τ φ * egbFixedChargeAMeanWeight τ φ ^ (2 : ℕ) +
      egbFixedChargeAMeanQuadraticB τ φ * egbFixedChargeAMeanWeight τ φ - egbFixedChargeAMeanQuadraticC τ = 0 := by
  rw [egbFixedChargeAMeanQuadraticA_transfer, egbFixedChargeAMeanQuadraticB_transfer, egbFixedChargeAMeanQuadraticC_transfer]
  unfold egbFixedChargeAMeanWeight
  linear_combination (1 + egbCoexistenceASymmetricRatio τ) ^ (6 : ℕ) / 2 * egbFixedChargeAWeight_quadratic τ φ

theorem egbFixedChargeAMeanWeight_critical_difference (τ φ : ℝ) :
    (egbFixedChargeAMeanWeight τ φ - egbFixedChargeACriticalWeight φ) *
      (egbFixedChargeAMeanQuadraticA τ φ * (egbFixedChargeAMeanWeight τ φ + egbFixedChargeACriticalWeight φ) +
        egbFixedChargeAMeanQuadraticB τ φ) =
    (egbFixedChargeAMeanQuadraticC τ - 1) -
      (egbFixedChargeAMeanQuadraticA τ φ - 12 * egbFixedChargeAFraction φ) * egbFixedChargeACriticalWeight φ ^ (2 : ℕ) -
      (egbFixedChargeAMeanQuadraticB τ φ - 6 * (1 + egbFixedChargeAFraction φ)) * egbFixedChargeACriticalWeight φ := by
  linear_combination egbFixedChargeAMeanWeight_quadratic τ φ - egbFixedChargeACriticalWeight_quadratic φ

theorem egbFixedChargeAMeanWeight_secant_denominator_pos (τ φ : ℝ) :
    0 < egbFixedChargeAMeanQuadraticA τ φ * (egbFixedChargeAMeanWeight τ φ + egbFixedChargeACriticalWeight φ) +
      egbFixedChargeAMeanQuadraticB τ φ := by
  have hA := egbFixedChargeAMeanQuadraticA_nonneg τ φ
  have hS := egbFixedChargeAMeanWeight_pos τ φ
  have hs := egbFixedChargeACriticalWeight_pos φ
  have hB := egbFixedChargeAMeanQuadraticB_pos τ φ
  positivity

end GaloisForLFunctions.HTGeometry
