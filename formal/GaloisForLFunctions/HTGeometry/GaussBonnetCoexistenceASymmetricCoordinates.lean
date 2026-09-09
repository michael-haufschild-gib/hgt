import GaloisForLFunctions.HTGeometry.GaussBonnetCoexistenceAKernel

/-!
# Exact conversion between phase-radius ratio and symmetric asymmetry

These identities recenter the two radii around their arithmetic mean.
They turn the fixed-charge equilibrium equation into one involving only
the squared asymmetry and the even logarithmic kernel.
-/
noncomputable section
open Real
namespace GaloisForLFunctions.HTGeometry
open CPV

theorem egbCoexistenceASymmetricRatio_cross (τ : ℝ) :
    thermalRatio τ * (1 + egbCoexistenceASymmetricRatio τ) = 1 - egbCoexistenceASymmetricRatio τ := by
  have hz := thermalRatio_pos τ
  unfold egbCoexistenceASymmetricRatio
  field_simp
  ring

theorem egbCoexistenceASymmetricRatio_inversion (τ : ℝ) :
    thermalRatio τ = (1 - egbCoexistenceASymmetricRatio τ) / (1 + egbCoexistenceASymmetricRatio τ) := by
  have hd := (egbCoexistenceASymmetricRatio_bounds τ).1
  exact (eq_div_iff (by positivity)).2 (egbCoexistenceASymmetricRatio_cross τ)

theorem egbCoexistenceASymmetricRatio_radius_sum (τ : ℝ) :
    1 + thermalRatio τ = 2 / (1 + egbCoexistenceASymmetricRatio τ) := by
  have hd := (egbCoexistenceASymmetricRatio_bounds τ).1
  apply (eq_div_iff (by positivity)).2
  nlinarith [egbCoexistenceASymmetricRatio_cross τ]

theorem egbCoexistenceASymmetricRatio_square_sum (τ : ℝ) :
    thermalRatio τ ^ 2 + 1 =
      2 * (1 + egbCoexistenceASymmetricRatio τ ^ 2) / (1 + egbCoexistenceASymmetricRatio τ) ^ 2 := by
  have hd := (egbCoexistenceASymmetricRatio_bounds τ).1
  rw [egbCoexistenceASymmetricRatio_inversion]
  field_simp
  ring

theorem egbCoexistenceASymmetricRatio_quadratic_sum (τ : ℝ) :
    thermalRatio τ ^ 2 + thermalRatio τ + 1 =
      (3 + egbCoexistenceASymmetricRatio τ ^ 2) / (1 + egbCoexistenceASymmetricRatio τ) ^ 2 := by
  have hd := (egbCoexistenceASymmetricRatio_bounds τ).1
  simp only [egbCoexistenceASymmetricRatio_inversion]
  field_simp
  ring

theorem egbCoexistenceASymmetricRatio_shape (τ : ℝ) :
    egbCoexistenceShape τ =
      (6 - 2 * egbCoexistenceASymmetricRatio τ ^ 2) / (1 + egbCoexistenceASymmetricRatio τ) ^ 2 := by
  have hd := (egbCoexistenceASymmetricRatio_bounds τ).1
  simp only [egbCoexistenceShape, egbCoexistenceASymmetricRatio_inversion]
  field_simp
  ring

end GaloisForLFunctions.HTGeometry
