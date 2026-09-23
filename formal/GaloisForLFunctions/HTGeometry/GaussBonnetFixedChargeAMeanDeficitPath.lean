import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAMeanDeficitShift
import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAGibbsKernel

/-!
# Positive paths from the phase mean to the true energy maximum

The normalized path is shorter than the full phase interval by one
additional power of asymmetry. Its exact displacement determines the
sixth-order normalization of the mean energy deficit.
-/
noncomputable section
open Real Filter Set
open scoped Topology
namespace GaloisForLFunctions.HTGeometry

def egbFixedChargeAMeanDeficitPathCoordinate (τ φ u : ℝ) : ℝ := egbFixedChargeAMiddleGapCoordinate τ φ * u

def egbFixedChargeAMeanDeficitPathRadius (w φ τ u : ℝ) : ℝ :=
  egbFixedChargeAMeanRadius w φ τ + (egbFixedChargeAMiddleRadius w φ τ - egbFixedChargeAMeanRadius w φ τ) * u

def egbFixedChargeAMeanGibbsDeficit (w φ τ l : ℝ) : ℝ :=
  egbOffShellGibbsA (egbFixedChargeAPressure w φ τ) (egbFixedChargeATemperature w φ τ)
    (exp w * cos φ) (exp w * sin φ) l (egbFixedChargeAMiddleRadius w φ τ) -
  egbOffShellGibbsA (egbFixedChargeAPressure w φ τ) (egbFixedChargeATemperature w φ τ)
    (exp w * cos φ) (exp w * sin φ) l (egbFixedChargeAMeanRadius w φ τ)

theorem egbFixedChargeAMeanDeficitPathCoordinate_mapsTo (τ φ : ℝ) :
    MapsTo (egbFixedChargeAMeanDeficitPathCoordinate τ φ) (Icc (0 : ℝ) 1) (Icc (-1 : ℝ) 1) := by
  intro u hu
  have ht := egbFixedChargeAMiddleGapCoordinate_bounds τ φ
  have hlo := mul_le_mul_of_nonneg_right ht.1.le hu.1
  have hhi := mul_le_mul_of_nonneg_right ht.2.le hu.1
  change -1 ≤ egbFixedChargeAMiddleGapCoordinate τ φ * u ∧ egbFixedChargeAMiddleGapCoordinate τ φ * u ≤ 1
  constructor <;> nlinarith only [hlo, hhi, hu.2]

theorem egbFixedChargeAMeanDeficitPathCoordinate_quadratic (τ φ u : ℝ) :
    egbCoexistenceASymmetricRatio τ * egbFixedChargeAMeanDeficitPathCoordinate τ φ u =
      egbCoexistenceASymmetricRatio τ ^ (2 : ℕ) * egbFixedChargeAMiddleQuadraticShift τ φ * u := by
  unfold egbFixedChargeAMeanDeficitPathCoordinate
  rw [← egbFixedChargeAMiddleQuadraticShift_gap]
  ring

theorem egbFixedChargeAMeanDeficitPathRadius_mean_formula (w φ τ u : ℝ) :
    egbFixedChargeAMeanDeficitPathRadius w φ τ u = egbFixedChargeAMeanRadius w φ τ *
      (1 + egbCoexistenceASymmetricRatio τ ^ (2 : ℕ) * egbFixedChargeAMiddleQuadraticShift τ φ * u) := by
  unfold egbFixedChargeAMeanDeficitPathRadius
  rw [egbFixedChargeAMiddleRadius_quadratic_displacement]
  ring

theorem egbFixedChargeAMeanDeficitPathScale_mapsTo (τ φ : ℝ) :
    MapsTo (fun u => 1 + egbCoexistenceASymmetricRatio τ ^ (2 : ℕ) * egbFixedChargeAMiddleQuadraticShift τ φ * u)
      (Icc (0 : ℝ) 1) (Icc (1 - egbCoexistenceASymmetricRatio τ) (1 + egbCoexistenceASymmetricRatio τ)) := by
  intro u hu
  dsimp only
  rw [← egbFixedChargeAMeanDeficitPathCoordinate_quadratic]
  exact egbFixedChargeAInteriorScale_mapsTo τ (egbFixedChargeAMeanDeficitPathCoordinate_mapsTo τ φ hu)

theorem egbFixedChargeAMeanDeficitPathRadius_mapsTo (w φ τ : ℝ) :
    MapsTo (egbFixedChargeAMeanDeficitPathRadius w φ τ) (Icc (0 : ℝ) 1)
      (Icc (egbFixedChargeASmallRadius w φ τ) (egbFixedChargeALargeRadius w φ τ)) := by
  intro u hu
  have hs := egbFixedChargeAMeanDeficitPathScale_mapsTo τ φ hu
  have hm := (egbFixedChargeAMeanRadius_pos w φ τ).le
  have hlo := mul_le_mul_of_nonneg_left hs.1 hm
  have hhi := mul_le_mul_of_nonneg_left hs.2 hm
  change egbFixedChargeASmallRadius w φ τ ≤ egbFixedChargeAMeanDeficitPathRadius w φ τ u ∧
    egbFixedChargeAMeanDeficitPathRadius w φ τ u ≤ egbFixedChargeALargeRadius w φ τ
  rw [egbFixedChargeAMeanDeficitPathRadius_mean_formula, egbFixedChargeA_small_radius_mean, egbFixedChargeA_large_radius_mean]
  constructor <;> nlinarith only [hlo, hhi]

theorem egbFixedChargeAMeanDeficitPathRadius_start (w φ τ : ℝ) :
    egbFixedChargeAMeanDeficitPathRadius w φ τ 0 = egbFixedChargeAMeanRadius w φ τ := by
  simp only [egbFixedChargeAMeanDeficitPathRadius, mul_zero, add_zero]

theorem egbFixedChargeAMeanDeficitPathRadius_end (w φ τ : ℝ) :
    egbFixedChargeAMeanDeficitPathRadius w φ τ 1 = egbFixedChargeAMiddleRadius w φ τ := by
  unfold egbFixedChargeAMeanDeficitPathRadius
  ring

theorem egbFixedChargeAMeanDeficitPathRadius_hasDerivAt (w φ τ u : ℝ) :
    HasDerivAt (egbFixedChargeAMeanDeficitPathRadius w φ τ)
      (egbFixedChargeAMeanRadius w φ τ * egbCoexistenceASymmetricRatio τ ^ (2 : ℕ) * egbFixedChargeAMiddleQuadraticShift τ φ) u := by
  rw [← egbFixedChargeAMiddleRadius_quadratic_displacement]
  unfold egbFixedChargeAMeanDeficitPathRadius
  simpa only [mul_one, id_eq] using
    ((hasDerivAt_id u).const_mul (egbFixedChargeAMiddleRadius w φ τ - egbFixedChargeAMeanRadius w φ τ)).const_add
      (egbFixedChargeAMeanRadius w φ τ)

end GaloisForLFunctions.HTGeometry
