import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAGibbsKernel

/-!
# Positive paths from the large phase to every interior radius

A sine endpoint gives a closed-data family covering the full phase
interval. Each affine path stays at positive radius, so the actual Gibbs
function and its derivative are available on the entire path.
-/
noncomputable section
open Real Filter Set MeasureTheory
open scoped Topology
namespace GaloisForLFunctions.HTGeometry

def egbFixedChargeAInteriorPathCoordinate (ψ u : ℝ) : ℝ := 1 + (sin ψ - 1) * u

def egbFixedChargeAInteriorPathRadius (w φ τ ψ u : ℝ) : ℝ :=
  egbFixedChargeALargeRadius w φ τ +
    (egbFixedChargeAInteriorRadius w φ τ ψ - egbFixedChargeALargeRadius w φ τ) * u

def egbFixedChargeAInteriorGibbsGap (w φ τ l ψ : ℝ) : ℝ :=
  egbOffShellGibbsA (egbFixedChargeAPressure w φ τ) (egbFixedChargeATemperature w φ τ)
    (exp w * cos φ) (exp w * sin φ) l (egbFixedChargeAInteriorRadius w φ τ ψ) -
  egbOffShellGibbsA (egbFixedChargeAPressure w φ τ) (egbFixedChargeATemperature w φ τ)
    (exp w * cos φ) (exp w * sin φ) l (egbFixedChargeALargeRadius w φ τ)

theorem egbFixedChargeAInteriorPathCoordinate_mapsTo (ψ : ℝ) :
    MapsTo (egbFixedChargeAInteriorPathCoordinate ψ) (Icc (0 : ℝ) 1) (Icc (-1 : ℝ) 1) := by
  intro u hu
  have hlo := neg_one_le_sin ψ
  have hhi := sin_le_one ψ
  change -1 ≤ 1 + (sin ψ - 1) * u ∧ 1 + (sin ψ - 1) * u ≤ 1
  have hprodlo := mul_nonneg (show 0 ≤ sin ψ + 1 by linarith) hu.1
  have hprodhi := mul_nonneg (show 0 ≤ 1 - sin ψ by linarith) hu.1
  constructor <;> nlinarith only [hprodlo, hprodhi, hu.2]

theorem egbFixedChargeAInteriorPathCoordinate_start (ψ : ℝ) : egbFixedChargeAInteriorPathCoordinate ψ 0 = 1 := by
  simp only [egbFixedChargeAInteriorPathCoordinate, mul_zero, add_zero]

theorem egbFixedChargeAInteriorPathCoordinate_end (ψ : ℝ) : egbFixedChargeAInteriorPathCoordinate ψ 1 = sin ψ := by
  unfold egbFixedChargeAInteriorPathCoordinate
  ring

theorem egbFixedChargeAInteriorPathRadius_mean_formula (w φ τ ψ u : ℝ) :
    egbFixedChargeAInteriorPathRadius w φ τ ψ u = egbFixedChargeAMeanRadius w φ τ *
      (1 + egbCoexistenceASymmetricRatio τ * egbFixedChargeAInteriorPathCoordinate ψ u) := by
  unfold egbFixedChargeAInteriorPathRadius egbFixedChargeAInteriorRadius egbFixedChargeAInteriorPathCoordinate
  rw [egbFixedChargeA_large_radius_mean]
  ring

theorem egbFixedChargeAInteriorPathScale_mapsTo (τ ψ : ℝ) :
    MapsTo (fun u => 1 + egbCoexistenceASymmetricRatio τ * egbFixedChargeAInteriorPathCoordinate ψ u)
      (Icc (0 : ℝ) 1) (Icc (1 - egbCoexistenceASymmetricRatio τ) (1 + egbCoexistenceASymmetricRatio τ)) := by
  intro u hu
  exact egbFixedChargeAInteriorScale_mapsTo τ (egbFixedChargeAInteriorPathCoordinate_mapsTo ψ hu)

theorem egbFixedChargeAInteriorPathRadius_mapsTo (w φ τ ψ : ℝ) :
    MapsTo (egbFixedChargeAInteriorPathRadius w φ τ ψ) (Icc (0 : ℝ) 1)
      (Icc (egbFixedChargeASmallRadius w φ τ) (egbFixedChargeALargeRadius w φ τ)) := by
  intro u hu
  have hs := egbFixedChargeAInteriorPathScale_mapsTo τ ψ hu
  have hm := (egbFixedChargeAMeanRadius_pos w φ τ).le
  have hlo := mul_le_mul_of_nonneg_left hs.1 hm
  have hhi := mul_le_mul_of_nonneg_left hs.2 hm
  change egbFixedChargeASmallRadius w φ τ ≤ egbFixedChargeAInteriorPathRadius w φ τ ψ u ∧
    egbFixedChargeAInteriorPathRadius w φ τ ψ u ≤ egbFixedChargeALargeRadius w φ τ
  rw [egbFixedChargeAInteriorPathRadius_mean_formula, egbFixedChargeA_small_radius_mean, egbFixedChargeA_large_radius_mean]
  constructor <;> nlinarith only [hlo, hhi]

theorem egbFixedChargeAInteriorPathRadius_start (w φ τ ψ : ℝ) :
    egbFixedChargeAInteriorPathRadius w φ τ ψ 0 = egbFixedChargeALargeRadius w φ τ := by
  simp only [egbFixedChargeAInteriorPathRadius, mul_zero, add_zero]

theorem egbFixedChargeAInteriorPathRadius_end (w φ τ ψ : ℝ) :
    egbFixedChargeAInteriorPathRadius w φ τ ψ 1 = egbFixedChargeAInteriorRadius w φ τ ψ := by
  unfold egbFixedChargeAInteriorPathRadius
  ring

theorem egbFixedChargeAInteriorPath_displacement (w φ τ ψ : ℝ) :
    egbFixedChargeAInteriorRadius w φ τ ψ - egbFixedChargeALargeRadius w φ τ =
      egbFixedChargeAMeanRadius w φ τ * egbCoexistenceASymmetricRatio τ * (sin ψ - 1) := by
  unfold egbFixedChargeAInteriorRadius
  rw [egbFixedChargeA_large_radius_mean]
  ring

theorem egbFixedChargeAInteriorPathCoordinate_hasDerivAt (ψ u : ℝ) :
    HasDerivAt (egbFixedChargeAInteriorPathCoordinate ψ) (sin ψ - 1) u := by
  unfold egbFixedChargeAInteriorPathCoordinate
  simpa only [mul_one, id_eq] using ((hasDerivAt_id u).const_mul (sin ψ - 1)).const_add 1

theorem egbFixedChargeAInteriorPathRadius_hasDerivAt (w φ τ ψ u : ℝ) :
    HasDerivAt (egbFixedChargeAInteriorPathRadius w φ τ ψ)
      (egbFixedChargeAMeanRadius w φ τ * egbCoexistenceASymmetricRatio τ * (sin ψ - 1)) u := by
  rw [← egbFixedChargeAInteriorPath_displacement]
  unfold egbFixedChargeAInteriorPathRadius
  simpa only [mul_one, id_eq] using
    ((hasDerivAt_id u).const_mul (egbFixedChargeAInteriorRadius w φ τ ψ - egbFixedChargeALargeRadius w φ τ)).const_add
      (egbFixedChargeALargeRadius w φ τ)

end GaloisForLFunctions.HTGeometry
