import GaloisForLFunctions.EulerFETransportTheory.TheGaussianRoughMeanSurvivesVanishingDamping
import GaloisForLFunctions.EulerFETransportTheory.ThePrimeCurrentPassesAcrossDyadicWindows
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspFinitePrimeFluxWindow
import GaloisForLFunctions.RHTower.IntervalMeanSquareTransfer

/-!
# Splitting the continued current into its prime head and rough variance

The small-prime component retains all prime powers. Its absolute admission
allows Gaussian damping to be removed uniformly in height. The rough
component is governed by its complete square mass under a smooth head probe.
-/

open Complex Filter Topology MeasureTheory RHTower
open scoped BigOperators

noncomputable section
namespace GaloisForLFunctions.EulerFETransportTheory

/-- The complete von Mangoldt component removed by the rough restriction. -/
def smallPrimeVonMangoldtCoeff (Y : ℕ) (σ : ℝ) (n : ℕ) : ℂ :=
  (woldVonMangoldtWeightedCoefficient σ n : ℂ) - roughVonMangoldtCoeff Y σ n

theorem smallPrimeVonMangoldtCoeff_zero (Y : ℕ) (σ : ℝ) :
    smallPrimeVonMangoldtCoeff Y σ 0 = 0 := by
  simp [smallPrimeVonMangoldtCoeff, woldVonMangoldtWeightedCoefficient,
    roughVonMangoldtCoeff_zero]

theorem small_add_rough_vonMangoldtCoeff (Y : ℕ) (σ : ℝ) (n : ℕ) :
    smallPrimeVonMangoldtCoeff Y σ n + roughVonMangoldtCoeff Y σ n =
      (woldVonMangoldtWeightedCoefficient σ n : ℂ) := sub_add_cancel _ _

theorem norm_smallPrimeVonMangoldtCoeff_le (Y : ℕ) (σ : ℝ) (n : ℕ) :
    ‖smallPrimeVonMangoldtCoeff Y σ n‖ ≤
      ‖(woldVonMangoldtWeightedCoefficient σ n : ℂ)‖ := by
  unfold smallPrimeVonMangoldtCoeff roughVonMangoldtCoeff
  split_ifs <;> simp [woldVonMangoldtWeightedCoefficient]

end GaloisForLFunctions.EulerFETransportTheory
