import GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap.NarainMeanMellinTail
import GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap.NarainAverageBoundaryRate
import GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap.NarainAverageDecay

/-!
# The regularized small-height Narain source

Removing the actual large-height tail gives a source supported below height one and its exact regularized Mellin transform.
-/

open Complex RHTower MeasureTheory Set Filter Topology Asymptotics
open GaloisForLFunctions.BlackHoleRingdown
open GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap
set_option autoImplicit false
noncomputable section
namespace GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap

/-- The actual logarithmically subtracted source with its large-height tail removed. -/
def narainMeanSmallSource (Y Z : Height) (y : ℝ) : ℂ :=
  narainAverageRemainder Y Z (-(3 / (Real.pi : ℂ))) (narainAverageConstant Y Z) y -
    narainMeanTailSource Y Z y

/-- The small-height continuation subtracts the entire large-height tail from the regular part. -/
def narainMeanSmallMellin (Y Z : Height) (s : ℂ) : ℂ :=
  narainMellinMeanRegularPart Y Z (s - 1 / 2) - narainMeanMellinTail Y Z s

/-- On the unit height interval the cutoff source is the normalized physical remainder. -/
theorem narainMeanSmallSource_of_le_one (Y Z : Height) {y : ℝ} (hy : 0 < y) (hy₁ : y ≤ 1) :
    narainMeanSmallSource Y Z y =
      ((y : ℂ) * narainScalarHeatAverage Y Z y +
        (3 / (Real.pi : ℂ)) * (Real.log y : ℂ) - narainAverageConstant Y Z) / (y : ℂ) := by
  rw [narainMeanSmallSource, narainAverageRemainder, scalarMellinMainTerm,
    indicator_of_mem (show y ∈ Ioc (0 : ℝ) 1 from ⟨hy, hy₁⟩),
    narainMeanTailSource, indicator_of_notMem (show y ∉ Ioi (1 : ℝ) from not_lt.mpr hy₁),
    sub_zero]
  field_simp [Complex.ofReal_ne_zero.mpr hy.ne']
  ring

/-- Removing the actual tail makes the source vanish above height one. -/
theorem narainMeanSmallSource_of_one_lt (Y Z : Height) {y : ℝ} (hy : 1 < y) :
    narainMeanSmallSource Y Z y = 0 := by
  simp [narainMeanSmallSource, narainAverageRemainder, scalarMellinMainTerm,
    narainMeanTailSource, not_le.mpr hy, hy]

/-- The unconditional square-root remainder gives absolute Mellin convergence to its boundary. -/
theorem mellinConvergent_narainMeanSmallSource (Y Z : Height) {s : ℂ} (hs : 1 / 2 < s.re) :
    MellinConvergent (narainMeanSmallSource Y Z) s := by
  have hrate : (fun y : ℝ => (y : ℂ) * narainScalarHeatAverage Y Z y -
      (-(3 / (Real.pi : ℂ)) * (Real.log y : ℂ) + narainAverageConstant Y Z))
      =O[𝓝[>] 0] (fun y : ℝ => y ^ ((1 : ℝ) / 2)) := by
    simpa only [neg_mul, sub_add_eq_sub_sub, sub_neg_eq_add] using
      (narainScalarHeatAverage_boundary_rate Y Z).isBigO
  obtain ⟨c, hc, htop⟩ := exists_isBigO_narainAverageRemainder_exp
    Y Z (-(3 / (Real.pi : ℂ))) (narainAverageConstant Y Z)
  have hrem : MellinConvergent (narainAverageRemainder Y Z
      (-(3 / (Real.pi : ℂ))) (narainAverageConstant Y Z)) s :=
    mellinConvergent_of_isBigO_rpow_exp hc
    (locallyIntegrableOn_narainAverageRemainder Y Z _ _) htop
    (isBigO_narainAverageRemainder_bot Y Z hrate) (by linarith only [hs])
  exact (hasMellin_sub hrem (mellinConvergent_narainMeanTailSource Y Z s)).1

/-- The actual cutoff source has the pole-preserving regularized Mellin transform. -/
theorem hasMellin_narainMeanSmallSource (Y Z : Height) {s : ℂ} (hs : 1 < s.re) :
    HasMellin (narainMeanSmallSource Y Z) s (narainMeanSmallMellin Y Z s) := by
  have hmain := hasMellin_scalarMellinMainTerm
    (-(3 / (Real.pi : ℂ))) (narainAverageConstant Y Z) hs
  have hrem := hasMellin_sub (mellinConvergent_narainScalarHeatAverage Y Z hs) hmain.1
  have hsmall := hasMellin_sub hrem.1 (mellinConvergent_narainMeanTailSource Y Z s)
  have hne : s - 1 / 2 ≠ (1 / 2 : ℂ) := by
    intro h
    have hr := congrArg Complex.re h
    norm_num at hr
    linarith only [hs, hr]
  have hpart := narainMellinMean_principalPart Y Z hne
  have hregular : mellin (narainAverageRemainder Y Z
      (-(3 / (Real.pi : ℂ))) (narainAverageConstant Y Z)) s =
        narainMellinMeanRegularPart Y Z (s - 1 / 2) := by
    calc
      _ = mellin (narainScalarHeatAverage Y Z) s -
          mellin (scalarMellinMainTerm (-(3 / (Real.pi : ℂ))) (narainAverageConstant Y Z)) s := hrem.2
      _ = _ := by
        rw [mellin_narainScalarHeatAverage Y Z hs, hmain.2, hpart,
          show s - 1 / 2 - 1 / 2 = s - 1 by ring]
        ring
  refine ⟨hsmall.1, ?_⟩
  change mellin (narainMeanSmallSource Y Z) s =
    narainMellinMeanRegularPart Y Z (s - 1 / 2) - narainMeanMellinTail Y Z s
  calc
    _ = mellin (narainAverageRemainder Y Z
        (-(3 / (Real.pi : ℂ))) (narainAverageConstant Y Z)) s -
        narainMeanMellinTail Y Z s := hsmall.2
    _ = _ := by rw [hregular]

#print axioms mellinConvergent_narainMeanSmallSource
#print axioms hasMellin_narainMeanSmallSource
end GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap
