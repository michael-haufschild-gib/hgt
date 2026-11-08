import GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap.NarainMeanBoundaryExponential
import GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap.NarainMeanSchwartzSource

/-!
# Holomorphic extension of the Narain source clock

Exponential Mellin-boundary decay gives a fixed holomorphic strip. The extension equals the exact physical remainder on the real clock.
-/

open Complex RHTower MeasureTheory
open GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap
set_option autoImplicit false
noncomputable section
namespace GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap

/-- The actual normalized source clock extended to complex logarithmic frequency. -/
def narainMeanComplexClock (Y Z : Height) (z : ℂ) : ℂ :=
  (1 / (2 * (Real.pi : ℂ))) *
    expFourier (fun t : ℝ => narainMellinMean Y Z ((t : ℂ) * I)) (-z)

/-- The extension retains the exact Fourier sign and inverse-Mellin constant. -/
theorem narainMeanComplexClock_eq_integral (Y Z : Height) (z : ℂ) :
    narainMeanComplexClock Y Z z = (1 / (2 * (Real.pi : ℂ))) *
      ∫ t : ℝ, Complex.exp (z * ((t : ℂ) * I)) * narainMellinMean Y Z ((t : ℂ) * I) := by
  unfold narainMeanComplexClock expFourier
  congr 1
  apply integral_congr_ae
  filter_upwards [] with t
  rw [mul_comm]
  congr 2
  ring

/-- Exponential spectral decay makes the actual complex clock holomorphic in a fixed strip. -/
theorem analyticAt_narainMeanComplexClock (Y Z : Height) {z : ℂ}
    (hz : |z.im| < Real.pi / 4) : AnalyticAt ℂ (narainMeanComplexClock Y Z) z := by
  obtain ⟨C, hC, hb⟩ := exists_narainMeanBoundary_exponential_bound Y Z
  have hc : Continuous (fun t : ℝ => narainMellinMean Y Z ((t : ℂ) * I)) := by
    simpa using continuous_narainMellinMean_vertical Y Z (a := 0) le_rfl (by norm_num)
  have ha := analyticOnNhd_expFourier (ε := Real.pi / 4) hc.aestronglyMeasurable hC
    (fun t => by simpa only [div_mul_eq_mul_div] using hb t)
  have hn : AnalyticAt ℂ
      (fun z : ℂ => expFourier (fun t : ℝ => narainMellinMean Y Z ((t : ℂ) * I)) (-z)) z :=
    AnalyticAt.comp (g := expFourier (fun t : ℝ => narainMellinMean Y Z ((t : ℂ) * I)))
      (f := fun z : ℂ => -z) (x := z) (ha (-z) (by simpa using hz)) (by fun_prop)
  exact analyticAt_const.mul hn

/-- On the real axis the complex extension is the literal physical clock remainder. -/
theorem narainMeanComplexClock_ofReal (Y Z : Height) (L : ℝ) :
    narainMeanComplexClock Y Z (L : ℂ) = narainMeanClockSchwartz Y Z L := by
  rw [narainMeanClockSchwartz, GaloisForLFunctions.HTGeometry.schwartzScale_apply,
    neg_one_mul, narainMeanFourierSchwartz_apply, narainMeanBoundaryFourier_eq_integral,
    narainMeanComplexClock_eq_integral]
  simp only [Complex.ofReal_neg, neg_neg, Complex.ofReal_div, Complex.ofReal_one,
    Complex.ofReal_mul, Complex.ofReal_ofNat]

#print axioms narainMeanComplexClock_eq_integral
#print axioms analyticAt_narainMeanComplexClock
#print axioms narainMeanComplexClock_ofReal
end GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap
