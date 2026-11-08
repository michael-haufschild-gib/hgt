import GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap.NarainTargetAverage
import GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap.NarainMeanPrincipalPart
import GaloisForLFunctions.RHTower.CompletedFluxGradedReality

/-!
# Reality of the Narain source and remainder

Real scalar weights and conjugation-compatible integration identify the physical remainder with a real continuous logarithmic-clock function.
-/

open Complex RHTower MeasureTheory Set
open GaloisForLFunctions.BlackHoleRingdown
open GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap
set_option autoImplicit false
noncomputable section
namespace GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap

/-- Every scalar Boltzmann weight is real, including the totalized heat sum. -/
theorem narainScalarHeat_conj (ρ σ : D4BMUpperHalfPlaneCoordinate) (y : ℝ) :
    (starRingEnd ℂ) (narainScalarHeat ρ σ y) = narainScalarHeat ρ σ y := by
  unfold narainScalarHeat
  rw [← Complex.ofReal_tsum]
  exact Complex.conj_ofReal _

/-- Target averaging preserves reality without an extra interchange premise. -/
theorem narainScalarHeatAverage_conj (Y Z : Height) (y : ℝ) :
    (starRingEnd ℂ) (narainScalarHeatAverage Y Z y) = narainScalarHeatAverage Y Z y := by
  unfold narainScalarHeatAverage
  rw [← integral_conj]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [← integral_conj]
  apply integral_congr_ae
  filter_upwards [] with w
  exact narainScalarHeat_conj _ _ y

/-- The exact logarithmic constant is real by Schwarz symmetry of xi and its derivative. -/
theorem narainAverageConstant_conj (Y Z : Height) :
    (starRingEnd ℂ) (narainAverageConstant Y Z) = narainAverageConstant Y Z := by
  rw [narainAverageConstant_explicit]
  simp only [map_add, map_mul, map_sub, map_div, map_neg, map_one, map_ofNat,
    Complex.conj_ofReal, ← xi_deriv_conj, ← xi_conj]
  norm_num

/-- The actual scalar remainder as a real-valued function. -/
def narainAverageRemainderReal (Y Z : Height) (y : ℝ) : ℝ :=
  y * (narainScalarHeatAverage Y Z y).re + (3 / Real.pi) * Real.log y -
    (narainAverageConstant Y Z).re

private theorem ofReal_re_eq_of_conj {z : ℂ} (hz : (starRingEnd ℂ) z = z) :
    (z.re : ℂ) = z := by
  have hi := congrArg Complex.im hz
  apply Complex.ext
  · simp
  · simp only [Complex.ofReal_im]
    simp only [Complex.conj_im] at hi
    linarith only [hi]

/-- The real remainder is exactly the complex Mellin remainder, with no projection loss. -/
theorem ofReal_narainAverageRemainderReal (Y Z : Height) (y : ℝ) :
    (narainAverageRemainderReal Y Z y : ℂ) =
      (y : ℂ) * narainScalarHeatAverage Y Z y +
        (3 / (Real.pi : ℂ)) * (Real.log y : ℂ) - narainAverageConstant Y Z := by
  unfold narainAverageRemainderReal
  push_cast
  rw [ofReal_re_eq_of_conj (narainScalarHeatAverage_conj Y Z y),
    ofReal_re_eq_of_conj (narainAverageConstant_conj Y Z)]

/-- The logarithmic-clock remainder is continuous on the entire real clock. -/
theorem continuous_narainAverageRemainderReal_exp (Y Z : Height) :
    Continuous (fun L : ℝ => narainAverageRemainderReal Y Z (Real.exp (-L))) := by
  have hA : Continuous (fun L : ℝ => narainScalarHeatAverage Y Z (Real.exp (-L))) :=
    (continuousOn_narainScalarHeatAverage Y Z).comp_continuous
      (Real.continuous_exp.comp continuous_neg) (fun L => Real.exp_pos _)
  unfold narainAverageRemainderReal
  simp_rw [Real.log_exp]
  exact (((Real.continuous_exp.comp continuous_neg).mul hA.re).add
    (continuous_const.mul continuous_neg)).sub continuous_const

#print axioms narainScalarHeatAverage_conj
#print axioms narainAverageConstant_conj
#print axioms ofReal_narainAverageRemainderReal
#print axioms continuous_narainAverageRemainderReal_exp
end GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap
