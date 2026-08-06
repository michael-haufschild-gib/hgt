import GaloisForLFunctions.HTGeometry.GaussianRadialPolarLaw
import Mathlib.Analysis.Fourier.RiemannLebesgueLemma

/-!
# The universal radial Fourier kernel of a Gaussian observer

The Fourier transform of the Gaussian radial density is the universal multiplier
attached to a dimensionless observer--spectral action.  It equals one at zero
action, it is exactly the Gaussian average of the corresponding radial character,
and by the Riemann--Lebesgue lemma it vanishes as the action leaves every compact
set.
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal Real

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The Gaussian radial density extended by zero off the positive half-line. -/
def gaussianRadialDensityExt (m : ℕ) : ℝ → ℝ :=
  (Ioi (0 : ℝ)).indicator (gaussianRadialDensity m)

/-- **Universal radial action kernel.**  The Fourier transform of the Gaussian
radial density, evaluated at a dimensionless observer--spectral action. -/
def radialActionKernel (m : ℕ) (u : ℝ) : ℂ :=
  ∫ y : ℝ, Complex.exp (-((u * y : ℝ) : ℂ) * Complex.I)
    * (gaussianRadialDensityExt m y : ℂ)

/-- The radial kernel is exactly the Gaussian average of the radial character. -/
theorem radialActionKernel_eq_integral_stdGaussian {m : ℕ} (hm : 0 < m) (u : ℝ) :
    radialActionKernel m u
      = ∫ x, Complex.exp (-((u * ‖x‖ : ℝ) : ℂ) * Complex.I)
          ∂(stdGaussian (EuclideanSpace ℝ (Fin m))) := by
  rw [integral_stdGaussian_fun_norm hm
    (fun y => Complex.exp (-((u * y : ℝ) : ℂ) * Complex.I))]
  rw [radialActionKernel, ← integral_indicator measurableSet_Ioi]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  dsimp only
  by_cases hy : y ∈ Ioi (0 : ℝ)
  · rw [Set.indicator_of_mem hy, gaussianRadialDensityExt,
      Set.indicator_of_mem hy, Complex.real_smul]
    ring
  · rw [Set.indicator_of_notMem hy, gaussianRadialDensityExt,
      Set.indicator_of_notMem hy]
    simp

/-- Zero action is perfectly locked. -/
theorem radialActionKernel_zero {m : ℕ} (hm : 0 < m) :
    radialActionKernel m 0 = 1 := by
  rw [radialActionKernel_eq_integral_stdGaussian hm]
  simp

/-- Division by a positive constant is cocompact-to-cocompact on the line. -/
theorem tendsto_div_const_cocompact {c : ℝ} (hc : 0 < c) :
    Tendsto (fun u : ℝ => u / c) (cocompact ℝ) (cocompact ℝ) := by
  rw [cocompact_eq_atBot_atTop, tendsto_sup]
  constructor
  · exact le_sup_of_le_left (Filter.Tendsto.atBot_div_const hc tendsto_id)
  · exact le_sup_of_le_right (Filter.Tendsto.atTop_div_const hc tendsto_id)

/-- **Radial dephasing.**  The radial action kernel vanishes as the action leaves
every compact set. -/
theorem tendsto_radialActionKernel_cocompact (m : ℕ) :
    Tendsto (radialActionKernel m) (cocompact ℝ) (𝓝 0) := by
  have hfourier := Real.tendsto_integral_exp_smul_cocompact
    (fun y : ℝ => ((gaussianRadialDensityExt m y : ℝ) : ℂ))
  have hcomp := hfourier.comp (tendsto_div_const_cocompact
    (c := 2 * Real.pi) (by positivity))
  refine hcomp.congr fun u => ?_
  rw [Function.comp_apply, radialActionKernel]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  dsimp only
  rw [Circle.smul_def, Real.fourierChar_apply]
  congr 2
  push_cast
  field_simp

end

end GaloisForLFunctions.HTGeometry
