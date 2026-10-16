import GaloisForLFunctions.RHTower.PaperThetaBoundedResolvent
import GaloisForLFunctions.HTGeometry.FourierUniquenessL1

/-! # Real theta moments separate literal bounded continuous profiles

The strictly positive theta density converts native moments into the Fourier
transform of an integrable function. No spectral completeness is needed.
-/

noncomputable section
open Complex MeasureTheory Set Filter Topology
open scoped FourierTransform BoundedContinuousFunction

namespace RHTower.PaperThetaEndpoint
open HedenmalmThetaSource HedenmalmQuantile

theorem boundedThetaMoment_ext (f g : NativeContinuousSpace)
    (h : ∀ t : ℝ, boundedThetaMomentCLM (t : ℂ) f = boundedThetaMomentCLM (t : ℂ) g) :
    f = g := by
  let W : NativeContinuousSpace → ℝ → ℂ := fun v x => flatCharDensity 0 x*v x
  have hF (v : NativeContinuousSpace) (t : ℝ) :
      𝓕 (W v) t = boundedThetaMomentCLM ((-2*Real.pi*t : ℝ) : ℂ) v := by
    rw [Real.fourier_real_eq_integral_exp_smul]
    change (∫ x : ℝ, exp ((-2*Real.pi*x*t : ℝ)*I)*(W v x)) =
      ∫ x : ℝ, flatCharDensity ((-2*Real.pi*t : ℝ) : ℂ) x*v x
    apply integral_congr_ae
    filter_upwards [] with x
    have he : exp ((-2*Real.pi*x*t : ℝ)*I) =
        exp (I*((-2*Real.pi*t : ℝ) : ℂ)*(x : ℂ)) := by
      congr 1
      push_cast
      ring
    rw [he]
    dsimp [W, flatCharDensity, sourceChar]
    simp only [mul_zero, zero_mul, exp_zero, mul_one]
    ring
  have hae := HTGeometry.ae_eq_of_fourierIntegral_eq
    (integrable_boundedThetaDensity 0 f) (integrable_boundedThetaDensity 0 g)
    (fun t => (hF f t).trans ((h _).trans (hF g t).symm))
  have he := MeasureTheory.Measure.eq_of_ae_eq hae
    ((continuous_flatCharDensity 0).mul f.continuous)
    ((continuous_flatCharDensity 0).mul g.continuous)
  apply BoundedContinuousFunction.ext
  intro x
  have hx := congrFun he x
  have hn : flatCharDensity 0 x ≠ 0 := by
    simp only [flatCharDensity, sourceChar, mul_zero, zero_mul, exp_zero, mul_one]
    exact Complex.ofReal_ne_zero.mpr (thetaSource.normalized_pos x).ne'
  exact mul_left_cancel₀ hn hx

end RHTower.PaperThetaEndpoint
