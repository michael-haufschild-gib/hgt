import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.CausalReflection.CausalExponentialReflectionEnergy
import GaloisForLFunctions.RHTower.XiThetaSquareRateLaplace

/-!
# Exponential weights and the exact reflection defect

Weighting a causal resolvent shifts its rate. Consequently the actual
weighted L² domain is invariant under reflection, and its norm defect is
an exact positive multiple of the weighted resolvent energy.
-/

noncomputable section
open MeasureTheory Filter
open scoped Convolution

namespace GaloisForLFunctions.HTGeometry
open _root_.RHTower

/-- Weighting the literal convolution shifts the kernel rate. -/
theorem causalLaplaceWeighted_causalExponentialConvolution (a x : ℝ) (f : ℝ → ℂ) :
    causalLaplaceWeighted x (causalFourierExponential a ⋆[ContinuousLinearMap.mul ℂ ℂ] f) =
      causalFourierExponential (a + x) ⋆[ContinuousLinearMap.mul ℂ ℂ]
        causalLaplaceWeighted x f := by
  rw [causalLaplaceWeighted_convolution]
  congr 1
  funext y
  exact exp_mul_causalFourierExponential a x y

/-- The weighted reflection uses the shifted resolvent with the original coefficient. -/
theorem causalLaplaceWeighted_causalBlaschkeStep (a x : ℝ) (f : ℝ → ℂ) :
    causalLaplaceWeighted x (causalBlaschkeStep a f) = fun y =>
      -causalLaplaceWeighted x f y + (2 * a : ℂ) *
        (causalFourierExponential (a + x) ⋆[ContinuousLinearMap.mul ℂ ℂ]
          causalLaplaceWeighted x f) y := by
  have hc := congrFun (causalLaplaceWeighted_causalExponentialConvolution a x f)
  funext y
  rw [← hc y]
  unfold causalLaplaceWeighted causalBlaschkeStep
  ring

/-- Exponential resolvents preserve the actual weighted L² domain. -/
theorem memLp_weighted_causalExponentialConvolution {a x : ℝ} (hb : 0 < a + x)
    {f : ℝ → ℂ} (hf : MemLp (causalLaplaceWeighted x f) 2 volume) :
    MemLp (causalLaplaceWeighted x
      (causalFourierExponential a ⋆[ContinuousLinearMap.mul ℂ ℂ] f)) 2 volume := by
  rw [causalLaplaceWeighted_causalExponentialConvolution]
  exact memLp_causalExponentialConvolution hb hf

/-- Actual weighted square integrability is preserved by the reflected profile. -/
theorem memLp_weighted_causalBlaschkeStep {a x : ℝ} (hb : 0 < a + x)
    {f : ℝ → ℂ} (hf : MemLp (causalLaplaceWeighted x f) 2 volume) :
    MemLp (causalLaplaceWeighted x (causalBlaschkeStep a f)) 2 volume := by
  rw [causalLaplaceWeighted_causalBlaschkeStep]
  exact hf.neg.add ((memLp_causalExponentialConvolution hb hf).const_mul (2 * a : ℂ))

/-- Exact weighted norm loss for the literal causal Blaschke reflection. -/
theorem integral_weighted_causalBlaschkeStep_energy {a x : ℝ} (hb : 0 < a + x)
    {f : ℝ → ℂ} (hf : MemLp (causalLaplaceWeighted x f) 2 volume) :
    (∫ u, ‖causalLaplaceWeighted x f u‖ ^ 2) =
      (∫ u, ‖causalLaplaceWeighted x (causalBlaschkeStep a f) u‖ ^ 2) +
      (4 * a * x) * (∫ u, ‖causalLaplaceWeighted x
        (causalFourierExponential a ⋆[ContinuousLinearMap.mul ℂ ℂ] f) u‖ ^ 2) := by
  rw [causalLaplaceWeighted_causalBlaschkeStep,
    causalLaplaceWeighted_causalExponentialConvolution]
  exact integral_causalExponential_reflection_energy hb hf

end GaloisForLFunctions.HTGeometry
