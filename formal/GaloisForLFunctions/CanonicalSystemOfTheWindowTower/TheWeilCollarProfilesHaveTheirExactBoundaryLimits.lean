import GaloisForLFunctions.CanonicalSystemOfTheWindowTower.TheExteriorWeilResponseHasItsScaledBoundaryLimit
import GaloisForLFunctions.CanonicalSystemOfTheWindowTower.ThePrimeAndPolarWeilResponsesAreContinuous

/-!
# Exact boundary limits of the full Weil collar profiles

The literal evaluation exponential and finite prime-polar response are
continuous at each old endpoint. After division by the square-root
logarithmic scale, only the exterior Gamma response remains. The full
collar profile therefore has the exact normalized endpoint readout, also
in mean square after dilation.
-/

open Complex MeasureTheory Set Filter Topology
noncomputable section
namespace GaloisForLFunctions.CanonicalSystemOfTheWindowTower
open _root_.RHTower HTGeometry

private theorem continuous_div_sqrt_log_tendsto_zero {f : ℝ → ℂ}
    (hf : ContinuousAt f 0) :
    Tendsto (fun d : ℝ => f d/(Real.sqrt (Real.log (1/d)) : ℂ))
      (𝓝[>] (0 : ℝ)) (nhds 0) := by
  have hlog : Tendsto (fun d : ℝ => Real.log (1/d)) (𝓝[>] (0 : ℝ)) atTop := by
    simpa only [one_div, Real.log_inv, Function.comp_def] using
      tendsto_neg_atBot_atTop.comp Real.tendsto_log_nhdsGT_zero
  have hinv := Complex.continuous_ofReal.continuousAt.tendsto.comp
    (tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp hlog))
  have h := (hf.tendsto.mono_left nhdsWithin_le_nhds).mul hinv
  simpa only [Function.comp_def, Complex.ofReal_zero, Complex.ofReal_inv, mul_zero,
    div_eq_mul_inv] using h

namespace WeilHilbertBeforeContact

/-- The literal right collar residual, with every prime and polar contribution retained. -/
def evalVectorRightCollarProfile (a : PrecontactAperture) (b : SuzukiPositiveAperture)
    (hab : a.1.1 ≤ b.1) (z : ℂ) (d : ℝ) : ℂ :=
  Complex.exp (-I*(starRingEnd ℂ z)*((a.1.1+d : ℝ) : ℂ)) -
    evalVectorRemainderProfile a b hab z (a.1.1+d) - evalVectorRightExteriorResponse a z d

/-- The reflected left collar residual uses the same full bounded remainder. -/
def evalVectorLeftCollarProfile (a : PrecontactAperture) (b : SuzukiPositiveAperture)
    (hab : a.1.1 ≤ b.1) (z : ℂ) (d : ℝ) : ℂ :=
  Complex.exp (-I*(starRingEnd ℂ z)*((-a.1.1-d : ℝ) : ℂ)) -
    evalVectorRemainderProfile a b hab z (-a.1.1-d) - evalVectorLeftExteriorResponse a z d

private theorem continuous_rightRegularProfile (a : PrecontactAperture) (b : SuzukiPositiveAperture)
    (hab : a.1.1 ≤ b.1) (z : ℂ) :
    Continuous (fun d : ℝ => Complex.exp (-I*(starRingEnd ℂ z)*((a.1.1+d : ℝ) : ℂ)) -
      evalVectorRemainderProfile a b hab z (a.1.1+d)) := by
  exact (by fun_prop : Continuous (fun d : ℝ =>
    Complex.exp (-I*(starRingEnd ℂ z)*((a.1.1+d : ℝ) : ℂ)))).sub
      ((continuous_evalVectorRemainderProfile a b hab z).comp (by fun_prop))

private theorem continuous_leftRegularProfile (a : PrecontactAperture) (b : SuzukiPositiveAperture)
    (hab : a.1.1 ≤ b.1) (z : ℂ) :
    Continuous (fun d : ℝ => Complex.exp (-I*(starRingEnd ℂ z)*((-a.1.1-d : ℝ) : ℂ)) -
      evalVectorRemainderProfile a b hab z (-a.1.1-d)) := by
  exact (by fun_prop : Continuous (fun d : ℝ =>
    Complex.exp (-I*(starRingEnd ℂ z)*((-a.1.1-d : ℝ) : ℂ)))).sub
      ((continuous_evalVectorRemainderProfile a b hab z).comp (by fun_prop))

theorem measurable_evalVectorRightCollarProfile (a : PrecontactAperture) (b : SuzukiPositiveAperture)
    (hab : a.1.1 ≤ b.1) (z : ℂ) : Measurable (evalVectorRightCollarProfile a b hab z) :=
  (continuous_rightRegularProfile a b hab z).measurable.sub
    (measurable_evalVectorRightExteriorResponse a z)

theorem measurable_evalVectorLeftCollarProfile (a : PrecontactAperture) (b : SuzukiPositiveAperture)
    (hab : a.1.1 ≤ b.1) (z : ℂ) : Measurable (evalVectorLeftCollarProfile a b hab z) :=
  (continuous_leftRegularProfile a b hab z).measurable.sub
    (measurable_evalVectorLeftExteriorResponse a z)

/-- The right full profile has exactly the actual right endpoint readout. -/
theorem evalVectorRightCollarProfile_normalized_limit (a : PrecontactAperture)
    (b : SuzukiPositiveAperture) (hab : a.1.1 ≤ b.1) (z : ℂ) :
    Tendsto (fun d : ℝ => evalVectorRightCollarProfile a b hab z d /
      (Real.sqrt (Real.log (1/d)) : ℂ)) (𝓝[>] (0 : ℝ))
      (nhds (∫ y : ℝ, (logarithmicCausalKernel y : ℂ)*
        (evalVectorRightEndpointForcing a z : RealLineL2) y)) := by
  have h := (continuous_div_sqrt_log_tendsto_zero
    (continuous_rightRegularProfile a b hab z).continuousAt).sub
      (evalVectorRightExteriorResponse_normalized_limit a z)
  simp only [zero_sub, neg_neg] at h
  convert h using 1
  funext d
  unfold evalVectorRightCollarProfile
  ring

/-- The left full profile has exactly the actual left endpoint readout. -/
theorem evalVectorLeftCollarProfile_normalized_limit (a : PrecontactAperture)
    (b : SuzukiPositiveAperture) (hab : a.1.1 ≤ b.1) (z : ℂ) :
    Tendsto (fun d : ℝ => evalVectorLeftCollarProfile a b hab z d /
      (Real.sqrt (Real.log (1/d)) : ℂ)) (𝓝[>] (0 : ℝ))
      (nhds (∫ y : ℝ, (logarithmicCausalKernel y : ℂ)*
        (evalVectorLeftEndpointForcing a z : RealLineL2) y)) := by
  have h := (continuous_div_sqrt_log_tendsto_zero
    (continuous_leftRegularProfile a b hab z).continuousAt).sub
      (evalVectorLeftExteriorResponse_normalized_limit a z)
  simp only [zero_sub, neg_neg] at h
  convert h using 1
  funext d
  unfold evalVectorLeftCollarProfile
  ring

/-- Dilation of the right full collar profile converges in L² to the actual constant trace. -/
theorem evalVectorRightCollarProfile_scaled_mean_square (a : PrecontactAperture)
    (b : SuzukiPositiveAperture) (hab : a.1.1 ≤ b.1) (z : ℂ) :
    Tendsto (fun h : ℝ => ∫ s in Ioc (0 : ℝ) 1,
      ‖evalVectorRightCollarProfile a b hab z (h*s)/(Real.sqrt (Real.log (1/h)) : ℂ) -
        (∫ y : ℝ, (logarithmicCausalKernel y : ℂ)*
          (evalVectorRightEndpointForcing a z : RealLineL2) y)‖^2)
      (𝓝[>] (0 : ℝ)) (nhds 0) :=
  logarithmic_boundary_limit_in_mean_square (measurable_evalVectorRightCollarProfile a b hab z)
    (evalVectorRightCollarProfile_normalized_limit a b hab z)

/-- Dilation of the left full collar profile has the same exact L² boundary law. -/
theorem evalVectorLeftCollarProfile_scaled_mean_square (a : PrecontactAperture)
    (b : SuzukiPositiveAperture) (hab : a.1.1 ≤ b.1) (z : ℂ) :
    Tendsto (fun h : ℝ => ∫ s in Ioc (0 : ℝ) 1,
      ‖evalVectorLeftCollarProfile a b hab z (h*s)/(Real.sqrt (Real.log (1/h)) : ℂ) -
        (∫ y : ℝ, (logarithmicCausalKernel y : ℂ)*
          (evalVectorLeftEndpointForcing a z : RealLineL2) y)‖^2)
      (𝓝[>] (0 : ℝ)) (nhds 0) :=
  logarithmic_boundary_limit_in_mean_square (measurable_evalVectorLeftCollarProfile a b hab z)
    (evalVectorLeftCollarProfile_normalized_limit a b hab z)

#print axioms evalVectorRightCollarProfile_normalized_limit
#print axioms evalVectorLeftCollarProfile_normalized_limit
#print axioms evalVectorRightCollarProfile_scaled_mean_square
#print axioms evalVectorLeftCollarProfile_scaled_mean_square
end WeilHilbertBeforeContact
end GaloisForLFunctions.CanonicalSystemOfTheWindowTower
