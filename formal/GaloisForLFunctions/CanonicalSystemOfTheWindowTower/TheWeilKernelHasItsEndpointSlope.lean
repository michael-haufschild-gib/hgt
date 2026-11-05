import GaloisForLFunctions.CanonicalSystemOfTheWindowTower.TheWeilKernelHasFiniteRightGrowth
import GaloisForLFunctions.CanonicalSystemOfTheWindowTower.TheConstantCollarsReadTheWeilTraces

/-!
# The exact endpoint slope of the Weil kernel

The logarithmic collar floor bounds the kernel slope from above. Constant
collars with coefficients equal to the actual endpoint traces give the
matching variational lower bound.
-/

open Complex MeasureTheory Set Filter Topology
noncomputable section
namespace GaloisForLFunctions.CanonicalSystemOfTheWindowTower
open _root_.RHTower HTGeometry
open ArithmeticContinuationAndCriticalEnergy
namespace WeilHilbertBeforeContact

/-- Constant trial collars attain the endpoint energy in the lower right
derivative of the actual reproducing kernel. -/
theorem eventually_endpoint_energy_le_kernel_increment
    {a c : PrecontactAperture} (hac : a.1.1 < c.1.1) (z : ℂ)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ h : ℝ in 𝓝[>] (0 : ℝ), ∀ (b : PrecontactAperture)
      (hab : a.1.1 ≤ b.1.1), b.1.1 = a.1.1+h →
      evalEndpointEnergy a z-ε < (kernel b z z-kernel a z z).re/h := by
  let α := ∫ y : ℝ, (logarithmicCausalKernel y : ℂ) *
    (evalVectorLeftEndpointForcing a z : RealLineL2) y
  let β := ∫ y : ℝ, (logarithmicCausalKernel y : ℂ) *
    (evalVectorRightEndpointForcing a z : RealLineL2) y
  let L : ℝ → ℝ := fun h => Real.log (1/h)
  let D := 3+‖weilLogarithmicCorrection c.1‖+weilExteriorCrossingBound c.1
  let S := ‖α‖^2+‖β‖^2
  let mL : ℝ → ℂ := fun h => inner ℂ (logarithmicIntervalSource 0 h)
    (suzukiPositiveZeroExtension (evalVectorLeftCollarResidual hac.le z)) /
      ((h*Real.sqrt (L h) : ℝ) : ℂ)
  let mR : ℝ → ℂ := fun h => inner ℂ (logarithmicIntervalSource 0 h)
    (suzukiPositiveZeroExtension (evalVectorRightCollarResidual hac.le z)) /
      ((h*Real.sqrt (L h) : ℝ) : ℂ)
  have hml : Tendsto mL (𝓝[>] (0 : ℝ)) (𝓝 α) :=
    evalVectorLeftCollarResidual_mean_limit hac z
  have hmr : Tendsto mR (𝓝[>] (0 : ℝ)) (𝓝 β) :=
    evalVectorRightCollarResidual_mean_limit hac z
  have hp : Tendsto (fun h => (starRingEnd ℂ α*mL h+starRingEnd ℂ β*mR h).re)
      (𝓝[>] (0 : ℝ)) (𝓝 S) := by
    have he := (hml.const_mul (starRingEnd ℂ α)).add
      (hmr.const_mul (starRingEnd ℂ β))
    have hr := Complex.continuous_re.continuousAt.tendsto.comp he
    simpa only [Function.comp_def, ← Complex.normSq_eq_conj_mul_self,
      Complex.add_re, Complex.ofReal_re, Complex.normSq_eq_norm_sq, S] using hr
  have hL : Tendsto L (𝓝[>] (0 : ℝ)) atTop := by
    simpa only [L, one_div, Real.log_inv, Function.comp_def] using
      tendsto_neg_atBot_atTop.comp Real.tendsto_log_nhdsGT_zero
  have hD : Tendsto (fun h => 1+D/L h) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    have hi := (tendsto_inv_atTop_zero.comp hL).const_mul D
    simpa only [div_eq_mul_inv, mul_zero, add_zero, Function.comp_def] using
      tendsto_const_nhds.add hi
  let F : ℝ → ℝ := fun h =>
    2*(starRingEnd ℂ α*mL h+starRingEnd ℂ β*mR h).re-(1+D/L h)*S
  have hF : Tendsto F (𝓝[>] (0 : ℝ)) (𝓝 S) := by
    have ht := (hp.const_mul 2).sub (hD.mul_const S)
    have he : 2*S-1*S = S := by ring
    rw [he] at ht
    exact ht.congr' (Eventually.of_forall fun _ => rfl)
  have hs := hF.eventually (Ioi_mem_nhds (sub_lt_self S hε))
  filter_upwards [hs, self_mem_nhdsWithin,
    (eventually_lt_nhds (sub_pos.mpr hac)).filter_mono nhdsWithin_le_nhds,
    (eventually_lt_nhds (show (0 : ℝ) < 1 from zero_lt_one)).filter_mono nhdsWithin_le_nhds]
    with h hs hh hhc hh1
  change 0 < h at hh
  intro b hab hb
  have hbc : b.1.1 ≤ c.1.1 := by rw [hb]; linarith only [hhc]
  have hlower := constantCollar_trial_lower hab hbc hh hh1 hb z α β
  change F h ≤ (kernel b z z-kernel a z z).re/h at hlower
  exact hs.trans_le hlower

/-- The right kernel difference quotient converges to the sum of the squared
actual endpoint traces at every strictly precontact aperture. -/
theorem eventually_abs_kernel_slope_sub_endpointEnergy_lt
    {a c : PrecontactAperture} (hac : a.1.1 < c.1.1) (z : ℂ)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ h : ℝ in 𝓝[>] (0 : ℝ), ∀ (b : PrecontactAperture)
      (hab : a.1.1 ≤ b.1.1), b.1.1 = a.1.1+h →
      |(kernel b z z-kernel a z z).re/h-evalEndpointEnergy a z| < ε := by
  filter_upwards [eventually_kernel_increment_le_endpoint_energy hac z hε,
    eventually_endpoint_energy_le_kernel_increment hac z hε] with h hu hl b hab hb
  exact abs_lt.mpr ⟨by linarith only [hl b hab hb], by linarith only [hu b hab hb]⟩

#print axioms eventually_endpoint_energy_le_kernel_increment
#print axioms eventually_abs_kernel_slope_sub_endpointEnergy_lt
end WeilHilbertBeforeContact
end GaloisForLFunctions.CanonicalSystemOfTheWindowTower
