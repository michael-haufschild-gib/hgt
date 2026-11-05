import GaloisForLFunctions.CanonicalSystemOfTheWindowTower.TheWeilRieszVectorsHaveNormalizedEndpointTraces
import GaloisForLFunctions.HTGeometry.QuasiPolynomialLaplaceCalculus

/-!
# The normalized Weil trace determines its truncated exterior integral

The substitution `t = exp(-s²)` turns the logarithmically normalized
endpoint profile into an ordinary Cesàro integrand. Its limiting average
is the exact coefficient of the truncated exterior logarithmic kernel.
-/

open MeasureTheory Set Filter Topology Complex
noncomputable section
namespace GaloisForLFunctions.CanonicalSystemOfTheWindowTower
open _root_.RHTower HTGeometry

private theorem tendsto_complex_average {F : ℝ → ℂ} (hF : Continuous F) {c : ℂ}
    (hc : Tendsto F atTop (nhds c)) :
    Tendsto (fun S : ℝ => (S : ℂ)⁻¹ * ∫ s in (0 : ℝ)..S, F s) atTop (nhds c) := by
  have hzero := HTGeometry.QuasiPolynomial.tendsto_average_of_tendsto_zero
    (f := fun s => F s-c) (hF.sub continuous_const)
    (by simpa only [sub_self] using hc.sub_const c)
  have h := hzero.add_const c
  simp only [zero_add] at h
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with S hS
  rw [intervalIntegral.integral_sub (hF.intervalIntegrable _ _)
    (continuous_const.intervalIntegrable _ _), intervalIntegral.integral_const]
  simp only [sub_zero, Complex.real_smul]
  field_simp [(Complex.ofReal_ne_zero.mpr hS.ne')]
  ring

private theorem tendsto_exp_neg_sq_zero :
    Tendsto (fun S : ℝ => Real.exp (-(S ^ 2))) atTop (𝓝[>] (0 : ℝ)) := by
  have hs : Tendsto (fun S : ℝ => S ^ 2) atTop atTop := by
    apply tendsto_atTop.mpr
    intro B
    filter_upwards [eventually_ge_atTop (max (1 : ℝ) B)] with S hS
    have h1 := (le_max_left (1 : ℝ) B).trans hS
    have hB := (le_max_right (1 : ℝ) B).trans hS
    nlinarith only [h1, hB, sq_nonneg (S-1)]
  rw [nhdsWithin]
  exact tendsto_inf.mpr ⟨Real.tendsto_exp_neg_atTop_nhds_zero.comp hs,
    tendsto_principal.mpr (Eventually.of_forall fun S => Real.exp_pos _)⟩

private theorem truncated_logarithmic_integral_eq {u : ℝ → ℂ} (hu : Continuous u) (S : ℝ) :
    (∫ s in (0 : ℝ)..S, (s : ℂ) * u (Real.exp (-(s ^ 2)))) =
      ∫ t in Real.exp (-(S ^ 2))..1, u t / (2 * (t : ℂ)) := by
  let f : ℝ → ℝ := fun s => Real.exp (-(s ^ 2))
  let f' : ℝ → ℝ := fun s => -2 * s * Real.exp (-(s ^ 2))
  let g : ℝ → ℂ := fun t => u t / (2 * (t : ℂ))
  have hd (s : ℝ) : HasDerivAt f (f' s) s := by
    convert (((hasDerivAt_id s).pow 2).neg.exp) using 1 <;>
      simp only [f, f', Pi.neg_apply, Pi.pow_apply, id_eq, mul_one]
    ring
  have hg : ContinuousOn g (f '' uIcc 0 S) := by
    apply hu.continuousOn.div (by fun_prop)
    rintro t ⟨s, hs, rfl⟩
    exact mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne')
  have h := intervalIntegral.integral_deriv_smul_comp'
    (a := 0) (b := S) (fun s _ => hd s) (by dsimp [f']; fun_prop) hg
  have he : (fun s : ℝ => f' s • (g ∘ f) s) =
      fun s : ℝ => -((s : ℂ) * u (Real.exp (-(s ^ 2)))) := by
    funext s
    dsimp only [f', g, f, Function.comp_apply]
    rw [Complex.real_smul]
    push_cast
    field_simp [Complex.ofReal_ne_zero.mpr (Real.exp_pos (-(s^2))).ne']
  rw [he, intervalIntegral.integral_neg] at h
  have h0 : f 0 = 1 := by simp only [f, zero_pow (by norm_num : (2 : ℕ) ≠ 0), neg_zero, Real.exp_zero]
  rw [h0] at h
  have hr : (∫ t in (1 : ℝ)..f S, g t) = -(∫ t in f S..1, g t) := by
    rw [intervalIntegral.integral_symm]
  rw [hr] at h
  exact neg_injective h

/-- A finite normalized logarithmic trace determines the leading truncated exterior integral. -/
theorem truncated_logarithmic_integral_normalized_limit {u : ℝ → ℂ} (hu : Continuous u) {τ : ℂ}
    (hτ : Tendsto (fun t : ℝ => u t * (Real.sqrt (Real.log (1/t)) : ℂ))
      (𝓝[>] (0 : ℝ)) (nhds τ)) :
    Tendsto (fun d : ℝ => (∫ t in d..1, u t / (2 * (t : ℂ))) /
      (Real.sqrt (Real.log (1/d)) : ℂ)) (𝓝[>] (0 : ℝ)) (nhds τ) := by
  have hprofile : Tendsto (fun S : ℝ => (S : ℂ) * u (Real.exp (-(S^2)))) atTop (nhds τ) := by
    have h := hτ.comp tendsto_exp_neg_sq_zero
    apply h.congr'
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with S hS
    simp only [Function.comp_apply, one_div, Real.log_inv, Real.log_exp, neg_neg,
      Real.sqrt_sq hS.le]
    exact mul_comm _ _
  have havg := tendsto_complex_average
    (F := fun S : ℝ => (S : ℂ) * u (Real.exp (-(S^2)) )) (by fun_prop) hprofile
  have he : (fun S : ℝ => (S : ℂ)⁻¹ * ∫ s in (0 : ℝ)..S,
      (s : ℂ) * u (Real.exp (-(s^2)))) =
      (fun S : ℝ => (∫ t in Real.exp (-(S^2))..1, u t / (2 * (t : ℂ))) / (S : ℂ)) := by
    funext S
    rw [truncated_logarithmic_integral_eq hu, div_eq_mul_inv, mul_comm]
  rw [he] at havg
  have hlog : Tendsto (fun d : ℝ => Real.log (1/d)) (𝓝[>] (0 : ℝ)) atTop := by
    simpa only [one_div, Real.log_inv, Function.comp_def] using
      tendsto_neg_atBot_atTop.comp Real.tendsto_log_nhdsGT_zero
  have h := havg.comp (Real.tendsto_sqrt_atTop.comp hlog)
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin,
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds] with d hd hd1
  change (0 : ℝ) < d at hd
  have hl : 0 ≤ Real.log (1/d) := Real.log_nonneg (by rw [le_div_iff₀ hd]; linarith only [hd1])
  dsimp only [Function.comp_apply]
  rw [Real.sq_sqrt hl, one_div, Real.log_inv, neg_neg, Real.exp_log hd]

namespace WeilHilbertBeforeContact

/-- The actual right endpoint readout is the coefficient of its truncated exterior logarithmic integral. -/
theorem evalVector_right_truncatedExterior_limit (a : PrecontactAperture) (z : ℂ) :
    Tendsto (fun d : ℝ =>
      (∫ t in d..1, evalVectorContinuousRepresentative a z (a.1.1-t) / (2 * (t : ℂ))) /
        (Real.sqrt (Real.log (1/d)) : ℂ)) (𝓝[>] (0 : ℝ))
      (nhds (∫ y : ℝ, (logarithmicCausalKernel y : ℂ) *
        (evalVectorRightEndpointForcing a z : RealLineL2) y)) :=
  truncated_logarithmic_integral_normalized_limit
    ((continuous_evalVectorContinuousRepresentative a z).comp (by fun_prop))
    (evalVectorContinuousRepresentative_right_normalized_limit a z)

/-- The same exact exterior coefficient holds at the left endpoint. -/
theorem evalVector_left_truncatedExterior_limit (a : PrecontactAperture) (z : ℂ) :
    Tendsto (fun d : ℝ =>
      (∫ t in d..1, evalVectorContinuousRepresentative a z (t-a.1.1) / (2 * (t : ℂ))) /
        (Real.sqrt (Real.log (1/d)) : ℂ)) (𝓝[>] (0 : ℝ))
      (nhds (∫ y : ℝ, (logarithmicCausalKernel y : ℂ) *
        (evalVectorLeftEndpointForcing a z : RealLineL2) y)) :=
  truncated_logarithmic_integral_normalized_limit
    ((continuous_evalVectorContinuousRepresentative a z).comp (by fun_prop))
    (evalVectorContinuousRepresentative_left_normalized_limit a z)

#print axioms evalVector_right_truncatedExterior_limit
#print axioms evalVector_left_truncatedExterior_limit
end WeilHilbertBeforeContact
end GaloisForLFunctions.CanonicalSystemOfTheWindowTower
