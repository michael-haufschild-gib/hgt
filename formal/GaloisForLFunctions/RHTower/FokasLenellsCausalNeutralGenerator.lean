import GaloisForLFunctions.RHTower.FokasLenellsCausalStrongStability

/-! Neutral generator modes would conserve orbit norm; actual strong stability forces them to vanish. -/
open Complex MeasureTheory Set Filter Topology
open scoped NNReal
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.FokasLenells
namespace RHTower.FokasLenells
noncomputable section
local instance : InnerProductSpace ℝ (hardyL2ᗮ) := InnerProductSpace.rclikeToReal ℂ (hardyL2ᗮ)

/-- The actual maximal-generator eigenspace at a purely imaginary spectral value. -/
def causalImaginaryGeneratorKernel (ω : ℝ) : Submodule ℂ causalGeneratorDomain :=
  (causalComplexGeneratorShift ((ω : ℂ)*I)).ker

private theorem imaginary_generator_eq (ω : ℝ) (u : causalImaginaryGeneratorKernel ω) :
    causalGenerator u.val = ((ω : ℂ)*I) • u.val.val := by
  have h := u.property
  change ((ω : ℂ)*I) • u.val.val - causalGenerator u.val = 0 at h
  exact (sub_eq_zero.mp h).symm

private theorem imaginary_inner_zero (ω : ℝ) (v : hardyL2ᗮ) :
    inner ℝ v (((ω : ℂ)*I) • v) = 0 := by
  change (inner ℂ v (((ω : ℂ)*I) • v)).re = 0
  rw [inner_smul_right, inner_self_eq_norm_sq_to_K]
  change (((ω : ℂ)*I) * ((‖v‖ : ℝ) : ℂ)^2).re = 0
  rw [← Complex.ofReal_pow, Complex.mul_re]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im, mul_zero, zero_mul, sub_zero]

/-- Every actual neutral mode has zero orbit-energy derivative at every positive time. -/
theorem causalImaginaryGeneratorKernel_energy_hasDerivAt (ω b : ℝ)
    (u : causalImaginaryGeneratorKernel ω) :
    HasDerivAt (fun r : ℝ => ‖causalForwardOrbit u.val.val r‖^2) 0 (Real.exp b) := by
  have hd := (causalGenerator_positiveOrbit_hasDerivAt b u.val).norm_sq
  have he : causalForwardOrbit (causalGenerator u.val) (Real.exp b) =
      ((ω : ℂ)*I) • causalForwardOrbit u.val.val (Real.exp b) := by
    rw [imaginary_generator_eq]
    exact map_smul (causalLowerCauchyEvolution (Real.exp b).toNNReal) _ _
  rw [he, imaginary_inner_zero, mul_zero] at hd
  exact hd

/-- Any actual purely imaginary generator eigenmode would preserve its norm for all positive times. -/
theorem causalImaginaryGeneratorKernel_energy_constant (ω : ℝ)
    (u : causalImaginaryGeneratorKernel ω) (t : ℝ≥0) :
    ‖causalLowerCauchyEvolution t u.val.val‖^2 = ‖u.val.val‖^2 := by
  have hd (r : ℝ) (hr : r ∈ Ioo (0 : ℝ) (t : ℝ)) :
      HasDerivAt (fun s : ℝ => ‖causalForwardOrbit u.val.val s‖^2) 0 r := by
    have h := causalImaginaryGeneratorKernel_energy_hasDerivAt ω (Real.log r) u
    rw [Real.exp_log hr.1] at h
    exact h
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    (f' := fun _ : ℝ => (0 : ℝ)) t.property
    ((causalForwardOrbit_continuous u.val.val).norm.pow 2).continuousOn hd
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (0 : ℝ)) volume 0 (t : ℝ))
  change (∫ _ in (0 : ℝ)..(t : ℝ), (0 : ℝ)) =
    ‖causalForwardOrbit u.val.val (t : ℝ)‖^2 - ‖causalForwardOrbit u.val.val 0‖^2 at h
  simp only [intervalIntegral.integral_zero, causalForwardOrbit, Real.toNNReal_coe,
    Real.toNNReal_zero, causalLowerCauchyEvolution_zero] at h
  linarith only [h]

/-- Every actual imaginary-axis maximal-generator eigenspace is zero. -/
theorem causalImaginaryGeneratorKernel_eq_bot (ω : ℝ) : causalImaginaryGeneratorKernel ω = ⊥ := by
  apply bot_unique
  intro u hu
  let v : causalImaginaryGeneratorKernel ω := ⟨u, hu⟩
  have ht := (causalLowerCauchyEvolution_strong_tendsto u.val).norm.pow 2
  have he (t : ℝ≥0) : ‖causalLowerCauchyEvolution t u.val‖^2 = ‖u.val‖^2 :=
    causalImaginaryGeneratorKernel_energy_constant ω v t
  have hz : Tendsto (fun _ : ℝ≥0 => ‖u.val‖^2) atTop (𝓝 (0 : ℝ)) := by
    simpa only [he, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using ht
  have hnorm : ‖u.val‖^2 = 0 := tendsto_nhds_unique tendsto_const_nhds hz
  change u = 0
  apply Subtype.ext
  exact norm_eq_zero.mp (by nlinarith only [hnorm, norm_nonneg u.val])

end
end RHTower.FokasLenells
