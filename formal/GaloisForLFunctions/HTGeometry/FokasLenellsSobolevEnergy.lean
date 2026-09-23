import GaloisForLFunctions.HTGeometry.FokasLenellsSobolevPackets

/-!
# Exact Sobolev energy for the Fokas–Lenells time phase

The phase in Proposition 5.1 of Yan–Zhang–Zhu, arXiv:2607.19649v1,
acts isometrically on L² but creates a linearly growing derivative cost.
For the corpus's singular Sobolev packets, the weak derivative energy is
an exact quadratic in time. Reverse triangle inequalities give matching
upper and lower slopes and a precise asymptotic law.
-/

open Complex MeasureTheory Filter Topology
open scoped InnerProductSpace
namespace GaloisForLFunctions.HTGeometry.FokasLenells
noncomputable section


theorem derivativeSeed_decomposition (f : SchwartzMap ℝ ℂ) (t : ℝ) :
    (derivativeSeed f t).toLp 2 volume =
      (derivativeSeed f 0).toLp 2 volume + (I*(t:ℂ)/2) • f.toLp 2 volume := by
  have h : derivativeSeed f t = derivativeSeed f 0 + (I*(t:ℂ)/2) • f := by
    simp [derivativeSeed]
  rw [h]
  exact (SchwartzMap.toLpCLM ℂ ℂ 2 volume).map_add _ _ |>.trans
    (congrArg (fun v => (derivativeSeed f 0).toLp 2 volume + v)
      ((SchwartzMap.toLpCLM ℂ ℂ 2 volume).map_smul _ _))

/-- The weak-derivative energy is an exact quadratic in time. -/
theorem packet_derivative_energy (f : SchwartzMap ℝ ℂ) (t : ℝ) :
    ‖packetDerivativeL2 f t‖^(2 : ℕ) = ‖(derivativeSeed f 0).toLp 2 volume‖^(2 : ℕ) -
      t*(inner ℂ ((derivativeSeed f 0).toLp 2 volume) (f.toLp 2 volume)).im +
      t^(2 : ℕ)/4*‖f.toLp 2 volume‖^(2 : ℕ) := by
  rw [packetDerivativeL2_eq_evolution, norm_evolution, derivativeSeed_decomposition,
    norm_add_sq (𝕜 := ℂ), inner_smul_right]
  change _ + 2*(I*(t:ℂ)/2 * inner ℂ ((derivativeSeed f 0).toLp 2 volume)
    (f.toLp 2 volume)).re + _ = _
  simp only [norm_smul, norm_div, norm_mul, norm_I, Complex.norm_real, Real.norm_eq_abs,
    norm_ofNat, one_mul, Complex.mul_re, Complex.mul_im, Complex.div_ofNat_re, Complex.div_ofNat_im,
    Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
  rw [mul_pow, div_pow, sq_abs]
  ring

theorem packet_derivative_energy_second_difference (f : SchwartzMap ℝ ℂ) (t h : ℝ) :
    ‖packetDerivativeL2 f (t+h)‖^(2 : ℕ) + ‖packetDerivativeL2 f (t-h)‖^(2 : ℕ) -
      2*‖packetDerivativeL2 f t‖^(2 : ℕ) = h^(2 : ℕ)/2*‖f.toLp 2 volume‖^(2 : ℕ) := by
  rw [packet_derivative_energy, packet_derivative_energy, packet_derivative_energy]
  ring

/-- The derivative norm has an affine lower bound with the same sharp slope as its upper bound. -/
theorem packet_derivative_time_lower_bound (f : SchwartzMap ℝ ℂ) (t : ℝ) :
    |t|/2*‖f.toLp 2 volume‖ - ‖(derivativeSeed f 0).toLp 2 volume‖ ≤
      ‖packetDerivativeL2 f t‖ := by
  rw [packetDerivativeL2_eq_evolution, norm_evolution, derivativeSeed_decomposition f t]
  have h := norm_sub_norm_le ((I*(t:ℂ)/2) • f.toLp 2 volume)
    (-(derivativeSeed f 0).toLp 2 volume)
  simp only [norm_smul, norm_div, norm_mul, norm_I, Complex.norm_real, Real.norm_eq_abs,
    norm_ofNat, one_mul, norm_neg, sub_neg_eq_add] at h
  simpa only [add_comm] using h

/-- Motion of the derivative norm is globally Lipschitz in time. -/
theorem packet_derivative_norm_lipschitz (f : SchwartzMap ℝ ℂ) (s t : ℝ) :
    |‖packetDerivativeL2 f s‖ - ‖packetDerivativeL2 f t‖| ≤
      |s-t|/2*‖f.toLp 2 volume‖ := by
  rw [packetDerivativeL2_eq_evolution, packetDerivativeL2_eq_evolution,
    norm_evolution, norm_evolution, derivativeSeed_decomposition f s, derivativeSeed_decomposition f t]
  refine (abs_norm_sub_norm_le _ _).trans_eq ?_
  rw [add_sub_add_left_eq_sub, ← sub_smul]
  have hc : I*(s:ℂ)/2 - I*(t:ℂ)/2 = I*((s-t:ℝ):ℂ)/2 := by push_cast; ring
  rw [hc]
  simp only [norm_smul, norm_div, norm_mul, norm_I, Complex.norm_real,
    Real.norm_eq_abs, norm_ofNat, one_mul]

/-- The coefficient in the paper's linear time estimate is the exact asymptotic slope. -/
theorem packet_derivative_asymptotic_slope (f : SchwartzMap ℝ ℂ) :
    Tendsto (fun t : ℝ => ‖packetDerivativeL2 f t‖ / t) atTop
      (𝓝 (‖f.toLp 2 volume‖ / 2)) := by
  let A := ‖(derivativeSeed f 0).toLp 2 volume‖
  let B := ‖f.toLp 2 volume‖ / 2
  have hz : Tendsto (fun t : ℝ => A / t) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using
      (tendsto_inv_atTop_zero : Tendsto (fun t : ℝ => t⁻¹) atTop (𝓝 0)).const_mul A
  have hlo : Tendsto (fun t : ℝ => B - A/t) atTop (𝓝 B) := by
    simpa only [sub_zero] using tendsto_const_nhds.sub hz
  have hhi : Tendsto (fun t : ℝ => B + A/t) atTop (𝓝 B) := by
    simpa only [add_zero] using tendsto_const_nhds.add hz
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi
  · filter_upwards [eventually_gt_atTop (0:ℝ)] with t ht
    have h := packet_derivative_time_lower_bound f t
    rw [abs_of_pos ht] at h
    apply (le_div_iff₀ ht).mpr
    dsimp [A,B]
    have he : (‖f.toLp 2 volume‖ / 2 - ‖(derivativeSeed f 0).toLp 2 volume‖ / t)*t =
        t/2*‖f.toLp 2 volume‖ - ‖(derivativeSeed f 0).toLp 2 volume‖ := by
      field_simp
    rwa [he]
  · filter_upwards [eventually_gt_atTop (0:ℝ)] with t ht
    have h := packet_derivative_time_bound f t
    rw [abs_of_pos ht] at h
    apply (div_le_iff₀ ht).mpr
    dsimp [A,B]
    have he : (‖f.toLp 2 volume‖ / 2 + ‖(derivativeSeed f 0).toLp 2 volume‖ / t)*t =
        ‖(derivativeSeed f 0).toLp 2 volume‖ + t/2*‖f.toLp 2 volume‖ := by
      field_simp
      ring
    rwa [he]

end
end GaloisForLFunctions.HTGeometry.FokasLenells
