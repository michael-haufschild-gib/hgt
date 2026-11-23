import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.AttenuatedBlocks.TraceProbes

/-! # Ground-state differentiation forces a linear trace floor -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open Set Filter Topology

private theorem left_unit_interval : ∀ᶠ x : ℝ in 𝓝[<] 1, 0 < x ∧ x < 1 := by
  have hx : Tendsto (fun x : ℝ => x) (𝓝[<] 1) (𝓝 1) := tendsto_id.mono_left nhdsWithin_le_nhds
  exact (hx.eventually_const_lt zero_lt_one).and self_mem_nhdsWithin

/-- An infinitesimal attenuation reads the modulus of complex inverse temperature relative to the quadratic response. -/
theorem ground_chord_slope {z : ℂ} (hz : 0 < z.re) :
    Tendsto (fun x : ℝ => ‖1-(x:ℂ)^z‖/(1-x^2)) (𝓝[<] 1) (𝓝 (‖z‖/2)) := by
  have hn : z ≠ 0 := fun h => by rw [h] at hz; exact (lt_irrefl _ hz)
  let f (x : ℝ) := (x:ℂ)^z
  have hder : HasDerivAt f z 1 := by
    simpa only [Complex.ofReal_one,Complex.one_cpow,mul_one] using hasDerivAt_ofReal_cpow_const (x := (1:ℝ)) one_ne_zero hn
  have hs := (hasDerivAt_iff_tendsto_slope_left_right.mp hder).1
  have hx : Tendsto (fun x : ℝ => x) (𝓝[<] 1) (𝓝 1) := tendsto_id.mono_left nhdsWithin_le_nhds
  have hden : Tendsto (fun x : ℝ => 1+x) (𝓝[<] 1) (𝓝 2) := by
    simpa only [one_add_one_eq_two] using hx.const_add 1
  apply (hs.norm.div hden (by norm_num)).congr'
  filter_upwards [left_unit_interval] with x hx'
  change ‖slope f 1 x‖/(1+x) = _
  rw [slope_def_module,norm_smul,Real.norm_eq_abs,abs_inv,abs_of_neg (sub_neg.mpr hx'.2)]
  have hf : f 1 = 1 := by simp only [f,Complex.ofReal_one,Complex.one_cpow]
  rw [hf,norm_sub_rev,neg_sub]
  change (1-x)⁻¹*‖1-(x:ℂ)^z‖/(1+x) = _
  rw [show 1-x^2 = (1-x)*(1+x) by ring]
  simp only [div_eq_mul_inv,mul_inv_rev]
  ring

private theorem positive_deficit {x : ℝ} (hx : 0 < x ∧ x < 1) : 0 < 1-x^2 := by
  rw [show 1-x^2 = (1-x)*(1+x) by ring]
  exact mul_pos (sub_pos.mpr hx.2) (add_pos zero_lt_one hx.1)

/-- Every positive power governing physical trace deficits is at least one, even at arbitrarily large inverse temperature. -/
theorem trace_control_forces_one (r : ℕ) {z : ℂ} (hz : 0 < z.re) {p K : ℝ} (hp : 0 < p)
    (h : traceControlsAt (r+1) z p K) : 1 ≤ p := by
  by_contra! hlt
  have hq : 0 < 1-p := sub_pos.mpr hlt
  have hx : Tendsto (fun x : ℝ => x) (𝓝[<] 1) (𝓝 1) := tendsto_id.mono_left nhdsWithin_le_nhds
  have hD : Tendsto (fun x : ℝ => 1-x^2) (𝓝[<] 1) (𝓝 0) := by
    simpa only [one_pow,sub_self] using (hx.pow 2).const_sub 1
  have hR := (((Real.continuous_rpow_const hq.le).tendsto 0).comp hD).const_mul K
  have hL := ((Real.continuous_rpow_const hp.le).tendsto _).comp (ground_chord_slope hz)
  have he : (‖z‖/2)^p ≤ K*(0:ℝ)^(1-p) := by
    apply le_of_tendsto_of_tendsto hL hR
    filter_upwards [left_unit_interval] with x hx'
    have hd := positive_deficit hx'
    have hb := trace_ground_chord r hz hp.le h ⟨x,hx'.1,hx'.2.le⟩
    change (‖1-(x:ℂ)^z‖/(1-x^2))^p ≤ K*(1-x^2)^(1-p)
    rw [Real.div_rpow (norm_nonneg _) hd.le,Real.rpow_sub hd,Real.rpow_one]
    rw [← mul_div_assoc]
    exact div_le_div_of_nonneg_right hb (Real.rpow_nonneg hd.le _)
  rw [Real.zero_rpow hq.ne',mul_zero] at he
  have hz' : z ≠ 0 := fun h => by rw [h] at hz; exact (lt_irrefl _ hz)
  exact (Real.rpow_pos_of_pos (div_pos (norm_pos_iff.mpr hz') (by norm_num)) p).not_ge he

/-- The ground-state tangent forces the sharp linear coefficient at all complex heights. -/
theorem linear_control_forces_factor (r : ℕ) {z : ℂ} (hz : 0 < z.re) {K : ℝ}
    (h : traceControlsAt (r+1) z 1 K) : ‖z‖/2 ≤ K := by
  apply le_of_tendsto (ground_chord_slope hz)
  filter_upwards [left_unit_interval] with x hx
  apply (div_le_iff₀ (positive_deficit hx)).mpr
  simpa only [Real.rpow_one] using trace_ground_chord r hz zero_le_one h ⟨x,hx.1,hx.2.le⟩

#print axioms ground_chord_slope
#print axioms trace_control_forces_one
#print axioms linear_control_forces_factor

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
