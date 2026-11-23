import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.AttenuatedBlocks.ImaginaryFactor
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ClockGrowth.BestCoefficient
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.BlockOmissions.QuarticFrontier

/-! # Ground half turns bound the coefficient at every fixed trace power -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open Set

/-- Dividing by the initial occupation separates its thermal size from the clock chord. -/
theorem norm_scaled_occupation_chord (z : ℂ) {a u : ℝ} (ha : 0 < a) (hu : 0 < u) :
    ‖(a:ℂ)^z-((a*u:ℝ):ℂ)^z‖ = a^z.re*‖1-(u:ℂ)^z‖ := by
  rw [Complex.ofReal_mul,Complex.mul_cpow_ofReal_nonneg ha.le hu.le,← mul_one_sub,norm_mul,
    Complex.norm_cpow_eq_rpow_re_of_pos ha]

/-- At positive height the attenuated phase is antipodal, irrespective of real temperature. -/
theorem halfTurn_chord_one_le {z : ℂ} (ht : 0 < z.im) :
    1 ≤ ‖1-((halfTurnFraction ht.ne').val:ℂ)^z‖ := by
  let v := -Real.pi/z.im
  have hpos := Real.exp_pos v
  have hphase : v*z.im = -Real.pi := div_mul_cancel₀ _ ht.ne'
  have hre : (((Real.exp v:ℝ):ℂ)^z).re = -Real.exp (v*z.re) := by
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hpos.ne'),← Complex.ofReal_log hpos.le,Real.log_exp,
      Complex.exp_re,Complex.mul_re,Complex.mul_im]
    simp only [Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero,add_zero,hphase,Real.cos_neg,Real.cos_pi,mul_neg_one]
  have hn := Complex.re_le_norm (1-((Real.exp v:ℝ):ℂ)^z)
  rw [Complex.sub_re,Complex.one_re,hre,sub_neg_eq_add] at hn
  change 1 ≤ ‖1-((Real.exp (-Real.pi/|z.im|):ℝ):ℂ)^z‖
  rw [abs_of_pos ht]
  exact (le_add_of_nonneg_right (Real.exp_pos _).le).trans hn

theorem halfTurn_fraction_loss {z : ℂ} (ht : 0 < z.im) :
    1-(halfTurnFraction ht.ne').val ≤ Real.pi/z.im := by
  have he := Real.add_one_le_exp (-Real.pi/z.im)
  change 1-Real.exp (-Real.pi/|z.im|) ≤ _
  rw [abs_of_pos ht,neg_div]
  rw [neg_div] at he
  linarith only [he]

/-- A finite physical coefficient at positive power is nonnegative, by a nontrivial ground attenuation. -/
theorem trace_coefficient_nonneg (r : ℕ) {z : ℂ} (hz : 0 < z.re) {p K : ℝ} (hp : 0 ≤ p)
    (h : traceControlsAt (r+1) z p K) : 0 ≤ K := by
  have he := trace_ground_chord r hz hp h ⟨1/2,by norm_num,by norm_num⟩
  have hd : 0 < 1-(1/2:ℝ)^2 := by norm_num
  exact nonneg_of_mul_nonneg_left ((Real.rpow_nonneg (norm_nonneg _) _).trans he) hd

/-- Every admissible power has at least linear coefficient growth, even with arbitrary finite positive missing rank. -/
theorem ground_clock_lower (r : ℕ) {z : ℂ} (hz : 0 < z.re) (ht : 0 < z.im) {p K : ℝ} (hp : 0 ≤ p)
    (h : traceControlsAt (r+1) z p K) : z.im/(2*Real.pi) ≤ K := by
  let u := halfTurnFraction ht.ne'
  have hg := trace_ground_chord r hz hp h ⟨u.val,u.property.1,u.property.2.le⟩
  have h1 : 1 ≤ K*(1-u.val^2) := (Real.one_le_rpow (halfTurn_chord_one_le ht) hp).trans hg
  have hd : 1-u.val^2 ≤ 2*(Real.pi/z.im) := by
    have hfrac := halfTurn_fraction_loss ht
    change 1-u.val ≤ _ at hfrac
    nlinarith only [hfrac,sq_nonneg (1-u.val)]
  have hK := trace_coefficient_nonneg r hz hp h
  have hbound := h1.trans (mul_le_mul_of_nonneg_left hd hK)
  rw [show K*(2*(Real.pi/z.im)) = (K*(2*Real.pi))/z.im by ring] at hbound
  apply (div_le_iff₀ (mul_pos (by norm_num) Real.pi_pos)).mpr
  simpa only [one_mul] using (le_div_iff₀ ht).mp hbound

/-- Least coefficient in a quartic estimate, wherever that estimate is feasible. -/
theorem quarticCoefficient_isLeast (r : ℕ) {z : ℂ} (hz : 1/2 ≤ z.re) :
    IsLeast {K : ℝ | traceControlsAt (r+1) z 4 K} (traceCoefficientAt (r+1) z 4) := by
  have hpos : 0 < z.re := (by norm_num : (0:ℝ)<1/2).trans_le hz
  let S := {K : ℝ | traceControlsAt (r+1) z 4 K}
  have hne : S.Nonempty := (quartic_trace_control_iff r hpos).mpr hz
  have hb : BddBelow S := ⟨0,fun _ h => trace_coefficient_nonneg r hpos (by norm_num : (0:ℝ)≤4) h⟩
  refine ⟨?_,fun K hK => csInf_le hb hK⟩
  intro P hd hc
  have hD := (physical_reading_interior quadraticResponse P (Nat.succ_pos r) hd hc).1
  rw [quadratic_physicalReading] at hD
  apply (div_le_iff₀ hD).mp
  exact le_csInf hne (fun K hK => (div_le_iff₀ hD).mpr (hK P hd hc))

#print axioms norm_scaled_occupation_chord
#print axioms halfTurn_chord_one_le
#print axioms ground_clock_lower
#print axioms quarticCoefficient_isLeast

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
