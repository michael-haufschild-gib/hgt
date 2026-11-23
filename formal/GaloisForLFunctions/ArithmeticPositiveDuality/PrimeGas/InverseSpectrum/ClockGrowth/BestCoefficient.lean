import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ClockGrowth.HeightGrowth

/-! # The least matched trace coefficient and its critical fourth-power growth -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open Set

/-- Infimum over all coefficients in the physical trace estimate at a given power. -/
def traceCoefficientAt (r : ℕ) (z : ℂ) (p : ℝ) : ℝ := sInf {K : ℝ | traceControlsAt r z p K}

/-- Least allowed coefficient at the power fixed by high occupations. -/
def matchedTraceCoefficient (r : ℕ) (z : ℂ) : ℝ := traceCoefficientAt r z (2/z.re)

/-- The infimum over physical estimates is itself a valid estimate at every positive rank up to real inverse temperature two. -/
theorem matchedTraceCoefficient_isLeast (r : ℕ) {z : ℂ} (hz : 0 < z.re) (h₂ : z.re ≤ 2) :
    IsLeast {K : ℝ | traceControlsAt (r+1) z (2/z.re) K} (matchedTraceCoefficient (r+1) z) := by
  let S := {K : ℝ | traceControlsAt (r+1) z (2/z.re) K}
  have hne : S.Nonempty := ⟨_,matched_trace_control (r+1) hz h₂⟩
  have hb : BddBelow S := by
    refine ⟨0,fun K hK => ?_⟩
    have hp : 0 < 2/z.re := div_pos (by norm_num) hz
    have hm : z.re*(2/z.re) = 2 := by rw [mul_comm,div_mul_cancel₀ _ hz.ne']
    have h := trace_control_forces_factor (r+1) hz ⟨2/z.re,hp⟩ hm hK
    have hr : 0 < ((r+1:ℕ):ℝ) := Nat.cast_pos.mpr (Nat.succ_pos r)
    apply le_of_mul_le_mul_right (a := ((r+1:ℕ):ℝ)) _ hr
    rw [zero_mul]
    exact (Real.rpow_nonneg hr.le _).trans h
  refine ⟨?_,fun K hK => csInf_le hb hK⟩
  intro P hd hc
  have hD := (physical_reading_interior quadraticResponse P (Nat.succ_pos r) hd hc).1
  rw [quadratic_physicalReading] at hD
  apply (div_le_iff₀ hD).mp
  exact le_csInf hne (fun K hK => (div_le_iff₀ hD).mpr (hK P hd hc))

/-- The least physical coefficient at rank one lies within the factor 4^(2/Re z) of the upper chord bound, uniformly in imaginary time. -/
theorem matchedTraceCoefficient_bounds {z : ℂ} (hz : 0 < z.re) (h₂ : z.re ≤ 2) :
    (‖z‖/(4*z.re))^(2/z.re) ≤ matchedTraceCoefficient 1 z ∧
      matchedTraceCoefficient 1 z ≤ (‖z‖/z.re)^(2/z.re) := by
  have he := matchedTraceCoefficient_isLeast 0 hz h₂
  have hm : z.re*(2/z.re) = 2 := by rw [mul_comm,div_mul_cancel₀ _ hz.ne']
  refine ⟨matched_height_factor_lower hz (div_pos (by norm_num) hz) hm he.1,he.2 ?_⟩
  simpa only [Nat.cast_one,Real.one_rpow,mul_one] using matched_trace_control 1 hz h₂

/-- On the isometric composition line the optimal rank-one coefficient grows to fourth order in the complex modulus. -/
theorem critical_sharp_factor_bounds {z : ℂ} (hz : z.re = 1/2) :
    (‖z‖/2)^4 ≤ matchedTraceCoefficient 1 z ∧ matchedTraceCoefficient 1 z ≤ (2*‖z‖)^4 := by
  have he := matchedTraceCoefficient_bounds (z := z) (by rw [hz]; norm_num) (by rw [hz]; norm_num)
  have ha : ‖z‖/(4*z.re) = ‖z‖/2 := by rw [hz]; norm_num
  have hb : ‖z‖/z.re = 2*‖z‖ := by rw [hz]; ring
  have hp : 2/z.re = 4 := by rw [hz]; norm_num
  have hpow (x : ℝ) : x^(4:ℝ) = x^4 := Real.rpow_natCast x 4
  simpa only [ha,hb,hp,hpow] using he

#print axioms matchedTraceCoefficient_isLeast
#print axioms matchedTraceCoefficient_bounds
#print axioms critical_sharp_factor_bounds

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
