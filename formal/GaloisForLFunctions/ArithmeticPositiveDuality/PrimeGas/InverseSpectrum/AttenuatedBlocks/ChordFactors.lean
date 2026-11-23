import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.AttenuatedBlocks.TraceProbes

/-! # Matched powers retain the full complex chord at high occupations -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open Set Filter Topology

/-- Every admissible matched coefficient pays the entire phase-sensitive attenuation chord on a high block. -/
theorem matched_block_chord (r : ℕ) {z : ℂ} (hz : 0 < z.re) {p K : ℝ} (hp : 0 < p) (hm : z.re*p = 2)
    (h : traceControlsAt r z p K) (t : Ioc (0:ℝ) 1) :
    ‖1-(t.val:ℂ)^z‖^p * (r:ℝ)^p ≤ K*(1-t.val^2)*(r:ℝ) := by
  let c := ‖1-(t.val:ℂ)^z‖^p
  let d := K*(1-t.val^2)
  have hd (N : ℕ) : relativeReading quadraticResponse (blockSpectrum N r) =
      occupationWeight N^(2:ℝ) * normalizedBlock fourthTraceExponent r N := by
    exact (reading_at_two _ fourthTraceExponent rfl).symm.trans
      ((relativeReading_block _ N r).trans (power_tailCeiling_eq_scaled fourthTraceExponent r N))
  have hn (N : ℕ) : c*‖complexBlock z r N‖^p ≤ d*normalizedBlock fourthTraceExponent r N := by
    have hb := trace_block_chord N r hz hp.le h t
    rw [relativePartition_block_scaled N r hz,norm_mul,norm_mul,Complex.norm_cpow_eq_rpow_re_of_pos (occupationWeight_pos N),
      Real.mul_rpow (norm_nonneg _) (mul_nonneg (Real.rpow_nonneg (occupationWeight_pos N).le _) (norm_nonneg _)),
      Real.mul_rpow (Real.rpow_nonneg (occupationWeight_pos N).le _) (norm_nonneg _),
      ← Real.rpow_mul (occupationWeight_pos N).le,hm,hd] at hb
    apply le_of_mul_le_mul_left (a := occupationWeight N^(2:ℝ)) _ (Real.rpow_pos_of_pos (occupationWeight_pos N) _)
    change _*(‖1-(t.val:ℂ)^z‖^p*_) ≤ _*(K*(1-t.val^2)*_)
    linarith only [hb]
  have hs := (complexBlock_tendsto z r).norm
  simp only [Complex.norm_natCast] at hs
  have hl := (((Real.continuous_rpow_const hp.le).tendsto _).comp hs).const_mul c
  exact le_of_tendsto_of_tendsto hl ((normalizedBlock_tendsto fourthTraceExponent r).const_mul d) (Eventually.of_forall hn)

/-- At positive rank the factor from the number of missing directions separates exactly from the scalar chord. -/
theorem matched_chord_factor (r : ℕ) {z : ℂ} (hz : 0 < z.re) {p K : ℝ} (hp : 0 < p) (hm : z.re*p = 2)
    (h : traceControlsAt (r+1) z p K) (t : Ioc (0:ℝ) 1) :
    ((r+1:ℕ):ℝ)^(p-1)*‖1-(t.val:ℂ)^z‖^p ≤ K*(1-t.val^2) := by
  have hr : 0 < ((r+1:ℕ):ℝ) := Nat.cast_pos.mpr (Nat.succ_pos r)
  have he : ((r+1:ℕ):ℝ)^p = ((r+1:ℕ):ℝ)^(p-1)*((r+1:ℕ):ℝ) := by
    rw [← Real.rpow_add_one hr.ne',sub_add_cancel]
  have hb := matched_block_chord (r+1) hz hp hm h t
  rw [he,← mul_assoc,mul_comm (‖1-(t.val:ℂ)^z‖^p) _] at hb
  exact le_of_mul_le_mul_right hb hr

#print axioms matched_chord_factor

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
