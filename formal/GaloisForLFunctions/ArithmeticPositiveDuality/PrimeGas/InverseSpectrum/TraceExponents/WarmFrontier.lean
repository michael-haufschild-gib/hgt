import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.TraceExponents.ThermalControl

/-! # Exact trace exponents on the full interval up to inverse temperature two -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open Set

/-- Between inverse temperatures zero and two, the admissible positive powers form the closed ray starting at 2/Re z. -/
theorem warm_trace_power_iff (r : ℕ) {z : ℂ} (hz : 0 < z.re) (h₂ : z.re ≤ 2) {p : ℝ} (hp : 0 < p) :
    (∃ K : ℝ, traceControlsAt (r+1) z p K) ↔ 2/z.re ≤ p := by
  constructor
  · rintro ⟨K,h⟩
    apply (div_le_iff₀ hz).mpr
    rw [mul_comm]
    exact trace_control_forces_exponent r hz ⟨p,hp⟩ h
  · intro h
    exact trace_control_raise hz (div_pos (by norm_num) hz) h (matched_trace_control (r+1) hz h₂)

/-- At real temperature the matching coefficient is exact at every positive rank and every real order. -/
theorem real_matched_factor_iff (r : ℕ) {σ : ℝ} (hσ : 0 < σ) (h₂ : σ ≤ 2) (K : ℝ) :
    traceControlsAt (r+1) (σ:ℂ) (2/σ) K ↔ ((r+1:ℕ):ℝ)^(2/σ-1) ≤ K := by
  have hp := div_pos (by norm_num : (0:ℝ)<2) hσ
  have hr : 0 < ((r+1:ℕ):ℝ) := Nat.cast_pos.mpr (Nat.succ_pos r)
  constructor
  · intro h
    have hm : (σ:ℂ).re * (2/σ) = 2 := by rw [Complex.ofReal_re,mul_comm,div_mul_cancel₀ _ hσ.ne']
    have hb := trace_control_forces_factor (r+1) (z := (σ:ℂ)) hσ ⟨2/σ,hp⟩ hm h
    change ((r+1:ℕ):ℝ)^(2/σ) ≤ K*((r+1:ℕ):ℝ) at hb
    have he : ((r+1:ℕ):ℝ)^(2/σ-1)*((r+1:ℕ):ℝ) = ((r+1:ℕ):ℝ)^(2/σ) := by
      rw [← Real.rpow_add_one hr.ne',sub_add_cancel]
    rw [← he] at hb
    exact le_of_mul_le_mul_right hb hr
  · intro h P hd hc
    have hb := matched_trace_control (r+1) (z := (σ:ℂ)) hσ h₂ P hd hc
    simp only [Complex.ofReal_re,Complex.norm_real,Real.norm_of_nonneg hσ.le,div_self hσ.ne',Real.one_rpow,one_mul] at hb
    exact hb.trans (mul_le_mul_of_nonneg_right h (traceLoss_nonneg P hd hc))

#print axioms warm_trace_power_iff
#print axioms real_matched_factor_iff

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
