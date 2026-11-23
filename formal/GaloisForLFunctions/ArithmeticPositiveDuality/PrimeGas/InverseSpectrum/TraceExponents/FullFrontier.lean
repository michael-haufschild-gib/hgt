import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.TraceExponents.WarmFrontier
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.TraceExponents.GroundSlope
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.DivisorSplitting

/-! # Least trace exponent and isometric quantum composition -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open Set

/-- The least admissible trace power is the larger of the ground-state and high-energy obstructions. -/
theorem trace_power_iff (r : ℕ) {z : ℂ} (hz : 0 < z.re) {p : ℝ} (hp : 0 < p) :
    (∃ K : ℝ, traceControlsAt (r+1) z p K) ↔ max 1 (2/z.re) ≤ p := by
  constructor
  · rintro ⟨K,h⟩
    apply max_le (trace_control_forces_one r hz hp h)
    apply (div_le_iff₀ hz).mpr
    rw [mul_comm]
    exact trace_control_forces_exponent r hz ⟨p,hp⟩ h
  · intro h
    rcases le_total z.re 2 with h₂ | h₂
    · exact (warm_trace_power_iff r hz h₂ hp).mpr ((le_max_right _ _).trans h)
    · exact trace_control_raise hz zero_lt_one ((le_max_left _ _).trans h) (linear_trace_control (r+1) h₂)

/-- In the full linear regime the least coefficient is independent of missing rank and equals half the complex modulus. -/
theorem linear_trace_factor_iff (r : ℕ) {z : ℂ} (hz : 0 < z.re) (K : ℝ) :
    traceControlsAt (r+1) z 1 K ↔ 2 ≤ z.re ∧ ‖z‖/2 ≤ K := by
  constructor
  · intro h
    have he := trace_control_forces_exponent r hz ⟨1,show (0:ℝ) < 1 from zero_lt_one⟩ h
    change 2 ≤ z.re*1 at he
    exact ⟨by simpa only [mul_one] using he,linear_control_forces_factor r hz h⟩
  · rintro ⟨h₂,hK⟩ P hd hc
    exact (linear_trace_control (r+1) h₂ P hd hc).trans (mul_le_mul_of_nonneg_right hK (traceLoss_nonneg P hd hc))

/-- Physical trace powers at one complex temperature and fixed missing dimension. -/
def admissibleTracePowers (r : ℕ) (z : ℂ) : Set ℝ := {p | 0 < p ∧ ∃ K : ℝ, traceControlsAt r z p K}

theorem admissibleTracePowers_eq (r : ℕ) {z : ℂ} (hz : 0 < z.re) :
    admissibleTracePowers (r+1) z = Ici (max 1 (2/z.re)) := by
  ext p
  constructor
  · rintro ⟨hp,h⟩
    exact (trace_power_iff r hz hp).mp h
  · intro h
    have hp : 0 < p := (zero_lt_one.trans_le (le_max_left _ _)).trans_le h
    exact ⟨hp,(trace_power_iff r hz hp).mpr h⟩

/-- A least power of exactly four characterizes the energy-preserving divisor split that is an isometry. -/
theorem least_trace_power_four_iff_split_isometric (r : ℕ) {z : ℂ} (hz : 0 < z.re) :
    IsLeast (admissibleTracePowers (r+1) z) 4 ↔
      ∃ T : Gas →ₗᵢ[ℂ] PairGas, ∀ f x, T f x = split z f x := by
  rw [admissibleTracePowers_eq r hz,split_isometric_iff]
  constructor
  · intro h
    have he := h.unique (isLeast_Ici (a := max 1 (2/z.re)))
    rcases le_total (2/z.re) 1 with hq | hq
    · rw [max_eq_left hq] at he
      norm_num at he
    · rw [max_eq_right hq] at he
      have hm := (eq_div_iff hz.ne').mp he
      linarith only [hm]
  · intro he
    rw [he,show max 1 (2/(1/2:ℝ)) = 4 by norm_num]
    exact isLeast_Ici

#print axioms trace_power_iff
#print axioms linear_trace_factor_iff
#print axioms least_trace_power_four_iff_split_isometric

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
