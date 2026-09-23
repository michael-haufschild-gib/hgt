import GaloisForLFunctions.HTGeometry.GaussBonnetFixedChargeAQuarticHarmonicJets

/-!
# Classification of the critical profile's odd differential operators

Among a*D^(5 : ℕ)+b*D^(3 : ℕ)+c*D, the critical quartic profile is annihilated
exactly by scalar multiples of D(D^(2 : ℕ)+4)(D^(2 : ℕ)+16). The two critical
frequencies force both coefficient ratios. Consequently no nonzero
operator b*D^(3 : ℕ)+c*D annihilates this profile. This classifies this
specific odd family; it does not assert a general variable-coefficient
minimal-order result.
-/
noncomputable section
open Real Filter Set
open scoped Topology
namespace GaloisForLFunctions.HTGeometry

theorem egbFixedChargeAQuarticProfile_first_sine_harmonics (ψ : ℝ) :
    iteratedDeriv 1 (fun x : ℝ => cos x ^ (4 : ℕ)) ψ = (-1 : ℝ) * sin (2 * ψ) + (-1 / 2 : ℝ) * sin (4 * ψ) := by
  have h := egbFixedChargeAQuarticProfile_harmonic_jet 0 ψ
  rw [iteratedDeriv_cos_mul_succ, iteratedDeriv_cos_mul_succ] at h
  simp only [iteratedDeriv_zero] at h
  convert h using 1 <;> ring

theorem egbFixedChargeAQuarticProfile_third_sine_harmonics (ψ : ℝ) :
    iteratedDeriv 3 (fun x : ℝ => cos x ^ (4 : ℕ)) ψ = (4 : ℝ) * sin (2 * ψ) + (8 : ℝ) * sin (4 * ψ) := by
  have h := egbFixedChargeAQuarticProfile_harmonic_jet 2 ψ
  rw [show 2 + 1 = 1 + 2 by omega, egbFixedChargeAQuarticMode_two_step,
    egbFixedChargeAQuarticMode_two_step] at h
  rw [iteratedDeriv_cos_mul_succ 2 0 ψ, iteratedDeriv_cos_mul_succ 4 0 ψ] at h
  simp only [iteratedDeriv_zero] at h
  convert h using 1 <;> ring

theorem egbFixedChargeAQuarticProfile_fifth_sine_harmonics (ψ : ℝ) :
    iteratedDeriv 5 (fun x : ℝ => cos x ^ (4 : ℕ)) ψ = (-16 : ℝ) * sin (2 * ψ) + (-128 : ℝ) * sin (4 * ψ) := by
  have h := egbFixedChargeAQuarticProfile_harmonic_jet 4 ψ
  rw [show 4 + 1 = 1 + 4 by omega, egbFixedChargeAQuarticMode_four_step,
    egbFixedChargeAQuarticMode_four_step] at h
  rw [iteratedDeriv_cos_mul_succ 2 0 ψ, iteratedDeriv_cos_mul_succ 4 0 ψ] at h
  simp only [iteratedDeriv_zero] at h
  convert h using 1 <;> ring

theorem egbFixedChargeAQuarticProfile_odd_operator_harmonics (a b c ψ : ℝ) :
    a * iteratedDeriv 5 (fun x : ℝ => cos x ^ (4 : ℕ)) ψ +
      b * iteratedDeriv 3 (fun x : ℝ => cos x ^ (4 : ℕ)) ψ +
      c * iteratedDeriv 1 (fun x : ℝ => cos x ^ (4 : ℕ)) ψ =
      (-16 * a + 4 * b - c) * sin (2 * ψ) +
      (-128 * a + 8 * b - c / 2) * sin (4 * ψ) := by
  rw [egbFixedChargeAQuarticProfile_fifth_sine_harmonics,
    egbFixedChargeAQuarticProfile_third_sine_harmonics,
    egbFixedChargeAQuarticProfile_first_sine_harmonics]
  ring

theorem egbFixedChargeAQuarticProfile_odd_operator_classification (a b c : ℝ) :
    (∀ ψ : ℝ, a * iteratedDeriv 5 (fun x : ℝ => cos x ^ (4 : ℕ)) ψ +
      b * iteratedDeriv 3 (fun x : ℝ => cos x ^ (4 : ℕ)) ψ +
      c * iteratedDeriv 1 (fun x : ℝ => cos x ^ (4 : ℕ)) ψ = 0) ↔
      b = 20 * a ∧ c = 64 * a := by
  constructor
  · intro h
    have h₁ := h (Real.pi / 4)
    have h₂ := h (Real.pi / 8)
    rw [egbFixedChargeAQuarticProfile_odd_operator_harmonics] at h₁ h₂
    have hp₁ : 2 * (Real.pi / 4) = Real.pi / 2 := by ring
    have hp₂ : 4 * (Real.pi / 4) = Real.pi := by ring
    have hp₃ : 4 * (Real.pi / 8) = Real.pi / 2 := by ring
    rw [hp₁, hp₂, sin_pi_div_two, sin_pi] at h₁
    simp only [mul_one, mul_zero, add_zero] at h₁
    rw [h₁, zero_mul, zero_add, hp₃, sin_pi_div_two, mul_one] at h₂
    constructor <;> linarith
  · rintro ⟨hb, hc⟩ ψ
    rw [egbFixedChargeAQuarticProfile_odd_operator_harmonics, hb, hc]
    ring

theorem egbFixedChargeAQuarticProfile_third_order_obstruction (b c : ℝ) :
    (∀ ψ : ℝ, b * iteratedDeriv 3 (fun x : ℝ => cos x ^ (4 : ℕ)) ψ +
      c * iteratedDeriv 1 (fun x : ℝ => cos x ^ (4 : ℕ)) ψ = 0) ↔ b = 0 ∧ c = 0 := by
  simpa only [mul_zero, zero_mul, zero_add] using
    egbFixedChargeAQuarticProfile_odd_operator_classification 0 b c

end GaloisForLFunctions.HTGeometry
