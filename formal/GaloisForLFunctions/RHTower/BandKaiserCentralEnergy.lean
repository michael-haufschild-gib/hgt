import GaloisForLFunctions.RHTower.BandLeakageEnvelope

/-!
# Central-frequency energy of the Kaiser trial

The first Kaiser leakage estimate used only its value at frequency zero.  A window of angular
frequencies of width `sqrt c` has the same exponential size.  Integrating over that window and
using Plancherel gains the missing factor `sqrt c` in the physical-energy lower bound.

This is a polynomial refinement of the unconditional Kaiser route.  It does not assert the Fuchs
asymptotic: the remaining exterior-tail estimate and the fixed-mode lower bound are separate.
-/

noncomputable section

open MeasureTheory Set intervalIntegral FourierTransform

namespace GaloisForLFunctions.RHTower

/-- On the central angular-frequency window `omega^2 <= c`, the Kaiser transform retains its
central exponential size. -/
theorem exp_sub_one_div_two_mul_le_integral_kaiserTrial_cos
    {c omega : ℝ} (hc : 2 ≤ c) (homega : omega ^ 2 ≤ c) :
    Real.exp (c - 1) / (2 * c) ≤
      ∫ x in (-1 : ℝ)..1, kaiserTrial c x * Real.cos (omega * x) := by
  have hcpos : 0 < c := by linarith
  have hvpos : 0 < c - 1 := by linarith
  have hz0 : 0 ≤ (c - 1) ^ 2 := sq_nonneg _
  have harg : (c - 1) ^ 2 ≤ c ^ 2 - omega ^ 2 := by
    nlinarith
  have hmono := tsum_oddFactorial_mono hz0 harg
  have hseries :
      2 * Real.sinh (c - 1) / (c - 1) ≤
        ∑' m : ℕ, 2 * (c ^ 2 - omega ^ 2) ^ m /
          (Nat.factorial (2 * m + 1) : ℝ) := by
    rw [← tsum_oddFactorial_sinh hvpos.ne']
    exact hmono
  have hexpTwo : 2 ≤ Real.exp (c - 1) := by
    calc
      (2 : ℝ) ≤ Real.exp 1 := by
        have h := Real.add_one_le_exp 1
        norm_num at h ⊢
        exact h
      _ ≤ Real.exp (c - 1) := Real.exp_le_exp.mpr (by linarith)
  have hexpNeg : Real.exp (-(c - 1)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    linarith
  have hsinh : Real.exp (c - 1) / 2 ≤ 2 * Real.sinh (c - 1) := by
    rw [Real.sinh_eq]
    nlinarith
  have hdiv : Real.exp (c - 1) / (2 * c) ≤
      2 * Real.sinh (c - 1) / (c - 1) := by
    rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < 2 * c) hvpos]
    have hmul := mul_le_mul_of_nonneg_right hsinh (show 0 ≤ 2 * (c - 1) by linarith)
    nlinarith [Real.exp_pos (c - 1)]
  rw [integral_kaiserTrial_cos]
  exact hdiv.trans hseries

/-- Plancherel integrated over the full central window gains a factor `sqrt c` over the
single-frequency squared-mean estimate. -/
theorem sqrt_mul_exp_sub_one_sq_div_le_energy_kaiserTrial
    {c : ℝ} (hc : 2 ≤ c) :
    Real.sqrt c / Real.pi * (Real.exp (c - 1) / (2 * c)) ^ 2 ≤
      ∫ x in (-1 : ℝ)..1, kaiserTrial c x ^ 2 := by
  let r : ℝ := Real.sqrt c / (2 * Real.pi)
  let q : ℝ := (Real.exp (c - 1) / (2 * c)) ^ 2
  let rho : ℝ → ℝ := fun xi =>
    ‖FourierTransform.fourier (bandTrunc (kaiserTrial c)) xi‖ ^ 2
  have hc0 : 0 ≤ c := by linarith
  have hcpos : 0 < c := by linarith
  have hr0 : 0 ≤ r := by
    dsimp [r]
    positivity
  have hq0 : 0 ≤ q := sq_nonneg _
  have hrho : Integrable rho :=
    integrable_norm_sq_fourier_bandTrunc (continuous_kaiserTrial c)
  have hpoint : ∀ xi ∈ Icc (-r) r, q ≤ rho xi := by
    intro xi hxi
    have habsxi : |xi| ≤ r := (abs_le).2 hxi
    have hpi : 0 < 2 * Real.pi := by positivity
    have hsqrtSq : Real.sqrt c ^ 2 = c := Real.sq_sqrt hc0
    have homega : (2 * Real.pi * xi) ^ 2 ≤ c := by
      have hsquare := pow_le_pow_left₀ (abs_nonneg xi) habsxi 2
      rw [sq_abs] at hsquare
      dsimp [r] at hsquare
      have hpine : (2 * Real.pi : ℝ) ≠ 0 := hpi.ne'
      field_simp [hpine] at hsquare
      nlinarith
    have hlower := exp_sub_one_div_two_mul_le_integral_kaiserTrial_cos hc homega
    have hnonneg : 0 ≤ Real.exp (c - 1) / (2 * c) := by positivity
    have hsquare := pow_le_pow_left₀ hnonneg hlower 2
    dsimp [q, rho]
    rw [norm_sq_fourier_bandTrunc_of_even
      (continuous_kaiserTrial c) (kaiserTrial_even c) xi]
    exact hsquare
  have hconst : IntegrableOn (fun _ : ℝ => q) (Icc (-r) r) := by
    exact integrableOn_const (C := q) (by simp [Real.volume_Icc])
  have hlower : (∫ xi in Icc (-r) r, q) ≤ ∫ xi in Icc (-r) r, rho xi := by
    exact setIntegral_mono_on hconst hrho.integrableOn measurableSet_Icc hpoint
  have hrestrict : (∫ xi in Icc (-r) r, rho xi) ≤ ∫ xi : ℝ, rho xi :=
    integral_mono_measure Measure.restrict_le_self
      (Filter.Eventually.of_forall fun xi => sq_nonneg _) hrho
  have hconstEval : (∫ _xi in Icc (-r) r, q) = Real.sqrt c / Real.pi * q := by
    rw [MeasureTheory.setIntegral_const, Real.volume_real_Icc_of_le (by linarith)]
    simp only [smul_eq_mul]
    dsimp [r]
    field_simp [Real.pi_ne_zero]
    ring
  have htotal : (∫ xi : ℝ, rho xi) =
      ∫ x in (-1 : ℝ)..1, kaiserTrial c x ^ 2 := by
    dsimp [rho]
    exact (integral_norm_sq_fourier_bandTrunc (continuous_kaiserTrial c)).trans
      (integral_norm_sq_bandTrunc (kaiserTrial c))
  dsimp [q] at hconstEval ⊢
  rw [← htotal, ← hconstEval]
  exact hlower.trans hrestrict

/-- Closed-form polynomial refinement of the ground Kaiser Rayleigh bound. -/
theorem one_sub_norm_bandOperatorL2_mul_sqrt_mul_exp_le
    {c : ℝ} (hc : 2 ≤ c) :
    (1 - ‖bandOperatorL2 c‖) *
        (Real.sqrt c / Real.pi * (Real.exp (c - 1) / (2 * c)) ^ 2) ≤ 8 := by
  have hcpos : 0 < c := by linarith
  have henergy := sqrt_mul_exp_sub_one_sq_div_le_energy_kaiserTrial hc
  have henergyPos : 0 < ∫ x in (-1 : ℝ)..1, kaiserTrial c x ^ 2 :=
    energy_kaiserTrial_pos hcpos
  have hvar := one_sub_norm_bandOperatorL2_le c (kaiserTrial c)
    (continuous_kaiserTrial c) (bandClass_kaiserTrial_ne_zero hcpos)
  rw [leakage_eq_spectral_tail hcpos (continuous_kaiserTrial c)] at hvar
  have htail := integral_tail_kaiser_le (c := c) hcpos.le
  rcases le_or_gt (1 - ‖bandOperatorL2 c‖) 0 with hnonpos | hpos
  · have hfactor : 0 ≤
        Real.sqrt c / Real.pi * (Real.exp (c - 1) / (2 * c)) ^ 2 := by positivity
    nlinarith
  · rw [le_div_iff₀ henergyPos] at hvar
    have hmul := mul_le_mul_of_nonneg_left henergy hpos.le
    nlinarith

end GaloisForLFunctions.RHTower

end
