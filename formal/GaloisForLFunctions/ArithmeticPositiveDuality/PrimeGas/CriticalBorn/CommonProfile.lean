import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.ElementaryWave
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.TiltWindow
import GaloisForLFunctions.RHTower.PrimeValuationReflectedHellingerCriticalProfile

/-! # Two prime ensembles measure the same critical overlap profile -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn

open Filter Real
open scoped Topology

/-- Elementary reflected transition probability at displacement c/log N
and clock time t. -/
def windowFidelity (c t : ℝ) (N : ℕ) :=
  reflectedFidelity (((1/2+c/log N : ℝ):ℂ)+(t:ℂ)*Complex.I) N

private def harmonicPacket (N : ℕ) := powerMass 0 N

private theorem harmonic_grows : Tendsto harmonicPacket atTop atTop := by
  apply (mass_diverges.comp (cutoff_atTop.comp tendsto_natCast_atTop_atTop)).congr
  intro N
  simp only [Function.comp_apply,harmonicPacket,powerMass,mass,weight,zero_sub,rpow_neg_one]

private theorem window_eq (c t : ℝ) (N : ℕ) :
    windowFidelity c t N = (harmonicPacket N)^2 /
      (powerMass (-(2*c)/log N) N * powerMass (2*c/log N) N) := by
  simp only [windowFidelity,reflectedFidelity_eq,Complex.add_re,Complex.ofReal_re,Complex.mul_I_re,
    Complex.ofReal_im,neg_zero,add_zero,harmonicPacket]
  rw [show 1-2*(1/2+c/log N) = -(2*c)/log N by ring,neg_div,neg_neg]

private theorem window_pos (c t : ℝ) (N : ℕ) : 0 < windowFidelity c t N := by
  rw [window_eq]
  exact div_pos (sq_pos_of_pos (powerMass_pos 0 N))
    (mul_pos (powerMass_pos _ N) (powerMass_pos _ N))

private theorem scaled_inverse (c t : ℝ) {N : ℕ} (hN : 2≤N) :
    harmonicPacket N*((windowFidelity c t N)⁻¹-1) =
      _root_.RHTower.primeClockCutoffEnergy N (c/log N) +
      tiltCorrection (2*c) N * tiltCorrection (-(2*c)) N / harmonicPacket N := by
  rw [←tilt_pair_energy c hN,window_eq]
  simp only [tiltCorrection,harmonicPacket]
  field_simp [(powerMass_pos 0 N).ne',(powerMass_pos (2*c/log N) N).ne',
    (powerMass_pos (-(2*c)/log N) N).ne']
  ring

private theorem inverse_profile (c t : ℝ) :
    Tendsto (fun N => harmonicPacket N*((windowFidelity c t N)⁻¹-1)) atTop
      (𝓝 (_root_.RHTower.primeClockUniversalProfile c)) := by
  have tiny := ((tiltCorrection_limit (2*c)).mul (tiltCorrection_limit (-(2*c)))).div_atTop harmonic_grows
  have lim := (_root_.RHTower.tendsto_primeClockCutoffEnergy_critical_profile c).add tiny
  rw [add_zero] at lim
  apply lim.congr'
  filter_upwards [eventually_ge_atTop 2] with N hN
  exact (scaled_inverse c t hN).symm

/-- At every fixed inverse-energy displacement the normalized elementary
transition probability tends to one. -/
theorem windowFidelity_one (c t : ℝ) : Tendsto (windowFidelity c t) atTop (𝓝 1) := by
  have h := ((inverse_profile c t).div_atTop harmonic_grows).add_const 1
  rw [zero_add] at h
  have inv := h.inv₀ one_ne_zero
  rw [inv_one] at inv
  apply inv.congr
  intro N
  change (harmonicPacket N*((windowFidelity c t N)⁻¹-1)/harmonicPacket N+1)⁻¹ = _
  rw [mul_div_cancel_left₀ _ (show harmonicPacket N ≠ 0 from (powerMass_pos 0 N).ne'),sub_add_cancel,inv_inv]

/-- The first loss of elementary fidelity has exactly the already
normalized prime-clock profile on the scale of the harmonic prime sum. -/
theorem windowFidelity_profile (c t : ℝ) :
    Tendsto (fun N : ℕ => powerMass 0 N*(1-windowFidelity c t N)) atTop
      (𝓝 (_root_.RHTower.primeClockUniversalProfile c)) := by
  have h := (inverse_profile c t).mul (windowFidelity_one c t)
  rw [mul_one] at h
  apply h.congr
  intro N
  change harmonicPacket N*((windowFidelity c t N)⁻¹-1)*windowFidelity c t N = harmonicPacket N*(1-_)
  field_simp [(window_pos c t N).ne']

/-- The full product affinity equals, asymptotically, the exponential of
the negative rescaled elementary loss. -/
theorem productAffinity_elementary_loss (c t : ℝ) :
    Tendsto (fun N : ℕ => _root_.RHTower.reflectedPrimeValuationSquaredHellingerLE N c *
      exp (powerMass 0 N*(1-windowFidelity c t N))) atTop (𝓝 1) := by
  have lim := (_root_.RHTower.tendsto_reflectedPrimeValuationSquaredHellingerLE_critical_profile c).mul
    (continuous_exp.continuousAt.tendsto.comp (windowFidelity_profile c t))
  rw [←exp_add,neg_add_cancel,exp_zero] at lim
  exact lim.congr (fun N => rfl)

#print axioms windowFidelity_one
#print axioms windowFidelity_profile
#print axioms productAffinity_elementary_loss

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn
