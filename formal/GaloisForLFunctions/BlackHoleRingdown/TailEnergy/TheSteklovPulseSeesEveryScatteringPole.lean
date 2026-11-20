import GaloisForLFunctions.BlackHoleRingdown.TailEnergy.SpectraOfCascadedRectangularWindows
import GaloisForLFunctions.BlackHoleRingdown.TailEnergy.OnePulseEnergyForcesItsOwnBlindFrequencies
import GaloisForLFunctions.TransMetzlerWeilPositivity.ReceiverRate.TheSincProfileIsAProductOfSincs
import GaloisForLFunctions.HTGeometry.CompactFourierEntire

/-!
# One specified Steklov pulse sees every scattering pole

The smooth unit-mass convolution of the Steklov boxes has a Fourier
transform given on the real axis by its sinc product. Analytic
continuation identifies both sides throughout the complex plane.
Positive box widths put every blind frequency on the real axis, whereas
each zeta scattering pole is sampled strictly above it. Both the fixed
pulse and its derivative test all strip widths simultaneously.
-/

noncomputable section
open Complex Filter Topology
open scoped FourierTransform
open GaloisForLFunctions.TransMetzlerWeilPositivity GaloisForLFunctions.SpacingScaleHarmonicAnalysis
open RHTower
namespace GaloisForLFunctions.BlackHoleRingdown

/-- Complex pulse obtained from the real unit-mass Steklov profile. -/
def steklovScatteringPulse : CompactPulse where
  toFun u := (sincProfile u:ℂ)
  smooth := Complex.ofRealCLM.contDiff.comp contDiff_sincProfile
  compact := (hasCompactSupport_of_vanishes sincProfile_vanishesOff).comp_left Complex.ofReal_zero

theorem steklov_window_bounds (n : ℕ) : 0<sincRadius n ∧ sincRadius n≤1 := by
  refine ⟨sincRadius_pos n,?_⟩
  cases n with
  | zero => norm_num [sincRadius]
  | succ j => exact (steklovRadius_le_twelfth j).trans (by norm_num)

theorem summable_steklov_window_widths : Summable sincRadius := by
  apply (summable_nat_add_iff (f:=sincRadius) 1).mp
  exact summable_of_sum_range_le (fun n => (steklovRadius_pos n).le) sum_range_steklovRadius_le_half

private theorem real_window (r x : ℝ) : rectangularWindow r (x:ℂ)=(Real.sinc (r*x):ℂ) := by
  rw [rectangularWindow,←Complex.ofReal_mul]
  by_cases h : r*x=0
  · simp only [h,Complex.ofReal_zero,entireSinc_zero,Real.sinc_zero,Complex.ofReal_one]
  · rw [entireSinc_of_ne_zero (by exact_mod_cast h),Real.sinc_of_ne_zero h,
      Complex.ofReal_div,Complex.ofReal_sin]

private theorem real_spectrum (x : ℝ) : 2*(Real.pi:ℂ)*pulseAmplitude steklovScatteringPulse x =
    windowSpectrum sincRadius x := by
  let ξ := x/(2*Real.pi)
  have he : 2*Real.pi*ξ=x := by dsimp [ξ]; field_simp
  have hf := steklovScatteringPulse.fourier_damped 0 ξ
  have hd : steklovScatteringPulse.damped 0=(fun u : ℝ => (sincProfile u:ℂ)) := by
    funext u
    simp only [CompactPulse.damped,Complex.ofReal_zero,neg_zero,zero_mul,
      Complex.exp_zero,mul_one,steklovScatteringPulse]
  rw [hd,he,Complex.ofReal_zero,zero_mul,sub_zero] at hf
  rw [←hf]
  have hp := (windowSpectrum_hasProd (fun j => ⟨(steklov_window_bounds j).1.le,(steklov_window_bounds j).2⟩)
    summable_steklov_window_widths (x:ℂ)).tendsto_prod_nat.comp (tendsto_add_atTop_nat 1)
  apply tendsto_nhds_unique (tendsto_sincPartial ξ)
  apply hp.congr
  intro n
  dsimp only [Function.comp_apply]
  rw [sincPartial,Complex.ofReal_prod]
  apply Finset.prod_congr rfl
  intro j _
  rw [real_window,show 2*Real.pi*sincRadius j*ξ=sincRadius j*x by rw [←he]; ring]

/-- The scattering amplitude of the Steklov pulse at every complex
frequency is its normalized sinc product. -/
theorem steklov_pulse_amplitude (z : ℂ) :
    2*(Real.pi:ℂ)*pulseAmplitude steklovScatteringPulse z=windowSpectrum sincRadius z := by
  apply sub_eq_zero.mp
  exact HTGeometry.entire_eq_zero_of_vanishing_on_real_interval
    ((steklovScatteringPulse.differentiable_amplitude.const_mul (2*(Real.pi:ℂ))).sub
      (differentiable_windowSpectrum (fun j => ⟨(steklov_window_bounds j).1.le,(steklov_window_bounds j).2⟩) summable_steklov_window_widths))
    (t₀:=0) (r:=1) (by norm_num) (fun t _ => sub_eq_zero.mpr (real_spectrum t)) z

/-- Exact blind frequencies of the Steklov pulse: some box has a nonzero
integer multiple of π as its scaled frequency. -/
theorem steklov_pulse_blind_iff (z : ℂ) :
    pulseAmplitude steklovScatteringPulse z=0 ↔
      ∃ n : ℕ, ∃ k : ℤ, k≠0 ∧ (sincRadius n:ℂ)*z=(k:ℂ)*(Real.pi:ℂ) := by
  have hc : 2*(Real.pi:ℂ)≠0 := by exact_mod_cast (show (2:ℝ)*Real.pi≠0 by positivity)
  rw [←mul_eq_zero_iff_left hc,steklov_pulse_amplitude,windowSpectrum_zero_iff_factor
    (fun j => ⟨(steklov_window_bounds j).1.le,(steklov_window_bounds j).2⟩) summable_steklov_window_widths]
  apply exists_congr
  intro n
  by_cases h : (sincRadius n:ℂ)*z=0
  · rw [rectangularWindow,h,entireSinc_zero]
    constructor
    · intro he; exact (one_ne_zero he).elim
    · rintro ⟨k,hk,he⟩
      exact (mul_ne_zero (by exact_mod_cast hk) (by exact_mod_cast Real.pi_ne_zero) he.symm).elim
  · rw [rectangularWindow,entireSinc_of_ne_zero h,div_eq_zero_iff,or_iff_left h,Complex.sin_eq_zero_iff]
    exact ⟨fun ⟨k,hk⟩ => ⟨k,fun he => h (by simpa only [he,Int.cast_zero,zero_mul] using hk),hk⟩,
      fun ⟨k,_,hk⟩ => ⟨k,hk⟩⟩

private theorem steklov_sees_pole (ρ : ℂ) (hρ : riemannZeta ρ=0) :
    pulseAmplitude steklovScatteringPulse (-I*((ρ-1)/2))≠0 := by
  have h₁ : ρ.re<1 := lt_of_not_ge fun hge => riemannZeta_ne_zero_of_one_le_re hge hρ
  let z := -I*((ρ-1)/2)
  have him : z.im≠0 := by
    have he : z.im= -(ρ.re-1)/2 := by simp [z,Complex.mul_im] <;> ring
    rw [he]; exact ne_of_gt (by linarith only [h₁])
  intro h
  exact windowSpectrum_ne_zero_off_axis steklov_window_bounds summable_steklov_window_widths him
    ((steklov_pulse_amplitude z).symm.trans (by rw [show pulseAmplitude steklovScatteringPulse z=0 from h,mul_zero]))

/-- The unmodified unit-mass pulse tests every positive strip width
through the cumulative energy of its own reflected field. -/
theorem steklov_energy_strip_iff {δ : ℝ} (hd : 0<δ) (hq : δ≤1/4) :
    pulseDecayThrough steklovScatteringPulse δ ↔
      ∀ ρ : ℂ, riemannZeta ρ=0 → 0<ρ.re → ρ.re≤1-2*δ :=
  single_pulse_energy_strip (fun ρ hρ _ => steklov_sees_pole ρ hρ) hd hq

/-- The derivative pulse, which has zero time integral, gives the same
strip criterion. Both profiles are fixed across all strip widths. -/
theorem steklov_pulse_strip_iff {δ : ℝ} (hd : 0<δ) (hq : δ≤1/4) :
    pulseDecayThrough steklovScatteringPulse.D δ ↔
      ∀ ρ : ℂ, riemannZeta ρ=0 → 0<ρ.re → ρ.re≤1-2*δ := by
  constructor
  · intro h ρ hρ hpos
    exact le_of_not_gt fun hright => steklov_sees_pole ρ hρ
      (fast_derivative_hides_zeta_zero steklovScatteringPulse h hρ hpos hright)
  · intro h σ hσ hσδ
    obtain ⟨C,hC⟩ := (zeroFreeStrip_tailEnergy_equivalences hd hq).2.2.1.mp h
      (δ-σ) (sub_pos.mpr hσδ) steklovScatteringPulse.D
    exact ⟨C,fun T hT => by simpa only [sub_sub_cancel] using hC T hT⟩

/-- RH is equivalent to the quarter-rate law for the original box-convolution pulse. -/
theorem rh_iff_steklov_pulse_energy :
    RiemannHypothesis ↔ pulseDecayThrough steklovScatteringPulse (1/4) := by
  have hs := zeroFreeStrip_tailEnergy_equivalences (δ:=1/4) (by norm_num) le_rfl
  exact ((steklov_energy_strip_iff (by norm_num) le_rfl).trans
    (hs.1.trans RingdownRate.riemannHypothesis_iff_pulse_ringdown.symm)).symm

/-- RH is equivalent to the quarter-rate law for this prescribed pulse. -/
theorem rh_iff_steklov_derivative_energy :
    RiemannHypothesis ↔ pulseDecayThrough steklovScatteringPulse.D (1/4) := by
  have hs := zeroFreeStrip_tailEnergy_equivalences (δ:=1/4) (by norm_num) le_rfl
  exact ((steklov_pulse_strip_iff (by norm_num) le_rfl).trans
    (hs.1.trans RingdownRate.riemannHypothesis_iff_pulse_ringdown.symm)).symm

#print axioms steklov_pulse_amplitude
#print axioms steklov_pulse_blind_iff
#print axioms rh_iff_steklov_pulse_energy
#print axioms steklov_pulse_strip_iff
#print axioms rh_iff_steklov_derivative_energy
end GaloisForLFunctions.BlackHoleRingdown
