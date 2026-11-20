import GaloisForLFunctions.BlackHoleRingdown.TailEnergy.TheExactTypeOfAWindowSpectrum
import GaloisForLFunctions.BlackHoleRingdown.TailEnergy.TheSteklovPulseSeesEveryScatteringPole
import GaloisForLFunctions.TransMetzlerWeilPositivity.ReceiverRate.TheScaleAveragedSincProfile

/-!
# Both support endpoints of the Steklov pulse

The sum of the box half-widths is the exact support radius of the
unit-mass Steklov profile. Both endpoints belong to the closed support,
even though the profile itself vanishes there. An endpoint gap would
give a strictly smaller exponential type on the corresponding imaginary ray.
-/

noncomputable section
open Complex Filter MeasureTheory Set Topology
open GaloisForLFunctions.TransMetzlerWeilPositivity GaloisForLFunctions.SpacingScaleHarmonicAnalysis
namespace GaloisForLFunctions.BlackHoleRingdown

def steklovSupportRadius : ℝ := ∑' j, sincRadius j

/-- The regularizing base at stage M already fits inside the unused
box with index M+1. Thus every approximant obeys the exact outer bound. -/
theorem steklov_profile_supported : SupportedIn steklovSupportRadius sincProfile := by
  intro x hx
  have h (M : ℕ) : boxSeq M x=0 := by
    have hR := summable_steklov_window_widths.sum_le_tsum (Finset.range (M+1+1))
      (fun j _ => (sincRadius_pos j).le)
    rw [Finset.sum_range_succ] at hR
    have hb : SupportedIn (steklovRadius M/2) (boxBase M) := fun _ hu => boxBase_eq_zero hu
    apply supportedIn_boxStek hb (M+1) x
    change (∑ j ∈ Finset.range (M+1), sincRadius j)+steklovRadius M ≤ steklovSupportRadius at hR
    linarith only [hR,hx,steklovRadius_pos M]
  exact tendsto_nhds_unique (tendstoUniformly_boxSeq.tendsto_at x)
    (tendsto_const_nhds.congr fun n => (h n).symm)

private theorem spectrum_at_signed_height (y : ℝ) {s : ℝ} (hs : s=1 ∨ s= -1) :
    windowSpectrum sincRadius (((s*y:ℝ):ℂ)*I)=windowSpectrum sincRadius ((y:ℂ)*I) := by
  rcases hs with rfl | rfl
  · rw [one_mul]
  · rw [neg_one_mul,Complex.ofReal_neg,neg_mul,windowSpectrum_even]

private theorem bound_from_one_end {s A : ℝ} (hs : s=1 ∨ s= -1)
    (hvan : ∀ x, A<s*x → sincProfile x=0) {y : ℝ} (hy : 0 < y) :
    ‖windowSpectrum sincRadius ((y:ℂ)*I)‖ ≤ Real.exp (A*y) := by
  let w : ℂ := ((s*y:ℝ):ℂ)*I
  have hp : (2*(Real.pi:ℂ))≠0 := mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)
  rw [←spectrum_at_signed_height y hs,←steklov_pulse_amplitude,pulseAmplitude,
    ←mul_assoc,mul_inv_cancel₀ hp,one_mul]
  have hi : Integrable sincProfile := contDiff_sincProfile.continuous.integrable_of_hasCompactSupport
    (hasCompactSupport_of_vanishes sincProfile_vanishesOff)
  have h := norm_integral_le_of_norm_le (hi.mul_const (Real.exp (A*y)))
    (f:=fun x : ℝ => steklovScatteringPulse x * Complex.exp (-(I*w*(x:ℂ)))) (Eventually.of_forall fun x => by
      change ‖(sincProfile x:ℂ)*Complex.exp (-(I*w*(x:ℂ)))‖ ≤ _
      rw [norm_mul,Complex.norm_real,Real.norm_of_nonneg (sincProfile_nonneg _),Complex.norm_exp]
      by_cases hx : A<s*x
      · simp only [hvan x hx,zero_mul]
      · apply mul_le_mul_of_nonneg_left _ (sincProfile_nonneg x)
        apply Real.exp_le_exp.mpr
        have he : (-(I*w*(x:ℂ))).re=s*x*y := by
          dsimp only [w]
          simp [Complex.mul_re,Complex.mul_im]
          <;> ring
        rw [he]
        exact mul_le_mul_of_nonneg_right (le_of_not_gt hx) hy.le)
  simpa only [integral_mul_const,integral_sincProfile,one_mul] using h

/-- In every neighborhood just inside either endpoint there is positive
pulse mass density. In particular neither end can be moved inward. -/
theorem steklov_both_ends_are_sharp {A : ℝ} (hA : A < steklovSupportRadius)
    {s : ℝ} (hs : s=1 ∨ s= -1) : ∃ x : ℝ, A<s*x ∧ 0<sincProfile x := by
  by_contra! hn
  have hvan (x : ℝ) (hx : A<s*x) := le_antisymm (hn x hx) (sincProfile_nonneg x)
  have ht := windowSpectrum_exact_type steklov_window_bounds summable_steklov_window_widths
  have hle : steklovSupportRadius≤A := le_of_tendsto ht (by
    filter_upwards [eventually_gt_atTop (0:ℝ)] with y hy
    have hw : (((y:ℂ)*I):ℂ).im≠0 := by simpa using hy.ne'
    have hpos := norm_pos_iff.mpr (windowSpectrum_ne_zero_off_axis steklov_window_bounds
      summable_steklov_window_widths hw)
    have hlog := Real.log_le_log hpos (bound_from_one_end hs hvan hy)
    rw [Real.log_exp] at hlog
    exact (div_le_iff₀ hy).mpr hlog)
  exact hA.not_ge hle

/-- Exact coordinate extrema of the ordinary support. -/
theorem steklov_support_least_upper_bounds :
    IsLUB (Function.support sincProfile) steklovSupportRadius ∧
      IsGLB (Function.support sincProfile) (-steklovSupportRadius) := by
  have hg {x : ℝ} (hx : x∈Function.support sincProfile) : |x|≤steklovSupportRadius := by
    by_contra! h; exact hx (steklov_profile_supported x h)
  constructor
  · refine ⟨fun x hx => (le_abs_self x).trans (hg hx),?_⟩
    intro b hb
    by_contra! h
    obtain ⟨x,hx,hpos⟩ := steklov_both_ends_are_sharp h (s:=1) (Or.inl rfl)
    rw [one_mul] at hx
    exact hx.not_ge (hb (show x∈Function.support sincProfile from hpos.ne'))
  · refine ⟨fun x hx => (abs_le.mp (hg hx)).1,?_⟩
    intro b hb
    by_contra! h
    have hh : -b<steklovSupportRadius := by linarith only [h]
    obtain ⟨x,hx,hpos⟩ := steklov_both_ends_are_sharp hh (s:= -1) (Or.inr rfl)
    rw [neg_one_mul] at hx
    have hb' := hb (show x∈Function.support sincProfile from hpos.ne')
    linarith only [hb',hx]

#print axioms steklov_profile_supported
#print axioms steklov_support_least_upper_bounds
end GaloisForLFunctions.BlackHoleRingdown
