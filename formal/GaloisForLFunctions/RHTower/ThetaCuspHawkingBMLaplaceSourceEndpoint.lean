import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMLaplaceSourceContinuation
import Mathlib.Analysis.Calculus.MeanValue

/-! Uniform endpoint control of the literal frequency-dependent source remainder. -/
namespace RHTower.D4BMLaplaceRadial
open Complex Filter Topology Set Metric
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

private def sourceLogHeight (t : ℝ) : ℝ := Real.log (1+Real.sqrt (1-t))
private def sourceLogHeightFirst (t : ℝ) : ℝ :=
  -(1/(2*Real.sqrt (1-t)))/(1+Real.sqrt (1-t))

private theorem sourceLogHeight_deriv {t : ℝ} (ht : t < 1) :
    HasDerivAt sourceLogHeight (sourceLogHeightFirst t) t := by
  have hs := (Real.hasDerivAt_sqrt (show 1-t ≠ 0 by linarith)).comp t ((hasDerivAt_id t).const_sub 1)
  have hp := hs.const_add 1
  have hl := (Real.hasDerivAt_log (show 1+Real.sqrt (1-t) ≠ 0 by positivity)).comp t hp
  unfold sourceLogHeight sourceLogHeightFirst
  convert! hl using 1
  ring

private theorem sourceLogHeight_continuous : Continuous sourceLogHeight := by
  unfold sourceLogHeight
  apply Continuous.log (by fun_prop)
  intro t
  positivity

private theorem sourceLogHeightFirst_continuousAt {t : ℝ} (ht : t < 1) :
    ContinuousAt sourceLogHeightFirst t := by
  have hs : 0 < Real.sqrt (1-t) := Real.sqrt_pos.mpr (by linarith)
  unfold sourceLogHeightFirst
  fun_prop (disch := positivity)

private theorem sourceRemainder_exp (s w a J K T : ℂ) (t : ℝ) :
    sourceRemainder s w a J K T t =
      Complex.exp ((sourceLogHeight t:ℂ)*(2*s-w))*a^(2 : ℕ)*
        (((5*s^(2 : ℕ)+15*s+4)/4)*J+(1-(t:ℂ))*(s*(s-1)/4*((s+2)^(2 : ℕ)*J-K)))*T := by
  unfold sourceRemainder power sourceLogHeight
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (show 1+Real.sqrt (1-t) ≠ 0 by positivity)),
    Complex.ofReal_log (show 0 ≤ 1+Real.sqrt (1-t) by positivity)]
  ring

private def sourceRemainderJet (s w a J K T : ℂ) (t : ℝ) : ℂ :=
  Complex.exp ((sourceLogHeight t:ℂ)*(2*s-w)) * ((sourceLogHeightFirst t:ℂ)*(2*s-w))*a^(2 : ℕ)*
    (((5*s^(2 : ℕ)+15*s+4)/4)*J+(1-(t:ℂ))*(s*(s-1)/4*((s+2)^(2 : ℕ)*J-K)))*T -
  Complex.exp ((sourceLogHeight t:ℂ)*(2*s-w))*a^(2 : ℕ)*(s*(s-1)/4*((s+2)^(2 : ℕ)*J-K))*T

private theorem sourceRemainder_hasDerivAt (s w a J K T : ℂ) {t : ℝ} (ht : t < 1) :
    HasDerivAt (sourceRemainder s w a J K T) (sourceRemainderJet s w a J K T t) t := by
  have he := (((sourceLogHeight_deriv ht).ofReal_comp).mul_const (2*s-w)).cexp
  have hpoly := ((((hasDerivAt_id t).ofReal_comp).const_sub (1:ℂ)).mul_const
    (s*(s-1)/4*((s+2)^(2 : ℕ)*J-K))).const_add (((5*s^(2 : ℕ)+15*s+4)/4)*J)
  have hd := (((he.mul_const (a^(2 : ℕ))).mul hpoly).mul_const T)
  have hf : sourceRemainder s w a J K T = fun v =>
      Complex.exp ((sourceLogHeight v:ℂ)*(2*s-w))*a^(2 : ℕ)*
        (((5*s^(2 : ℕ)+15*s+4)/4)*J+(1-(v:ℂ))*(s*(s-1)/4*((s+2)^(2 : ℕ)*J-K)))*T :=
    funext (sourceRemainder_exp s w a J K T)
  rw [hf]
  convert! hd using 1
  simp only [sourceRemainderJet,Complex.ofReal_one,id_eq]
  ring

private theorem sourceRemainderJet_joint_continuousAt (s a J K T : ℂ) (p : ℂ × ℝ) (hp : p.2 < 1) :
    ContinuousAt (fun q : ℂ × ℝ => sourceRemainderJet s q.1 a J K T q.2) p := by
  have hh := sourceLogHeight_continuous.continuousAt.comp (continuous_snd.continuousAt (x := p))
  have hd := (sourceLogHeightFirst_continuousAt hp).comp (continuous_snd.continuousAt (x := p))
  unfold sourceRemainderJet
  fun_prop

/-- The undressed source remainder is entire in frequency, also at the horizon itself. -/
theorem sourceRemainder_frequency_entire (s a J K T : ℂ) (t : ℝ) :
    Differentiable ℂ (fun w => sourceRemainder s w a J K T t) := by
  have hp := (power_exponent_entire (show 0 < 1+Real.sqrt (1-t) by positivity)).comp
    (show Differentiable ℂ (fun w : ℂ => 2*s-w) by fun_prop)
  simpa only [sourceRemainder,Function.comp_def] using!
    (((hp.mul_const (a^(2 : ℕ))).mul_const
      (((5*s^(2 : ℕ)+15*s+4)/4)*J+(1-(t:ℂ))*s*(s-1)/4*((s+2)^(2 : ℕ)*J-K))).mul_const T)

/-- The literal undressed remainder is jointly continuous in frequency and radius. -/
theorem sourceRemainder_joint_continuous (s a J K T : ℂ) :
    Continuous (fun p : ℂ × ℝ => sourceRemainder s p.1 a J K T p.2) := by
  have hh : Continuous (fun p : ℂ × ℝ => sourceLogHeight p.2) := sourceLogHeight_continuous.comp continuous_snd
  simp_rw [sourceRemainder_exp]
  fun_prop

/-- The original source remainder has a uniform first-order endpoint bound on a
frequency ball; source amplitudes and angular coefficients remain fixed. -/
theorem sourceRemainder_uniform_first_bound (s w a J K T : ℂ) {b : ℝ} (_hb : 0 ≤ b) (hb1 : b < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u ∈ ball w 1, ∀ t ∈ Icc (0:ℝ) b,
      ‖sourceRemainder s u a J K T t-sourceRemainder s u a J K T 0‖ ≤ C*t := by
  have hcompact : IsCompact (closedBall w 1 ×ˢ Icc (0:ℝ) b) := (isCompact_closedBall w 1).prod isCompact_Icc
  have hcont : ContinuousOn (fun p : ℂ × ℝ => sourceRemainderJet s p.1 a J K T p.2)
      (closedBall w 1 ×ˢ Icc (0:ℝ) b) := by
    intro p hp
    exact (sourceRemainderJet_joint_continuousAt s a J K T p (hp.2.2.trans_lt hb1)).continuousWithinAt
  obtain ⟨C,hC⟩ := hcompact.exists_bound_of_continuousOn hcont
  refine ⟨max C 0,le_max_right _ _,?_⟩
  intro u hu t ht
  have hd (v : ℝ) (hv : v ∈ Icc (0:ℝ) b) :=
    (sourceRemainder_hasDerivAt s u a J K T (hv.2.trans_lt hb1)).hasDerivWithinAt (s := Icc (0:ℝ) b)
  have hbound (v : ℝ) (hv : v ∈ Ico (0:ℝ) b) : ‖sourceRemainderJet s u a J K T v‖ ≤ max C 0 :=
    (hC (u,v) ⟨ball_subset_closedBall hu,⟨hv.1,hv.2.le⟩⟩).trans (le_max_left _ _)
  simpa only [sub_zero] using norm_image_sub_le_of_norm_deriv_le_segment' hd hbound t ht

end
end RHTower.D4BMLaplaceRadial
