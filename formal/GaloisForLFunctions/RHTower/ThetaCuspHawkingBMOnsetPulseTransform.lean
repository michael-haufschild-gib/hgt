import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMSmoothOnsetLaplace

/-!
# The onset derivative-pulse transform

`onsetCorrection v w = ∫_{0}^{1} (χ(u) - 1) e^{(v-w)u} du` with `χ = Real.smoothTransition`.
One integration by parts gives

`1 + (w - v) * onsetCorrection v w = ∫_{0}^{1} χ'(u) e^{(v-w)u} du`.

The right-hand side is the Laplace transform of the onset derivative pulse at exponent `v - w`.
It is an entire function of the exponent with value `1` at exponent `0`.  Hence along every ray
`L ↦ L * z₀` of exponents its zeros are isolated, and at real exponents it is strictly positive.

This isolates the onset factor of the fundamental Laurent coefficient; it evaluates no physical
source and proves no extinction.
-/

open MeasureTheory Set Filter Topology intervalIntegral
open GaloisForLFunctions.HTGeometry
namespace RHTower.D4BMModularCore
set_option autoImplicit false
noncomputable section

/-- Laplace transform of the onset derivative pulse at exponent `z`. -/
def onsetPulseTransform (z : ℂ) : ℂ :=
  ∫ u in (0:ℝ)..1, ((deriv Real.smoothTransition u : ℝ) : ℂ) * Complex.exp (z * (u:ℂ))

private theorem hasDerivAt_transition_sub_one (x : ℝ) :
    HasDerivAt (fun u : ℝ => ((Real.smoothTransition u : ℂ) - 1))
      ((deriv Real.smoothTransition x : ℝ) : ℂ) x := by
  have h : HasDerivAt Real.smoothTransition (deriv Real.smoothTransition x) x :=
    (((Real.smoothTransition.contDiff (n := 1)).differentiable (by simp)) x).hasDerivAt
  exact h.ofReal_comp.sub_const 1

private theorem hasDerivAt_exp_ray (z : ℂ) (x : ℝ) :
    HasDerivAt (fun u : ℝ => Complex.exp (z * (u:ℂ))) (z * Complex.exp (z * (x:ℂ))) x := by
  have hg : HasDerivAt (fun y : ℂ => z * y) z (x:ℂ) := by
    simpa using (hasDerivAt_id (x:ℂ)).const_mul z
  have h : HasDerivAt (fun y : ℂ => Complex.exp (z * y)) (Complex.exp (z * (x:ℂ)) * z) (x:ℂ) :=
    (Complex.hasDerivAt_exp (z * (x:ℂ))).comp (x:ℂ) hg
  rw [mul_comm]
  exact h.comp_ofReal

/-- One integration by parts: the cleared onset numerator is the derivative-pulse transform. -/
theorem onsetPulseTransform_sub (v w : ℂ) :
    onsetPulseTransform (v - w) = 1 + (w - v) * onsetCorrection v w := by
  have hu : ∀ x ∈ uIcc (0:ℝ) 1, HasDerivAt (fun u : ℝ => ((Real.smoothTransition u : ℂ) - 1))
      ((deriv Real.smoothTransition x : ℝ) : ℂ) x := fun x _ => hasDerivAt_transition_sub_one x
  have hv : ∀ x ∈ uIcc (0:ℝ) 1, HasDerivAt (fun u : ℝ => Complex.exp ((v - w) * (u:ℂ)))
      ((v - w) * Complex.exp ((v - w) * (x:ℂ))) x := fun x _ => hasDerivAt_exp_ray (v - w) x
  have hcχ : Continuous fun x : ℝ => ((deriv Real.smoothTransition x : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp continuous_deriv_smoothTransition
  have hce : Continuous fun x : ℝ => Complex.exp ((v - w) * (x:ℂ)) := by fun_prop
  have hu' : IntervalIntegrable (fun x : ℝ => ((deriv Real.smoothTransition x : ℝ) : ℂ)) volume 0 1 :=
    hcχ.intervalIntegrable 0 1
  have hv' : IntervalIntegrable (fun x : ℝ => (v - w) * Complex.exp ((v - w) * (x:ℂ))) volume 0 1 :=
    (continuous_const.mul hce).intervalIntegrable 0 1
  have key := integral_deriv_mul_eq_sub hu hv hu' hv'
  have hA : IntervalIntegrable (fun x : ℝ => ((deriv Real.smoothTransition x : ℝ) : ℂ) *
      Complex.exp ((v - w) * (x:ℂ))) volume 0 1 := (hcχ.mul hce).intervalIntegrable 0 1
  have hB : IntervalIntegrable (fun x : ℝ => ((Real.smoothTransition x : ℂ) - 1) *
      ((v - w) * Complex.exp ((v - w) * (x:ℂ)))) volume 0 1 :=
    (((Complex.continuous_ofReal.comp Real.smoothTransition.continuous).sub continuous_const).mul
      (continuous_const.mul hce)).intervalIntegrable 0 1
  rw [integral_add hA hB] at key
  have hbd : ((Real.smoothTransition (1:ℝ) : ℂ) - 1) * Complex.exp ((v - w) * ((1:ℝ):ℂ)) -
      ((Real.smoothTransition (0:ℝ) : ℂ) - 1) * Complex.exp ((v - w) * ((0:ℝ):ℂ)) = 1 := by
    simp [Real.smoothTransition.one, Real.smoothTransition.zero]
  have key2 : (∫ x in (0:ℝ)..1, ((deriv Real.smoothTransition x : ℝ) : ℂ) *
      Complex.exp ((v - w) * (x:ℂ))) +
      (∫ x in (0:ℝ)..1, ((Real.smoothTransition x : ℂ) - 1) *
        ((v - w) * Complex.exp ((v - w) * (x:ℂ)))) = 1 := by
    exact key.trans hbd
  have hB' : (∫ x in (0:ℝ)..1, ((Real.smoothTransition x : ℂ) - 1) *
      ((v - w) * Complex.exp ((v - w) * (x:ℂ)))) = (v - w) * onsetCorrection v w := by
    rw [onsetCorrection, ← intervalIntegral.integral_of_le zero_le_one,
      ← intervalIntegral.integral_const_mul]
    apply integral_congr
    intro x _
    ring
  rw [hB'] at key2
  unfold onsetPulseTransform
  linear_combination key2

theorem onsetPulseTransform_zero : onsetPulseTransform 0 = 1 := by
  have h := onsetPulseTransform_sub 0 0
  simpa using h

theorem onsetPulseTransform_eq_one_sub (z : ℂ) :
    onsetPulseTransform z = 1 - z * onsetCorrection 0 (-z) := by
  have h := onsetPulseTransform_sub 0 (-z)
  rw [zero_sub, neg_neg, sub_zero] at h
  rw [h]
  ring

/-- The derivative-pulse transform is entire. -/
theorem differentiable_onsetPulseTransform : Differentiable ℂ onsetPulseTransform := by
  have he : onsetPulseTransform = fun z => 1 - z * onsetCorrection 0 (-z) :=
    funext onsetPulseTransform_eq_one_sub
  rw [he]
  exact (differentiable_const (1:ℂ)).sub
    (differentiable_id.mul ((onsetCorrection_entire 0).comp differentiable_neg))

theorem analyticOnNhd_onsetPulseTransform : AnalyticOnNhd ℂ onsetPulseTransform univ :=
  Complex.analyticOnNhd_univ_iff_differentiable.mpr differentiable_onsetPulseTransform

/-- Along any ray of exponents the pulse transform has only isolated zeros. -/
theorem onsetPulseTransform_ray_eventually_ne_zero (z₀ L₀ : ℂ) :
    ∀ᶠ L in 𝓝[≠] L₀, onsetPulseTransform (L * z₀) ≠ 0 := by
  have hd : Differentiable ℂ (fun L : ℂ => onsetPulseTransform (L * z₀)) :=
    differentiable_onsetPulseTransform.comp (differentiable_id.mul_const z₀)
  have ha : AnalyticOnNhd ℂ (fun L : ℂ => onsetPulseTransform (L * z₀)) univ :=
    Complex.analyticOnNhd_univ_iff_differentiable.mpr hd
  rcases (ha L₀ (mem_univ _)).eventually_eq_zero_or_eventually_ne_zero with h | h
  · exfalso
    have h0 := ha.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ
      (mem_univ L₀) h (mem_univ (0:ℂ))
    simp [onsetPulseTransform_zero] at h0
  · exact h

/-- Every real duration has arbitrarily close real durations with nonzero transform. -/
theorem exists_real_near_onsetPulseTransform_ne_zero (z₀ : ℂ) (L₀ ε : ℝ) (hε : 0 < ε) :
    ∃ L : ℝ, |L - L₀| < ε ∧ L ≠ L₀ ∧ onsetPulseTransform ((L:ℂ) * z₀) ≠ 0 := by
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhdsWithin_iff.mp
    (onsetPulseTransform_ray_eventually_ne_zero z₀ (L₀:ℂ))
  have hm0 : 0 < min δ ε := lt_min hδ hε
  refine ⟨L₀ + min δ ε / 2, ?_, ?_, ?_⟩
  · rw [add_sub_cancel_left, abs_of_pos (by linarith)]
    linarith [min_le_right δ ε]
  · intro h
    linarith
  · apply hball
    refine ⟨?_, ?_⟩
    · rw [Metric.mem_ball, Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real,
        Real.norm_eq_abs, add_sub_cancel_left,
        abs_of_pos (by linarith)]
      linarith [min_le_left δ ε]
    · simp only [mem_compl_iff, mem_singleton_iff]
      intro h
      have h' := Complex.ofReal_inj.mp h
      linarith

/-- At a real exponent the transform is the real derivative-pulse integral. -/
theorem onsetPulseTransform_ofReal_eq (x : ℝ) :
    onsetPulseTransform (x:ℂ) =
      ((∫ u in (0:ℝ)..1, deriv Real.smoothTransition u * Real.exp (x * u) : ℝ) : ℂ) := by
  unfold onsetPulseTransform
  rw [← intervalIntegral.integral_ofReal]
  apply integral_congr
  intro u _
  push_cast
  ring

/-- At a real exponent the transform is strictly positive. -/
theorem onsetPulseTransform_ofReal_re_pos (x : ℝ) : 0 < (onsetPulseTransform (x:ℂ)).re := by
  rw [onsetPulseTransform_ofReal_eq, Complex.ofReal_re]
  have hm0 : 0 < min 1 (Real.exp x) := lt_min one_pos (Real.exp_pos x)
  have hχ' : ∀ u, 0 ≤ deriv Real.smoothTransition u :=
    fun _ => Real.smoothTransition.monotone.deriv_nonneg
  have hexp : ∀ u ∈ Icc (0:ℝ) 1, min 1 (Real.exp x) ≤ Real.exp (x * u) := by
    intro u hu
    rcases le_or_gt 0 x with hx | hx
    · calc min 1 (Real.exp x) ≤ 1 := min_le_left _ _
        _ = Real.exp 0 := Real.exp_zero.symm
        _ ≤ Real.exp (x * u) := Real.exp_le_exp.mpr (by nlinarith [hu.1])
    · calc min 1 (Real.exp x) ≤ Real.exp x := min_le_right _ _
        _ ≤ Real.exp (x * u) := Real.exp_le_exp.mpr (by nlinarith [hu.1, hu.2])
  have hlow : (∫ u in (0:ℝ)..1, deriv Real.smoothTransition u * min 1 (Real.exp x)) ≤
      ∫ u in (0:ℝ)..1, deriv Real.smoothTransition u * Real.exp (x * u) := by
    apply intervalIntegral.integral_mono_on zero_le_one
    · exact (continuous_deriv_smoothTransition.mul continuous_const).intervalIntegrable 0 1
    · exact (continuous_deriv_smoothTransition.mul (by fun_prop)).intervalIntegrable 0 1
    · intro u hu
      exact mul_le_mul_of_nonneg_left (hexp u hu) (hχ' u)
  have hval : (∫ u in (0:ℝ)..1, deriv Real.smoothTransition u * min 1 (Real.exp x)) =
      min 1 (Real.exp x) := by
    rw [intervalIntegral.integral_mul_const, integral_deriv_eq_sub]
    · simp [Real.smoothTransition.one, Real.smoothTransition.zero]
    · intro u _
      exact ((Real.smoothTransition.contDiff (n := 1)).differentiable (by simp)) u
    · exact continuous_deriv_smoothTransition.intervalIntegrable 0 1
  linarith

theorem onsetPulseTransform_ofReal_ne_zero (x : ℝ) : onsetPulseTransform (x:ℂ) ≠ 0 := by
  intro h
  have hp := onsetPulseTransform_ofReal_re_pos x
  rw [h] at hp
  simp at hp

end
end RHTower.D4BMModularCore
