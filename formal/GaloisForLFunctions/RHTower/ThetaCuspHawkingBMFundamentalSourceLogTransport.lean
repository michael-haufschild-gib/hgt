import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMFundamentalJacobiLogIntegral
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMFundamentalCountertermTransport
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMFundamentalSourceMomentTransport

/-! Original physical-radius logarithmic action, with its original finite counterterm. -/
open Complex Set Filter Topology MeasureTheory
namespace RHTower.D4BMJointSource
open D4BMLaplaceRadial GaloisForLFunctions.HTGeometry
noncomputable section
set_option autoImplicit false

def fundamentalSourceTortoiseMoment (w s a : ℂ) : ℂ :=
  2*a^(2 : ℕ)*(fundamentalMomentConstant s*fundamentalJacobiTortoiseMoment 2 w s+
    fundamentalMomentQuadratic w s*fundamentalJacobiTortoiseMoment 4 w s)

theorem fundamentalJacobiTortoiseDensity_intervalIntegrable (n : ℕ) (w s : ℂ)
    {e : ℝ} (he : 0<e) (he1 : e≤1) :
    IntervalIntegrable (fun x : ℝ => (x:ℂ)^w*fundamentalJacobiCore n s x*
      (((Real.log x:ℂ)-(Real.log (2-x):ℂ))/2)) volume e 1 := by
  apply ContinuousOn.intervalIntegrable_of_Icc he1
  intro x hx
  have hx0 := he.trans_le hx.1
  have hx2 : 0<2-x := by linarith [hx.2]
  exact (((power_derivatives w hx0).1.continuousAt.mul
    (fundamentalJacobiCore_continuousAt n s (by linarith [hx.2]))).mul
      (((Real.hasDerivAt_log hx0.ne').ofReal_comp.continuousAt.sub
        (Complex.continuous_ofReal.continuousAt.comp
          ((Real.hasDerivAt_log hx2.ne').continuousAt.comp (continuousAt_const.sub continuousAt_id)))).div_const 2)).continuousWithinAt

/-- Exact positive-cutoff pullback of the physical tortoise-weighted source. -/
theorem fundamentalSourceTortoise_polynomial_cutoff (w s a : ℂ) {e : ℝ}
    (he : 0<e) (he1 : e≤1) :
    (∫ z in (e*(2-e))..1, (z:ℂ)^w*fundamentalSourceCore w s a z*(tortoiseOf z:ℂ))=
      2*a^(2 : ℕ)*(fundamentalMomentConstant s*
        (∫ x in e..1, (x:ℂ)^w*fundamentalJacobiCore 2 s x*
          (((Real.log x:ℂ)-(Real.log (2-x):ℂ))/2))+
      fundamentalMomentQuadratic w s*
        (∫ x in e..1, (x:ℂ)^w*fundamentalJacobiCore 4 s x*
          (((Real.log x:ℂ)-(Real.log (2-x):ℂ))/2))) := by
  have hd (x : ℝ) : HasDerivAt (fun y : ℝ => y*(2-y)) (2*(1-x)) x := by
    have h := (hasDerivAt_id x).mul ((hasDerivAt_id x).const_sub 2)
    exact h.congr_deriv (by dsimp only [id_eq];ring)
  have hi := intervalIntegral.integral_deriv_smul_comp_of_deriv_nonneg
    (g:=fun z : ℝ => (z:ℂ)^w*fundamentalSourceCore w s a z*(tortoiseOf z:ℂ))
    (f:=fun x : ℝ => x*(2-x)) (f':=fun x=>2*(1-x))
    (a:=e) (b:=1) (by fun_prop) (fun x _=>hd x)
    (fun x hx=>by rw [min_eq_left he1,max_eq_right he1] at hx;linarith [hx.2])
  norm_num only [sub_self,sub_zero,mul_one,one_mul] at hi
  rw [← hi]
  calc
    _ = ∫ x in e..1, 2*a^(2 : ℕ)*(fundamentalMomentConstant s*
        ((x:ℂ)^w*fundamentalJacobiCore 2 s x*(((Real.log x:ℂ)-(Real.log (2-x):ℂ))/2))+
      fundamentalMomentQuadratic w s*
        ((x:ℂ)^w*fundamentalJacobiCore 4 s x*(((Real.log x:ℂ)-(Real.log (2-x):ℂ))/2))) := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [uIcc_of_le he1] at hx
      have hx0 := he.trans_le hx.1
      have hs := fundamentalSourceDensity_polynomial_coordinate w s a hx0 hx.2
      simp only [Function.comp_apply,Complex.real_smul]
      rw [tortoiseOf_polynomial_coordinate hx0 hx.2]
      push_cast at hs ⊢
      linear_combination (((Real.log x:ℂ)-(Real.log (2-x):ℂ))/2)*hs
    _ = _ := by
      rw [intervalIntegral.integral_const_mul,
        intervalIntegral.integral_add
          ((fundamentalJacobiTortoiseDensity_intervalIntegrable 2 w s he he1).const_mul _)
          ((fundamentalJacobiTortoiseDensity_intervalIntegrable 4 w s he he1).const_mul _),
        intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul]

/-- The logarithmic action in the original radius has exactly the compact
period value; the nonlinear transport introduces no new finite constant. -/
theorem fundamentalSourceTortoiseMoment_original_cutoff (w s a : ℂ)
    (hw : -2<w.re) (hw1 : w+1≠0) :
    Tendsto (fun e : ℝ =>
      (∫ z in (e*(2-e))..1, (z:ℂ)^w*fundamentalSourceCore w s a z*(tortoiseOf z:ℂ))+
      fundamentalSourceCore w s a 0*((e*(2-e):ℝ):ℂ)^(w+1)*
        (((Real.log (e*(2-e)):ℂ)/2-(Real.log 2:ℂ))/(w+1)-1/(2*(w+1)^(2 : ℕ))))
      (𝓝[>] (0:ℝ)) (𝓝 (fundamentalSourceTortoiseMoment w s a)) := by
  have hj := (((fundamentalJacobiTortoiseMoment_cutoff 2 w s hw hw1).const_mul (fundamentalMomentConstant s)).add
    ((fundamentalJacobiTortoiseMoment_cutoff 4 w s hw hw1).const_mul (fundamentalMomentQuadratic w s))).const_mul (2*a^(2 : ℕ))
  have hc := fundamentalMoment_log_counterterm_transport (fundamentalSourceCore w s a 0) w hw
  have h := hj.add hc
  simp only [add_zero] at h
  apply h.congr'
  filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0:ℝ)<1)] with e he
  rw [fundamentalSourceTortoise_polynomial_cutoff w s a he.1 he.2.le,
    fundamentalSourceCore_scaled_endpoint]
  simp only [fundamentalJacobiTortoisePrimitive,fundamentalJacobiCore_zero]
  ring

end
end RHTower.D4BMJointSource
