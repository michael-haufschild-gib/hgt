import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMFundamentalForcingMoment
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMOriginalElementaryQNMAction

/-! Attachment of both original forcing coefficients and the full physical forcing integral. -/
open Complex Set Filter Topology MeasureTheory
namespace RHTower.D4BMJointSource
open D4BMLaplaceRadial D4BMOriginalSourceResolvent GaloisForLFunctions.HTGeometry
noncomputable section
set_option autoImplicit false

def fundamentalSourceForcingMoment (w s a : ℂ) : ℂ :=
  2*a^(2 : ℕ)*(fundamentalMomentConstant s*fundamentalJacobiForcingMoment 2 w s+
    fundamentalMomentQuadratic w s*fundamentalJacobiForcingMoment 4 w s)

theorem fundamentalSourceDensity_forcing_coordinate (w s a : ℂ) {x : ℝ}
    (hx : 0<x) (hx1 : x≤1) :
    ((2*(1-x):ℝ):ℂ)*((x*(2-x):ℝ):ℂ)^(w-1)*fundamentalSourceCore w s a (x*(2-x))=
      2*a^(2 : ℕ)*(fundamentalMomentConstant s*((x:ℂ)^(w-1)*fundamentalJacobiCore 2 (s-1/2) x)+
        fundamentalMomentQuadratic w s*((x:ℂ)^(w-1)*fundamentalJacobiCore 4 (s-1/2) x)) := by
  have hx2 : 0<2-x := by linarith
  have hs := fundamentalSourceDensity_polynomial_coordinate w s a hx hx1
  have hz0 : ((x*(2-x):ℝ):ℂ)≠0 := Complex.ofReal_ne_zero.mpr (mul_pos hx hx2).ne'
  have hx0 : (x:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hx.ne'
  have hx20 : ((2-x:ℝ):ℂ)≠0 := Complex.ofReal_ne_zero.mpr hx2.ne'
  dsimp only [fundamentalJacobiCore] at hs ⊢
  rw [show 2*(s-1/2)=2*s-1 by ring,
    Complex.cpow_sub _ _ hz0,Complex.cpow_sub _ _ hx0,
    Complex.cpow_sub _ _ hx20,Complex.cpow_one,Complex.cpow_one,Complex.cpow_one]
  rw [Complex.ofReal_mul]
  field_simp [hx0,hx20]
  push_cast at hs ⊢
  linear_combination (x:ℂ)*(2-(x:ℂ))*hs

theorem fundamentalSourceForcing_polynomial_cutoff (w s a : ℂ) {e : ℝ}
    (he : 0<e) (he1 : e≤1) :
    (∫ z in (e*(2-e))..1, (z:ℂ)^(w-1)*fundamentalSourceCore w s a z)=
      2*a^(2 : ℕ)*(fundamentalMomentConstant s*
        (∫ x in e..1, (x:ℂ)^(w-1)*fundamentalJacobiCore 2 (s-1/2) x)+
      fundamentalMomentQuadratic w s*
        (∫ x in e..1, (x:ℂ)^(w-1)*fundamentalJacobiCore 4 (s-1/2) x)) := by
  have hd (x : ℝ) : HasDerivAt (fun y : ℝ => y*(2-y)) (2*(1-x)) x := by
    exact ((hasDerivAt_id x).mul ((hasDerivAt_id x).const_sub 2)).congr_deriv
      (by dsimp only [id_eq];ring)
  have hi := intervalIntegral.integral_deriv_smul_comp_of_deriv_nonneg
    (g:=fun z : ℝ => (z:ℂ)^(w-1)*fundamentalSourceCore w s a z)
    (f:=fun x : ℝ => x*(2-x)) (f':=fun x=>2*(1-x))
    (a:=e) (b:=1) (by fun_prop) (fun x _=>hd x)
    (fun x hx=>by rw [min_eq_left he1,max_eq_right he1] at hx;linarith [hx.2])
  norm_num only [sub_self,sub_zero,mul_one,one_mul] at hi
  rw [← hi]
  calc
    _ = ∫ x in e..1, 2*a^(2 : ℕ)*(fundamentalMomentConstant s*
        ((x:ℂ)^(w-1)*fundamentalJacobiCore 2 (s-1/2) x)+
      fundamentalMomentQuadratic w s*((x:ℂ)^(w-1)*fundamentalJacobiCore 4 (s-1/2) x)) := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [uIcc_of_le he1] at hx
      simpa only [Function.comp_apply,Complex.real_smul,mul_assoc] using
        fundamentalSourceDensity_forcing_coordinate w s a (he.trans_le hx.1) hx.2
    _ = _ := by
      rw [intervalIntegral.integral_const_mul,
        intervalIntegral.integral_add
          ((fundamentalJacobiDensity_intervalIntegrable 2 (w-1) (s-1/2) he he1).const_mul _)
          ((fundamentalJacobiDensity_intervalIntegrable 4 (w-1) (s-1/2) he he1).const_mul _),
        intervalIntegral.integral_const_mul,intervalIntegral.integral_const_mul]

/-- Exact transported value and slope of the actual degree-four source. -/
theorem fundamentalSourceForcing_endpoint_coefficients (w s a : ℂ) :
    fundamentalSourceCore w s a 0*(2:ℂ)^w=
      2*a^(2 : ℕ)*(fundamentalMomentConstant s*fundamentalJacobiCore 2 (s-1/2) 0+
        fundamentalMomentQuadratic w s*fundamentalJacobiCore 4 (s-1/2) 0) ∧
    -(w+1)*fundamentalSourceCore w s a 0*(2:ℂ)^w/2+
        (2:ℂ)^(w+1)*fundamentalSourceCoreSlope w s a=
      2*a^(2 : ℕ)*(fundamentalMomentConstant s*fundamentalJacobiCoreFirst 2 (s-1/2) 0+
        fundamentalMomentQuadratic w s*fundamentalJacobiCoreFirst 4 (s-1/2) 0) := by
  have htwo : (2:ℂ)≠0 := by norm_num
  have hp : (2:ℂ)^(2*s-w)*(2:ℂ)^w=(2:ℂ)^(2*s) := by
    rw [← Complex.cpow_add _ _ htwo]
    congr 1
    ring
  have hhalf : (2:ℂ)^(2*(s-1/2))=(2:ℂ)^(2*s)/2 := by
    rw [show 2*(s-1/2)=2*s-1 by ring,Complex.cpow_sub _ _ htwo,Complex.cpow_one]
  rw [fundamentalSourceCore_zero_polynomial]
  constructor
  · simp only [fundamentalJacobiCore_zero,hhalf]
    calc
      _ = ((2:ℂ)^(2*s-w)*(2:ℂ)^w)*a^(2 : ℕ)*(fundamentalMomentConstant s+fundamentalMomentQuadratic w s) := by ring
      _ = _ := by rw [hp];ring
  · rw [Complex.cpow_add _ _ htwo,Complex.cpow_one,fundamentalSourceCoreSlope]
    dsimp only [fundamentalJacobiCoreFirst,powerFirst,power]
    norm_num only [Complex.ofReal_zero,sub_zero,one_pow,one_mul,Complex.ofReal_ofNat,Nat.cast_ofNat]
    rw [hhalf]
    calc
      _ = ((2:ℂ)^(2*s-w)*(2:ℂ)^w)*
        (-(a^(2 : ℕ))/2*((2*s+3)*fundamentalMomentConstant s+(2*s+7)*fundamentalMomentQuadratic w s)) := by ring
      _ = _ := by rw [hp];ring

/-- The original physical-radius forcing finite part is the exact retained
first-period combination, with both endpoint coefficients attached. -/
theorem fundamentalSourceForcingMoment_original_cutoff (w s a : ℂ)
    (hw : -2<w.re) (hw1 : w+1≠0) :
    Tendsto (fun e : ℝ =>
      w*(∫ z in (e*(2-e))..1, (z:ℂ)^(w-1)*fundamentalSourceCore w s a z)+
      fundamentalSourceCore w s a 0*((e*(2-e):ℝ):ℂ)^w+
      w*fundamentalSourceCoreSlope w s a*((e*(2-e):ℝ):ℂ)^(w+1)/(w+1))
      (𝓝[>] (0:ℝ)) (𝓝 (fundamentalSourceForcingMoment w s a)) := by
  have hj := (((fundamentalJacobiForcingMoment_cutoff 2 (by norm_num) w s hw hw1).const_mul (fundamentalMomentConstant s)).add
    ((fundamentalJacobiForcingMoment_cutoff 4 (by norm_num) w s hw hw1).const_mul (fundamentalMomentQuadratic w s))).const_mul (2*a^(2 : ℕ))
  have hc := fundamentalMoment_forcing_counterterm_transport
    (fundamentalSourceCore w s a 0) (fundamentalSourceCoreSlope w s a) w hw hw1
  have h := hj.add hc
  simp only [add_zero] at h
  apply h.congr'
  filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0:ℝ)<1)] with e he
  rw [fundamentalSourceForcing_polynomial_cutoff w s a he.1 he.2.le,
    (fundamentalSourceForcing_endpoint_coefficients w s a).1,
    (fundamentalSourceForcing_endpoint_coefficients w s a).2]
  ring

end
end RHTower.D4BMJointSource
