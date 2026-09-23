import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMFundamentalMomentEndpoint
import GaloisForLFunctions.HTGeometry.FirstEndpointMellinLimit

/-! Polynomial-coordinate reduction of the literal fundamental source, before taking its endpoint limit. -/
namespace RHTower.D4BMJointSource
open Complex Set Filter Topology MeasureTheory D4BMLaplaceRadial GaloisForLFunctions.HTGeometry
noncomputable section
set_option autoImplicit false

def fundamentalMomentConstant (s : ℂ) : ℂ := (5*s^(2 : ℕ)+15*s+4)/4

def fundamentalMomentQuadratic (w s : ℂ) : ℂ :=
  s*(s-1)*((s+2)*(2*s+3)-(w+1)*(w+2)/2)/4

/-- Smooth polynomial-weighted core on the physical half-beta interval. -/
def fundamentalJacobiCore (n : ℕ) (s : ℂ) (x : ℝ) : ℂ :=
  (1-(x:ℂ))^n * ((2-x:ℝ):ℂ)^(2*s)

/-- The existing one-subtraction finite part, applied to the exact transformed source core. -/
def fundamentalJacobiMoment (n : ℕ) (w s : ℂ) : ℂ :=
  firstEndpointMellin (fun _ => fundamentalJacobiCore n s) 1 w

theorem fundamentalJacobiCore_continuousAt (n : ℕ) (s : ℂ) {x : ℝ} (hx : x < 2) :
    ContinuousAt (fundamentalJacobiCore n s) x := by
  have hp : ContinuousAt (fun y : ℝ => ((2-y:ℝ):ℂ)^(2*s)) x :=
    (power_derivatives (2*s) (by linarith : 0 < 2-x)).1.continuousAt.comp
      (continuousAt_const.sub continuousAt_id)
  exact ((continuousAt_const.sub Complex.continuous_ofReal.continuousAt).pow n).mul hp

theorem fundamentalJacobiDensity_intervalIntegrable (n : ℕ) (w s : ℂ)
    {e : ℝ} (he : 0 < e) (he1 : e ≤ 1) :
    IntervalIntegrable (fun x : ℝ => (x:ℂ)^w*fundamentalJacobiCore n s x) volume e 1 := by
  apply ContinuousOn.intervalIntegrable_of_Icc he1
  intro x hx
  exact ((power_derivatives w (he.trans_le hx.1)).1.continuousAt.mul
    (fundamentalJacobiCore_continuousAt n s (by linarith [hx.2]))).continuousWithinAt

/-- Exact endpoint coefficient, including the source's quadratic term. -/
theorem fundamentalSourceCore_zero_polynomial (w s a : ℂ) :
    fundamentalSourceCore w s a 0 = (2:ℂ)^(2*s-w)*a^(2 : ℕ)*
      (fundamentalMomentConstant s+fundamentalMomentQuadratic w s) := by
  simp only [fundamentalSourceCore, sourceRemainder, sub_zero, Real.sqrt_one,
    power, Complex.ofReal_zero, Complex.ofReal_one, Complex.one_cpow, one_mul, mul_one]
  norm_num only [Complex.ofReal_add, Complex.ofReal_one, Complex.ofReal_ofNat]
  unfold fundamentalMomentConstant fundamentalMomentQuadratic
  ring

/-- The actual source density under z=x(2-x), with its complete degree-four polynomial. -/
theorem fundamentalSourceDensity_polynomial_coordinate (w s a : ℂ) {x : ℝ}
    (hx : 0 < x) (hx1 : x ≤ 1) :
    ((2*(1-x):ℝ):ℂ) * ((x*(2-x):ℝ):ℂ)^w *
      fundamentalSourceCore w s a (x*(2-x)) =
      2*a^(2 : ℕ) * (fundamentalMomentConstant s*((x:ℂ)^w*fundamentalJacobiCore 2 s x)+
        fundamentalMomentQuadratic w s*((x:ℂ)^w*fundamentalJacobiCore 4 s x)) := by
  have h2 : 0 < 2-x := by linarith
  have hr : 1-x*(2-x)=(1-x)^(2 : ℕ) := by ring
  have hsqrt : Real.sqrt (1-x*(2-x))=1-x := by
    rw [hr, Real.sqrt_sq (sub_nonneg.mpr hx1)]
  have hhalf : power (1/2) (1-x*(2-x))=(1-(x:ℂ)) := by
    rw [power_half_eq_sqrt (by rw [hr]; positivity), hsqrt]
    push_cast
    rfl
  have hp : ((x*(2-x):ℝ):ℂ)^w = (x:ℂ)^w*((2-x:ℝ):ℂ)^w := by
    simpa only [Complex.ofReal_mul] using Complex.mul_cpow_ofReal_nonneg hx.le h2.le w
  have hsum : ((2-x:ℝ):ℂ)^w * ((2-x:ℝ):ℂ)^(2*s-w)=((2-x:ℝ):ℂ)^(2*s) := by
    rw [← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr h2.ne')]
    congr 1
    ring
  rw [fundamentalSourceCore, hhalf, sourceRemainder, hsqrt,
    show 1+(1-x)=2-x by ring, hp]
  dsimp only [power, fundamentalJacobiCore, fundamentalMomentConstant, fundamentalMomentQuadratic]
  push_cast
  calc
    _ = (x:ℂ)^w * (((2-x:ℝ):ℂ)^w*((2-x:ℝ):ℂ)^(2*s-w)) *
      (2*a^(2 : ℕ)*((5*s^(2 : ℕ)+15*s+4)/4*(1-(x:ℂ))^(2 : ℕ)+
        s*(s-1)*((s+2)*(2*s+3)-(w+1)*(w+2)/2)/4*(1-(x:ℂ))^(4 : ℕ))) := by
      push_cast
      ring
    _ = _ := by rw [hsum]; push_cast; ring

/-- An exact change of variables of the original source integral at every positive cutoff. -/
theorem fundamentalSourceMoment_polynomial_cutoff (w s a : ℂ) {e : ℝ}
    (he : 0 < e) (he1 : e ≤ 1) :
    (∫ z in (e*(2-e))..1, (z:ℂ)^w*fundamentalSourceCore w s a z) =
      2*a^(2 : ℕ)*(fundamentalMomentConstant s*
        (∫ x in e..1, (x:ℂ)^w*fundamentalJacobiCore 2 s x)+
      fundamentalMomentQuadratic w s*
        (∫ x in e..1, (x:ℂ)^w*fundamentalJacobiCore 4 s x)) := by
  have hd (x : ℝ) : HasDerivAt (fun y : ℝ => y*(2-y)) (2*(1-x)) x := by
    have h := (hasDerivAt_id x).mul ((hasDerivAt_const x (2:ℝ)).sub (hasDerivAt_id x))
    exact h.congr_deriv (by change 1*(2-x)+x*(0-1)=2*(1-x); ring)
  have hi := intervalIntegral.integral_deriv_smul_comp_of_deriv_nonneg
    (g := fun z : ℝ => (z:ℂ)^w*fundamentalSourceCore w s a z)
    (f := fun x : ℝ => x*(2-x)) (f' := fun x => 2*(1-x))
    (a := e) (b := 1) (by fun_prop) (fun x _ => hd x)
    (fun x hx => by rw [min_eq_left he1, max_eq_right he1] at hx; linarith [hx.2])
  norm_num only [sub_self, sub_zero, mul_one, one_mul] at hi
  rw [← hi]
  calc
    _ = ∫ x in e..1, 2*a^(2 : ℕ)*(fundamentalMomentConstant s*((x:ℂ)^w*fundamentalJacobiCore 2 s x)+
        fundamentalMomentQuadratic w s*((x:ℂ)^w*fundamentalJacobiCore 4 s x)) := by
      apply intervalIntegral.integral_congr
      intro x hx
      rw [uIcc_of_le he1] at hx
      simpa only [Function.comp_apply, Complex.real_smul, mul_assoc] using
        fundamentalSourceDensity_polynomial_coordinate w s a (he.trans_le hx.1) hx.2
    _ = _ := by
      rw [intervalIntegral.integral_const_mul,
        intervalIntegral.integral_add
          ((fundamentalJacobiDensity_intervalIntegrable 2 w s he he1).const_mul _)
          ((fundamentalJacobiDensity_intervalIntegrable 4 w s he he1).const_mul _),
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]

end
end RHTower.D4BMJointSource
