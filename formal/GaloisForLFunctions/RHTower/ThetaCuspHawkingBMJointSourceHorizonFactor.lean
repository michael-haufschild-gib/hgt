import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMJointSourceTimeAdmission

/-! Both coefficients of the actual time source retain two powers of horizon decay. -/
namespace RHTower.D4BMJointSource
open D4BMLaplaceRadial
noncomputable section

/-- The exact polynomial left after extracting the horizon zero from the reduced source. -/
def reducedHorizonPolynomial (s u : ℂ) : ℂ :=
  -2*(1+u)*u*((5*s^2+15*s+4)/4+s*(s-1)*(s+2)^2*u^2/4)+
    s*(s-1)/4*(4*s^2*(u-1)*u^3+12*s*u^2*(u^2-1)+2*s*(u+1)*u^3+
      6*u*(u-1)*(u+1)^2+6*u^3*(u+1))-
    2*(1+u)*(s+1)*(s+2)*(s*(s-1)/4)*u^3

/-- The independent-frequency constant coefficient has a genuine horizon zero. -/
theorem reducedPolynomial_horizon (s u : ℂ) :
    reducedPolynomial s 0 u = (1-u)*reducedHorizonPolynomial s u := by
  unfold reducedPolynomial reducedHorizonPolynomial liftSecondPolynomial amplitudeRate
  ring

/-- The frequency slope has the same horizon zero. -/
theorem reducedSlope_horizon (s u : ℂ) :
    reducedSlope s u = (1-u)*(s*(s-1)/2*u^2*((2*s+3)*u+3)) := by
  unfold reducedSlope
  ring

/-- The compact horizon zero is exactly a tortoise exponential times a bounded-radius factor. -/
theorem radialUnit_one_sub (t : ℝ) :
    1-radialUnit t = Real.exp (2*t)*(1+radialUnit t) := by
  have h := horizonCoordinate_factor t
  have he : (Real.exp t)^2 = Real.exp (2*t) := by
    rw [pow_two,← Real.exp_add]
    congr 1
    ring
  rw [mul_pow,he] at h
  unfold horizonCoordinate at h
  apply mul_right_cancel₀ (ne_of_gt (radialUnit_add_one_pos t))
  nlinarith [h]

/-- The two compact-radius factors multiplying the exact common horizon exponential. -/
def sourceHorizonProfile (s a : ℂ) (i : Fin 2) (u : ℝ) : ℂ :=
  power (2*s) (1+u)*a^2*(1+(u:ℂ))*
    (if i=0 then reducedHorizonPolynomial s u
      else s*(s-1)/2*(u:ℂ)^2*((2*s+3)*(u:ℂ)+3))

theorem sourceHorizonProfile_continuousOn (s a : ℂ) (i : Fin 2) :
    ContinuousOn (sourceHorizonProfile s a i) (Set.Icc 0 1) := by
  have hp : ContinuousOn (fun u : ℝ => power (2*s) (1+u)) (Set.Icc 0 1) := by
    intro u hu
    have h := (power_derivatives (2*s) (by linarith [hu.1] : 0 < 1+u)).1.continuousAt
    exact (h.comp_of_eq (continuous_const.add continuous_id).continuousAt rfl).continuousWithinAt
  unfold sourceHorizonProfile reducedHorizonPolynomial
  split_ifs <;> fun_prop

/-- Exact decay factor in the original zero-frequency reduced coefficient. -/
theorem reducedCoefficient_horizon (s a : ℂ) (t : ℝ) :
    reducedCoefficient s 0 a 1 t =
      (Real.exp (2*t):ℂ)*sourceHorizonProfile s a 0 (radialUnit t) := by
  rw [reducedCoefficient,reducedPolynomial_horizon]
  simp only [sourceAmplitude,zero_mul,Complex.exp_zero,one_mul,mul_one,sourceHorizonProfile,
    ↓reduceIte]
  have he : (1-(radialUnit t:ℂ)) = (Real.exp (2*t):ℂ)*(1+(radialUnit t:ℂ)) := by
    exact_mod_cast radialUnit_one_sub t
  rw [he]
  ring

/-- Exact decay factor in twice the actual radial derivative of the source lift. -/
theorem radialLiftFirst_horizon (s a : ℂ) (t : ℝ) :
    2*radialLiftFirst s 0 a 1 t =
      (Real.exp (2*t):ℂ)*sourceHorizonProfile s a 1 (radialUnit t) := by
  rw [← reducedSlope_liftFirst,reducedSlope_horizon]
  simp only [sourceAmplitude,zero_mul,Complex.exp_zero,one_mul,mul_one,sourceHorizonProfile,
    show (1:Fin 2) ≠ 0 by norm_num,↓reduceIte]
  have he : (1-(radialUnit t:ℂ)) = (Real.exp (2*t):ℂ)*(1+(radialUnit t:ℂ)) := by
    exact_mod_cast radialUnit_one_sub t
  rw [he]
  ring

end
end RHTower.D4BMJointSource
