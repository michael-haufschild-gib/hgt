import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMJointSourceAmplitude

/-! Actual two radial derivatives of the explicit field retaining the full gradient source. -/
namespace RHTower.D4BMJointSource
noncomputable section
attribute [-instance] instInnerProductSpaceRealComplex
attribute [-instance] RCLike.toInnerProductSpaceReal
attribute [-instance] NormedSpace.complexToReal

def liftFirstPolynomial (s w u : ℂ) : ℂ :=
  amplitudeRate s w u*u^(3 : ℕ)+3*u^(2 : ℕ)*(u^(2 : ℕ)-1)

def liftSecondPolynomial (s w u : ℂ) : ℂ :=
  (amplitudeRate s w u)^(2 : ℕ)*u^(3 : ℕ)+6*amplitudeRate s w u*u^(2 : ℕ)*(u^(2 : ℕ)-1)+
    2*s*(u^(2 : ℕ)-1)*u^(3 : ℕ)+6*u*(u^(2 : ℕ)-1)^(2 : ℕ)+6*u^(3 : ℕ)*(u^(2 : ℕ)-1)

/-- Explicit original radial field absorbing the full coexact gradient contribution. -/
def radialLift (s w a T : ℂ) (t : ℝ) : ℂ :=
  (-s*(s-1)/4)*(sourceAmplitude s w a T t*(radialUnit t:ℂ)^(3 : ℕ))

def radialLiftFirst (s w a T : ℂ) (t : ℝ) : ℂ :=
  (-s*(s-1)/4)*(sourceAmplitude s w a T t*liftFirstPolynomial s w (radialUnit t))

def radialLiftSecond (s w a T : ℂ) (t : ℝ) : ℂ :=
  (-s*(s-1)/4)*(sourceAmplitude s w a T t*liftSecondPolynomial s w (radialUnit t))

theorem radialLift_hasDerivAt (s w a T : ℂ) (t : ℝ) :
    HasDerivAt (radialLift s w a T) (radialLiftFirst s w a T t) t := by
  have hR := sourceAmplitude_hasDerivAt s w a T t
  have hU := (radialUnit_hasDerivAt t).ofReal_comp
  apply ((hR.mul (hU.pow 3)).const_mul (-s*(s-1)/4)).congr_deriv
  dsimp only [radialLiftFirst,liftFirstPolynomial]
  simp only [Pi.pow_apply]
  push_cast
  ring

theorem radialLiftFirst_hasDerivAt (s w a T : ℂ) (t : ℝ) :
    HasDerivAt (radialLiftFirst s w a T) (radialLiftSecond s w a T t) t := by
  have hR := sourceAmplitude_hasDerivAt s w a T t
  have hU := (radialUnit_hasDerivAt t).ofReal_comp
  have hA := ((hU.sub_const 1).const_mul (2*s)).const_add w
  have hP := (hA.mul (hU.pow 3)).add (((hU.pow 2).const_mul 3).mul ((hU.pow 2).sub_const 1))
  apply ((hR.mul hP).const_mul (-s*(s-1)/4)).congr_deriv
  dsimp only [radialLiftSecond,liftSecondPolynomial,amplitudeRate]
  simp only [Pi.pow_apply,Pi.mul_apply,Pi.add_apply]
  push_cast
  ring

/-- Both slots are actual derivatives of the constructed radial field. -/
theorem radialLift_derivatives (s w a T : ℂ) :
    deriv (radialLift s w a T) = radialLiftFirst s w a T ∧
      deriv (deriv (radialLift s w a T)) = radialLiftSecond s w a T := by
  have h : deriv (radialLift s w a T) = radialLiftFirst s w a T :=
    funext (fun t => (radialLift_hasDerivAt s w a T t).deriv)
  exact ⟨h,by rw [h]; exact funext (fun t => (radialLiftFirst_hasDerivAt s w a T t).deriv)⟩

end
end RHTower.D4BMJointSource
