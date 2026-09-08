import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMJointSourceGradientReduction

/-! The exact reduced source retains one frequency derivative after cancellation of the quadratic terms. -/
namespace RHTower.D4BMJointSource
noncomputable section

/-- Coefficient of the independent transform frequency in the original reduced source. -/
def reducedSlope (s u : ℂ) : ℂ :=
  -s*(s-1)/2*u^2*(u-1)*((2*s+3)*u+3)

/-- The frequency-square terms cancel in the literal source polynomial. -/
theorem reducedPolynomial_affine (s w u : ℂ) :
    reducedPolynomial s w u = reducedPolynomial s 0 u+w*reducedSlope s u := by
  unfold reducedPolynomial reducedSlope liftSecondPolynomial amplitudeRate
  ring

/-- The surviving slope is exactly twice the radial derivative of the original lift. -/
theorem reducedSlope_liftFirst (s a : ℂ) (t : ℝ) :
    sourceAmplitude s 0 a 1 t*reducedSlope s (radialUnit t) =
      2*radialLiftFirst s 0 a 1 t := by
  unfold reducedSlope radialLiftFirst liftFirstPolynomial amplitudeRate
  ring

/-- The radial Laplace factor and the temporal transform remain separate from the physical profile. -/
theorem sourceAmplitude_frequency (s w a T : ℂ) (t : ℝ) :
    sourceAmplitude s w a T t = Complex.exp (w*(t:ℂ))*T*sourceAmplitude s 0 a 1 t := by
  simp only [sourceAmplitude,zero_mul,Complex.exp_zero,one_mul,mul_one]
  ring

/-- Exact affine-frequency decomposition of the original reduced source coefficient. -/
theorem reducedCoefficient_frequency (s w a T : ℂ) (t : ℝ) :
    reducedCoefficient s w a T t = Complex.exp (w*(t:ℂ))*T*
      (reducedCoefficient s 0 a 1 t+2*w*radialLiftFirst s 0 a 1 t) := by
  unfold reducedCoefficient
  rw [sourceAmplitude_frequency,reducedPolynomial_affine]
  have he := reducedSlope_liftFirst s a t
  linear_combination Complex.exp (w*(t:ℂ))*T*w*he

end
end RHTower.D4BMJointSource
