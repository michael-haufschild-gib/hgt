import GaloisForLFunctions.RHTower.XiCTaylorThetaTailPrimitiveRayPolarization

/-!
# Reflection covariance of the primitive-ray theta seam

The finite theta-tail core-pair current is symmetric in its two source coordinates.  On primitive
polar fibres, transposing the arithmetic direction is therefore the angular reflection
`u ↦ 1-u`.  This file records the exact covariance of the endpoint flux and the unsplit
translation derivative.

The decisive sign is that both factors in the interior seam change sign.  Their product is
reflection invariant, not anti-invariant.  Thus pairing the ordered primitive directions
`(a,b)` and `(b,a)` reinforces the unresolved seam; it cannot be its cancellation mechanism.
-/

open Complex Real Polynomial

namespace RHTower

noncomputable section

/-- The finite Hermitian core-pair current is exactly symmetric in its two source coordinates. -/
theorem xiCTaylorThetaTailCorePairCurrent_swap
    (d : ℕ) (z : ℂ) (x y : ℝ) :
    xiCTaylorThetaTailCorePairCurrent d z (y, x) =
      xiCTaylorThetaTailCorePairCurrent d z (x, y) := by
  unfold xiCTaylorThetaTailCorePairCurrent
  ring

/-- Every finite second-section vanishes at the positive-half-line endpoint. -/
@[simp] theorem thetaCuspTailSecondSection_at_zero
    (d : ℕ) (z : ℂ) :
    thetaCuspTailSecondSection d z 0 = 0 := by
  unfold thetaCuspTailSecondSection
  simp

/-- **Exact endpoint value relation.**  Every finite theta-tail core atom has the same endpoint
value `1`, independently of the Taylor depth and spectral point. -/
@[simp] theorem thetaCuspTailSecondCoreAtom_at_zero
    (d : ℕ) (z : ℂ) :
    thetaCuspTailSecondCoreAtom d z 0 = 1 := by
  simp [thetaCuspTailSecondCoreAtom, thetaCuspTailSecondSection]

/-- The endpoint pair current is rank one: only the spectral derivative of the non-endpoint atom
survives.  This is the exact value relation available for arithmetic boundary reassembly. -/
theorem xiCTaylorThetaTailCorePairCurrent_zero_left
    (d : ℕ) (z : ℂ) (y : ℝ) :
    xiCTaylorThetaTailCorePairCurrent d z (0, y) =
      (thetaCuspTailSecondCoreAtomDerivative d z y).im / 2 := by
  unfold xiCTaylorThetaTailCorePairCurrent
  rw [thetaCuspTailSecondCoreAtomDerivative_zero]
  simp [thetaCuspTailSecondCoreAtom, thetaCuspTailSecondSection]

/-- Symmetric endpoint form of the same rank-one current relation. -/
theorem xiCTaylorThetaTailCorePairCurrent_zero_right
    (d : ℕ) (z : ℂ) (x : ℝ) :
    xiCTaylorThetaTailCorePairCurrent d z (x, 0) =
      (thetaCuspTailSecondCoreAtomDerivative d z x).im / 2 := by
  rw [xiCTaylorThetaTailCorePairCurrent_swap]
  exact xiCTaylorThetaTailCorePairCurrent_zero_left d z x

/-- Angular reflection exchanges the first primitive polar coordinate with the second. -/
theorem thetaCuspPrimitiveRayCorePolarX_one_sub
    (r alpha u : ℝ) :
    thetaCuspPrimitiveRayCorePolarX r alpha (1 - u) =
      thetaCuspPrimitiveRayCorePolarY r alpha u := by
  unfold thetaCuspPrimitiveRayCorePolarX thetaCuspPrimitiveRayCorePolarY
  congr 2

/-- Angular reflection exchanges the second primitive polar coordinate with the first. -/
theorem thetaCuspPrimitiveRayCorePolarY_one_sub
    (r alpha u : ℝ) :
    thetaCuspPrimitiveRayCorePolarY r alpha (1 - u) =
      thetaCuspPrimitiveRayCorePolarX r alpha u := by
  unfold thetaCuspPrimitiveRayCorePolarX thetaCuspPrimitiveRayCorePolarY
  rw [show 1 - (1 - u) = u by ring]

/-- Transposing the primitive direction is exactly angular reflection of the finite core. -/
theorem thetaCuspPrimitiveRayCorePolarKernel_one_sub
    (d : ℕ) (z : ℂ) (r alpha beta u : ℝ) :
    thetaCuspPrimitiveRayCorePolarKernel d z r alpha beta (1 - u) =
      thetaCuspPrimitiveRayCorePolarKernel d z r beta alpha u := by
  unfold thetaCuspPrimitiveRayCorePolarKernel
  rw [thetaCuspPrimitiveRayCorePolarX_one_sub,
    thetaCuspPrimitiveRayCorePolarY_one_sub,
    xiCTaylorThetaTailCorePairCurrent_swap]

/-- The primitive angular moment is reflection invariant. -/
theorem thetaCuspPrimitiveRayMoment_one_sub (u : ℝ) :
    thetaCuspPrimitiveRayMoment (1 - u) =
      thetaCuspPrimitiveRayMoment u := by
  unfold thetaCuspPrimitiveRayMoment
  ring

/-- The growing completion coefficient is reflection invariant. -/
theorem thetaCuspPrimitiveRayGrowingCoefficient_one_sub (u : ℝ) :
    thetaCuspPrimitiveRayGrowingCoefficient (1 - u) =
      thetaCuspPrimitiveRayGrowingCoefficient u := by
  unfold thetaCuspPrimitiveRayGrowingCoefficient
  rw [thetaCuspPrimitiveRayMoment_one_sub]

/-- The angular flux is reflection anti-invariant. -/
theorem thetaCuspPrimitiveRayAngularFlux_one_sub (u : ℝ) :
    thetaCuspPrimitiveRayAngularFlux (1 - u) =
      -thetaCuspPrimitiveRayAngularFlux u := by
  unfold thetaCuspPrimitiveRayAngularFlux
  rw [thetaCuspPrimitiveRayMoment_one_sub]
  ring

/-- The unsplit finite-core angular derivative is also reflection anti-invariant after the
primitive direction is transposed. -/
theorem thetaCuspPrimitiveRayCorePolarKernelDerivative_one_sub
    (d : ℕ) (z : ℂ) (r alpha beta u : ℝ) :
    thetaCuspPrimitiveRayCorePolarKernelDerivative d z r alpha beta (1 - u) =
      -thetaCuspPrimitiveRayCorePolarKernelDerivative d z r beta alpha u := by
  unfold thetaCuspPrimitiveRayCorePolarKernelDerivative
  rw [thetaCuspPrimitiveRayCorePolarX_one_sub,
    thetaCuspPrimitiveRayCorePolarY_one_sub,
    show 1 - (1 - u) = u by ring]
  ring

/-- **Transposition reinforcement of the interior seam.**  The flux and the finite-core angular
derivative both reverse sign, so their joint signed product is invariant.  The transposed
primitive ray therefore adds the same interior seam rather than cancelling it. -/
theorem thetaCuspPrimitiveRayAngularSeamIntegrand_one_sub
    (d : ℕ) (z : ℂ) (r alpha beta u : ℝ) :
    thetaCuspPrimitiveRayAngularFlux (1 - u) *
        thetaCuspPrimitiveRayCorePolarKernelDerivative
          d z r alpha beta (1 - u) =
      thetaCuspPrimitiveRayAngularFlux u *
        thetaCuspPrimitiveRayCorePolarKernelDerivative
          d z r beta alpha u := by
  rw [thetaCuspPrimitiveRayAngularFlux_one_sub,
    thetaCuspPrimitiveRayCorePolarKernelDerivative_one_sub]
  ring

/-- The original growing-character seam integrand has the same transposition covariance. -/
theorem thetaCuspPrimitiveRayGrowingCoreIntegrand_one_sub
    (d : ℕ) (z : ℂ) (r alpha beta u : ℝ) :
    thetaCuspPrimitiveRayGrowingCoefficient (1 - u) *
          (thetaCuspPrimitiveRayMoment (1 - u)) ^ (-(3 / 4 : ℝ)) *
          thetaCuspPrimitiveRayCorePolarKernel d z r alpha beta (1 - u) =
      thetaCuspPrimitiveRayGrowingCoefficient u *
          (thetaCuspPrimitiveRayMoment u) ^ (-(3 / 4 : ℝ)) *
          thetaCuspPrimitiveRayCorePolarKernel d z r beta alpha u := by
  rw [thetaCuspPrimitiveRayGrowingCoefficient_one_sub,
    thetaCuspPrimitiveRayMoment_one_sub,
    thetaCuspPrimitiveRayCorePolarKernel_one_sub]

/-- Reflection sends a lower active endpoint to the upper endpoint with the same source shift. -/
theorem one_sub_thetaCuspPrimitiveRayCorePolarLowerEndpoint
    (r alpha : ℝ) :
    1 - thetaCuspPrimitiveRayCorePolarLowerEndpoint r alpha =
      thetaCuspPrimitiveRayCorePolarUpperEndpoint r alpha := by
  unfold thetaCuspPrimitiveRayCorePolarLowerEndpoint
    thetaCuspPrimitiveRayCorePolarUpperEndpoint
  rfl

/-- Reflection sends an upper active endpoint to the lower endpoint with the same source shift. -/
theorem one_sub_thetaCuspPrimitiveRayCorePolarUpperEndpoint
    (r alpha : ℝ) :
    1 - thetaCuspPrimitiveRayCorePolarUpperEndpoint r alpha =
      thetaCuspPrimitiveRayCorePolarLowerEndpoint r alpha := by
  unfold thetaCuspPrimitiveRayCorePolarLowerEndpoint
    thetaCuspPrimitiveRayCorePolarUpperEndpoint
  ring

end


end RHTower
