import GaloisForLFunctions.RHTower.XiCTaylorThetaTailPrimitiveRayPolarization

/-!
# Joint radial reflection and angular seam identity

The primitive-ray radial reflection is combined here with the angular integration-by-parts
identity before any term is estimated.  The parity packet, the universal favorable exponential
square, both active-window endpoint fluxes, and the finite-core angular derivative therefore
remain in one exact formula.
-/

open Complex Real Polynomial MeasureTheory Set

namespace RHTower

noncomputable section

private theorem intervalIntegrable_primitiveRayCoefficient_mul_corePolarWeight
    (C : ℝ → ℝ) (hC : Continuous C)
    (d : ℕ) (z : ℂ) (r alpha beta : ℝ) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hb : b < 1) :
    IntervalIntegrable (fun u : ℝ =>
      C u *
        (thetaCuspPrimitiveRayMoment u) ^ (-(3 / 4 : ℝ)) *
        thetaCuspPrimitiveRayCorePolarKernel d z r alpha beta u)
      volume a b := by
  have hsub : Set.uIcc a b ⊆ Set.Ioo 0 1 := by
    rw [Set.uIcc_of_le hab]
    intro u hu
    exact ⟨lt_of_lt_of_le ha hu.1, lt_of_le_of_lt hu.2 hb⟩
  apply ContinuousOn.intervalIntegrable
  intro u hu
  have hui := hsub hu
  have hmoment : 0 < thetaCuspPrimitiveRayMoment u := by
    unfold thetaCuspPrimitiveRayMoment
    exact mul_pos hui.1 (sub_pos.mpr hui.2)
  have hmomentCont : ContinuousAt thetaCuspPrimitiveRayMoment u := by
    unfold thetaCuspPrimitiveRayMoment
    fun_prop
  have hweight : ContinuousAt
      (fun t : ℝ =>
        (thetaCuspPrimitiveRayMoment t) ^ (-(3 / 4 : ℝ))) u :=
    hmomentCont.rpow_const (Or.inl hmoment.ne')
  have hkernel : ContinuousAt
      (thetaCuspPrimitiveRayCorePolarKernel d z r alpha beta) u :=
    (hasDerivAt_thetaCuspPrimitiveRayCorePolarKernel
      d z r alpha beta hui).continuousAt
  have hcontinuous : ContinuousWithinAt
      (C * ((fun t : ℝ =>
        thetaCuspPrimitiveRayMoment t ^ (-(3 / 4 : ℝ))) *
          thetaCuspPrimitiveRayCorePolarKernel d z r alpha beta))
      (Set.uIcc a b) u :=
    (hC.continuousAt.mul (hweight.mul hkernel)).continuousWithinAt
  refine hcontinuous.congr (fun y _hy => ?_) ?_
  · simp only [Pi.mul_apply]
    ring
  · simp only [Pi.mul_apply]
    ring

/-- **Joint reflected primitive-ray identity.**  The growing completion character is eliminated
by angular integration by parts only after the radial reflection has been inserted.  In
particular, the favorable `-exp(r)/32` term is not separated from the parity packet, and the two
endpoint fluxes remain joined to the finite-core angular derivative. -/
theorem integral_exp_half_mul_thetaCuspPrimitiveRayRadialPacket_mul_corePolarKernel_eq_joint
    (d : ℕ) (z : ℂ) (r alpha beta : ℝ) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hb : b < 1) :
    (∫ u : ℝ in a..b,
      (Real.exp (r / 2) * thetaCuspPrimitiveRayRadialPacket u r) *
          (thetaCuspPrimitiveRayMoment u) ^ (-(3 / 4 : ℝ)) *
          thetaCuspPrimitiveRayCorePolarKernel d z r alpha beta u) =
      (∫ u : ℝ in a..b,
        (Real.exp (r / 2) * thetaCuspPrimitiveRayParityPacket u (-r) -
            (1 / 32 : ℝ) * Real.exp r) *
          (thetaCuspPrimitiveRayMoment u) ^ (-(3 / 4 : ℝ)) *
          thetaCuspPrimitiveRayCorePolarKernel d z r alpha beta u) +
        thetaCuspPrimitiveRayAngularFlux b *
          thetaCuspPrimitiveRayCorePolarKernel d z r alpha beta b -
        thetaCuspPrimitiveRayAngularFlux a *
          thetaCuspPrimitiveRayCorePolarKernel d z r alpha beta a -
        ∫ u : ℝ in a..b,
          thetaCuspPrimitiveRayAngularFlux u *
            thetaCuspPrimitiveRayCorePolarKernelDerivative
              d z r alpha beta u := by
  let R : ℝ → ℝ := fun u =>
    Real.exp (r / 2) * thetaCuspPrimitiveRayParityPacket u (-r) -
      (1 / 32 : ℝ) * Real.exp r
  let G : ℝ → ℝ := thetaCuspPrimitiveRayGrowingCoefficient
  have hR : Continuous R := by
    unfold R thetaCuspPrimitiveRayParityPacket
      thetaCuspPrimitiveRayCoefficientZero
      thetaCuspPrimitiveRayCoefficientOne
      thetaCuspPrimitiveRayCoefficientTwo
      thetaCuspPrimitiveRayCoefficientThree
      thetaCuspPrimitiveRayCoefficientFour
      thetaCuspPrimitiveRayMoment
    fun_prop
  have hG : Continuous G := by
    unfold G thetaCuspPrimitiveRayGrowingCoefficient
      thetaCuspPrimitiveRayMoment
    fun_prop
  have hRint :=
    intervalIntegrable_primitiveRayCoefficient_mul_corePolarWeight
      R hR d z r alpha beta ha hab hb
  have hGint :=
    intervalIntegrable_primitiveRayCoefficient_mul_corePolarWeight
      G hG d z r alpha beta ha hab hb
  calc
    (∫ u : ℝ in a..b,
        (Real.exp (r / 2) * thetaCuspPrimitiveRayRadialPacket u r) *
          (thetaCuspPrimitiveRayMoment u) ^ (-(3 / 4 : ℝ)) *
          thetaCuspPrimitiveRayCorePolarKernel d z r alpha beta u) =
      ∫ u : ℝ in a..b,
        (R u *
            (thetaCuspPrimitiveRayMoment u) ^ (-(3 / 4 : ℝ)) *
            thetaCuspPrimitiveRayCorePolarKernel d z r alpha beta u) +
          (G u *
            (thetaCuspPrimitiveRayMoment u) ^ (-(3 / 4 : ℝ)) *
            thetaCuspPrimitiveRayCorePolarKernel d z r alpha beta u) := by
        apply intervalIntegral.integral_congr
        intro u _hu
        dsimp only
        rw [exp_half_mul_thetaCuspPrimitiveRayRadialPacket_eq_reflected]
        dsimp only [R, G]
        ring
    _ = (∫ u : ℝ in a..b,
          R u *
            (thetaCuspPrimitiveRayMoment u) ^ (-(3 / 4 : ℝ)) *
            thetaCuspPrimitiveRayCorePolarKernel d z r alpha beta u) +
        ∫ u : ℝ in a..b,
          G u *
            (thetaCuspPrimitiveRayMoment u) ^ (-(3 / 4 : ℝ)) *
            thetaCuspPrimitiveRayCorePolarKernel d z r alpha beta u := by
      rw [intervalIntegral.integral_add hRint hGint]
    _ = _ := by
      rw [integral_thetaCuspPrimitiveRayGrowingCoefficient_mul_corePolarKernel
        d z r alpha beta ha hab hb]
      dsimp only [R, G]
      ring

/-- Active positive-half-line form of the joint reflected identity.  The two boundary terms are
literally the rank-one currents at the swept source endpoints. -/
theorem integral_exp_half_mul_thetaCuspPrimitiveRayRadialPacket_mul_corePolarKernel_activeWindow
    (d : ℕ) (z : ℂ) (r alpha beta : ℝ)
    (hactive : thetaCuspPrimitiveRayCorePolarLowerEndpoint r alpha ≤
      thetaCuspPrimitiveRayCorePolarUpperEndpoint r beta) :
    (∫ u : ℝ in
        thetaCuspPrimitiveRayCorePolarLowerEndpoint r alpha..
          thetaCuspPrimitiveRayCorePolarUpperEndpoint r beta,
      (Real.exp (r / 2) * thetaCuspPrimitiveRayRadialPacket u r) *
          (thetaCuspPrimitiveRayMoment u) ^ (-(3 / 4 : ℝ)) *
          thetaCuspPrimitiveRayCorePolarKernel d z r alpha beta u) =
      (∫ u : ℝ in
        thetaCuspPrimitiveRayCorePolarLowerEndpoint r alpha..
          thetaCuspPrimitiveRayCorePolarUpperEndpoint r beta,
        (Real.exp (r / 2) * thetaCuspPrimitiveRayParityPacket u (-r) -
            (1 / 32 : ℝ) * Real.exp r) *
          (thetaCuspPrimitiveRayMoment u) ^ (-(3 / 4 : ℝ)) *
          thetaCuspPrimitiveRayCorePolarKernel d z r alpha beta u) +
        thetaCuspPrimitiveRayAngularFlux
            (thetaCuspPrimitiveRayCorePolarUpperEndpoint r beta) *
          xiCTaylorThetaTailCorePairCurrent d z
            (thetaCuspPrimitiveRayCorePolarX r alpha
                (thetaCuspPrimitiveRayCorePolarUpperEndpoint r beta), 0) -
        thetaCuspPrimitiveRayAngularFlux
            (thetaCuspPrimitiveRayCorePolarLowerEndpoint r alpha) *
          xiCTaylorThetaTailCorePairCurrent d z
            (0, thetaCuspPrimitiveRayCorePolarY r beta
                (thetaCuspPrimitiveRayCorePolarLowerEndpoint r alpha)) -
        ∫ u : ℝ in
          thetaCuspPrimitiveRayCorePolarLowerEndpoint r alpha..
            thetaCuspPrimitiveRayCorePolarUpperEndpoint r beta,
          thetaCuspPrimitiveRayAngularFlux u *
            thetaCuspPrimitiveRayCorePolarKernelDerivative
              d z r alpha beta u := by
  have hlower : 0 < thetaCuspPrimitiveRayCorePolarLowerEndpoint r alpha := by
    unfold thetaCuspPrimitiveRayCorePolarLowerEndpoint
    positivity
  have hupper : thetaCuspPrimitiveRayCorePolarUpperEndpoint r beta < 1 := by
    unfold thetaCuspPrimitiveRayCorePolarUpperEndpoint
    linarith [Real.exp_pos (-2 * (r + beta))]
  rw [integral_exp_half_mul_thetaCuspPrimitiveRayRadialPacket_mul_corePolarKernel_eq_joint
    d z r alpha beta hlower hactive hupper]
  unfold thetaCuspPrimitiveRayCorePolarKernel
  rw [thetaCuspPrimitiveRayCorePolarY_upperEndpoint,
    thetaCuspPrimitiveRayCorePolarX_lowerEndpoint]

end

end RHTower
