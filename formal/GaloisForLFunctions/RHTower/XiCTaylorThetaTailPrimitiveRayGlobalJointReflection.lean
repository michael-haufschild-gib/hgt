import GaloisForLFunctions.RHTower.XiCTaylorThetaTailPrimitiveRayActiveFubini
import GaloisForLFunctions.RHTower.XiCTaylorThetaTailPrimitiveRayJointReflection
import GaloisForLFunctions.RHTower.XiCTaylorThetaTailPrimitiveRayShellBirth

/-!
# Global joint reflection on one complete primitive theta ray

The measure-level primitive-ray disintegration and the fixed-radius joint reflection are composed
here without splitting the swept endpoints from the finite-core angular derivative.  The radial
domain starts at the exact Euclidean shell-birth height.  The sole analytic premise is absolute
integrability of the original chamber-restricted kernel needed for Fubini; no sign, zero-location,
or limiting-measure hypothesis is used.
-/

open Complex Real Polynomial MeasureTheory Set

namespace RHTower

noncomputable section

/-- The polar integrand produced by the complete common-scale packet of one primitive direction. -/
def thetaCuspPrimitiveRayPolarCoreIntegrand
    (a b : ℕ) (d : ℕ) (z : ℂ) (q : ℝ × ℝ) : ℝ :=
  (8 * Real.exp
      (q.1 / 2 - (Real.log (a : ℝ) + Real.log (b : ℝ)) / 2) *
    (thetaCuspPrimitiveRayMoment q.2) ^ (-(3 / 4 : ℝ)) *
    thetaCuspPrimitiveRayRadialPacket q.2 q.1) *
  thetaCuspPrimitiveRayCorePolarKernel d z q.1
    (-Real.log (a : ℝ)) (-Real.log (b : ℝ)) q.2

/-- The reflected fixed-radius seam packet, retaining the parity term, the favorable exponential
square, both swept endpoint currents, and the finite-core angular derivative in one expression. -/
def thetaCuspPrimitiveRayJointSeamIntegrand
    (d : ℕ) (z : ℂ) (r alpha beta : ℝ) : ℝ :=
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
        thetaCuspPrimitiveRayCorePolarKernelDerivative d z r alpha beta u

/-- At every active radius, the raw radial packet equals the complete joint reflected seam
integrand. -/
theorem integral_thetaCuspPrimitiveRayRawPacket_eq_jointSeamIntegrand
    (d : ℕ) (z : ℂ) (r alpha beta : ℝ)
    (hactive : thetaCuspPrimitiveRayCorePolarLowerEndpoint r alpha ≤
      thetaCuspPrimitiveRayCorePolarUpperEndpoint r beta) :
    (∫ u : ℝ in
        thetaCuspPrimitiveRayCorePolarLowerEndpoint r alpha..
          thetaCuspPrimitiveRayCorePolarUpperEndpoint r beta,
      (Real.exp (r / 2) * thetaCuspPrimitiveRayRadialPacket u r) *
        (thetaCuspPrimitiveRayMoment u) ^ (-(3 / 4 : ℝ)) *
        thetaCuspPrimitiveRayCorePolarKernel d z r alpha beta u) =
      thetaCuspPrimitiveRayJointSeamIntegrand d z r alpha beta := by
  exact integral_exp_half_mul_thetaCuspPrimitiveRayRadialPacket_mul_corePolarKernel_activeWindow
    d z r alpha beta hactive

/-- **Global seam-preserving primitive-ray bridge.**  The complete common-scale convolution along
one positive primitive direction is exactly the radial integral, from its shell-birth height, of
the joint reflected seam packet.  In particular, the endpoint and top-edge derivative terms have
not been estimated separately. -/
theorem integral_thetaCuspPrimitiveRayDensityPair_mul_coreCurrent_eq_globalJoint
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (d : ℕ) (z : ℂ)
    (hint : Integrable
      ((thetaCuspPrimitiveRayActiveSet a b).indicator
        (thetaCuspPrimitiveRayPolarCoreIntegrand a b d z))
      (volume.prod volume)) :
    (∫ p in thetaCuspPositiveQuadrantSet,
      (∑' g : ℕ,
        thetaCuspTailSecondDensityAtom (a * (g + 1)) p.1 *
          thetaCuspTailSecondDensityAtom (b * (g + 1)) p.2) *
        xiCTaylorThetaTailCorePairCurrent d z p) =
      ∫ r : ℝ in Ici (thetaCuspPrimitiveRayRadialLog a b 0 0),
        (8 * Real.exp
          (-(Real.log (a : ℝ) + Real.log (b : ℝ)) / 2)) *
        thetaCuspPrimitiveRayJointSeamIntegrand d z r
          (-Real.log (a : ℝ)) (-Real.log (b : ℝ)) := by
  rw [integral_thetaCuspPrimitiveRayDensityPair_mul_coreCurrent_eq_polar ha hb]
  change
    (∫ q in thetaCuspPrimitiveRayActiveSet a b,
      thetaCuspPrimitiveRayPolarCoreIntegrand a b d z q) = _
  rw [integral_thetaCuspPrimitiveRayActiveSet_eq_movingIoo a b
    (thetaCuspPrimitiveRayPolarCoreIntegrand a b d z) hint]
  rw [← integral_indicator measurableSet_Ici]
  apply integral_congr_ae
  filter_upwards with r
  by_cases hr : thetaCuspPrimitiveRayRadialLog a b 0 0 ≤ r
  · have hactive :
        thetaCuspPrimitiveRayCorePolarLowerEndpoint r (-Real.log (a : ℝ)) ≤
          thetaCuspPrimitiveRayCorePolarUpperEndpoint r (-Real.log (b : ℝ)) :=
      (thetaCuspPrimitiveRayArithmeticPolar_activeWindow_iff_radialThreshold
        ha hb r).2 hr
    simp only [Set.indicator_apply, mem_Ici, if_pos hr]
    rw [← integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le hactive]
    calc
      (∫ u : ℝ in
          thetaCuspPrimitiveRayCorePolarLowerEndpoint r (-Real.log (a : ℝ))..
            thetaCuspPrimitiveRayCorePolarUpperEndpoint r (-Real.log (b : ℝ)),
          thetaCuspPrimitiveRayPolarCoreIntegrand a b d z (r, u)) =
        (8 * Real.exp
          (-(Real.log (a : ℝ) + Real.log (b : ℝ)) / 2)) *
          ∫ u : ℝ in
            thetaCuspPrimitiveRayCorePolarLowerEndpoint r (-Real.log (a : ℝ))..
              thetaCuspPrimitiveRayCorePolarUpperEndpoint r (-Real.log (b : ℝ)),
            (Real.exp (r / 2) * thetaCuspPrimitiveRayRadialPacket u r) *
              (thetaCuspPrimitiveRayMoment u) ^ (-(3 / 4 : ℝ)) *
              thetaCuspPrimitiveRayCorePolarKernel d z r
                (-Real.log (a : ℝ)) (-Real.log (b : ℝ)) u := by
          rw [← intervalIntegral.integral_const_mul]
          apply intervalIntegral.integral_congr
          intro u _hu
          unfold thetaCuspPrimitiveRayPolarCoreIntegrand
          dsimp only
          rw [show r / 2 -
              (Real.log (a : ℝ) + Real.log (b : ℝ)) / 2 =
            -(Real.log (a : ℝ) + Real.log (b : ℝ)) / 2 + r / 2 by ring,
            Real.exp_add]
          ring
      _ = _ := by
        rw [integral_thetaCuspPrimitiveRayRawPacket_eq_jointSeamIntegrand
          d z r (-Real.log (a : ℝ)) (-Real.log (b : ℝ)) hactive]
  · have hnot :
        ¬thetaCuspPrimitiveRayCorePolarLowerEndpoint r (-Real.log (a : ℝ)) <
          thetaCuspPrimitiveRayCorePolarUpperEndpoint r (-Real.log (b : ℝ)) := by
      have hreverse :
          thetaCuspPrimitiveRayCorePolarUpperEndpoint r (-Real.log (b : ℝ)) <
            thetaCuspPrimitiveRayCorePolarLowerEndpoint r (-Real.log (a : ℝ)) := by
        exact not_le.mp ((thetaCuspPrimitiveRayArithmeticPolar_activeWindow_iff_radialThreshold
          ha hb r).not.mpr hr)
      exact not_lt_of_ge hreverse.le
    rw [Set.Ioo_eq_empty hnot]
    simp only [Set.indicator_apply, mem_Ici, if_neg hr]
    simp

end

end RHTower
