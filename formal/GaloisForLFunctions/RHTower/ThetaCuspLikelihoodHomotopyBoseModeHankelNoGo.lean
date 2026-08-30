import GaloisForLFunctions.RHTower.ThetaCuspLikelihoodHomotopyBoseBernsteinCone

/-!
# Reverse Hankel law for the C5 Bose-mode transport

The failed fixed four-face cone leaves open a weaker idea: control only the cubic transport on
the occupied Bose modes by a Lorentz/Hankel condition on its first three shifted faces. This file
closes that idea sharply.

The `2 × 2` shifted-face determinant is independent of the Bose shift. For the literal C5 source,
positive action velocity, negative velocity centre, and strict positive centre curvature force the
determinant to be strictly negative. Thus the proposed positive Lorentz/Hankel cone has exactly the
wrong inertia already at the first-atom endpoint. The surviving datum is the strict reverse-Hankel
orientation; any modewise proof must use the full cubic face and its signed Bose pairing, rather
than a positive `2 × 2` moment cone.
-/

namespace RHTower

noncomputable section

namespace C5LikelihoodAffineData

/-- The Bose shift cancels from the first shifted Hankel determinant. What remains is the
log-curvature determinant of the cubic transport `v H`, including the affine-velocity tax. -/
theorem boseShiftedTransport_hankelDet_eq
    (d : C5LikelihoodAffineData) (l : ℝ) :
    d.boseShiftedTransportZero l * d.boseShiftedTransportTwo l -
        d.boseShiftedTransportOne l ^ 2 =
      (d.t * d.jetOne l) ^ 2 *
          (d.velocityCenter l * d.velocityCenterTwo -
            d.velocityCenterOne l ^ 2) -
        (d.t * d.da) ^ 2 * d.velocityCenter l ^ 2 := by
  simp only [boseShiftedTransportZero, boseShiftedTransportOne,
    boseShiftedTransportTwo]
  ring

/-- Strict reverse-Hankel orientation. A positive affine action velocity multiplying a negative,
strictly convex centre can never enter the positive Lorentz/Hankel cone, for any Bose shift. -/
theorem boseShiftedTransport_hankelDet_neg
    (d : C5LikelihoodAffineData) {l : ℝ}
    (hv : 0 < d.t * d.jetOne l)
    (hH : d.velocityCenter l < 0)
    (hHtwo : 0 < d.velocityCenterTwo) :
    d.boseShiftedTransportZero l * d.boseShiftedTransportTwo l -
        d.boseShiftedTransportOne l ^ 2 < 0 := by
  rw [boseShiftedTransport_hankelDet_eq]
  have hcore : d.velocityCenter l * d.velocityCenterTwo -
      d.velocityCenterOne l ^ 2 < 0 := by
    have hprod : d.velocityCenter l * d.velocityCenterTwo < 0 :=
      mul_neg_of_neg_of_pos hH hHtwo
    nlinarith [sq_nonneg (d.velocityCenterOne l)]
  have hmain : (d.t * d.jetOne l) ^ 2 *
      (d.velocityCenter l * d.velocityCenterTwo -
        d.velocityCenterOne l ^ 2) < 0 :=
    mul_neg_of_pos_of_neg (sq_pos_of_pos hv) hcore
  have htax : 0 ≤ (d.t * d.da) ^ 2 * d.velocityCenter l ^ 2 :=
    mul_nonneg (sq_nonneg _) (sq_nonneg _)
  linarith

end C5LikelihoodAffineData

private theorem thetaCuspSingleAtomReflectionScale_one_mono_boseModeHankel
    {x y : ℝ} (hxy : x ≤ y) :
    thetaCuspSingleAtomReflectionScale 1 x ≤
      thetaCuspSingleAtomReflectionScale 1 y := by
  unfold thetaCuspSingleAtomReflectionScale
  norm_num
  exact mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.mpr (by linarith)) Real.pi_pos.le

/-- Source-specialized no-go. At every scale-six first-atom endpoint, the literal occupied-mode
transport has negative first Hankel determinant. Consequently no proof can replace the false
four-face cone by a positive Lorentz/Hankel condition on faces zero through two. -/
theorem thetaCuspC5LikelihoodHomotopy_boseShiftedTransport_hankelDet_zero_neg
    {u t : ℝ} (ht : 0 < t) (htu : t ≤ u)
    (hscale : 6 ≤ thetaCuspSingleAtomReflectionScale 1 (u - t)) :
    let d := thetaCuspC5LikelihoodHomotopyData u t
    d.boseShiftedTransportZero 0 * d.boseShiftedTransportTwo 0 -
        d.boseShiftedTransportOne 0 ^ 2 < 0 := by
  let d := thetaCuspC5LikelihoodHomotopyData u t
  have hv : 0 < d.t * d.jetOne 0 := by
    simpa only [d, thetaCuspC5LikelihoodHomotopyData,
      C5LikelihoodAffineData.jetOne, C5LikelihoodAffineData.affine,
      zero_mul, add_zero] using
      mul_pos ht
        (thetaCuspSingleAtomReflectedActionJetOne_pos_of_sameHalfLine ht htu)
  have hscaleU : 6 ≤ thetaCuspSingleAtomReflectionScale 1 u := by
    exact hscale.trans
      (thetaCuspSingleAtomReflectionScale_one_mono_boseModeHankel (by linarith))
  have hH : d.velocityCenter 0 < 0 := by
    simpa only [d, thetaCuspC5LikelihoodHomotopyData,
      C5LikelihoodAffineData.velocityCenter,
      C5LikelihoodAffineData.jetOne, C5LikelihoodAffineData.jetTwo,
      C5LikelihoodAffineData.scaleAction, C5LikelihoodAffineData.scaleMixedOne,
      C5LikelihoodAffineData.affine, c5SingleAtomVelocityCenterNumerator,
      zero_mul, add_zero] using
      c5SingleAtomVelocityCenterNumerator_neg_of_sameHalfLine ht htu hscaleU
  have hHtwo : 0 < d.velocityCenterTwo := by
    simpa only [d] using
      thetaCuspC5LikelihoodHomotopy_velocityCenterTwo_pos ht htu hscale
  exact d.boseShiftedTransport_hankelDet_neg hv hH hHtwo

end


end RHTower
