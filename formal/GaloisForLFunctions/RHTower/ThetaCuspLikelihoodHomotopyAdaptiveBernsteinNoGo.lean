import GaloisForLFunctions.RHTower.ThetaCuspLikelihoodHomotopyBoseBernsteinCone

/-!
# Adaptive-shift no-go for the C5 likelihood homotopy

An arbitrary scalar shift `sigma` acts on the cubic transport `v H` by the first four
`(D + sigma)` faces.  There is a unique adaptive shift cancelling the affine velocity drift,
`dv + sigma v = 0`.  That cancellation looks favorable, but its second face is exactly

`v * (H'' - sigma^(2 : ℕ) H)`.

Hence the physical chamber `v > 0`, `H < 0`, `H'' > 0` forces this face to be strictly positive.
At the first-atom endpoint of the literal theta-cusp homotopy, all three signs are already proved.
Therefore no all-nonpositive shifted Bernstein cone can be obtained by cancelling the velocity
drift.  This kills the whole adaptive-cancellation variant; the fixed lowest-mode Bose shift
remains the surviving shifted-cone route.

RH chain being tested: shifted transport cone -> positive `M'''` -> convex likelihood lift ->
structural-tail direct-J orientation -> reflection-odd rank-four/Ptolemy -> CLG/TTF or Weil
positivity -> RH.
-/

namespace RHTower

noncomputable section

namespace C5LikelihoodAffineData

/-- Zeroth face of the scalar-shifted cubic transport. -/
def shiftedTransportZero (d : C5LikelihoodAffineData) (l _sigma : ℝ) : ℝ :=
  (d.t * d.jetOne l) * d.velocityCenter l

/-- First face of the scalar-shifted cubic transport. -/
def shiftedTransportOne (d : C5LikelihoodAffineData) (l sigma : ℝ) : ℝ :=
  d.t * d.da * d.velocityCenter l +
    (d.t * d.jetOne l) * d.velocityCenterOne l +
    sigma * d.shiftedTransportZero l sigma

/-- Second face of the scalar-shifted cubic transport. -/
def shiftedTransportTwo (d : C5LikelihoodAffineData) (l sigma : ℝ) : ℝ :=
  2 * (d.t * d.da) * d.velocityCenterOne l +
      (d.t * d.jetOne l) * d.velocityCenterTwo +
    2 * sigma *
      (d.t * d.da * d.velocityCenter l +
        (d.t * d.jetOne l) * d.velocityCenterOne l) +
    sigma ^ (2 : ℕ) * d.shiftedTransportZero l sigma

/-- Third face of the scalar-shifted cubic transport. -/
def shiftedTransportThree (d : C5LikelihoodAffineData) (l sigma : ℝ) : ℝ :=
  3 * (d.t * d.da) * d.velocityCenterTwo +
    3 * sigma *
      (2 * (d.t * d.da) * d.velocityCenterOne l +
        (d.t * d.jetOne l) * d.velocityCenterTwo) +
    3 * sigma ^ (2 : ℕ) *
      (d.t * d.da * d.velocityCenter l +
        (d.t * d.jetOne l) * d.velocityCenterOne l) +
    sigma ^ (3 : ℕ) * d.shiftedTransportZero l sigma

/-- All-nonpositive shifted Bernstein faces through cubic order. -/
def ShiftedTransportCone (d : C5LikelihoodAffineData) (l sigma : ℝ) : Prop :=
  d.shiftedTransportZero l sigma ≤ 0 ∧
    d.shiftedTransportOne l sigma ≤ 0 ∧
    d.shiftedTransportTwo l sigma ≤ 0 ∧
    d.shiftedTransportThree l sigma ≤ 0

/-- The fixed physical shift `sigma = -dq` is exactly the previously isolated Bose cone. -/
theorem shiftedTransportCone_neg_dq_iff_boseShiftedTransportCone
    (d : C5LikelihoodAffineData) (l : ℝ) :
    d.ShiftedTransportCone l (-d.dq) ↔ d.BoseShiftedTransportCone l := by
  unfold ShiftedTransportCone shiftedTransportOne shiftedTransportTwo
    shiftedTransportThree shiftedTransportZero BoseShiftedTransportCone
    boseShiftedTransportOne boseShiftedTransportTwo boseShiftedTransportThree
    boseShiftedTransportZero
  ring_nf

/-- Unique scalar shift cancelling the affine velocity derivative. -/
def velocityCancellationShift (d : C5LikelihoodAffineData) (l : ℝ) : ℝ :=
  -(d.t * d.da) / (d.t * d.jetOne l)

private theorem shiftedTransportTwo_cancellation_algebra
    (v dv H H1 H2 sigma : ℝ) (hcancel : dv + sigma * v = 0) :
    2 * dv * H1 + v * H2 +
        2 * sigma * (dv * H + v * H1) + sigma ^ (2 : ℕ) * (v * H) =
      v * (H2 - sigma ^ (2 : ℕ) * H) := by
  have hdv : dv = -sigma * v := by linarith
  rw [hdv]
  ring

/-- Exact second-face law after adaptive velocity cancellation. -/
theorem shiftedTransportTwo_eq_of_velocityCancellation
    (d : C5LikelihoodAffineData) (l sigma : ℝ)
    (hcancel : d.t * d.da + sigma * (d.t * d.jetOne l) = 0) :
    d.shiftedTransportTwo l sigma =
      (d.t * d.jetOne l) *
        (d.velocityCenterTwo - sigma ^ (2 : ℕ) * d.velocityCenter l) := by
  unfold shiftedTransportTwo shiftedTransportZero
  exact shiftedTransportTwo_cancellation_algebra
    (d.t * d.jetOne l) (d.t * d.da) (d.velocityCenter l)
    (d.velocityCenterOne l) d.velocityCenterTwo sigma hcancel

/-- In the physical sign chamber, velocity cancellation reverses the required second face. -/
theorem shiftedTransportTwo_pos_of_velocityCancellation
    (d : C5LikelihoodAffineData) (l sigma : ℝ)
    (hv : 0 < d.t * d.jetOne l) (hH : d.velocityCenter l < 0)
    (hHtwo : 0 < d.velocityCenterTwo)
    (hcancel : d.t * d.da + sigma * (d.t * d.jetOne l) = 0) :
    0 < d.shiftedTransportTwo l sigma := by
  rw [d.shiftedTransportTwo_eq_of_velocityCancellation l sigma hcancel]
  have hsH : sigma ^ (2 : ℕ) * d.velocityCenter l ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (sq_nonneg sigma) hH.le
  exact mul_pos hv (sub_pos.mpr (lt_of_le_of_lt hsH hHtwo))

theorem velocityCancellationShift_cancels
    (d : C5LikelihoodAffineData) (l : ℝ)
    (hv : 0 < d.t * d.jetOne l) :
    d.t * d.da + d.velocityCancellationShift l * (d.t * d.jetOne l) = 0 := by
  unfold velocityCancellationShift
  rw [div_mul_cancel₀ _ (ne_of_gt hv)]
  ring

/-- No all-nonpositive shifted cone can use the velocity-cancelling shift in the physical
quadratic chamber. -/
theorem not_shiftedTransportCone_velocityCancellationShift
    (d : C5LikelihoodAffineData) (l : ℝ)
    (hv : 0 < d.t * d.jetOne l) (hH : d.velocityCenter l < 0)
    (hHtwo : 0 < d.velocityCenterTwo) :
    ¬d.ShiftedTransportCone l (d.velocityCancellationShift l) := by
  intro hcone
  have hface : d.shiftedTransportTwo l (d.velocityCancellationShift l) ≤ 0 :=
    hcone.2.2.1
  have hpositive : 0 < d.shiftedTransportTwo l (d.velocityCancellationShift l) :=
    d.shiftedTransportTwo_pos_of_velocityCancellation l
      (d.velocityCancellationShift l) hv hH hHtwo
      (d.velocityCancellationShift_cancels l hv)
  exact (not_lt_of_ge hface) hpositive

end C5LikelihoodAffineData

private theorem thetaCuspSingleAtomReflectionScale_one_mono_adaptiveNoGo
    {x y : ℝ} (hxy : x ≤ y) :
    thetaCuspSingleAtomReflectionScale 1 x ≤
      thetaCuspSingleAtomReflectionScale 1 y := by
  unfold thetaCuspSingleAtomReflectionScale
  norm_num
  exact mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.mpr (by linarith)) Real.pi_pos.le

/-- **Positive survivor.** At the literal first-atom endpoint, the unique shift cancelling affine
velocity variation has a strictly positive second face. -/
theorem thetaCuspC5LikelihoodHomotopy_shiftedTransportTwo_velocityCancellationShift_zero_pos
    {u t : ℝ} (ht : 0 < t) (htu : t ≤ u)
    (hscale : 6 ≤ thetaCuspSingleAtomReflectionScale 1 (u - t)) :
    let d := thetaCuspC5LikelihoodHomotopyData u t
    0 < d.shiftedTransportTwo 0 (d.velocityCancellationShift 0) := by
  let d := thetaCuspC5LikelihoodHomotopyData u t
  have hv : 0 < d.t * d.jetOne 0 := by
    simpa only [d, thetaCuspC5LikelihoodHomotopyData,
      C5LikelihoodAffineData.jetOne, C5LikelihoodAffineData.affine,
      zero_mul, add_zero] using
      mul_pos ht
        (thetaCuspSingleAtomReflectedActionJetOne_pos_of_sameHalfLine ht htu)
  have hscaleU : 6 ≤ thetaCuspSingleAtomReflectionScale 1 u := by
    exact hscale.trans
      (thetaCuspSingleAtomReflectionScale_one_mono_adaptiveNoGo (by linarith))
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
  exact d.shiftedTransportTwo_pos_of_velocityCancellation 0
    (d.velocityCancellationShift 0) hv hH hHtwo
    (d.velocityCancellationShift_cancels 0 hv)

/-- **Adaptive-shift route kill.** The velocity-cancelling shift cannot satisfy the all-nonpositive
Bernstein cone required by the C5 likelihood route. -/
theorem thetaCuspC5LikelihoodHomotopy_not_shiftedTransportCone_velocityCancellationShift_zero
    {u t : ℝ} (ht : 0 < t) (htu : t ≤ u)
    (hscale : 6 ≤ thetaCuspSingleAtomReflectionScale 1 (u - t)) :
    let d := thetaCuspC5LikelihoodHomotopyData u t
    ¬d.ShiftedTransportCone 0 (d.velocityCancellationShift 0) := by
  let d := thetaCuspC5LikelihoodHomotopyData u t
  change ¬d.ShiftedTransportCone 0 (d.velocityCancellationShift 0)
  intro hcone
  have hface : d.shiftedTransportTwo 0 (d.velocityCancellationShift 0) ≤ 0 :=
    hcone.2.2.1
  have hpositive : 0 < d.shiftedTransportTwo 0 (d.velocityCancellationShift 0) := by
    simpa only [d] using
      thetaCuspC5LikelihoodHomotopy_shiftedTransportTwo_velocityCancellationShift_zero_pos
        ht htu hscale
  exact (not_lt_of_ge hface) hpositive

end

end RHTower
