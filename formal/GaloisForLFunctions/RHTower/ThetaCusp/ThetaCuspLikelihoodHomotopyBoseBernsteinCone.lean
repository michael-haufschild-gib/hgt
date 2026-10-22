import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspLikelihoodHomotopyLowerTransport

/-!
# Shifted Bose--Bernstein cone for the C5 likelihood homotopy

The literal Bose denominator contains every mode `exp (-n q)`, `n ≥ 1`.  Expanding at the
lowest mode does not require a series: the first three centered Bose jets have closed positive
rational forms.  This converts the whole lower-transport balance into four polynomial cone faces.

The tempting alternating derivative cone is impossible.  If `P(z) = z H(z)`, `z > 0`,
`H < 0`, and `H'' > 0`, then `P' > 0` forces `P'' > 0`, not `P'' < 0`.  The shifted cone below is
the surviving replacement.

RH chain: shifted Bose cone -> positive `M'''` -> convex likelihood lift -> structural-tail
direct-J orientation -> reflection-odd rank-four/Ptolemy -> CLG/TTF or Weil positivity -> RH.
-/

namespace RHTower

noncomputable section

/-- A negative convex quadratic multiplied by the positive affine coordinate cannot have the
naive alternating first two derivative signs. -/
theorem cubicTransport_second_pos_of_value_neg_of_first_pos
    {z H Hq Hqq : ℝ} (hz : 0 < z) (hH : H < 0)
    (hfirst : 0 < H + z * Hq) (hconvex : 0 < Hqq) :
    0 < 2 * Hq + z * Hqq := by
  have hHq : 0 < Hq := by
    have hzHq : 0 < z * Hq := by linarith
    rcases mul_pos_iff.mp hzHq with hpos | hneg
    · exact hpos.2
    · linarith
  exact add_pos (mul_pos (by norm_num) hHq) (mul_pos hz hconvex)

/-- No-go for the unshifted alternating Bose-mode cone. -/
theorem not_cubicTransport_alternatingCone
    {z H Hq Hqq : ℝ} (hz : 0 < z) (hH : H < 0) (hconvex : 0 < Hqq) :
    ¬(0 < H + z * Hq ∧ 2 * Hq + z * Hqq < 0) := by
  rintro ⟨hfirst, hsecond⟩
  exact (not_lt_of_ge (cubicTransport_second_pos_of_value_neg_of_first_pos
    hz hH hfirst hconvex).le) hsecond

namespace C5LikelihoodAffineData

/-- Zeroth lowest-mode-shifted jet of `v H`. -/
def boseShiftedTransportZero (d : C5LikelihoodAffineData) (l : ℝ) : ℝ :=
  (d.t * d.jetOne l) * d.velocityCenter l

/-- First lowest-mode-shifted jet of `v H`, with shift `-dq`. -/
def boseShiftedTransportOne (d : C5LikelihoodAffineData) (l : ℝ) : ℝ :=
  d.t * d.da * d.velocityCenter l +
    (d.t * d.jetOne l) * d.velocityCenterOne l -
    d.dq * d.boseShiftedTransportZero l

/-- Second lowest-mode-shifted jet of `v H`. -/
def boseShiftedTransportTwo (d : C5LikelihoodAffineData) (l : ℝ) : ℝ :=
  2 * (d.t * d.da) * d.velocityCenterOne l +
      (d.t * d.jetOne l) * d.velocityCenterTwo -
    2 * d.dq *
      (d.t * d.da * d.velocityCenter l +
        (d.t * d.jetOne l) * d.velocityCenterOne l) +
    d.dq ^ (2 : ℕ) * d.boseShiftedTransportZero l

/-- Third lowest-mode-shifted jet of `v H`. -/
def boseShiftedTransportThree (d : C5LikelihoodAffineData) (l : ℝ) : ℝ :=
  3 * (d.t * d.da) * d.velocityCenterTwo -
    3 * d.dq *
      (2 * (d.t * d.da) * d.velocityCenterOne l +
        (d.t * d.jetOne l) * d.velocityCenterTwo) +
    3 * d.dq ^ (2 : ℕ) *
      (d.t * d.da * d.velocityCenter l +
        (d.t * d.jetOne l) * d.velocityCenterOne l) -
    d.dq ^ (3 : ℕ) * d.boseShiftedTransportZero l

/-- Finite four-face replacement for termwise control of all Bose modes. -/
def BoseShiftedTransportCone (d : C5LikelihoodAffineData) (l : ℝ) : Prop :=
  d.boseShiftedTransportZero l ≤ 0 ∧
    d.boseShiftedTransportOne l ≤ 0 ∧
    d.boseShiftedTransportTwo l ≤ 0 ∧
    d.boseShiftedTransportThree l ≤ 0

private theorem boseCenteredJetOne_pos
    (d : C5LikelihoodAffineData) {l : ℝ}
    (haction : 0 < d.action l) (hdq : d.dq < 0) :
    0 < d.boseReciprocalOne l + d.dq * d.boseReciprocal l := by
  have he : 1 < Real.exp (d.action l) := by
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.mpr haction
  have hr : 0 < Real.exp (d.action l) - 1 := sub_pos.mpr he
  unfold boseReciprocal boseReciprocalOne
  dsimp only
  rw [show
      (-Real.exp (d.action l)) * d.dq /
            (Real.exp (d.action l) - 1) ^ (2 : ℕ) +
          d.dq * (1 / (Real.exp (d.action l) - 1)) =
        (-d.dq) / (Real.exp (d.action l) - 1) ^ (2 : ℕ) by
      field_simp [hr.ne']
      ring]
  exact div_pos (neg_pos.mpr hdq) (pow_pos hr 2)

private theorem boseCenteredJetTwo_pos
    (d : C5LikelihoodAffineData) {l : ℝ}
    (haction : 0 < d.action l) (hdq : d.dq < 0) :
    0 < d.boseReciprocalTwo l +
      2 * d.dq * d.boseReciprocalOne l +
      d.dq ^ (2 : ℕ) * d.boseReciprocal l := by
  have he : 1 < Real.exp (d.action l) := by
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.mpr haction
  have hr : 0 < Real.exp (d.action l) - 1 := sub_pos.mpr he
  unfold boseReciprocal boseReciprocalOne boseReciprocalTwo
  dsimp only
  rw [show
      Real.exp (d.action l) * (Real.exp (d.action l) + 1) * d.dq ^ (2 : ℕ) /
            (Real.exp (d.action l) - 1) ^ (3 : ℕ) +
          2 * d.dq *
            ((-Real.exp (d.action l)) * d.dq /
              (Real.exp (d.action l) - 1) ^ (2 : ℕ)) +
          d.dq ^ (2 : ℕ) * (1 / (Real.exp (d.action l) - 1)) =
        d.dq ^ (2 : ℕ) * (Real.exp (d.action l) + 1) /
          (Real.exp (d.action l) - 1) ^ (3 : ℕ) by
      field_simp [hr.ne']
      ring]
  exact div_pos
    (mul_pos (sq_pos_of_neg hdq) (by positivity)) (pow_pos hr 3)

private theorem boseCenteredJetThree_pos
    (d : C5LikelihoodAffineData) {l : ℝ}
    (haction : 0 < d.action l) (hdq : d.dq < 0) :
    0 < d.boseReciprocalThree l +
      3 * d.dq * d.boseReciprocalTwo l +
      3 * d.dq ^ (2 : ℕ) * d.boseReciprocalOne l +
      d.dq ^ (3 : ℕ) * d.boseReciprocal l := by
  have he : 1 < Real.exp (d.action l) := by
    rw [← Real.exp_zero]
    exact Real.exp_lt_exp.mpr haction
  have hr : 0 < Real.exp (d.action l) - 1 := sub_pos.mpr he
  unfold boseReciprocal boseReciprocalOne boseReciprocalTwo boseReciprocalThree
  dsimp only
  rw [show
      (-Real.exp (d.action l)) *
              (Real.exp (d.action l) ^ (2 : ℕ) + 4 * Real.exp (d.action l) + 1) *
              d.dq ^ (3 : ℕ) /
            (Real.exp (d.action l) - 1) ^ (4 : ℕ) +
          3 * d.dq *
            (Real.exp (d.action l) * (Real.exp (d.action l) + 1) * d.dq ^ (2 : ℕ) /
              (Real.exp (d.action l) - 1) ^ (3 : ℕ)) +
          3 * d.dq ^ (2 : ℕ) *
            ((-Real.exp (d.action l)) * d.dq /
              (Real.exp (d.action l) - 1) ^ (2 : ℕ)) +
          d.dq ^ (3 : ℕ) * (1 / (Real.exp (d.action l) - 1)) =
        (-d.dq) ^ (3 : ℕ) *
            (Real.exp (d.action l) ^ (2 : ℕ) + 4 * Real.exp (d.action l) + 1) /
          (Real.exp (d.action l) - 1) ^ (4 : ℕ) by
      field_simp [hr.ne']
      ring]
  exact div_pos
    (mul_pos (pow_pos (neg_pos.mpr hdq) 3) (by positivity)) (pow_pos hr 4)

private theorem lowerTransportBalance_algebra
    (dv v H H1 H2 dq f f1 f2 f3 : ℝ) :
    8 * (3 * dv * f2 + v * f3) * H +
        3 * (8 * (2 * dv * f1 + v * f2)) * H1 +
        3 * (10 * dv + 8 * (dv * f + v * f1)) * H2 =
      30 * dv * H2 +
        8 * (f *
            (3 * dv * H2 - 3 * dq * (2 * dv * H1 + v * H2) +
              3 * dq ^ (2 : ℕ) * (dv * H + v * H1) - dq ^ (3 : ℕ) * (v * H)) +
          3 * (f1 + dq * f) *
            (2 * dv * H1 + v * H2 - 2 * dq * (dv * H + v * H1) +
              dq ^ (2 : ℕ) * (v * H)) +
          3 * (f2 + 2 * dq * f1 + dq ^ (2 : ℕ) * f) *
            (dv * H + v * H1 - dq * (v * H)) +
          (f3 + 3 * dq * f2 + 3 * dq ^ (2 : ℕ) * f1 + dq ^ (3 : ℕ) * f) *
            (v * H)) := by
  ring

private theorem lowerTransportBalance_eq_boseShifted
    (d : C5LikelihoodAffineData) (l : ℝ) :
    d.boseCoefficientThree l * d.velocityCenter l +
        3 * d.boseCoefficientTwo l * d.velocityCenterOne l +
        3 * d.boseCoefficientOne l * d.velocityCenterTwo =
      30 * (d.t * d.da) * d.velocityCenterTwo +
        8 * (d.boseReciprocal l * d.boseShiftedTransportThree l +
          3 * (d.boseReciprocalOne l + d.dq * d.boseReciprocal l) *
            d.boseShiftedTransportTwo l +
          3 * (d.boseReciprocalTwo l +
              2 * d.dq * d.boseReciprocalOne l +
              d.dq ^ (2 : ℕ) * d.boseReciprocal l) *
            d.boseShiftedTransportOne l +
          (d.boseReciprocalThree l +
              3 * d.dq * d.boseReciprocalTwo l +
              3 * d.dq ^ (2 : ℕ) * d.boseReciprocalOne l +
              d.dq ^ (3 : ℕ) * d.boseReciprocal l) *
            d.boseShiftedTransportZero l) := by
  unfold boseCoefficientOne boseCoefficientTwo boseCoefficientThree
  dsimp only
  simpa only [boseShiftedTransportZero, boseShiftedTransportOne,
    boseShiftedTransportTwo, boseShiftedTransportThree] using
    lowerTransportBalance_algebra
      (d.t * d.da) (d.t * d.jetOne l)
      (d.velocityCenter l) (d.velocityCenterOne l) d.velocityCenterTwo d.dq
      (d.boseReciprocal l) (d.boseReciprocalOne l)
      (d.boseReciprocalTwo l) (d.boseReciprocalThree l)

/-- Shifted Bernstein cone closes the exact Bose balance, with no truncation or infinite-series
interchange. -/
theorem compensationThree_pos_of_boseShiftedTransportCone
    (d : C5LikelihoodAffineData) {l : ℝ}
    (haction : 0 < d.action l) (hdq : d.dq < 0)
    (hdv : d.t * d.da < 0) (hHtwo : 0 < d.velocityCenterTwo)
    (hcone : d.BoseShiftedTransportCone l) :
    0 < d.compensationThree l := by
  have hr : 0 < d.boseReciprocal l := by
    have he : 1 < Real.exp (d.action l) := by
      rw [← Real.exp_zero]
      exact Real.exp_lt_exp.mpr haction
    unfold boseReciprocal
    positivity
  have hr1 := boseCenteredJetOne_pos d haction hdq
  have hr2 := boseCenteredJetTwo_pos d haction hdq
  have hr3 := boseCenteredJetThree_pos d haction hdq
  rcases hcone with ⟨hzero, hone, htwo, hthree⟩
  have hbase : 30 * (d.t * d.da) * d.velocityCenterTwo < 0 := by
    exact mul_neg_of_neg_of_pos
      (mul_neg_of_pos_of_neg (by norm_num) hdv) hHtwo
  have hsum :
      d.boseReciprocal l * d.boseShiftedTransportThree l +
          3 * (d.boseReciprocalOne l + d.dq * d.boseReciprocal l) *
            d.boseShiftedTransportTwo l +
          3 * (d.boseReciprocalTwo l +
              2 * d.dq * d.boseReciprocalOne l +
              d.dq ^ (2 : ℕ) * d.boseReciprocal l) *
            d.boseShiftedTransportOne l +
          (d.boseReciprocalThree l +
              3 * d.dq * d.boseReciprocalTwo l +
              3 * d.dq ^ (2 : ℕ) * d.boseReciprocalOne l +
              d.dq ^ (3 : ℕ) * d.boseReciprocal l) *
            d.boseShiftedTransportZero l ≤ 0 := by
    have h0 := mul_nonpos_of_nonneg_of_nonpos hr.le hthree
    have h1 := mul_nonpos_of_nonneg_of_nonpos hr1.le htwo
    have h2 := mul_nonpos_of_nonneg_of_nonpos hr2.le hone
    have h3 := mul_nonpos_of_nonneg_of_nonpos hr3.le hzero
    nlinarith
  rw [compensationThree_pos_iff_lowerTransportBalance_neg]
  rw [lowerTransportBalance_eq_boseShifted]
  nlinarith

end C5LikelihoodAffineData

/-- Source-specialized closure: previous projective-curvature theorem supplies strict `H''>0`;
the remaining exact burden is only the four polynomial shifted-cone faces. -/
theorem thetaCuspC5LikelihoodHomotopyCompensationThree_pos_of_boseShiftedTransportCone
    {u t l : ℝ} (ht : 0 < t) (htu : t ≤ u)
    (hscale : 6 ≤ thetaCuspSingleAtomReflectionScale 1 (u - t))
    (hl0 : 0 ≤ l) (hl1 : l ≤ 1)
    (hcone : (thetaCuspC5LikelihoodHomotopyData u t).BoseShiftedTransportCone l) :
    0 < thetaCuspC5LikelihoodHomotopyCompensationThree u t l := by
  let d := thetaCuspC5LikelihoodHomotopyData u t
  have haction : 0 < d.action l := by
    simpa only [d] using thetaCuspC5LikelihoodHomotopyAction_pos ht htu hl0 hl1
  have hdq : d.dq < 0 := by
    simpa only [d, thetaCuspC5LikelihoodHomotopyData] using
      thetaCuspReflectedLikelihoodCumulantAction_neg ht htu
  have hda : d.da < 0 := by
    simpa only [d, thetaCuspC5LikelihoodHomotopyData] using
      thetaCuspReflectedLikelihoodCumulantJetOne_neg ht htu
  have hdv : d.t * d.da < 0 := by
    dsimp only [d, thetaCuspC5LikelihoodHomotopyData]
    exact mul_neg_of_pos_of_neg ht hda
  have hHtwo : 0 < d.velocityCenterTwo := by
    simpa only [d] using
      thetaCuspC5LikelihoodHomotopy_velocityCenterTwo_pos ht htu hscale
  exact d.compensationThree_pos_of_boseShiftedTransportCone
    haction hdq hdv hHtwo hcone

end

end RHTower
