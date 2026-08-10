import GaloisForLFunctions.RHTower.XiShiftedHankelCassiniContactFourthCumulant

/-!
# Fourth-cumulant contact cap is the terminal sign

The proposed degree-one arithmetic reserve

`t^3 K4 <= 3 A (1-e)(1-2e^2)`

does not weaken the Route-U terminal orientation problem.  On the actual contact locus it is
equivalent to nonnegative contact flow, then to nonnegative terminal flux, and finally to the
adjacent shifted Hankel minor

`m_1 m_3 - m_2^2 >= 0`.

Thus a fourth-cumulant proof must produce this inequality before cumulant compression; assuming or
re-proving the displayed cap as an abstract contact inequality is exactly the original sign goal.
-/

namespace RHTower

noncomputable section

/-- Adjacent shifted `2 x 2` Hankel minor at degree one. -/
def xiShiftedDegreeOneAdjacentHankelMinor (y : ℝ) : ℝ :=
  (xiShiftedReciprocalMoment y 1).re *
      (xiShiftedReciprocalMoment y 3).re -
    (xiShiftedReciprocalMoment y 2).re ^ 2

/-- At a flat first face, multiplying terminal flux by the positive first shifted moment gives
exactly the adjacent shifted Hankel minor. -/
theorem re_xiShiftedReciprocalMoment_one_mul_terminalFlux_eq_adjacentMinor_of_flat
    {y : ℝ} (hy : 0 < y)
    (hflat : xiShiftedDegreeOneHankelMinor y = 0) :
    (xiShiftedReciprocalMoment y 1).re *
        xiShiftedDegreeOneTerminalFlux y =
      xiShiftedDegreeOneAdjacentHankelMinor y := by
  let m0 : ℝ := (xiShiftedReciprocalMoment y 0).re
  let m1 : ℝ := (xiShiftedReciprocalMoment y 1).re
  let m2 : ℝ := (xiShiftedReciprocalMoment y 2).re
  let m3 : ℝ := (xiShiftedReciprocalMoment y 3).re
  have hm0 : 0 < m0 := xiShiftedCassiniResponse_pos hy
  have hcontact : m0 * m2 = m1 ^ 2 := by
    rw [xiShiftedDegreeOneHankelMinor] at hflat
    dsimp only [xiShiftedCassiniResponse, m0, m1, m2] at hflat
    linarith
  rw [xiShiftedDegreeOneTerminalFlux_eq_moments]
  change m1 * (m3 - 2 * (m1 / m0) * m2 + (m1 / m0) ^ 2 * m1) =
    m1 * m3 - m2 ^ 2
  field_simp [hm0.ne']
  nlinarith [hcontact]

/-- On contact, the fourth-cumulant cap is equivalent, not merely sufficient, to nonnegative
outgoing contact flow. -/
theorem thetaCuspCassiniFourthCumulantCap_iff_contactFlow_nonneg_of_contact
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    (hcontact : thetaCuspCassiniEulerContactNumerator t = 0) :
    (t ^ 3 * thetaCuspCassiniEsscherFourthCumulant t ≤
        3 * thetaCuspCassiniEsscherMean t *
          (1 - thetaCuspCassiniContactElasticity t) *
          (1 - 2 * thetaCuspCassiniContactElasticity t ^ 2)) ↔
      0 ≤ thetaCuspCassiniEulerContactFlow t := by
  let A := thetaCuspCassiniEsscherMean t
  let e := thetaCuspCassiniContactElasticity t
  let K4 := thetaCuspCassiniEsscherFourthCumulant t
  have hA : 0 < A := by
    dsimp only [A]
    rw [thetaCuspCassiniEsscherMean_eq ht0 ht1]
    exact mul_pos ht0 (xiShiftedCassiniResponse_pos (sq_pos_of_pos ht0))
  rw [thetaCuspCassiniEulerContactFlow_eq_fourthCumulantWall_of_contact
    ht0 ht1 hcontact]
  change (t ^ 3 * K4 ≤ 3 * A * (1 - e) * (1 - 2 * e ^ 2)) ↔
    0 ≤ 3 * A ^ 2 / t * (1 - e) * (1 - 2 * e ^ 2) - t ^ 2 * A * K4
  have heq :
      3 * A ^ 2 / t * (1 - e) * (1 - 2 * e ^ 2) - t ^ 2 * A * K4 =
        (A / t) *
          (3 * A * (1 - e) * (1 - 2 * e ^ 2) - t ^ 3 * K4) := by
    field_simp [ht0.ne']
  rw [heq]
  constructor
  · intro h
    exact mul_nonneg (div_pos hA ht0).le (sub_nonneg.mpr h)
  · intro h
    rcases mul_nonneg_iff.mp h with hpos | hneg
    · exact sub_nonneg.mp hpos.2
    · exact (not_le_of_gt (div_pos hA ht0) hneg.1).elim

/-- On a theta contact, contact-flow orientation and the original terminal-flux orientation have
the same weak sign. -/
theorem thetaCuspCassiniContactFlow_nonneg_iff_terminalFlux_nonneg_of_contact
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    (hcontact : thetaCuspCassiniEulerContactNumerator t = 0) :
    0 ≤ thetaCuspCassiniEulerContactFlow t ↔
      0 ≤ xiShiftedDegreeOneTerminalFlux (t ^ 2) := by
  have hflat : xiShiftedDegreeOneHankelMinor (t ^ 2) = 0 :=
    (thetaCuspCassiniEulerContactNumerator_eq_zero_iff_minor_eq_zero
      ht0 ht1).mp hcontact
  have hneg :
      xiShiftedDegreeOneTerminalFlux (t ^ 2) < 0 ↔
        thetaCuspCassiniEulerContactFlow t < 0 := by
    constructor
    · intro hterminal
      exact (xiShiftedDegreeOne_flat_negative_iff_thetaCumulantContactFlow
        ht0 ht1).mp ⟨hflat, hterminal⟩ |>.2
    · intro hflow
      exact (xiShiftedDegreeOne_flat_negative_iff_thetaCumulantContactFlow
        ht0 ht1).mpr ⟨hcontact, hflow⟩ |>.2
  constructor
  · intro hflow
    exact le_of_not_gt fun hterminal =>
      (not_lt_of_ge hflow) (hneg.mp hterminal)
  · intro hterminal
    exact le_of_not_gt fun hflow =>
      (not_lt_of_ge hterminal) (hneg.mpr hflow)

/-- At a flat first face, terminal flux is nonnegative exactly when the adjacent shifted minor is
nonnegative. -/
theorem xiShiftedDegreeOneTerminalFlux_nonneg_iff_adjacentMinor_nonneg_of_flat
    {y : ℝ} (hy : 0 < y)
    (hflat : xiShiftedDegreeOneHankelMinor y = 0) :
    0 ≤ xiShiftedDegreeOneTerminalFlux y ↔
      0 ≤ xiShiftedDegreeOneAdjacentHankelMinor y := by
  have hm1 : 0 < (xiShiftedReciprocalMoment y 1).re :=
    re_xiShiftedReciprocalMoment_pos hy (by norm_num)
  have heq :=
    re_xiShiftedReciprocalMoment_one_mul_terminalFlux_eq_adjacentMinor_of_flat
      hy hflat
  constructor
  · intro hterminal
    rw [← heq]
    exact mul_nonneg hm1.le hterminal
  · intro hadjacent
    rw [← heq] at hadjacent
    rcases mul_nonneg_iff.mp hadjacent with hpos | hneg
    · exact hpos.2
    · exact (not_le_of_gt hm1 hneg.1).elim

/-- **Fourth-cumulant reserve circularity theorem.** On the actual theta contact locus, the
proposed quantitative fourth-cumulant reserve is exactly positivity of the next shifted Hankel
minor.  It is therefore the terminal sign in different coordinates, not an independent producer. -/
theorem thetaCuspCassiniFourthCumulantCap_iff_adjacentMinor_nonneg_of_contact
    {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    (hcontact : thetaCuspCassiniEulerContactNumerator t = 0) :
    (t ^ 3 * thetaCuspCassiniEsscherFourthCumulant t ≤
        3 * thetaCuspCassiniEsscherMean t *
          (1 - thetaCuspCassiniContactElasticity t) *
          (1 - 2 * thetaCuspCassiniContactElasticity t ^ 2)) ↔
      0 ≤ xiShiftedDegreeOneAdjacentHankelMinor (t ^ 2) := by
  have hflat : xiShiftedDegreeOneHankelMinor (t ^ 2) = 0 :=
    (thetaCuspCassiniEulerContactNumerator_eq_zero_iff_minor_eq_zero
      ht0 ht1).mp hcontact
  exact
    (thetaCuspCassiniFourthCumulantCap_iff_contactFlow_nonneg_of_contact
      ht0 ht1 hcontact).trans
      ((thetaCuspCassiniContactFlow_nonneg_iff_terminalFlux_nonneg_of_contact
        ht0 ht1 hcontact).trans
        (xiShiftedDegreeOneTerminalFlux_nonneg_iff_adjacentMinor_nonneg_of_flat
          (sq_pos_of_pos ht0) hflat))

end

end RHTower
