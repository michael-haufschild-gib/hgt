import GaloisForLFunctions.RHTower.XiCTaylorThetaTailCoreCurrentCapstone

/-!
# The finite-arithmetic remainder condition is RH-equivalent

The exact finite-arithmetic bridge writes the theta-tail core current as

`J = (1 / 8) * prefix + (1 / 4) * remainder`.

The cofinal arithmetic selector makes the prefix arbitrarily small.  This module proves the
converse direction omitted by the terminal composition: under RH the raw current is absolutely
sublinear on every anisotropic fibre, and hence the exact combined remainder admits the required
joint estimate.  Consequently the concrete remainder condition is not an independent source
estimate: on every source-selected superaccurate schedule it is logically equivalent to RH.
-/

open Complex Real MeasureTheory Set Filter Topology Polynomial

namespace RHTower

noncomputable section

/-- RH supplies the concrete same-parameter joint estimate for the exact combined finite
arithmetic remainder.  The prefix is selected below the full epsilon budget; the identity
`remainder = 4 * J - (1 / 2) * prefix` reduces its normalized absolute value to the bounded raw
current plus one eighth of that prefix. -/
theorem xiCTaylorThetaTailCoreFiniteArithmeticRemainderJointSublinearUpper_of_riemannHypothesis
    {D : ℕ → ℕ} (hD : XiCTaylorOddThetaTailSuperaccurateSchedule D)
    (hRH : RiemannHypothesis) :
    XiCTaylorThetaTailCoreCurrentJointSublinearUpper
      (1 / 8 : ℝ) (1 / 4 : ℝ) D
      canonicalThetaTailCoreFiniteArithmeticPrefixCurrent
      canonicalThetaTailCoreFiniteArithmeticRemainderCurrent := by
  intro sigma hsigma0 hsigmaHalf epsilon hepsilon
  have hraw :=
    eventually_abs_xiCTaylorThetaTailCoreCurrent_lt_scaled_normSq_of_riemannHypothesis
      hD hRH sigma hsigmaHalf (epsilon / 4) (div_pos hepsilon (by norm_num))
  have himPos :=
    eventually_xiCTaylorAnisotropicCenteredPoint_im_pos sigma hsigmaHalf
  have himHalf :=
    eventually_xiCTaylorAnisotropicCenteredPoint_im_lt_half sigma hsigma0
  filter_upwards [hraw, himPos, himHalf] with n hnRaw hzn0 hznHalf
  let d : ℕ := D (xiCTaylorAnisotropicScheduleStage sigma n)
  let z : ℂ := xiCTaylorAnisotropicCenteredPoint sigma n
  let B : ℝ := (epsilon * ((n + 1 : ℕ) : ℝ)) *
    Complex.normSq
      ((xiCTaylorPolynomial
        (xiCTaylorOddDegreeSchedule D
          (xiCTaylorAnisotropicScheduleStage sigma n))).eval z)
  have hnRawQuarter :
      |orientedPolynomialCurrent (xiCTaylorThetaTailCorePolynomial d) z| <
        (1 / 4 : ℝ) * B := by
    calc
      |orientedPolynomialCurrent (xiCTaylorThetaTailCorePolynomial d) z| <
          ((epsilon / 4) * ((n + 1 : ℕ) : ℝ)) *
            Complex.normSq
              ((xiCTaylorPolynomial
                (xiCTaylorOddDegreeSchedule D
                  (xiCTaylorAnisotropicScheduleStage sigma n))).eval z) := by
        simpa only [d, z] using hnRaw
      _ = (1 / 4 : ℝ) * B := by
        dsimp only [B]
        ring
  have hB : 0 < B := by
    have hnonneg :
        0 ≤ |orientedPolynomialCurrent (xiCTaylorThetaTailCorePolynomial d) z| :=
      abs_nonneg _
    nlinarith
  obtain ⟨M, N, _hden, _htau, hprefixNorm, _htopNorm⟩ :=
    exists_canonicalThetaTailFiniteArithmeticCofinalSelection
      d (xiCTaylorThetaTailCoreProuhetOrder d) hzn0 hznHalf hB
  have hprefixAbs :
      |canonicalThetaTailCoreFiniteArithmeticPrefixCurrent d N M z| < B := by
    simpa only [canonicalThetaTailCoreFiniteArithmeticPrefixCurrent,
      Real.norm_eq_abs] using hprefixNorm
  refine ⟨N, M, ?_, ?_⟩
  · have hprefixLe :
        canonicalThetaTailCoreFiniteArithmeticPrefixCurrent d N M z ≤
          |canonicalThetaTailCoreFiniteArithmeticPrefixCurrent d N M z| :=
      le_abs_self _
    calc
      (1 / 8 : ℝ) * canonicalThetaTailCoreFiniteArithmeticPrefixCurrent d N M z ≤
          (1 / 8 : ℝ) *
            |canonicalThetaTailCoreFiniteArithmeticPrefixCurrent d N M z| :=
        mul_le_mul_of_nonneg_left hprefixLe (by norm_num)
      _ < (1 / 8 : ℝ) * B :=
        mul_lt_mul_of_pos_left hprefixAbs (by norm_num)
      _ < (1 / 2 : ℝ) * B := by nlinarith
      _ = ((epsilon / 2) * ((n + 1 : ℕ) : ℝ)) *
          Complex.normSq
            ((xiCTaylorPolynomial
              (xiCTaylorOddDegreeSchedule D
                (xiCTaylorAnisotropicScheduleStage sigma n))).eval
                  (xiCTaylorAnisotropicCenteredPoint sigma n)) := by
        dsimp only [B, z]
        ring
  · have hrem :=
      canonicalThetaTailCoreFiniteArithmeticRemainderCurrent_eq_raw_sub_prefix
        d N M hzn0 hznHalf
    calc
      |(1 / 4 : ℝ) *
          canonicalThetaTailCoreFiniteArithmeticRemainderCurrent d N M z| =
          |orientedPolynomialCurrent (xiCTaylorThetaTailCorePolynomial d) z -
            (1 / 8 : ℝ) *
              canonicalThetaTailCoreFiniteArithmeticPrefixCurrent d N M z| := by
        rw [hrem]
        congr 1
        ring
      _ ≤ |orientedPolynomialCurrent (xiCTaylorThetaTailCorePolynomial d) z| +
          |(1 / 8 : ℝ) *
            canonicalThetaTailCoreFiniteArithmeticPrefixCurrent d N M z| :=
        abs_sub _ _
      _ = |orientedPolynomialCurrent (xiCTaylorThetaTailCorePolynomial d) z| +
          (1 / 8 : ℝ) *
            |canonicalThetaTailCoreFiniteArithmeticPrefixCurrent d N M z| := by
        rw [abs_mul]
        norm_num
      _ < (1 / 4 : ℝ) * B + (1 / 8 : ℝ) * B :=
        add_lt_add hnRawQuarter
          (mul_lt_mul_of_pos_left hprefixAbs (by norm_num))
      _ < (1 / 2 : ℝ) * B := by nlinarith
      _ = ((epsilon / 2) * ((n + 1 : ℕ) : ℝ)) *
          Complex.normSq
            ((xiCTaylorPolynomial
              (xiCTaylorOddDegreeSchedule D
                (xiCTaylorAnisotropicScheduleStage sigma n))).eval
                  (xiCTaylorAnisotropicCenteredPoint sigma n)) := by
        dsimp only [B, z]
        ring

/-- **No-shortcut theorem.**  On every source-selected odd superaccurate schedule, the concrete
finite-arithmetic joint remainder estimate is equivalent to RH.  It therefore cannot serve as an
independent source producer unless its proof contributes genuinely new orientation information. -/
theorem xiCTaylorThetaTailCoreFiniteArithmeticRemainderJointSublinearUpper_iff_riemannHypothesis
    {D : ℕ → ℕ} (hD : XiCTaylorOddThetaTailSuperaccurateSchedule D) :
    XiCTaylorThetaTailCoreCurrentJointSublinearUpper
        (1 / 8 : ℝ) (1 / 4 : ℝ) D
        canonicalThetaTailCoreFiniteArithmeticPrefixCurrent
        canonicalThetaTailCoreFiniteArithmeticRemainderCurrent ↔
      RiemannHypothesis := by
  constructor
  · exact riemannHypothesis_of_xiCTaylorThetaTailCoreCurrent_finiteArithmeticRemainderJoint hD
  · exact
      xiCTaylorThetaTailCoreFiniteArithmeticRemainderJointSublinearUpper_of_riemannHypothesis hD

/-- The concrete joint remainder estimate and the raw theta-tail core-current estimate carry
exactly the same information on a superaccurate schedule. -/
theorem xiCTaylorThetaTailCoreFiniteArithmeticRemainderJointSublinearUpper_iff_coreCurrentSublinearUpper
    {D : ℕ → ℕ} (hD : XiCTaylorOddThetaTailSuperaccurateSchedule D) :
    XiCTaylorThetaTailCoreCurrentJointSublinearUpper
        (1 / 8 : ℝ) (1 / 4 : ℝ) D
        canonicalThetaTailCoreFiniteArithmeticPrefixCurrent
        canonicalThetaTailCoreFiniteArithmeticRemainderCurrent ↔
      XiCTaylorThetaTailCoreCurrentSublinearUpper D := by
  rw [xiCTaylorThetaTailCoreFiniteArithmeticRemainderJointSublinearUpper_iff_riemannHypothesis hD,
    xiCTaylorThetaTailCoreCurrentSublinearUpper_iff_riemannHypothesis hD]

/-- Existence of one source-selected odd schedule satisfying the concrete finite-arithmetic joint
remainder estimate is exactly RH. -/
theorem
    exists_xiCTaylorThetaTailCoreFiniteArithmeticRemainderJointSublinearUpper_iff_riemannHypothesis :
    (∃ D : ℕ → ℕ, XiCTaylorOddThetaTailSuperaccurateSchedule D ∧
      XiCTaylorThetaTailCoreCurrentJointSublinearUpper
        (1 / 8 : ℝ) (1 / 4 : ℝ) D
        canonicalThetaTailCoreFiniteArithmeticPrefixCurrent
        canonicalThetaTailCoreFiniteArithmeticRemainderCurrent) ↔
      RiemannHypothesis := by
  constructor
  · rintro ⟨D, hD, hremainder⟩
    exact
      (xiCTaylorThetaTailCoreFiniteArithmeticRemainderJointSublinearUpper_iff_riemannHypothesis
        hD).1 hremainder
  · intro hRH
    obtain ⟨D, hD⟩ := exists_xiCTaylorOddThetaTailSuperaccurateSchedule
    exact ⟨D, hD,
      (xiCTaylorThetaTailCoreFiniteArithmeticRemainderJointSublinearUpper_iff_riemannHypothesis
        hD).2 hRH⟩

/-- The concrete finite-arithmetic joint remainder estimate on every source-selected odd schedule
is exactly RH. -/
theorem
    forall_xiCTaylorThetaTailCoreFiniteArithmeticRemainderJointSublinearUpper_iff_riemannHypothesis :
    (∀ D : ℕ → ℕ, XiCTaylorOddThetaTailSuperaccurateSchedule D →
      XiCTaylorThetaTailCoreCurrentJointSublinearUpper
        (1 / 8 : ℝ) (1 / 4 : ℝ) D
        canonicalThetaTailCoreFiniteArithmeticPrefixCurrent
        canonicalThetaTailCoreFiniteArithmeticRemainderCurrent) ↔
      RiemannHypothesis := by
  constructor
  · intro hall
    obtain ⟨D, hD⟩ := exists_xiCTaylorOddThetaTailSuperaccurateSchedule
    exact
      (xiCTaylorThetaTailCoreFiniteArithmeticRemainderJointSublinearUpper_iff_riemannHypothesis
        hD).1 (hall D hD)
  · intro hRH D hD
    exact
      (xiCTaylorThetaTailCoreFiniteArithmeticRemainderJointSublinearUpper_iff_riemannHypothesis
        hD).2 hRH

end

end RHTower
