import GaloisForLFunctions.RHTower.XiCTaylorThetaTailCoreCurrentEquivalence
import GaloisForLFunctions.RHTower.XiCTaylorThetaTailFiniteArithmeticCofinalSelection
import GaloisForLFunctions.RHTower.XiCTaylorThetaTailPhaseAdaptedRawCoreBridge

/-!
# Terminal composition for the finite theta-tail core current

This module isolates the exact logical composition still needed after the phase-adapted arithmetic
Haar construction.  It deliberately separates two inputs:

* an exact identity writing the raw core current as one normalized reflected-prefix contribution
  plus one normalized weighted top-row contribution;
* a joint selector controlling those two contributions at the same arithmetic cutoff and Haar
  depth.

The first estimate is one-sided and the second is absolute.  If `J = A + R`, then

`J <= A + |R| < epsilon B / 2 + epsilon B / 2 = epsilon B`.

Thus no sign of the top row and no estimate of the completed pieces separately is required.  The
interfaces below are strictly source-facing: they do not assume the raw core-current bound.
-/

open Complex Real MeasureTheory Set Filter Topology Polynomial

namespace RHTower

noncomputable section

/-- The minimal integer strictly above the source-parameter degree of the two finite phase
channels attached to the depth-`d` theta-tail core.  The core translation law uses phase depth
`d + 1`, hence degree `2 * (d + 1)`. -/
def xiCTaylorThetaTailCoreProuhetOrder (d : ℕ) : ℕ :=
  2 * (d + 1) + 1

theorem two_mul_succ_lt_xiCTaylorThetaTailCoreProuhetOrder (d : ℕ) :
    2 * (d + 1) < xiCTaylorThetaTailCoreProuhetOrder d := by
  unfold xiCTaylorThetaTailCoreProuhetOrder
  omega

/-- Exact two-term interface expected from the raw-to-reflected current bridge.  The two real
functions are already-normalized contributions: every factor and sign in the raw Haar identity
must be included in them before this interface can be instantiated. -/
def XiCTaylorThetaTailCoreCurrentTwoTermBridge
    (prefixScale topRowScale : ℝ)
    (m : ℕ → ℕ)
    (prefixContribution topRowContribution : ℕ → ℕ → ℕ → ℂ → ℝ) : Prop :=
  ∀ d N M : ℕ, ∀ z : ℂ,
    0 < z.im → z.im < 1 / 2 → 2 * (d + 1) < m d →
      orientedPolynomialCurrent (xiCTaylorThetaTailCorePolynomial d) z =
        prefixScale * prefixContribution d N M z +
          topRowScale * topRowContribution d N M z

/-- Joint selection interface at one common arithmetic cutoff and Haar depth.  The prefix is
controlled one-sided, while the top row is controlled in absolute value. -/
def XiCTaylorThetaTailCoreCurrentJointSublinearUpper
    (prefixScale topRowScale : ℝ)
    (D : ℕ → ℕ)
    (prefixContribution topRowContribution : ℕ → ℕ → ℕ → ℂ → ℝ) : Prop :=
  ∀ sigma : ℂ, 0 < sigma.re → sigma.re < 1 / 2 →
    ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ n : ℕ in atTop, ∃ N M : ℕ,
        prefixScale *
            prefixContribution
              (D (xiCTaylorAnisotropicScheduleStage sigma n)) N M
              (xiCTaylorAnisotropicCenteredPoint sigma n) <
          ((epsilon / 2) * ((n + 1 : ℕ) : ℝ)) *
            Complex.normSq
              ((xiCTaylorPolynomial
                (xiCTaylorOddDegreeSchedule D
                  (xiCTaylorAnisotropicScheduleStage sigma n))).eval
                    (xiCTaylorAnisotropicCenteredPoint sigma n)) ∧
        |topRowScale *
            topRowContribution
              (D (xiCTaylorAnisotropicScheduleStage sigma n)) N M
              (xiCTaylorAnisotropicCenteredPoint sigma n)| <
          ((epsilon / 2) * ((n + 1 : ℕ) : ℝ)) *
            Complex.normSq
              ((xiCTaylorPolynomial
                (xiCTaylorOddDegreeSchedule D
                  (xiCTaylorAnisotropicScheduleStage sigma n))).eval
                    (xiCTaylorAnisotropicCenteredPoint sigma n))

/-! ## Concrete finite-arithmetic data

The corrected raw-current audit has three displayed contributions.  The reflected-prefix integral
is `1 / 2` of the returned finite-arithmetic current and the raw correlation has outer factor
`1 / 4`, giving coefficient `1 / 8`.  Both the weighted top row and the surviving finite-translation
current retain coefficient `1 / 4`.  We keep the latter two together as one remainder: estimating
them separately is neither required nor mathematically safe.
-/

/-- Returned reflected-prefix current at the minimal Prouhet order for the local core depth. -/
def canonicalThetaTailCoreFiniteArithmeticPrefixCurrent
    (d N M : ℕ) (z : ℂ) : ℝ :=
  canonicalThetaTailFiniteArithmeticUntruncatedCurrent
    (xiCTaylorThetaTailCoreProuhetOrder d) N M z

/-- Complete coefficient-weighted top row at the same endpoint, depth, and local core degree. -/
def canonicalThetaTailCoreFiniteArithmeticTopRowCurrent
    (d N M : ℕ) (z : ℂ) : ℝ :=
  (canonicalThetaTailFiniteArithmeticWeightedTopRowCurrent
    d (xiCTaylorThetaTailCoreProuhetOrder d) N M z).re

/-- The exact finite-translation current left by reflection transport and replacement of the
finite core kernel by the untruncated phase kernel. -/
def canonicalThetaTailCoreFiniteArithmeticSurvivingTranslationCurrent
    (d N M : ℕ) (z : ℂ) : ℝ :=
  phaseAdaptedRawCoreSurvivingFiniteTranslationCurrent
    d (xiCTaylorThetaTailCoreProuhetOrder d) N z
    (canonicalThetaTailFiniteArithmeticProuhetEndpoint
      (xiCTaylorThetaTailCoreProuhetOrder d) N M z)

/-- The remainder which must be bounded without destroying the exact cancellation between its
cofinal top-row and finite-translation pieces. -/
def canonicalThetaTailCoreFiniteArithmeticRemainderCurrent
    (d N M : ℕ) (z : ℂ) : ℝ :=
  canonicalThetaTailCoreFiniteArithmeticTopRowCurrent d N M z +
    canonicalThetaTailCoreFiniteArithmeticSurvivingTranslationCurrent d N M z

/-- The complex weighted top-row pairing has no hidden imaginary part; its real part is exactly
the literal coefficient-weighted integrated top-row current. -/
theorem canonicalThetaTailCoreFiniteArithmeticTopRowCurrent_eq_raw
    (d N M : ℕ) (z : ℂ) :
    canonicalThetaTailCoreFiniteArithmeticTopRowCurrent d N M z =
      phaseAdaptedRawCoreWeightedTopRowIntegratedCurrent
        (canonicalPhaseAdaptedWeightedHaarPolynomial
          (xiCTaylorThetaTailCoreProuhetOrder d) z
          (canonicalThetaTailFiniteArithmeticProuhetEndpoint
            (xiCTaylorThetaTailCoreProuhetOrder d) N M z))
        dyadicProuhetDecayCharacter N d z := by
  unfold canonicalThetaTailCoreFiniteArithmeticTopRowCurrent
    canonicalThetaTailFiniteArithmeticWeightedTopRowCurrent
  rw [phaseAdaptedProuhetWeightedTopRowCurrent_eq_ofReal]
  rfl

/-- **Exact concrete raw bridge.**  At the finite-arithmetic endpoint the raw core current is the
`1 / 8` returned prefix plus `1 / 4` times the combined top-row/finite-translation remainder.
The order hypothesis belongs to the phase-cancellation mechanism; the corrected algebraic bridge
itself is valid without using it. -/
theorem xiCTaylorThetaTailCoreCurrentFiniteArithmeticTwoTermBridge :
    XiCTaylorThetaTailCoreCurrentTwoTermBridge
      (1 / 8 : ℝ) (1 / 4 : ℝ)
      xiCTaylorThetaTailCoreProuhetOrder
      canonicalThetaTailCoreFiniteArithmeticPrefixCurrent
      canonicalThetaTailCoreFiniteArithmeticRemainderCurrent := by
  intro d N M z hz0 hzHalf _horder
  let tau := canonicalThetaTailFiniteArithmeticProuhetEndpoint
    (xiCTaylorThetaTailCoreProuhetOrder d) N M z
  have h :=
    xiCTaylorThetaTailCore_current_eq_returnedSource_add_topRows_add_survivor
      d (xiCTaylorThetaTailCoreProuhetOrder d) N hz0 hzHalf tau
  dsimp only at h
  unfold canonicalThetaTailCoreFiniteArithmeticRemainderCurrent
  rw [canonicalThetaTailCoreFiniteArithmeticTopRowCurrent_eq_raw]
  unfold canonicalThetaTailCoreFiniteArithmeticPrefixCurrent
    canonicalThetaTailCoreFiniteArithmeticSurvivingTranslationCurrent
    canonicalThetaTailFiniteArithmeticUntruncatedCurrent
  dsimp only [tau] at h
  linarith

/-- The combined remainder is exactly the raw current minus the returned prefix.  Thus the top-row
decay cannot by itself make this remainder small: the finite-translation survivor carries whatever
raw current is not already present in the prefix. -/
theorem canonicalThetaTailCoreFiniteArithmeticRemainderCurrent_eq_raw_sub_prefix
    (d N M : ℕ) {z : ℂ} (hz0 : 0 < z.im) (hzHalf : z.im < 1 / 2) :
    canonicalThetaTailCoreFiniteArithmeticRemainderCurrent d N M z =
      4 * orientedPolynomialCurrent (xiCTaylorThetaTailCorePolynomial d) z -
        (1 / 2 : ℝ) *
          canonicalThetaTailCoreFiniteArithmeticPrefixCurrent d N M z := by
  have h := xiCTaylorThetaTailCoreCurrentFiniteArithmeticTwoTermBridge
    d N M z hz0 hzHalf
      (two_mul_succ_lt_xiCTaylorThetaTailCoreProuhetOrder d)
  linarith

/-- Wherever the affine endpoint denominator is nonzero, the combined remainder loses all Haar
depth dependence: it is the raw current minus one half of the finite density-transform defect. -/
theorem canonicalThetaTailCoreFiniteArithmeticRemainderCurrent_eq_raw_sub_densityDefect
    (d N M : ℕ) {z : ℂ} (hz0 : 0 < z.im) (hzHalf : z.im < 1 / 2)
    (hden : phaseAdaptedCriticalSelfConsistentDenominator
      (xiCTaylorThetaTailCoreProuhetOrder d) N
      (spectralTranslationPhase (Real.log 2) z)
      dyadicProuhetGrowthCharacter z
      (thetaHalfExponentialPhaseValue z)
      (thetaHalfExponentialPhaseDerivative z) ≠ 0) :
    canonicalThetaTailCoreFiniteArithmeticRemainderCurrent d N M z =
      4 * orientedPolynomialCurrent (xiCTaylorThetaTailCorePolynomial d) z -
        (1 / 2 : ℝ) *
          canonicalThetaTailFiniteArithmeticDensityDefectCurrent M z := by
  rw [canonicalThetaTailCoreFiniteArithmeticRemainderCurrent_eq_raw_sub_prefix
    d N M hz0 hzHalf]
  unfold canonicalThetaTailCoreFiniteArithmeticPrefixCurrent
  rw [canonicalThetaTailFiniteArithmeticUntruncatedCurrent_eq_densityDefect
    (xiCTaylorThetaTailCoreProuhetOrder d) N M hden]

/-- Two admissible Haar depths give the same combined remainder.  Cofinal selection in `N` can
shrink the displayed top row only by transferring exactly the opposite amount into the surviving
finite-translation current. -/
theorem canonicalThetaTailCoreFiniteArithmeticRemainderCurrent_eq_of_denominators_ne_zero
    (d M N₁ N₂ : ℕ) {z : ℂ} (hz0 : 0 < z.im) (hzHalf : z.im < 1 / 2)
    (hden₁ : phaseAdaptedCriticalSelfConsistentDenominator
      (xiCTaylorThetaTailCoreProuhetOrder d) N₁
      (spectralTranslationPhase (Real.log 2) z)
      dyadicProuhetGrowthCharacter z
      (thetaHalfExponentialPhaseValue z)
      (thetaHalfExponentialPhaseDerivative z) ≠ 0)
    (hden₂ : phaseAdaptedCriticalSelfConsistentDenominator
      (xiCTaylorThetaTailCoreProuhetOrder d) N₂
      (spectralTranslationPhase (Real.log 2) z)
      dyadicProuhetGrowthCharacter z
      (thetaHalfExponentialPhaseValue z)
      (thetaHalfExponentialPhaseDerivative z) ≠ 0) :
    canonicalThetaTailCoreFiniteArithmeticRemainderCurrent d N₁ M z =
    canonicalThetaTailCoreFiniteArithmeticRemainderCurrent d N₂ M z := by
  rw [canonicalThetaTailCoreFiniteArithmeticRemainderCurrent_eq_raw_sub_densityDefect
      d N₁ M hz0 hzHalf hden₁,
    canonicalThetaTailCoreFiniteArithmeticRemainderCurrent_eq_raw_sub_densityDefect
      d N₂ M hz0 hzHalf hden₂]

/-- **Exact Haar-refinement current conservation.**  Between two admissible depths, every change
in the displayed top row is transferred with the opposite sign into the finite-translation
survivor.  Thus cofinal refinement does not dissipate the unresolved current; it only moves that
current between the two summands of the depth-independent remainder. -/
theorem canonicalThetaTailCoreFiniteArithmeticSurvivor_sub_eq_neg_topRow_sub
    (d M N₁ N₂ : ℕ) {z : ℂ} (hz0 : 0 < z.im) (hzHalf : z.im < 1 / 2)
    (hden₁ : phaseAdaptedCriticalSelfConsistentDenominator
      (xiCTaylorThetaTailCoreProuhetOrder d) N₁
      (spectralTranslationPhase (Real.log 2) z)
      dyadicProuhetGrowthCharacter z
      (thetaHalfExponentialPhaseValue z)
      (thetaHalfExponentialPhaseDerivative z) ≠ 0)
    (hden₂ : phaseAdaptedCriticalSelfConsistentDenominator
      (xiCTaylorThetaTailCoreProuhetOrder d) N₂
      (spectralTranslationPhase (Real.log 2) z)
      dyadicProuhetGrowthCharacter z
      (thetaHalfExponentialPhaseValue z)
      (thetaHalfExponentialPhaseDerivative z) ≠ 0) :
    canonicalThetaTailCoreFiniteArithmeticSurvivingTranslationCurrent d N₂ M z -
        canonicalThetaTailCoreFiniteArithmeticSurvivingTranslationCurrent d N₁ M z =
      -(canonicalThetaTailCoreFiniteArithmeticTopRowCurrent d N₂ M z -
        canonicalThetaTailCoreFiniteArithmeticTopRowCurrent d N₁ M z) := by
  have hrem :=
    canonicalThetaTailCoreFiniteArithmeticRemainderCurrent_eq_of_denominators_ne_zero
      d M N₁ N₂ hz0 hzHalf hden₁ hden₂
  unfold canonicalThetaTailCoreFiniteArithmeticRemainderCurrent at hrem
  linarith

/-- **Cofinal survivor law.**  For a fixed finite arithmetic cutoff, the top row vanishes but its
current does not disappear: the survivor converges to the conserved raw-current residue

`4 J_d(z) - (1/2) densityDefect_M(z)`.

This is the positive content of the failed two-term bridge and rules out interpreting top-row
decay as decay of the complete finite-translation remainder. -/
theorem tendsto_canonicalThetaTailCoreFiniteArithmeticSurvivingTranslationCurrent
    (d M : ℕ) {z : ℂ} (hz0 : 0 < z.im) (hzHalf : z.im < 1 / 2) :
    Tendsto (fun N : ℕ =>
      canonicalThetaTailCoreFiniteArithmeticSurvivingTranslationCurrent d N M z)
      atTop
      (nhds (4 * orientedPolynomialCurrent
          (xiCTaylorThetaTailCorePolynomial d) z -
        (1 / 2 : ℝ) *
          canonicalThetaTailFiniteArithmeticDensityDefectCurrent M z)) := by
  let L : ℝ :=
    4 * orientedPolynomialCurrent (xiCTaylorThetaTailCorePolynomial d) z -
      (1 / 2 : ℝ) * canonicalThetaTailFiniteArithmeticDensityDefectCurrent M z
  have hzLower : -(1 / 2 : ℝ) < z.im := by linarith
  have hden := canonicalThetaTailFiniteArithmeticDenominator_eventually_ne_zero
    (xiCTaylorThetaTailCoreProuhetOrder d) hzLower hzHalf
  have htopComplex :=
    tendsto_canonicalThetaTailFiniteArithmeticWeightedTopRowCurrent
      d (xiCTaylorThetaTailCoreProuhetOrder d) M hzLower hzHalf
  have htop : Tendsto (fun N : ℕ =>
      canonicalThetaTailCoreFiniteArithmeticTopRowCurrent d N M z)
      atTop (nhds 0) := by
    have hre := Complex.continuous_re.continuousAt.tendsto.comp htopComplex
    simpa only [canonicalThetaTailCoreFiniteArithmeticTopRowCurrent,
      Complex.zero_re] using hre
  have hlimit : Tendsto (fun N : ℕ =>
      L - canonicalThetaTailCoreFiniteArithmeticTopRowCurrent d N M z)
      atTop (nhds L) := by
    simpa using (tendsto_const_nhds.sub htop)
  apply hlimit.congr'
  filter_upwards [hden] with N hN
  rw [show canonicalThetaTailCoreFiniteArithmeticSurvivingTranslationCurrent d N M z =
      canonicalThetaTailCoreFiniteArithmeticRemainderCurrent d N M z -
        canonicalThetaTailCoreFiniteArithmeticTopRowCurrent d N M z by
      unfold canonicalThetaTailCoreFiniteArithmeticRemainderCurrent
      ring,
    canonicalThetaTailCoreFiniteArithmeticRemainderCurrent_eq_raw_sub_densityDefect
      d N M hz0 hzHalf hN]

/-- As the finite square-index cutoff exhausts the canonical density, the depth-independent
remainder expression converges to four times the raw core current, not to zero. -/
theorem tendsto_canonicalThetaTailCore_raw_sub_half_densityDefect
    (d : ℕ) {z : ℂ} (hz : 0 ≤ z.im) :
    Tendsto (fun M : ℕ =>
      4 * orientedPolynomialCurrent (xiCTaylorThetaTailCorePolynomial d) z -
        (1 / 2 : ℝ) *
          canonicalThetaTailFiniteArithmeticDensityDefectCurrent M z)
      atTop
      (nhds (4 * orientedPolynomialCurrent
        (xiCTaylorThetaTailCorePolynomial d) z)) := by
  have hdefect :=
    (tendsto_canonicalThetaTailFiniteArithmeticDensityDefectCurrent hz).const_mul
      (1 / 2 : ℝ)
  simpa using
    (tendsto_const_nhds.sub hdefect : Tendsto (fun M : ℕ =>
      4 * orientedPolynomialCurrent (xiCTaylorThetaTailCorePolynomial d) z -
        (1 / 2 : ℝ) *
          canonicalThetaTailFiniteArithmeticDensityDefectCurrent M z)
      atTop (nhds
        (4 * orientedPolynomialCurrent (xiCTaylorThetaTailCorePolynomial d) z -
          (1 / 2 : ℝ) * 0)))

/-- The finite-arithmetic cofinal selector supplies the concrete joint estimate.  Notice that the
top-row degree is the local core depth `D(stage n)`, while the Prouhet order is the associated odd
degree `2 * (D(stage n) + 1) + 1`; these two parameters must not be interchanged. -/
theorem xiCTaylorThetaTailCoreCurrentFiniteArithmeticPrefixTopJointSublinearUpper
    {D : ℕ → ℕ} (hD : XiCTaylorOddThetaTailSuperaccurateSchedule D) :
    XiCTaylorThetaTailCoreCurrentJointSublinearUpper
      (1 / 8 : ℝ) (1 / 4 : ℝ) D
      canonicalThetaTailCoreFiniteArithmeticPrefixCurrent
      canonicalThetaTailCoreFiniteArithmeticTopRowCurrent := by
  intro sigma hsigma0 hsigmaHalf epsilon hepsilon
  have hzero : Tendsto (fun n : ℕ =>
      (0 : ℝ) * (((n + 1 : ℕ) : ℝ) ^
        (2 * (analyticOrderAt xi sigma).toNat))) atTop (nhds 0) := by
    simpa using (tendsto_const_nhds :
      Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (nhds 0))
  have hpositive :=
    eventually_remainder_lt_scaled_xiCTaylor_normSq_of_tendsto_localOrder
      hD sigma (fun _ : ℕ => (0 : ℝ)) hzero hepsilon
  have himPos :=
    eventually_xiCTaylorAnisotropicCenteredPoint_im_pos sigma hsigmaHalf
  have himHalf :=
    eventually_xiCTaylorAnisotropicCenteredPoint_im_lt_half sigma hsigma0
  filter_upwards [hpositive, himPos, himHalf] with n hn hzn0 hznHalf
  let d := D (xiCTaylorAnisotropicScheduleStage sigma n)
  let z := xiCTaylorAnisotropicCenteredPoint sigma n
  let B := (epsilon * ((n + 1 : ℕ) : ℝ)) *
    Complex.normSq
      ((xiCTaylorPolynomial
        (xiCTaylorOddDegreeSchedule D
          (xiCTaylorAnisotropicScheduleStage sigma n))).eval z)
  have hB : 0 < B := by
    simpa only [B, z] using hn
  obtain ⟨M, N, _hden, _htau, hprefixNorm, htopNorm⟩ :=
    exists_canonicalThetaTailFiniteArithmeticCofinalSelection
      d (xiCTaylorThetaTailCoreProuhetOrder d) hzn0 hznHalf hB
  refine ⟨N, M, ?_, ?_⟩
  · have hprefixAbs :
        |canonicalThetaTailCoreFiniteArithmeticPrefixCurrent d N M z| < B := by
      simpa only [canonicalThetaTailCoreFiniteArithmeticPrefixCurrent,
        Real.norm_eq_abs] using hprefixNorm
    have hprefixLe :
        canonicalThetaTailCoreFiniteArithmeticPrefixCurrent d N M z ≤
          |canonicalThetaTailCoreFiniteArithmeticPrefixCurrent d N M z| :=
      le_abs_self _
    calc
      (1 / 8 : ℝ) *
          canonicalThetaTailCoreFiniteArithmeticPrefixCurrent d N M z ≤
        (1 / 8 : ℝ) *
          |canonicalThetaTailCoreFiniteArithmeticPrefixCurrent d N M z| :=
        mul_le_mul_of_nonneg_left hprefixLe (by norm_num)
      _ < (1 / 8 : ℝ) * B :=
        mul_lt_mul_of_pos_left hprefixAbs (by norm_num)
      _ < (1 / 2 : ℝ) * B := by nlinarith [hB]
      _ = ((epsilon / 2) * ((n + 1 : ℕ) : ℝ)) *
          Complex.normSq
            ((xiCTaylorPolynomial
              (xiCTaylorOddDegreeSchedule D
                (xiCTaylorAnisotropicScheduleStage sigma n))).eval
                  (xiCTaylorAnisotropicCenteredPoint sigma n)) := by
        dsimp only [B, z]
        ring
  · have htopRe :
        |canonicalThetaTailCoreFiniteArithmeticTopRowCurrent d N M z| ≤
          ‖canonicalThetaTailFiniteArithmeticWeightedTopRowCurrent
            d (xiCTaylorThetaTailCoreProuhetOrder d) N M z‖ := by
      exact Complex.abs_re_le_norm _
    have htopAbs :
        |canonicalThetaTailCoreFiniteArithmeticTopRowCurrent d N M z| < B :=
      htopRe.trans_lt (by simpa only [B, d, z] using htopNorm)
    calc
      |(1 / 4 : ℝ) *
          canonicalThetaTailCoreFiniteArithmeticTopRowCurrent d N M z| =
        (1 / 4 : ℝ) *
          |canonicalThetaTailCoreFiniteArithmeticTopRowCurrent d N M z| := by
        rw [abs_mul]
        norm_num
      _ < (1 / 4 : ℝ) * B :=
        mul_lt_mul_of_pos_left htopAbs (by norm_num)
      _ < (1 / 2 : ℝ) * B := by nlinarith [hB]
      _ = ((epsilon / 2) * ((n + 1 : ℕ) : ℝ)) *
          Complex.normSq
            ((xiCTaylorPolynomial
              (xiCTaylorOddDegreeSchedule D
                (xiCTaylorAnisotropicScheduleStage sigma n))).eval
                  (xiCTaylorAnisotropicCenteredPoint sigma n)) := by
        dsimp only [B, z]
        ring

/-- The exact two-term bridge and a same-parameter joint estimate imply the raw theta-tail core
current condition.  This is the terminal epsilon-budget composition; it contains no sign input
beyond the one-sided prefix bound and `r ≤ |r|` for the top row. -/
theorem xiCTaylorThetaTailCoreCurrentSublinearUpper_of_twoTermBridge
    {D m : ℕ → ℕ}
    {prefixScale topRowScale : ℝ}
    {prefixContribution topRowContribution : ℕ → ℕ → ℕ → ℂ → ℝ}
    (horder : ∀ d : ℕ, 2 * (d + 1) < m d)
    (hbridge : XiCTaylorThetaTailCoreCurrentTwoTermBridge
      prefixScale topRowScale m prefixContribution topRowContribution)
    (hjoint : XiCTaylorThetaTailCoreCurrentJointSublinearUpper
      prefixScale topRowScale D prefixContribution topRowContribution) :
    XiCTaylorThetaTailCoreCurrentSublinearUpper D := by
  intro sigma hsigma0 hsigmaHalf epsilon hepsilon
  have hjointEventually := hjoint sigma hsigma0 hsigmaHalf epsilon hepsilon
  have himPos :=
    eventually_xiCTaylorAnisotropicCenteredPoint_im_pos sigma hsigmaHalf
  have himHalf :=
    eventually_xiCTaylorAnisotropicCenteredPoint_im_lt_half sigma hsigma0
  filter_upwards [hjointEventually, himPos, himHalf] with n hn hzn0 hznHalf
  obtain ⟨N, M, hprefix, htop⟩ := hn
  rw [hbridge
    (D (xiCTaylorAnisotropicScheduleStage sigma n)) N M
    (xiCTaylorAnisotropicCenteredPoint sigma n) hzn0 hznHalf
    (horder (D (xiCTaylorAnisotropicScheduleStage sigma n)))]
  calc
    prefixScale *
          prefixContribution
            (D (xiCTaylorAnisotropicScheduleStage sigma n)) N M
            (xiCTaylorAnisotropicCenteredPoint sigma n) +
        topRowScale *
          topRowContribution
            (D (xiCTaylorAnisotropicScheduleStage sigma n)) N M
            (xiCTaylorAnisotropicCenteredPoint sigma n) ≤
      prefixScale *
          prefixContribution
            (D (xiCTaylorAnisotropicScheduleStage sigma n)) N M
            (xiCTaylorAnisotropicCenteredPoint sigma n) +
        |topRowScale *
          topRowContribution
            (D (xiCTaylorAnisotropicScheduleStage sigma n)) N M
            (xiCTaylorAnisotropicCenteredPoint sigma n)| := by
            gcongr
            exact le_abs_self _
    _ <
      ((epsilon / 2) * ((n + 1 : ℕ) : ℝ)) *
          Complex.normSq
            ((xiCTaylorPolynomial
              (xiCTaylorOddDegreeSchedule D
                (xiCTaylorAnisotropicScheduleStage sigma n))).eval
                  (xiCTaylorAnisotropicCenteredPoint sigma n)) +
        ((epsilon / 2) * ((n + 1 : ℕ) : ℝ)) *
          Complex.normSq
            ((xiCTaylorPolynomial
              (xiCTaylorOddDegreeSchedule D
                (xiCTaylorAnisotropicScheduleStage sigma n))).eval
                  (xiCTaylorAnisotropicCenteredPoint sigma n)) :=
      add_lt_add hprefix htop
    _ =
      (epsilon * ((n + 1 : ℕ) : ℝ)) *
        Complex.normSq
          ((xiCTaylorPolynomial
            (xiCTaylorOddDegreeSchedule D
              (xiCTaylorAnisotropicScheduleStage sigma n))).eval
                (xiCTaylorAnisotropicCenteredPoint sigma n)) := by ring

/-- Terminal logical composition.  It is deliberately conditional on the strictly stronger,
source-facing bridge and joint selector; it does not assume the raw core-current predicate. -/
theorem riemannHypothesis_of_xiCTaylorThetaTailCoreCurrent_twoTermBridge
    {D m : ℕ → ℕ}
    {prefixScale topRowScale : ℝ}
    {prefixContribution topRowContribution : ℕ → ℕ → ℕ → ℂ → ℝ}
    (hD : XiCTaylorOddThetaTailSuperaccurateSchedule D)
    (horder : ∀ d : ℕ, 2 * (d + 1) < m d)
    (hbridge : XiCTaylorThetaTailCoreCurrentTwoTermBridge
      prefixScale topRowScale m prefixContribution topRowContribution)
    (hjoint : XiCTaylorThetaTailCoreCurrentJointSublinearUpper
      prefixScale topRowScale D prefixContribution topRowContribution) :
    RiemannHypothesis :=
  riemannHypothesis_of_xiCTaylorThetaTailCoreCurrentSublinearUpper hD
    (xiCTaylorThetaTailCoreCurrentSublinearUpper_of_twoTermBridge
      horder hbridge hjoint)

/-!
## Concrete instantiation contract

The exact raw-current bridge is now instantiated at `xiCTaylorThetaTailCoreProuhetOrder`.  Its
first function is the returned finite-arithmetic reflected-prefix current with scale `1 / 8`.
Its second function, with scale `1 / 4`, is the sum of the real weighted top row and the surviving
finite-translation current formed with the same polynomial

`canonicalPhaseAdaptedWeightedHaarPolynomial m z
  (canonicalThetaTailFiniteArithmeticProuhetEndpoint m N M z)`.

The completed cofinal selector already controls the prefix and top row at the same `N,M`; it does
not control the surviving finite-translation current.  The remaining joint estimate must retain
the top row and survivor together, unless a separate estimate is proved compatible with the same
`N,M`.  Eventual strict positivity of the scheduled Taylor denominator is supplied upstream by
`eventually_remainder_lt_scaled_xiCTaylor_normSq_of_tendsto_localOrder`; it is not an additional
sign hypothesis here.
-/

/-- Canonical-order specialization of the terminal composition. -/
theorem xiCTaylorThetaTailCoreCurrentSublinearUpper_of_canonicalProuhetBridge
    {D : ℕ → ℕ}
    {prefixScale topRowScale : ℝ}
    {prefixContribution topRowContribution : ℕ → ℕ → ℕ → ℂ → ℝ}
    (hbridge : XiCTaylorThetaTailCoreCurrentTwoTermBridge
      prefixScale topRowScale xiCTaylorThetaTailCoreProuhetOrder
        prefixContribution topRowContribution)
    (hjoint : XiCTaylorThetaTailCoreCurrentJointSublinearUpper
      prefixScale topRowScale D prefixContribution topRowContribution) :
    XiCTaylorThetaTailCoreCurrentSublinearUpper D :=
  xiCTaylorThetaTailCoreCurrentSublinearUpper_of_twoTermBridge
    two_mul_succ_lt_xiCTaylorThetaTailCoreProuhetOrder hbridge hjoint

/-- Canonical-order terminal endpoint.  Once the concrete bridge and joint selector instantiate
the two source-facing interfaces, the existing finite coefficient gate gives RH. -/
theorem riemannHypothesis_of_xiCTaylorThetaTailCoreCurrent_canonicalProuhetBridge
    {D : ℕ → ℕ}
    {prefixScale topRowScale : ℝ}
    {prefixContribution topRowContribution : ℕ → ℕ → ℕ → ℂ → ℝ}
    (hD : XiCTaylorOddThetaTailSuperaccurateSchedule D)
    (hbridge : XiCTaylorThetaTailCoreCurrentTwoTermBridge
      prefixScale topRowScale xiCTaylorThetaTailCoreProuhetOrder
        prefixContribution topRowContribution)
    (hjoint : XiCTaylorThetaTailCoreCurrentJointSublinearUpper
      prefixScale topRowScale D prefixContribution topRowContribution) :
    RiemannHypothesis :=
  riemannHypothesis_of_xiCTaylorThetaTailCoreCurrent_twoTermBridge hD
    two_mul_succ_lt_xiCTaylorThetaTailCoreProuhetOrder hbridge hjoint

/-- Concrete terminal core-current theorem.  After the exact bridge and the completed prefix/top
selector, the sole remaining input is the joint upper estimate for the combined top-row and
finite-translation remainder at the same finite arithmetic parameters. -/
theorem xiCTaylorThetaTailCoreCurrentSublinearUpper_of_finiteArithmeticRemainderJoint
    {D : ℕ → ℕ}
    (hjoint : XiCTaylorThetaTailCoreCurrentJointSublinearUpper
      (1 / 8 : ℝ) (1 / 4 : ℝ) D
      canonicalThetaTailCoreFiniteArithmeticPrefixCurrent
      canonicalThetaTailCoreFiniteArithmeticRemainderCurrent) :
    XiCTaylorThetaTailCoreCurrentSublinearUpper D :=
  xiCTaylorThetaTailCoreCurrentSublinearUpper_of_twoTermBridge
    two_mul_succ_lt_xiCTaylorThetaTailCoreProuhetOrder
    xiCTaylorThetaTailCoreCurrentFiniteArithmeticTwoTermBridge hjoint

/-- Concrete terminal RH endpoint.  This theorem does not hide the remaining obstruction: its
single source-facing hypothesis is precisely the joint bound for the exact combined remainder. -/
theorem riemannHypothesis_of_xiCTaylorThetaTailCoreCurrent_finiteArithmeticRemainderJoint
    {D : ℕ → ℕ}
    (hD : XiCTaylorOddThetaTailSuperaccurateSchedule D)
    (hjoint : XiCTaylorThetaTailCoreCurrentJointSublinearUpper
      (1 / 8 : ℝ) (1 / 4 : ℝ) D
      canonicalThetaTailCoreFiniteArithmeticPrefixCurrent
      canonicalThetaTailCoreFiniteArithmeticRemainderCurrent) :
    RiemannHypothesis :=
  riemannHypothesis_of_xiCTaylorThetaTailCoreCurrentSublinearUpper hD
    (xiCTaylorThetaTailCoreCurrentSublinearUpper_of_finiteArithmeticRemainderJoint
      hjoint)

end

end RHTower
