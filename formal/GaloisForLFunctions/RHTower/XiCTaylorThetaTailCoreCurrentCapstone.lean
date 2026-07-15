import GaloisForLFunctions.RHTower.XiCTaylorThetaTailCoreCurrentEquivalence
import GaloisForLFunctions.RHTower.XiCTaylorThetaTailFiniteArithmeticCofinalSelection

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

The literal raw-current identity has the outer factor `1 / 4`.  The reflected-prefix integral is
itself `1 / 2` of the returned finite-arithmetic current, so its coefficient in the raw current is
`1 / 8`.  The weighted top row remains under the outer `1 / 4`; since its coefficient packet is
complex-valued but formed from real integrated rows, the raw bridge uses its real part.
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

/-- Exact concrete bridge contract.  Its constants are forced by the two already-formalized
normalizations: `1 / 4` from the raw correlation integral and `1 / 2` from the integrated
reflected-prefix identification. -/
def XiCTaylorThetaTailCoreCurrentFiniteArithmeticBridge : Prop :=
  XiCTaylorThetaTailCoreCurrentTwoTermBridge
    (1 / 8 : ℝ) (1 / 4 : ℝ)
    xiCTaylorThetaTailCoreProuhetOrder
    canonicalThetaTailCoreFiniteArithmeticPrefixCurrent
    canonicalThetaTailCoreFiniteArithmeticTopRowCurrent

/-- The finite-arithmetic cofinal selector supplies the concrete joint estimate.  Notice that the
top-row degree is the local core depth `D(stage n)`, while the Prouhet order is the associated odd
degree `2 * (D(stage n) + 1) + 1`; these two parameters must not be interchanged. -/
theorem xiCTaylorThetaTailCoreCurrentFiniteArithmeticJointSublinearUpper
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
    dsimp only [B] at hB
    dsimp only [B] at hprefixAbs
    nlinarith
  · have htopRe :
        |canonicalThetaTailCoreFiniteArithmeticTopRowCurrent d N M z| ≤
          ‖canonicalThetaTailFiniteArithmeticWeightedTopRowCurrent
            d (xiCTaylorThetaTailCoreProuhetOrder d) N M z‖ := by
      exact Complex.abs_re_le_norm _
    dsimp only [B] at hB
    dsimp only [B] at htopNorm
    rw [abs_mul]
    norm_num
    nlinarith

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

The raw-current bridge should instantiate `m` with `xiCTaylorThetaTailCoreProuhetOrder`.  Its
prefix function is the finite-arithmetic weighted reflected-prefix current, after applying every
normalization found in the exact raw-to-reflected identity.  Its top-row function is the real part
of `phaseAdaptedProuhetWeightedTopRowCurrent` formed with the same polynomial

`canonicalPhaseAdaptedWeightedHaarPolynomial m z
  (canonicalThetaTailFiniteArithmeticProuhetEndpoint m N M z)`.

The two real scales in this interface are where the bridge records the exact outer factors; the
joint selector must estimate the scaled terms rather than silently discard those constants.  It
must choose the same `N` and `M` for both terms.  Eventual strict positivity of the scheduled Taylor
denominator is supplied upstream by
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

end

end RHTower
