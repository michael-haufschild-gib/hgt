import GaloisForLFunctions.RHTower.XiCTaylorAnisotropicGaugeCharge
import GaloisForLFunctions.RHTower.XiCTaylorThetaTailMonotonePacketAnisotropic
import GaloisForLFunctions.RHTower.ChargeTomography

/-!
# Moving positive-completion gauges cannot screen Xi divisor charge

Fixed meromorphic gauges have an integer local charge, but a source gauge could instead vary with
every anisotropic mesh point.  This module closes the entire moving positive-completion class.

No normal-family or common-density hypothesis is used.  At each mesh point the density, source
value, derivative, phase lag, and packet depth may be different.  Positivity gives the uniform
half-plane estimate

`|Im (D / F)| ≤ 2 / Im z`.

The anisotropic horizontal step tends to zero while the centered imaginary part stays positive.
Thus every such moving gauge has zero mesh charge.  Subtraction from a superaccurate finite Xi
Taylor section preserves the exact Xi multiplicity, and screening occurs exactly off the Xi
divisor.

The final specialization applies this to literal recombined theta-tail packets with arbitrary
nonnegative phase-lag schedule and arbitrary positive depth schedule.
-/

open Complex Real MeasureTheory Set Filter Topology

namespace RHTower

noncomputable section

/-- Pointwise data asserting that `F,D` arise from a positive one-sided completion through the
two exact integration-by-parts connections. -/
structure PositiveTailCompletionGaugeAt
    (h : ℝ → ℝ) (F D z : ℂ) : Prop where
  nonneg : ∀ t ∈ Ioi (0 : ℝ), 0 ≤ h t
  completionIntegrable : IntegrableOn (fun t : ℝ =>
    (h t : ℂ) * (1 - spectralTranslationPhase t z)) (Ioi 0)
  derivativeIntegrable : IntegrableOn (fun t : ℝ =>
    (h t : ℂ) * (-((t : ℂ) * I) * spectralTranslationPhase t z)) (Ioi 0)
  completion_eq : positiveTailCompletion h z = -I * z * F
  completionDerivative_eq :
    positiveTailCompletionDerivative h z = -I * (F + z * D)
  value_ne_zero : F ≠ 0

/-- A positive-completion gauge has uniformly bounded logarithmic phase velocity.  The bound is
independent of the density, its mass and moments, and every source-depth parameter. -/
theorem PositiveTailCompletionGaugeAt.abs_im_derivative_div_value_le
    {h : ℝ → ℝ} {F D z : ℂ}
    (hg : PositiveTailCompletionGaugeAt h F D z)
    (hz : 0 < z.im) :
    |(D / F).im| ≤ 2 / z.im := by
  have hcontract :
      ‖positiveTailCompletionDerivative h z‖ ≤
        ‖positiveTailCompletion h z‖ / z.im := by
    calc
      ‖positiveTailCompletionDerivative h z‖ ≤
          (positiveTailCompletion h z).re / z.im :=
        norm_positiveTailCompletionDerivative_le_re_div hz hg.nonneg
          hg.completionIntegrable hg.derivativeIntegrable
      _ ≤ ‖positiveTailCompletion h z‖ / z.im :=
        (div_le_div_iff_of_pos_right hz).2 (Complex.re_le_norm _)
  have hD :
      ‖D‖ ≤ (2 / z.im) * ‖F‖ :=
    norm_derivative_le_two_div_im_of_completion_contraction
      hz hg.completion_eq hg.completionDerivative_eq hcontract
  have hFnorm : 0 < ‖F‖ := norm_pos_iff.mpr hg.value_ne_zero
  calc
    |(D / F).im| ≤ ‖D / F‖ := Complex.abs_im_le_norm _
    _ = ‖D‖ / ‖F‖ := norm_div D F
    _ ≤ ((2 / z.im) * ‖F‖) / ‖F‖ :=
      div_le_div_of_nonneg_right hD hFnorm.le
    _ = 2 / z.im := by field_simp

/-- **Arbitrary moving positive-gauge no-go.**  Even if all positive source data change with the
mesh index and have no local limit, their normalized horizontal charge tends to zero. -/
theorem tendsto_movingPositiveTailCompletionGauge_horizontalCharge_zero
    {h : ℕ → ℝ → ℝ} {F D : ℕ → ℂ} {sigma : ℂ}
    (hsigma : sigma.re < 1 / 2)
    (hg : ∀ᶠ n : ℕ in atTop, PositiveTailCompletionGaugeAt
      (h n) (F n) (D n) (xiCTaylorAnisotropicCenteredPoint sigma n)) :
    Tendsto
      (fun n : ℕ =>
        xiTaylorAnisotropicHorizontalStep sigma n *
          (D n / F n).im)
      atTop (nhds 0) := by
  let eta : ℝ := (xiCTaylorCenteredPoint sigma).im
  have heta : 0 < eta := by
    dsimp only [eta, xiCTaylorCenteredPoint]
    rw [mul_im]
    simp only [sub_re, neg_re, I_re, neg_im, I_im]
    norm_num
    linarith
  have himTend : Tendsto
      (fun n : ℕ => (xiCTaylorAnisotropicCenteredPoint sigma n).im)
      atTop (nhds eta) :=
    Complex.continuous_im.continuousAt.tendsto.comp
      (tendsto_xiCTaylorAnisotropicCenteredPoint sigma)
  have himLower : ∀ᶠ n : ℕ in atTop,
      eta / 2 < (xiCTaylorAnisotropicCenteredPoint sigma n).im :=
    himTend.eventually (eventually_gt_nhds (by linarith))
  have hx := tendsto_xiTaylorAnisotropicHorizontalStep sigma
  have hxNorm : Tendsto
      (fun n : ℕ => ‖xiTaylorAnisotropicHorizontalStep sigma n‖)
      atTop (nhds 0) := by
    simpa using hx.norm
  have hmajor : Tendsto
      (fun n : ℕ =>
        ‖xiTaylorAnisotropicHorizontalStep sigma n‖ * (4 / eta))
      atTop (nhds 0) := by
    simpa using hxNorm.mul_const (4 / eta)
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero' (Eventually.of_forall fun n => norm_nonneg _) ?_ hmajor
  filter_upwards [himLower, hg] with n him hgn
  have himPos : 0 < (xiCTaylorAnisotropicCenteredPoint sigma n).im :=
    (half_pos heta).trans him
  have hlog :=
    hgn.abs_im_derivative_div_value_le himPos
  have hcoefficient :
      2 / (xiCTaylorAnisotropicCenteredPoint sigma n).im ≤ 4 / eta := by
    calc
      2 / (xiCTaylorAnisotropicCenteredPoint sigma n).im ≤ 2 / (eta / 2) :=
        div_le_div_of_nonneg_left (by norm_num) (half_pos heta) him.le
      _ = 4 / eta := by field_simp; ring
  rw [Real.norm_eq_abs, abs_mul]
  calc
    |xiTaylorAnisotropicHorizontalStep sigma n| * |(D n / F n).im| ≤
        |xiTaylorAnisotropicHorizontalStep sigma n| *
          (2 / (xiCTaylorAnisotropicCenteredPoint sigma n).im) :=
      mul_le_mul_of_nonneg_left hlog (abs_nonneg _)
    _ ≤ |xiTaylorAnisotropicHorizontalStep sigma n| * (4 / eta) :=
      mul_le_mul_of_nonneg_left hcoefficient (abs_nonneg _)
    _ = ‖xiTaylorAnisotropicHorizontalStep sigma n‖ * (4 / eta) := by
      rw [Real.norm_eq_abs]

/-- Subtracting any arbitrary moving positive-completion gauge preserves the exact finite-Taylor
Xi divisor charge. -/
theorem xiCTaylor_movingPositiveTailCompletionGaugeTransferCharge_tendsto
    {N : ℕ → ℕ} (hN : XiCTaylorSuperaccurateSchedule N)
    {h : ℕ → ℝ → ℝ} {F D : ℕ → ℂ} {sigma : ℂ}
    (hsigma : sigma.re < 1 / 2)
    (hg : ∀ᶠ n : ℕ in atTop, PositiveTailCompletionGaugeAt
      (h n) (F n) (D n) (xiCTaylorAnisotropicCenteredPoint sigma n)) :
    Tendsto
      (fun n : ℕ =>
        xiTaylorAnisotropicHorizontalStep sigma n *
          ((logDeriv
              (xiCTaylorApprox
                (N (xiCTaylorAnisotropicScheduleStage sigma n)))
              (xiCTaylorAnisotropicCenteredPoint sigma n)).im -
            (D n / F n).im))
      atTop (nhds ((analyticOrderAt xi sigma).toNat : ℝ)) := by
  have hTaylor :=
    xiCTaylor_logDeriv_anisotropicHorizontalCharge_tendsto hN sigma
  have hGauge :=
    tendsto_movingPositiveTailCompletionGauge_horizontalCharge_zero hsigma hg
  convert hTaylor.sub hGauge using 1
  · funext n
    ring
  · ring

/-- Exact screening predicate for an index-dependent positive-completion gauge. -/
def XiCTaylorMovingPositiveTailCompletionGaugeChargeScreenedAt
    (N : ℕ → ℕ) (F D : ℕ → ℂ) (sigma : ℂ) : Prop :=
  Tendsto
    (fun n : ℕ =>
      xiTaylorAnisotropicHorizontalStep sigma n *
        ((logDeriv
            (xiCTaylorApprox
              (N (xiCTaylorAnisotropicScheduleStage sigma n)))
            (xiCTaylorAnisotropicCenteredPoint sigma n)).im -
          (D n / F n).im))
    atTop (nhds 0)

/-- **Sharp moving-gauge screening classification.**  An arbitrary moving positive completion
screens exactly at points which are not in the Xi divisor. -/
theorem xiCTaylor_movingPositiveTailCompletionGaugeChargeScreenedAt_iff_xi_ne_zero
    {N : ℕ → ℕ} (hN : XiCTaylorSuperaccurateSchedule N)
    {h : ℕ → ℝ → ℝ} {F D : ℕ → ℂ} {sigma : ℂ}
    (hsigma : sigma.re < 1 / 2)
    (hg : ∀ᶠ n : ℕ in atTop, PositiveTailCompletionGaugeAt
      (h n) (F n) (D n) (xiCTaylorAnisotropicCenteredPoint sigma n)) :
    XiCTaylorMovingPositiveTailCompletionGaugeChargeScreenedAt N F D sigma ↔
      xi sigma ≠ 0 := by
  have hlimit :=
    xiCTaylor_movingPositiveTailCompletionGaugeTransferCharge_tendsto
      hN hsigma hg
  constructor
  · intro hscreen
    have hzero : ((analyticOrderAt xi sigma).toNat : ℝ) = 0 :=
      tendsto_nhds_unique hlimit hscreen
    have hnat : (analyticOrderAt xi sigma).toNat = 0 := by
      exact_mod_cast hzero
    exact (xi_orderToNat_eq_zero_iff sigma).mp hnat
  · intro hxi
    have hnat : (analyticOrderAt xi sigma).toNat = 0 :=
      (xi_orderToNat_eq_zero_iff sigma).mpr hxi
    simpa only [
      XiCTaylorMovingPositiveTailCompletionGaugeChargeScreenedAt,
      hnat, Nat.cast_zero] using hlimit

/-- A literal nonempty recombined critical theta-tail packet is pointwise a positive-completion
gauge. -/
theorem criticalLogPhaseTailPacket_positiveTailCompletionGaugeAt
    {L : ℝ} (hL : 0 ≤ L) {N : ℕ} (hN : 0 < N)
    {z : ℂ} (hz : 0 < z.im) :
    PositiveTailCompletionGaugeAt
      (fun t : ℝ =>
        -criticalLogPhaseTranslatedDensityProfileDerivative L N t)
      (criticalLogPhaseTailPacketValue L N z)
      (criticalLogPhaseTailPacketDerivative L N z) z := by
  constructor
  · intro t ht
    exact neg_criticalLogPhaseTranslatedDensityProfileDerivative_nonneg
      hL N ht.le
  · exact integrableOn_neg_profileDerivative_mul_one_sub_phase hL N hz.le
  · exact integrableOn_neg_profileDerivative_mul_phaseDerivative hL N hz.le
  · rw [positiveTailCompletion_neg_profileDerivative_eq hL N hz.le]
    rw [← criticalLogPhase_tail_packet_eq_translatedProfile hL hz.le N]
    rfl
  · rw [positiveTailCompletionDerivative_neg_profileDerivative_eq hL N hz.le]
    rw [← criticalLogPhase_tail_packet_eq_translatedProfile hL hz.le N]
    rw [← criticalLogPhase_tail_packetDerivative_eq_translatedProfile hL hz.le N]
    rfl
  · exact criticalLogPhaseTailPacketValue_ne_zero hL hN hz

/-- Arbitrary nonnegative phase-lag and positive depth schedules eventually instantiate the moving
positive-completion interface on every left-half-strip anisotropic fibre. -/
theorem eventually_criticalLogPhaseTailPacket_positiveTailCompletionGaugeAt
    {L : ℕ → ℝ} {M : ℕ → ℕ} {sigma : ℂ}
    (hsigma : sigma.re < 1 / 2)
    (hL : ∀ n : ℕ, 0 ≤ L n) (hM : ∀ n : ℕ, 0 < M n) :
    ∀ᶠ n : ℕ in atTop,
      PositiveTailCompletionGaugeAt
        (fun t : ℝ =>
          -criticalLogPhaseTranslatedDensityProfileDerivative (L n) (M n) t)
        (criticalLogPhaseTailPacketValue (L n) (M n)
          (xiCTaylorAnisotropicCenteredPoint sigma n))
        (criticalLogPhaseTailPacketDerivative (L n) (M n)
          (xiCTaylorAnisotropicCenteredPoint sigma n))
        (xiCTaylorAnisotropicCenteredPoint sigma n) := by
  let eta : ℝ := (xiCTaylorCenteredPoint sigma).im
  have heta : 0 < eta := by
    dsimp only [eta, xiCTaylorCenteredPoint]
    rw [mul_im]
    simp only [sub_re, neg_re, I_re, neg_im, I_im]
    norm_num
    linarith
  have himTend : Tendsto
      (fun n : ℕ => (xiCTaylorAnisotropicCenteredPoint sigma n).im)
      atTop (nhds eta) :=
    Complex.continuous_im.continuousAt.tendsto.comp
      (tendsto_xiCTaylorAnisotropicCenteredPoint sigma)
  have him : ∀ᶠ n : ℕ in atTop,
      0 < (xiCTaylorAnisotropicCenteredPoint sigma n).im :=
    himTend.eventually (eventually_gt_nhds heta)
  filter_upwards [him] with n hzn
  exact criticalLogPhaseTailPacket_positiveTailCompletionGaugeAt
    (hL n) (hM n) hzn

/-- Literal source corollary: arbitrary simultaneous movement in theta phase lag and packet depth
still preserves the exact Xi multiplicity after transfer. -/
theorem xiCTaylor_movingCriticalLogPhaseTailPacketTransferCharge_tendsto
    {S : ℕ → ℕ} (hS : XiCTaylorSuperaccurateSchedule S)
    {L : ℕ → ℝ} {M : ℕ → ℕ} {sigma : ℂ}
    (hsigma : sigma.re < 1 / 2)
    (hL : ∀ n : ℕ, 0 ≤ L n) (hM : ∀ n : ℕ, 0 < M n) :
    Tendsto
      (fun n : ℕ =>
        xiTaylorAnisotropicHorizontalStep sigma n *
          ((logDeriv
              (xiCTaylorApprox
                (S (xiCTaylorAnisotropicScheduleStage sigma n)))
              (xiCTaylorAnisotropicCenteredPoint sigma n)).im -
            (criticalLogPhaseTailPacketDerivative (L n) (M n)
                (xiCTaylorAnisotropicCenteredPoint sigma n) /
              criticalLogPhaseTailPacketValue (L n) (M n)
                (xiCTaylorAnisotropicCenteredPoint sigma n)).im))
      atTop (nhds ((analyticOrderAt xi sigma).toNat : ℝ)) := by
  apply xiCTaylor_movingPositiveTailCompletionGaugeTransferCharge_tendsto
    hS hsigma
  exact eventually_criticalLogPhaseTailPacket_positiveTailCompletionGaugeAt
    hsigma hL hM

/-- Exact screening predicate for arbitrary moving literal critical theta-tail packets. -/
def XiCTaylorMovingCriticalLogPhaseTailPacketChargeScreenedAt
    (S : ℕ → ℕ) (L : ℕ → ℝ) (M : ℕ → ℕ) (sigma : ℂ) : Prop :=
  Tendsto
    (fun n : ℕ =>
      xiTaylorAnisotropicHorizontalStep sigma n *
        ((logDeriv
            (xiCTaylorApprox
              (S (xiCTaylorAnisotropicScheduleStage sigma n)))
            (xiCTaylorAnisotropicCenteredPoint sigma n)).im -
          (criticalLogPhaseTailPacketDerivative (L n) (M n)
              (xiCTaylorAnisotropicCenteredPoint sigma n) /
            criticalLogPhaseTailPacketValue (L n) (M n)
              (xiCTaylorAnisotropicCenteredPoint sigma n)).im))
    atTop (nhds 0)

/-- **Literal moving theta-packet no-go.**  Arbitrary positive depth and nonnegative phase-lag
schedules screen the finite Taylor charge exactly off, and only off, the Xi divisor. -/
theorem
    xiCTaylor_movingCriticalLogPhaseTailPacketChargeScreenedAt_iff_xi_ne_zero
    {S : ℕ → ℕ} (hS : XiCTaylorSuperaccurateSchedule S)
    {L : ℕ → ℝ} {M : ℕ → ℕ} {sigma : ℂ}
    (hsigma : sigma.re < 1 / 2)
    (hL : ∀ n : ℕ, 0 ≤ L n) (hM : ∀ n : ℕ, 0 < M n) :
    XiCTaylorMovingCriticalLogPhaseTailPacketChargeScreenedAt
      S L M sigma ↔ xi sigma ≠ 0 := by
  have hg :=
    eventually_criticalLogPhaseTailPacket_positiveTailCompletionGaugeAt
      hsigma hL hM
  simpa only [
    XiCTaylorMovingCriticalLogPhaseTailPacketChargeScreenedAt,
    XiCTaylorMovingPositiveTailCompletionGaugeChargeScreenedAt]
    using
      xiCTaylor_movingPositiveTailCompletionGaugeChargeScreenedAt_iff_xi_ne_zero
        hS hsigma hg

end

end RHTower
