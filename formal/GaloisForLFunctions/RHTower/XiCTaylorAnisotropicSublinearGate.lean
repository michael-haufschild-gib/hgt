import GaloisForLFunctions.RHTower.XiCTaylorAnisotropicLocalBounds
import GaloisForLFunctions.RHTower.LogDerivQuotientPerturbation
import GaloisForLFunctions.RHTower.XiAnisotropicSublinearGate
import GaloisForLFunctions.RHTower.XiRelativeResolventFlux

/-!
# Finite Xi Taylor logarithmic derivatives on the anisotropic mesh

A super-accurate Taylor schedule converges rapidly enough, relative to every finite local order of
`XiC`, that its logarithmic derivatives follow the Xi logarithmic derivative even along a mesh
fibre approaching a hypothetical zero.  Hence sublinear upper flux for the finite Taylor
polynomials on every left-strip fibre excludes every off-line Xi zero.

This is the finite-to-limit gate.  It does not prove the finite coefficient upper bound.
-/

open Complex Metric Filter Topology

namespace RHTower

noncomputable section

/-- At every Xi zero, a super-accurate finite Taylor schedule tracks the logarithmic derivative of
`XiC` along the moving anisotropic mesh. -/
theorem tendsto_norm_xiCTaylor_logDeriv_sub_XiC_at_anisotropic
    {N : ℕ → ℕ} (hN : XiCTaylorSuperaccurateSchedule N)
    (sigma : ℂ) :
    Tendsto
      (fun n : ℕ =>
        ‖logDeriv
              (xiCTaylorApprox (N (xiCTaylorAnisotropicScheduleStage sigma n)))
              (xiCTaylorAnisotropicCenteredPoint sigma n) -
            logDeriv XiC (xiCTaylorAnisotropicCenteredPoint sigma n)‖)
      atTop (nhds 0) := by
  let m : ℕ := (analyticOrderAt xi sigma).toNat
  obtain ⟨c, hc, hvalueLower⟩ := eventually_xiC_anisotropic_value_lower sigma
  obtain ⟨C, hC, hderivUpper⟩ := eventually_xiC_anisotropic_deriv_upper sigma
  have htolM := tendsto_xiCTaylorScheduleTolerance_stage_mul_pow sigma m
  have htolTwoM := tendsto_xiCTaylorScheduleTolerance_stage_mul_pow sigma (2 * m)
  have hsmall : ∀ᶠ n : ℕ in atTop,
      xiCTaylorScheduleTolerance (xiCTaylorAnisotropicScheduleStage sigma n) *
          (((n + 1 : ℕ) : ℝ) ^ m) < c / 2 :=
    htolM.eventually (eventually_lt_nhds (half_pos hc))
  let bound : ℕ → ℝ := fun n =>
    (2 / c) *
        (xiCTaylorScheduleTolerance (xiCTaylorAnisotropicScheduleStage sigma n) *
          (((n + 1 : ℕ) : ℝ) ^ m)) +
      (2 * C / (c * c)) *
        (xiCTaylorScheduleTolerance (xiCTaylorAnisotropicScheduleStage sigma n) *
          (((n + 1 : ℕ) : ℝ) ^ (2 * m)))
  have hboundTend : Tendsto bound atTop (nhds 0) := by
    have h₁ := htolM.const_mul (2 / c)
    have h₂ := htolTwoM.const_mul (2 * C / (c * c))
    simpa only [bound, mul_zero, zero_add] using h₁.add h₂
  apply squeeze_zero' (Eventually.of_forall fun n => norm_nonneg _)
    ?_ hboundTend
  filter_upwards [hvalueLower, hderivUpper, hsmall] with n hnValue hnDeriv hnSmall
  let z : ℂ := xiCTaylorAnisotropicCenteredPoint sigma n
  let k : ℕ := xiCTaylorAnisotropicScheduleStage sigma n
  let P : ℂ → ℂ := xiCTaylorApprox (N k)
  let q : ℝ := ((n + 1 : ℕ) : ℝ)
  have hq : 0 < q := by dsimp [q]; positivity
  have hqpow : 0 < q ^ m := pow_pos hq _
  have happ := xiCTaylorSuperaccurateSchedule_at_anisotropicCenteredPoint hN sigma n
  have hvalueErr : ‖P z - XiC z‖ < xiCTaylorScheduleTolerance k := by
    simpa only [P, z, k, dist_eq_norm, norm_sub_rev] using happ.1
  have hderivErr : ‖deriv P z - deriv XiC z‖ < xiCTaylorScheduleTolerance k := by
    simpa only [P, z, k, dist_eq_norm, norm_sub_rev] using happ.2
  have hnValue' : c / (q ^ m) ≤ ‖XiC z‖ := by
    simpa only [z, q, one_div_pow, mul_one_div, m] using hnValue
  have hXiC : XiC z ≠ 0 := by
    exact norm_pos_iff.mp (lt_of_lt_of_le (div_pos hc hqpow) hnValue')
  have htwoClose : 2 * ‖P z - XiC z‖ ≤ ‖XiC z‖ := by
    apply le_trans ?_ hnValue'
    rw [le_div_iff₀ hqpow]
    have hmul := mul_lt_mul_of_pos_right hvalueErr hqpow
    have hnSmall' : xiCTaylorScheduleTolerance k * q ^ m < c / 2 := by
      simpa only [k, q] using hnSmall
    nlinarith
  have hquot := norm_logDeriv_sub_logDeriv_le_of_two_norm_sub_le hXiC htwoClose
  have hinv : 1 / ‖XiC z‖ ≤ q ^ m / c := by
    calc
      1 / ‖XiC z‖ ≤ 1 / (c / q ^ m) :=
        one_div_le_one_div_of_le (div_pos hc hqpow) hnValue'
      _ = q ^ m / c := by field_simp
  have htwoInv : 2 / ‖XiC z‖ ≤ (2 / c) * q ^ m := by
    calc
      2 / ‖XiC z‖ = 2 * (1 / ‖XiC z‖) := by ring
      _ ≤ 2 * (q ^ m / c) := mul_le_mul_of_nonneg_left hinv (by positivity)
      _ = (2 / c) * q ^ m := by ring
  have htermOne :
      ‖deriv P z - deriv XiC z‖ * (2 / ‖XiC z‖) ≤
        xiCTaylorScheduleTolerance k * ((2 / c) * q ^ m) :=
    mul_le_mul hderivErr.le htwoInv (by positivity)
      (xiCTaylorScheduleTolerance_pos k).le
  have hderivValue :
      ‖deriv XiC z‖ * ‖P z - XiC z‖ ≤
        C * xiCTaylorScheduleTolerance k :=
    mul_le_mul hnDeriv hvalueErr.le (norm_nonneg _) hC.le
  have hderivValueTwo :
      ‖deriv XiC z‖ * ‖P z - XiC z‖ * (2 / ‖XiC z‖) ≤
        C * xiCTaylorScheduleTolerance k * ((2 / c) * q ^ m) :=
    mul_le_mul hderivValue htwoInv
      (div_nonneg (by norm_num) (norm_nonneg _))
      (mul_nonneg hC.le (xiCTaylorScheduleTolerance_pos k).le)
  have htermTwo :
      ‖deriv XiC z‖ * ‖P z - XiC z‖ * (2 / ‖XiC z‖) *
          (1 / ‖XiC z‖) ≤
        C * xiCTaylorScheduleTolerance k * ((2 / c) * q ^ m) *
          (q ^ m / c) :=
    mul_le_mul hderivValueTwo hinv
      (div_nonneg (by norm_num) (norm_nonneg _))
      (mul_nonneg
        (mul_nonneg hC.le (xiCTaylorScheduleTolerance_pos k).le)
        (mul_nonneg (div_nonneg (by norm_num) hc.le) (pow_nonneg hq.le _)))
  calc
    ‖logDeriv P z - logDeriv XiC z‖ ≤
        ‖deriv P z - deriv XiC z‖ * (2 / ‖XiC z‖) +
          ‖deriv XiC z‖ * ‖P z - XiC z‖ * (2 / ‖XiC z‖) *
            (1 / ‖XiC z‖) := hquot.2
    _ ≤ xiCTaylorScheduleTolerance k * ((2 / c) * q ^ m) +
          C * xiCTaylorScheduleTolerance k * ((2 / c) * q ^ m) *
            (q ^ m / c) := by
      exact add_le_add htermOne htermTwo
    _ = bound n := by
      dsimp [bound, k, q]
      rw [show 2 * m = m + m by omega, pow_add]
      ring

/-- Finite-polynomial source condition: on every anisotropic mesh fibre based in the open left
critical strip, a super-accurate canonical Xi Taylor schedule has sublinear upper flux. -/
def XiCTaylorAnisotropicLogDerivSublinearUpper (N : ℕ → ℕ) : Prop :=
  ∀ sigma : ℂ, 0 < sigma.re → sigma.re < 1 / 2 →
    ∀ epsilon : ℝ, 0 < epsilon →
      ∀ᶠ n : ℕ in atTop,
        (logDeriv
            (xiCTaylorApprox (N (xiCTaylorAnisotropicScheduleStage sigma n)))
            (xiCTaylorAnisotropicCenteredPoint sigma n)).im /
          ((n + 1 : ℕ) : ℝ) < epsilon

/-- At an Xi zero, the finite Taylor logarithmic derivative retains a positive normalized upper
flux along the anisotropic mesh. -/
theorem eventually_xiOrder_div_twenty_lt_xiCTaylor_logDeriv_anisotropicMesh_im_div
    {N : ℕ → ℕ} (hN : XiCTaylorSuperaccurateSchedule N)
    {sigma : ℂ} (hzero : xi sigma = 0) :
    ∀ᶠ n : ℕ in atTop,
      (((analyticOrderAt xi sigma).toNat : ℝ) / 20) <
        (logDeriv
            (xiCTaylorApprox (N (xiCTaylorAnisotropicScheduleStage sigma n)))
            (xiCTaylorAnisotropicCenteredPoint sigma n)).im /
          ((n + 1 : ℕ) : ℝ) := by
  let m : ℕ := (analyticOrderAt xi sigma).toNat
  have hm : 0 < m := Nat.pos_of_ne_zero (xi_order_toNat_ne_zero hzero)
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have htrack := tendsto_norm_xiCTaylor_logDeriv_sub_XiC_at_anisotropic hN sigma
  have htrackSmall : ∀ᶠ n : ℕ in atTop,
      ‖logDeriv
            (xiCTaylorApprox (N (xiCTaylorAnisotropicScheduleStage sigma n)))
            (xiCTaylorAnisotropicCenteredPoint sigma n) -
          logDeriv XiC (xiCTaylorAnisotropicCenteredPoint sigma n)‖ <
        (m : ℝ) / 20 :=
    htrack.eventually (eventually_lt_nhds (div_pos hmR (by norm_num)))
  have hlower := eventually_xiOrder_div_ten_lt_logDeriv_anisotropicMesh_re_div hzero
  filter_upwards [htrackSmall, hlower] with n hnTrack hnLower
  let s : ℂ := xiTaylorAnisotropicRightApprox sigma (n + 1)
  let z : ℂ := xiCTaylorAnisotropicCenteredPoint sigma n
  let Lp : ℂ := logDeriv
    (xiCTaylorApprox (N (xiCTaylorAnisotropicScheduleStage sigma n))) z
  let L : ℂ := logDeriv XiC z
  have hcoord : 1 / 2 + z * I = s := by
    simp only [z, xiCTaylorAnisotropicCenteredPoint, s,
      half_add_xiCTaylorCenteredPoint_mul_I]
  have hLim : L.im = (logDeriv xi s).re := by
    change (logDeriv XiC z).im = (logDeriv xi s).re
    rw [RHTower.logDeriv_XiC_eq_mul_I_logDeriv_xi, hcoord]
    simp
  have himDiff : |(Lp - L).im| < (m : ℝ) / 20 :=
    (Complex.abs_im_le_norm (Lp - L)).trans_lt (by simpa only [Lp, L] using hnTrack)
  have hNpos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  have hNge : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  change (m : ℝ) / 20 < Lp.im / ((n + 1 : ℕ) : ℝ)
  change (m : ℝ) / 10 < (logDeriv xi s).re / ((n + 1 : ℕ) : ℝ) at hnLower
  rw [sub_im, hLim, abs_lt] at himDiff
  rw [lt_div_iff₀ hNpos] at hnLower ⊢
  nlinarith

/-- A super-accurate canonical Xi Taylor schedule with sublinear anisotropic upper flux proves RH. -/
theorem riemannHypothesis_of_xiCTaylorAnisotropicLogDerivSublinearUpper
    {N : ℕ → ℕ} (hN : XiCTaylorSuperaccurateSchedule N)
    (hsub : XiCTaylorAnisotropicLogDerivSublinearUpper N) :
    RiemannHypothesis := by
  rw [rh_iff_xi_ne_zero_right]
  intro rho hrho hzero
  have hrhoHalf : 1 / 2 < rho.re := mem_rightHalf.mp hrho
  have hrhoPos : 0 < rho.re := lt_trans (by norm_num) hrhoHalf
  have hrhoOne : rho.re < 1 := xi_zero_re_lt_one hzero
  let sigma : ℂ := 1 - rho
  have hsigmaZero : xi sigma = 0 := by
    dsimp only [sigma]
    rw [xi_one_sub, hzero]
  have hsigmaPos : 0 < sigma.re := by
    dsimp only [sigma]
    simp only [sub_re, one_re]
    linarith
  have hsigmaHalf : sigma.re < 1 / 2 := by
    dsimp only [sigma]
    simp only [sub_re, one_re]
    linarith
  let m : ℕ := (analyticOrderAt xi sigma).toNat
  have hm : 0 < m := Nat.pos_of_ne_zero (xi_order_toNat_ne_zero hsigmaZero)
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hlower :=
    eventually_xiOrder_div_twenty_lt_xiCTaylor_logDeriv_anisotropicMesh_im_div
      hN hsigmaZero
  have hupper := hsub sigma hsigmaPos hsigmaHalf ((m : ℝ) / 40)
    (div_pos hmR (by norm_num))
  obtain ⟨n, hnLower, hnUpper⟩ := (hlower.and hupper).exists
  change (m : ℝ) / 20 <
      (logDeriv
          (xiCTaylorApprox (N (xiCTaylorAnisotropicScheduleStage sigma n)))
          (xiCTaylorAnisotropicCenteredPoint sigma n)).im /
        ((n + 1 : ℕ) : ℝ) at hnLower
  linarith

/-- Under RH, every open-left-strip mesh fibre converges to an Xi-regular point.  A superaccurate
finite Taylor schedule tracks the Xi logarithmic derivative on that moving fibre, so it inherits
the sublinear upper bound. -/
theorem xiCTaylorAnisotropicLogDerivSublinearUpper_of_riemannHypothesis
    {N : ℕ → ℕ} (hN : XiCTaylorSuperaccurateSchedule N)
    (hRH : RiemannHypothesis) :
    XiCTaylorAnisotropicLogDerivSublinearUpper N := by
  intro sigma hsigmaPos hsigmaHalf epsilon hepsilon
  have htrack := tendsto_norm_xiCTaylor_logDeriv_sub_XiC_at_anisotropic hN sigma
  have htrackSmall : ∀ᶠ n : ℕ in atTop,
      ‖logDeriv
            (xiCTaylorApprox (N (xiCTaylorAnisotropicScheduleStage sigma n)))
            (xiCTaylorAnisotropicCenteredPoint sigma n) -
          logDeriv XiC (xiCTaylorAnisotropicCenteredPoint sigma n)‖ < epsilon / 2 :=
    htrack.eventually (eventually_lt_nhds (half_pos hepsilon))
  have hinfinite :=
    xiAnisotropicLogDerivSublinearUpper_of_riemannHypothesis hRH
      sigma hsigmaPos hsigmaHalf (epsilon / 2) (half_pos hepsilon)
  filter_upwards [htrackSmall, hinfinite] with n hnTrack hnInfinite
  let s : ℂ := xiTaylorAnisotropicRightApprox sigma (n + 1)
  let z : ℂ := xiCTaylorAnisotropicCenteredPoint sigma n
  let Lp : ℂ := logDeriv
    (xiCTaylorApprox (N (xiCTaylorAnisotropicScheduleStage sigma n))) z
  let L : ℂ := logDeriv XiC z
  have hcoord : 1 / 2 + z * I = s := by
    simp only [z, xiCTaylorAnisotropicCenteredPoint, s,
      half_add_xiCTaylorCenteredPoint_mul_I]
  have hLim : L.im = (logDeriv xi s).re := by
    change (logDeriv XiC z).im = (logDeriv xi s).re
    rw [RHTower.logDeriv_XiC_eq_mul_I_logDeriv_xi, hcoord]
    simp
  have himDiff : |(Lp - L).im| < epsilon / 2 :=
    (Complex.abs_im_le_norm (Lp - L)).trans_lt
      (by simpa only [Lp, L, z] using hnTrack)
  have hqPos : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  have hqOne : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  change Lp.im / ((n + 1 : ℕ) : ℝ) < epsilon
  change (logDeriv xi s).re / ((n + 1 : ℕ) : ℝ) < epsilon / 2 at hnInfinite
  rw [sub_im, hLim, abs_lt] at himDiff
  rw [div_lt_iff₀ hqPos] at hnInfinite ⊢
  nlinarith

/-- **Exact finite Xi-Taylor anisotropic criterion for every superaccurate schedule.** -/
theorem xiCTaylorAnisotropicLogDerivSublinearUpper_iff_riemannHypothesis
    {N : ℕ → ℕ} (hN : XiCTaylorSuperaccurateSchedule N) :
    XiCTaylorAnisotropicLogDerivSublinearUpper N ↔ RiemannHypothesis :=
  ⟨riemannHypothesis_of_xiCTaylorAnisotropicLogDerivSublinearUpper hN,
    xiCTaylorAnisotropicLogDerivSublinearUpper_of_riemannHypothesis hN⟩

/-- Existence of one superaccurate Taylor schedule with sublinear logarithmic-derivative current
is exactly RH; the schedule is supplied by the unconditional diagonal construction. -/
theorem exists_xiCTaylorAnisotropicLogDerivSublinearUpper_iff_riemannHypothesis :
    (∃ N : ℕ → ℕ, XiCTaylorSuperaccurateSchedule N ∧
      XiCTaylorAnisotropicLogDerivSublinearUpper N) ↔ RiemannHypothesis := by
  constructor
  · rintro ⟨N, hN, hlogDeriv⟩
    exact (xiCTaylorAnisotropicLogDerivSublinearUpper_iff_riemannHypothesis hN).1 hlogDeriv
  · intro hRH
    obtain ⟨N, hN⟩ := exists_xiCTaylorSuperaccurateSchedule
    exact ⟨N, hN,
      (xiCTaylorAnisotropicLogDerivSublinearUpper_iff_riemannHypothesis hN).2 hRH⟩

/-- Sublinear finite Taylor logarithmic-derivative current on every superaccurate schedule is
exactly RH. -/
theorem forall_xiCTaylorAnisotropicLogDerivSublinearUpper_iff_riemannHypothesis :
    (∀ N : ℕ → ℕ, XiCTaylorSuperaccurateSchedule N →
      XiCTaylorAnisotropicLogDerivSublinearUpper N) ↔ RiemannHypothesis := by
  constructor
  · intro hall
    obtain ⟨N, hN⟩ := exists_xiCTaylorSuperaccurateSchedule
    exact
      (xiCTaylorAnisotropicLogDerivSublinearUpper_iff_riemannHypothesis hN).1
        (hall N hN)
  · intro hRH N hN
    exact (xiCTaylorAnisotropicLogDerivSublinearUpper_iff_riemannHypothesis hN).2 hRH

end

end RHTower
