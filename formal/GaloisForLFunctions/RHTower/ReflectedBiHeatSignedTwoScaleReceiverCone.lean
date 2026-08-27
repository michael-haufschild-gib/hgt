import GaloisForLFunctions.RHTower.ReflectedBiHeatPositiveMatrixApertureClassification

/-!
# Reflected bi-heat signed two-scale receiver cone

The positive-matrix aperture theorem does not classify indefinite receivers.  For commensurate
aperture rates, the first signed problem reduces exactly to

`a sinh(t) + b sinh(2t) = sinh(t) (a + 2 b cosh(t))`.

This file classifies the complete coefficient cone for which the wall `t = 0` is the only real
zero, proves the exact physical two-aperture leading-jet factorization, and obtains a genuinely
signed RH receiver with coefficients `(-2, 1)`.

`[NEW] [SIGNED RECEIVER CONE] [EXACT CLASSIFICATION] [PAPER-PROVED] [LEAN-PROVED]`
-/

open Complex Filter Topology

namespace RHTower

noncomputable section

/-- Signed two-scale RBH reporter at normalized wall displacement `t`. -/
def reflectedBiHeatSignedTwoScaleReporter (a b t : ℝ) : ℝ :=
  a * Real.sinh t + b * Real.sinh (2 * t)

/-- The two-scale reporter factors into its forced wall zero and one affine `cosh` factor. -/
theorem reflectedBiHeatSignedTwoScaleReporter_factor (a b t : ℝ) :
    reflectedBiHeatSignedTwoScaleReporter a b t =
      Real.sinh t * (a + 2 * b * Real.cosh t) := by
  rw [reflectedBiHeatSignedTwoScaleReporter, Real.sinh_two_mul]
  ring

/-- Exact coefficient cone for which the two-scale reporter vanishes only at the wall. -/
def ReflectedBiHeatSignedTwoScaleWallSelective (a b : ℝ) : Prop :=
  (b = 0 ∧ a ≠ 0) ∨ (b ≠ 0 ∧ 0 ≤ b * (a + 2 * b))

/-- Complete signed two-scale classification, including construction of an off-wall zero outside
the cone by `arcosh (-a/(2b))`. -/
theorem reflectedBiHeatSignedTwoScaleWallSelective_iff
    (a b : ℝ) :
    ReflectedBiHeatSignedTwoScaleWallSelective a b ↔
      ∀ t : ℝ, reflectedBiHeatSignedTwoScaleReporter a b t = 0 ↔ t = 0 := by
  constructor
  · intro hcone t
    rw [reflectedBiHeatSignedTwoScaleReporter_factor]
    constructor
    · intro hzero
      rcases hcone with ⟨hb, ha⟩ | ⟨hb, hbd⟩
      · rw [hb] at hzero
        simp only [mul_zero, zero_mul, add_zero] at hzero
        exact Real.sinh_eq_zero.mp ((mul_eq_zero.mp hzero).resolve_right ha)
      · by_contra ht
        have hcosh : 1 < Real.cosh t := Real.one_lt_cosh.mpr ht
        have hb2 : 0 < b ^ 2 := sq_pos_of_ne_zero hb
        have hfac : 0 < b * (a + 2 * b * Real.cosh t) := by
          nlinarith
        rcases mul_eq_zero.mp hzero with hsinh | hsecond
        · exact ht (Real.sinh_eq_zero.mp hsinh)
        · exact hfac.ne' (mul_eq_zero.mpr (Or.inr hsecond))
    · rintro rfl
      simp
  · intro hselect
    by_cases hb : b = 0
    · left
      refine ⟨hb, ?_⟩
      intro ha
      have hzero : reflectedBiHeatSignedTwoScaleReporter a b 1 = 0 := by
        simp [reflectedBiHeatSignedTwoScaleReporter, ha, hb]
      have : (1 : ℝ) = 0 := (hselect 1).mp hzero
      norm_num at this
    · right
      refine ⟨hb, ?_⟩
      by_contra hnonneg
      have hneg : b * (a + 2 * b) < 0 := lt_of_not_ge hnonneg
      let c : ℝ := -a / (2 * b)
      have hc : 1 < c := by
        rcases lt_or_gt_of_ne hb with hbneg | hbpos
        · rw [show c = -a / (2 * b) by rfl]
          rw [lt_div_iff_of_neg (by linarith : 2 * b < 0)]
          nlinarith
        · rw [show c = -a / (2 * b) by rfl]
          rw [lt_div_iff₀ (by linarith : 0 < 2 * b)]
          nlinarith
      let t := Real.arcosh c
      have htpos : 0 < t := Real.arcosh_pos hc
      have hcosh : Real.cosh t = c := Real.cosh_arcosh hc.le
      have hfactor : a + 2 * b * Real.cosh t = 0 := by
        rw [hcosh]
        dsimp [c]
        field_simp
        ring
      have hzero : reflectedBiHeatSignedTwoScaleReporter a b t = 0 := by
        rw [reflectedBiHeatSignedTwoScaleReporter_factor, hfactor, mul_zero]
      exact htpos.ne' ((hselect t).mp hzero)

/-- Physical two-aperture diagonal gap, normalized only by fixed positive aperture weights. -/
def reflectedBiHeatSignedTwoApertureGap
    (a b x : ℝ) (rho : XiDivisorSupport) : ℝ :=
  a * x ^ (1 / 2 : ℝ) *
      (reflectedBiHeatLeftLeadingJetNorm rho x ^ 2 -
        reflectedBiHeatRightLeadingJetNorm rho x ^ 2) +
    b * x *
      (reflectedBiHeatLeftLeadingJetNorm rho (x ^ 2) ^ 2 -
        reflectedBiHeatRightLeadingJetNorm rho (x ^ 2) ^ 2)

/-- Exact reduction of the physical gaps at apertures `x` and `x²` to the two-scale reporter. -/
theorem reflectedBiHeatSignedTwoApertureGap_eq_reporter
    (a b : ℝ) {x : ℝ} (hx : 0 < x) (rho : XiDivisorSupport) :
    reflectedBiHeatSignedTwoApertureGap a b x rho =
      2 * ‖reflectedBiHeatMultiplicityLeadingCoefficient rho‖ ^ 2 *
        reflectedBiHeatSignedTwoScaleReporter a b
          (Real.log x * ((rho : ℂ).re - 1 / 2)) := by
  rw [reflectedBiHeatSignedTwoApertureGap,
    reflectedBiHeatLeftLeadingJetNorm_eq rho hx,
    reflectedBiHeatRightLeadingJetNorm_eq rho hx,
    reflectedBiHeatLeftLeadingJetNorm_eq rho (sq_pos_of_pos hx),
    reflectedBiHeatRightLeadingJetNorm_eq rho (sq_pos_of_pos hx)]
  simp only [reflectedBiHeatLeftScaleOrder, reflectedBiHeatRightScaleOrder,
    reflectedBiHeatSignedTwoScaleReporter]
  rw [Real.rpow_def_of_pos hx, Real.rpow_def_of_pos hx,
    Real.rpow_def_of_pos hx,
    Real.rpow_def_of_pos (sq_pos_of_pos hx),
    Real.rpow_def_of_pos (sq_pos_of_pos hx),
    Real.log_pow, Real.sinh_eq, Real.sinh_eq]
  let r : ℝ := (rho : ℂ).re
  let L : ℝ := Real.log x
  have h1 : Real.exp (L * (1 / 2)) *
      Real.exp (L * ((r - 1) / 2)) ^ 2 =
      Real.exp (L * (r - 1 / 2)) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    norm_num
    ring
  have h2 : Real.exp (L * (1 / 2)) *
      Real.exp (L * (-r / 2)) ^ 2 =
      Real.exp (-(L * (r - 1 / 2))) := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    norm_num
    ring
  have h3 : x * Real.exp ((2 * L) * ((r - 1) / 2)) ^ 2 =
      Real.exp (2 * (L * (r - 1 / 2))) := by
    rw [← Real.exp_log hx, ← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    norm_num
    ring
  have h4 : x * Real.exp ((2 * L) * (-r / 2)) ^ 2 =
      Real.exp (-(2 * (L * (r - 1 / 2)))) := by
    rw [← Real.exp_log hx, ← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    norm_num
    ring
  change
    a * Real.exp (L * (1 / 2)) *
          ((‖reflectedBiHeatMultiplicityLeadingCoefficient rho‖ *
              Real.exp (L * ((r - 1) / 2))) ^ 2 -
            (‖reflectedBiHeatMultiplicityLeadingCoefficient rho‖ *
              Real.exp (L * (-r / 2))) ^ 2) +
        b * x *
          ((‖reflectedBiHeatMultiplicityLeadingCoefficient rho‖ *
              Real.exp ((2 * L) * ((r - 1) / 2))) ^ 2 -
            (‖reflectedBiHeatMultiplicityLeadingCoefficient rho‖ *
              Real.exp ((2 * L) * (-r / 2))) ^ 2) = _
  simp only [mul_pow]
  change
    a * Real.exp (L * (1 / 2)) *
          (‖reflectedBiHeatMultiplicityLeadingCoefficient rho‖ ^ 2 *
              Real.exp (L * ((r - 1) / 2)) ^ 2 -
            ‖reflectedBiHeatMultiplicityLeadingCoefficient rho‖ ^ 2 *
              Real.exp (L * (-r / 2)) ^ 2) +
        b * x *
          (‖reflectedBiHeatMultiplicityLeadingCoefficient rho‖ ^ 2 *
              Real.exp ((2 * L) * ((r - 1) / 2)) ^ 2 -
            ‖reflectedBiHeatMultiplicityLeadingCoefficient rho‖ ^ 2 *
              Real.exp ((2 * L) * (-r / 2)) ^ 2) =
      2 * ‖reflectedBiHeatMultiplicityLeadingCoefficient rho‖ ^ 2 *
        (a * ((Real.exp (L * (r - 1 / 2)) -
            Real.exp (-(L * (r - 1 / 2)))) / 2) +
          b * ((Real.exp (2 * (L * (r - 1 / 2))) -
            Real.exp (-(2 * (L * (r - 1 / 2))))) / 2))
  linear_combination
    a * ‖reflectedBiHeatMultiplicityLeadingCoefficient rho‖ ^ 2 * h1 -
    a * ‖reflectedBiHeatMultiplicityLeadingCoefficient rho‖ ^ 2 * h2 +
    b * ‖reflectedBiHeatMultiplicityLeadingCoefficient rho‖ ^ 2 * h3 -
    b * ‖reflectedBiHeatMultiplicityLeadingCoefficient rho‖ ^ 2 * h4

/-- Under the exact signed coefficient cone, physical two-aperture balance occurs only on wall. -/
theorem reflectedBiHeatSignedTwoApertureGap_eq_zero_iff
    {a b : ℝ} (hcone : ReflectedBiHeatSignedTwoScaleWallSelective a b)
    {x : ℝ} (hx : 1 < x) (rho : XiDivisorSupport) :
    reflectedBiHeatSignedTwoApertureGap a b x rho = 0 ↔
      (rho : ℂ).re = 1 / 2 := by
  rw [reflectedBiHeatSignedTwoApertureGap_eq_reporter a b
    (lt_trans zero_lt_one hx) rho]
  have hcoef :
      2 * ‖reflectedBiHeatMultiplicityLeadingCoefficient rho‖ ^ 2 ≠ 0 := by
    exact mul_ne_zero (by norm_num)
      (pow_ne_zero 2 (norm_ne_zero_iff.mpr
        (reflectedBiHeatMultiplicityLeadingCoefficient_ne_zero rho)))
  constructor
  · intro hzero
    have hreport : reflectedBiHeatSignedTwoScaleReporter a b
        (Real.log x * ((rho : ℂ).re - 1 / 2)) = 0 :=
      (mul_eq_zero.mp hzero).resolve_left hcoef
    have hu :=
      ((reflectedBiHeatSignedTwoScaleWallSelective_iff a b).mp hcone
        (Real.log x * ((rho : ℂ).re - 1 / 2))).mp hreport
    have hlog : 0 < Real.log x := Real.log_pos hx
    have hsub : (rho : ℂ).re - 1 / 2 = 0 :=
      (mul_eq_zero.mp hu).resolve_left hlog.ne'
    exact sub_eq_zero.mp hsub
  · intro hre
    rw [hre, sub_self, mul_zero]
    simp [reflectedBiHeatSignedTwoScaleReporter]

/-- Every coefficient pair in the exact cone supplies a signed two-aperture RH receiver. -/
theorem riemannHypothesis_iff_reflectedBiHeatSignedTwoApertureGap_eq_zero
    {a b : ℝ} (hcone : ReflectedBiHeatSignedTwoScaleWallSelective a b)
    {x : ℝ} (hx : 1 < x) :
    RiemannHypothesis ↔
      ∀ rho : XiDivisorSupport,
        reflectedBiHeatSignedTwoApertureGap a b x rho = 0 := by
  constructor
  · intro hRH rho
    exact (reflectedBiHeatSignedTwoApertureGap_eq_zero_iff hcone hx rho).mpr
      (xi_divisor_support_re_eq_half_of_rh hRH rho)
  · intro h
    exact riemannHypothesis_of_forall_xiDivisorSupport_re_eq_half fun rho =>
      (reflectedBiHeatSignedTwoApertureGap_eq_zero_iff hcone hx rho).mp (h rho)

/-- The first genuinely signed boundary receiver: `sinh(2t) - 2 sinh(t)`. -/
theorem reflectedBiHeatSignedTwoScaleWallSelective_neg_two_one :
    ReflectedBiHeatSignedTwoScaleWallSelective (-2) 1 := by
  right
  norm_num [ReflectedBiHeatSignedTwoScaleWallSelective]

/-- A negative first-aperture weight and positive second-aperture weight still give an exact RH
receiver, despite lying outside the entrywise-nonnegative matrix cone. -/
theorem riemannHypothesis_iff_reflectedBiHeatSignedNegTwoOneApertureGap_eq_zero
    {x : ℝ} (hx : 1 < x) :
    RiemannHypothesis ↔
      ∀ rho : XiDivisorSupport,
        reflectedBiHeatSignedTwoApertureGap (-2) 1 x rho = 0 :=
  riemannHypothesis_iff_reflectedBiHeatSignedTwoApertureGap_eq_zero
    reflectedBiHeatSignedTwoScaleWallSelective_neg_two_one hx

end

end RHTower
