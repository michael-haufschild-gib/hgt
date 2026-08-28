import GaloisForLFunctions.RHTower.Sieve.MaynardFixedAmbientPacketNatOrder
import GaloisForLFunctions.RHTower.Sieve.InghamUniformDetectorMellinEveryBaseThetaMass
import GaloisForLFunctions.RHTower.Sieve.MaynardHandoffPrimeFreePhysicalDefect
import GaloisForLFunctions.RHTower.Sieve.MaynardDyadicBlockPerron
import GaloisForLFunctions.RHTower.Sieve.MaynardPrimeFreeRangePacketCanonicalCutoff

open Complex MeasureTheory Set
open Filter ArithmeticFunction

namespace RHTower.Sieve

noncomputable section

/-!
# Maynard common central mode

Two normalized physical widths have the same point-mass Mellin character on a common central
ordinate band.  Splitting each one-width integral into that common mode, its central width error,
and its complementary high tail cancels the common mode without a width ladder.  A large endpoint
defect therefore forces one of only two high tails once the two central errors are small.
-/

/-- Width-independent point-mass contribution on the symmetric central ordinate band. -/
def maynardCommonCentralMode
    (a : ℝ → ℂ) (N U : ℝ) : ℂ :=
  ∫ y in (-U)..U,
    a y * (N : ℂ) ^ (((1 : ℂ) + (y : ℝ) * Complex.I) - 1)

/-- Central error made by replacing one normalized window kernel by its point-mass character. -/
def maynardCentralWidthError
    (a : ℝ → ℂ) (N W U : ℝ) : ℂ :=
  ∫ y in (-U)..U,
    a y *
      (routeTNormalizedSmoothWindowMellin N W
          ((1 : ℂ) + (y : ℝ) * Complex.I) -
        (N : ℂ) ^ (((1 : ℂ) + (y : ℝ) * Complex.I) - 1))

/-- Complementary one-width contribution, defined as full integral minus its central band. -/
def maynardWidthHighTail
    (a : ℝ → ℂ) (N W U : ℝ) : ℂ :=
  (∫ y : ℝ,
      a y * routeTNormalizedSmoothWindowMellin N W
        ((1 : ℂ) + (y : ℝ) * Complex.I)) -
    ∫ y in (-U)..U,
      a y * routeTNormalizedSmoothWindowMellin N W
        ((1 : ℂ) + (y : ℝ) * Complex.I)

/-- Exact decomposition of one normalized window into common mode, central error, and high tail. -/
theorem integral_mul_normalizedMellin_eq_common_add_centralError_add_highTail
    (a : ℝ → ℂ) (ha : Continuous a) {N W U : ℝ}
    (hN : 0 < N) (hW : 0 < W) :
    (∫ y : ℝ,
        a y * routeTNormalizedSmoothWindowMellin N W
          ((1 : ℂ) + (y : ℝ) * Complex.I)) =
      maynardCommonCentralMode a N U +
        maynardCentralWidthError a N W U +
        maynardWidthHighTail a N W U := by
  have hpoint : Continuous (fun y : ℝ =>
      a y * (N : ℂ) ^ (((1 : ℂ) + (y : ℝ) * Complex.I) - 1)) := by
    apply ha.mul
    apply Continuous.const_cpow
    · fun_prop
    · exact Or.inl (by exact_mod_cast hN.ne')
  have herror : Continuous (fun y : ℝ =>
      a y *
        (routeTNormalizedSmoothWindowMellin N W
            ((1 : ℂ) + (y : ℝ) * Complex.I) -
          (N : ℂ) ^ (((1 : ℂ) + (y : ℝ) * Complex.I) - 1))) := by
    apply ha.mul
    apply (continuous_routeTNormalizedSmoothWindowMellin_line hN hW
      (by norm_num)).sub
    apply Continuous.const_cpow
    · fun_prop
    · exact Or.inl (by exact_mod_cast hN.ne')
  have hsplit :
      (∫ y in (-U)..U,
          a y * routeTNormalizedSmoothWindowMellin N W
            ((1 : ℂ) + (y : ℝ) * Complex.I)) =
        maynardCommonCentralMode a N U +
          maynardCentralWidthError a N W U := by
    calc
      (∫ y in (-U)..U,
          a y * routeTNormalizedSmoothWindowMellin N W
            ((1 : ℂ) + (y : ℝ) * Complex.I)) =
          ∫ y in (-U)..U,
            (a y * (N : ℂ) ^ (((1 : ℂ) + (y : ℝ) * Complex.I) - 1) +
              a y *
                (routeTNormalizedSmoothWindowMellin N W
                    ((1 : ℂ) + (y : ℝ) * Complex.I) -
                  (N : ℂ) ^ (((1 : ℂ) + (y : ℝ) * Complex.I) - 1))) := by
            apply intervalIntegral.integral_congr
            intro y _hy
            ring
      _ = (∫ y in (-U)..U,
            a y * (N : ℂ) ^ (((1 : ℂ) + (y : ℝ) * Complex.I) - 1)) +
          ∫ y in (-U)..U,
            a y *
              (routeTNormalizedSmoothWindowMellin N W
                  ((1 : ℂ) + (y : ℝ) * Complex.I) -
                (N : ℂ) ^ (((1 : ℂ) + (y : ℝ) * Complex.I) - 1)) :=
            intervalIntegral.integral_add
              (hpoint.intervalIntegrable (-U) U)
              (herror.intervalIntegrable (-U) U)
      _ = maynardCommonCentralMode a N U +
          maynardCentralWidthError a N W U := rfl
  rw [maynardWidthHighTail, hsplit]
  ring

/-- Subtracting two one-width decompositions cancels the common central mode exactly. -/
theorem integral_adjacentNormalizedMellin_eq_lowErrors_add_highTails
    (a : ℝ → ℂ) (ha : Continuous a) {N H R U : ℝ}
    (hN : 0 < N) (hH : 0 < H) (hR : 0 < R)
    (hintR : Integrable (fun y : ℝ =>
      a y * routeTNormalizedSmoothWindowMellin N R
        ((1 : ℂ) + (y : ℝ) * Complex.I)))
    (hintH : Integrable (fun y : ℝ =>
      a y * routeTNormalizedSmoothWindowMellin N H
        ((1 : ℂ) + (y : ℝ) * Complex.I))) :
    (∫ y : ℝ,
        a y *
          (routeTNormalizedSmoothWindowMellin N R
              ((1 : ℂ) + (y : ℝ) * Complex.I) -
            routeTNormalizedSmoothWindowMellin N H
              ((1 : ℂ) + (y : ℝ) * Complex.I))) =
      (maynardCentralWidthError a N R U -
          maynardCentralWidthError a N H U) +
        (maynardWidthHighTail a N R U -
          maynardWidthHighTail a N H U) := by
  calc
    (∫ y : ℝ,
        a y *
          (routeTNormalizedSmoothWindowMellin N R
              ((1 : ℂ) + (y : ℝ) * Complex.I) -
            routeTNormalizedSmoothWindowMellin N H
              ((1 : ℂ) + (y : ℝ) * Complex.I))) =
        (∫ y : ℝ, a y * routeTNormalizedSmoothWindowMellin N R
            ((1 : ℂ) + (y : ℝ) * Complex.I)) -
          ∫ y : ℝ, a y * routeTNormalizedSmoothWindowMellin N H
            ((1 : ℂ) + (y : ℝ) * Complex.I) := by
      rw [← integral_sub hintR hintH]
      apply integral_congr_ae
      filter_upwards with y
      ring
    _ = (maynardCommonCentralMode a N U +
          maynardCentralWidthError a N R U +
          maynardWidthHighTail a N R U) -
        (maynardCommonCentralMode a N U +
          maynardCentralWidthError a N H U +
          maynardWidthHighTail a N H U) := by
      rw [integral_mul_normalizedMellin_eq_common_add_centralError_add_highTail
          a ha hN hR,
        integral_mul_normalizedMellin_eq_common_add_centralError_add_highTail
          a ha hN hH]
    _ = _ := by ring

/-- A bounded source pays only `8 P U² (W/N)` for one central width error. -/
theorem norm_maynardCentralWidthError_le
    (a : ℝ → ℂ) {P N W U : ℝ}
    (hP : 0 ≤ P) (haBound : ∀ y, ‖a y‖ ≤ P)
    (hN : 0 < N) (hW : 0 < W) (hU : 0 ≤ U)
    (hsmall : U * (2 * W / N) ≤ 1) :
    ‖maynardCentralWidthError a N W U‖ ≤
      8 * P * U ^ 2 * (W / N) := by
  have hpoint : ∀ y ∈ Set.uIoc (-U) U,
      ‖a y *
        (routeTNormalizedSmoothWindowMellin N W
            ((1 : ℂ) + (y : ℝ) * Complex.I) -
          (N : ℂ) ^ (((1 : ℂ) + (y : ℝ) * Complex.I) - 1))‖ ≤
        4 * P * U * (W / N) := by
    intro y hy
    rw [Set.uIoc_of_le (by linarith : -U ≤ U)] at hy
    have hyabs : |y| ≤ U := abs_le.mpr ⟨by linarith [hy.1], hy.2⟩
    let s : ℂ := (1 : ℂ) + (y : ℝ) * Complex.I
    have hsre : 0 < s.re := by simp [s]
    have hsnorm : ‖s - 1‖ = |y| := by
      dsimp only [s]
      simp [Real.norm_eq_abs]
    have hsmallY : ‖s - 1‖ * (2 * W / N) ≤ 1 := by
      rw [hsnorm]
      exact (mul_le_mul_of_nonneg_right hyabs (by positivity)).trans hsmall
    have hk := norm_routeTNormalizedSmoothWindowMellin_sub_pointMass_le
      hN hW hsre hsmallY
    have hNpow : N ^ (s.re - 1) = 1 := by simp [s]
    norm_num [hNpow, hsnorm] at hk
    rw [norm_mul]
    calc
      ‖a y‖ *
          ‖routeTNormalizedSmoothWindowMellin N W
              ((1 : ℂ) + (y : ℝ) * Complex.I) -
            (N : ℂ) ^ (((1 : ℂ) + (y : ℝ) * Complex.I) - 1)‖ ≤
          P * (4 * |y| * (W / N)) :=
        mul_le_mul (haBound y) (by simpa only [s] using hk)
          (norm_nonneg _) hP
      _ ≤ P * (4 * U * (W / N)) := by
        gcongr
      _ = 4 * P * U * (W / N) := by ring
  have hint := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := -U) (b := U) (C := 4 * P * U * (W / N)) hpoint
  rw [maynardCentralWidthError]
  calc
    ‖∫ y in (-U)..U,
        a y *
          (routeTNormalizedSmoothWindowMellin N W
              ((1 : ℂ) + (y : ℝ) * Complex.I) -
            (N : ℂ) ^ (((1 : ℂ) + (y : ℝ) * Complex.I) - 1))‖ ≤
        (4 * P * U * (W / N)) * |U - -U| := hint
    _ = 8 * P * U ^ 2 * (W / N) := by
      rw [abs_of_nonneg (by linarith : 0 ≤ U - -U)]
      ring

/-- Abstract two-tail pigeonhole after the common mode has cancelled. -/
theorem commonMode_highTail_dichotomy
    {lowR lowH highR highH : ℂ} {B : ℝ}
    (hlarge : B ≤ ‖(lowR - lowH) + (highR - highH)‖)
    (hlow : ‖lowR‖ + ‖lowH‖ ≤ B / 2) :
    B / 4 ≤ ‖highR‖ ∨ B / 4 ≤ ‖highH‖ := by
  have htotal : B ≤
      (‖lowR‖ + ‖lowH‖) + (‖highR‖ + ‖highH‖) := by
    calc
      B ≤ ‖(lowR - lowH) + (highR - highH)‖ := hlarge
      _ ≤ ‖lowR - lowH‖ + ‖highR - highH‖ := norm_add_le _ _
      _ ≤ (‖lowR‖ + ‖lowH‖) + (‖highR‖ + ‖highH‖) := by
        exact add_le_add (norm_sub_le lowR lowH) (norm_sub_le highR highH)
  have hhigh : B / 2 ≤ ‖highR‖ + ‖highH‖ := by linarith
  by_contra h
  push Not at h
  linarith

/-- A large endpoint defect with small central errors forces one reference or target high tail. -/
theorem large_adjacentNormalizedMellin_forces_commonMode_highTail
    (a : ℝ → ℂ) (ha : Continuous a) {N H R U B : ℝ}
    (hN : 0 < N) (hH : 0 < H) (hR : 0 < R)
    (hintR : Integrable (fun y : ℝ =>
      a y * routeTNormalizedSmoothWindowMellin N R
        ((1 : ℂ) + (y : ℝ) * Complex.I)))
    (hintH : Integrable (fun y : ℝ =>
      a y * routeTNormalizedSmoothWindowMellin N H
        ((1 : ℂ) + (y : ℝ) * Complex.I)))
    (hlarge : B ≤ ‖∫ y : ℝ,
      a y *
        (routeTNormalizedSmoothWindowMellin N R
            ((1 : ℂ) + (y : ℝ) * Complex.I) -
          routeTNormalizedSmoothWindowMellin N H
            ((1 : ℂ) + (y : ℝ) * Complex.I))‖)
    (hlow : ‖maynardCentralWidthError a N R U‖ +
        ‖maynardCentralWidthError a N H U‖ ≤ B / 2) :
    B / 4 ≤ ‖maynardWidthHighTail a N R U‖ ∨
      B / 4 ≤ ‖maynardWidthHighTail a N H U‖ := by
  rw [integral_adjacentNormalizedMellin_eq_lowErrors_add_highTails
    a ha hN hH hR hintR hintH] at hlarge
  exact commonMode_highTail_dichotomy hlarge hlow

/-- One relative reference width shared by every physical base in the dyadic block `[x, 2x]`.
The upper block endpoint is used so that its handoff-scale window dominates every shifted
handoff window needed by the mass argument. -/
def routeTCommonModeReferenceRelativeWidth (x : ℝ) : ℝ :=
  4 * (2 * x) ^ routeTPhysicalSliceHandoffTheta / x

/-- Uniform density retained by the common-mode reference window. -/
def routeTCommonModeReferenceDensity : ℝ := 1 / 262144

/-- Width-independent central cutoff inherited from Maynard's calibrated short-interval split. -/
def routeTCommonModeCutoff (x : ℝ) : ℝ := x ^ (1 / 8 : ℝ)

theorem routeTCommonModeReferenceDensity_pos :
    0 < routeTCommonModeReferenceDensity := by
  norm_num [routeTCommonModeReferenceDensity]

theorem routeTCommonModeReferenceRelativeWidth_pos {x : ℝ} (hx : 0 < x) :
    0 < routeTCommonModeReferenceRelativeWidth x := by
  unfold routeTCommonModeReferenceRelativeWidth
  positivity

private theorem tendsto_routeTCommonModeReferenceRelativeWidth_zero :
    Tendsto routeTCommonModeReferenceRelativeWidth atTop (nhds 0) := by
  let theta : ℝ := routeTPhysicalSliceHandoffTheta
  have hgap : 0 < 1 - theta := by
    dsimp only [theta]
    linarith [routeTPhysicalSliceHandoffTheta_lt_three_fourths]
  have hdecay := (tendsto_rpow_neg_atTop hgap).const_mul
    (4 * 2 ^ theta)
  have heq : ∀ᶠ x : ℝ in atTop,
      routeTCommonModeReferenceRelativeWidth x =
        (4 * 2 ^ theta) * x ^ (-(1 - theta)) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    unfold routeTCommonModeReferenceRelativeWidth
    dsimp only [theta]
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hx.le,
      Real.rpow_neg hx.le, Real.rpow_sub hx, Real.rpow_one]
    field_simp
  have ht : Tendsto routeTCommonModeReferenceRelativeWidth atTop
      (nhds ((4 * 2 ^ theta) * 0)) := by
    apply hdecay.congr'
    filter_upwards [heq] with x hx
    exact hx.symm
  simpa only [mul_zero] using ht

theorem eventually_routeTCommonModeReferenceRelativeWidth_le_one_half :
    ∀ᶠ x : ℝ in atTop,
      routeTCommonModeReferenceRelativeWidth x ≤ 1 / 2 := by
  have h := Filter.Tendsto.eventually_lt
    tendsto_routeTCommonModeReferenceRelativeWidth_zero
    (tendsto_const_nhds : Tendsto (fun _ : ℝ => (1 / 2 : ℝ)) atTop (nhds (1 / 2)))
    (by norm_num : (0 : ℝ) < 1 / 2)
  filter_upwards [h] with x hx
  exact hx.le

theorem eventually_routeTCommonModeReferenceRelativeWidth_le_one_fourth :
    ∀ᶠ x : ℝ in atTop,
      routeTCommonModeReferenceRelativeWidth x ≤ 1 / 4 := by
  have h := Filter.Tendsto.eventually_lt
    tendsto_routeTCommonModeReferenceRelativeWidth_zero
    (tendsto_const_nhds : Tendsto (fun _ : ℝ => (1 / 4 : ℝ)) atTop (nhds (1 / 4)))
    (by norm_num : (0 : ℝ) < 1 / 4)
  filter_upwards [h] with x hx
  exact hx.le

/-- A shifted handoff-scale theta interval lies inside the common reference's central plateau.
Consequently the reference carries a fixed fraction of its own width in smooth von Mangoldt
mass. -/
theorem routeT_commonMode_fixedReference_smooth_vonMangoldt_mass_lower
    {x lambda : ℝ} (hx : 0 < x) (hlambda : lambda ∈ Set.Icc x (2 * x))
    (hwidth : routeTCommonModeReferenceRelativeWidth x ≤ 1 / 2)
    (htheta :
      let R := lambda * routeTCommonModeReferenceRelativeWidth x
      let z := lambda + R / 2
      z ^ routeTPhysicalSliceHandoffTheta / 16384 <
        Chebyshev.theta
            (z + 3 * z ^ routeTPhysicalSliceHandoffTheta / 2) -
          Chebyshev.theta
            (z + z ^ routeTPhysicalSliceHandoffTheta / 2)) :
    routeTSmoothWindowCentralMargin *
        (routeTCommonModeReferenceDensity *
          (lambda * routeTCommonModeReferenceRelativeWidth x)) <
      ∑' n : ℕ, (vonMangoldt n : ℝ) *
        routeTSmoothWindowWeight lambda
          (lambda * routeTCommonModeReferenceRelativeWidth x) n := by
  let theta : ℝ := routeTPhysicalSliceHandoffTheta
  let r : ℝ := routeTCommonModeReferenceRelativeWidth x
  let R : ℝ := lambda * r
  let z : ℝ := lambda + R / 2
  have hlambda0 : 0 < lambda := hx.trans_le hlambda.1
  have hr0 : 0 < r := by
    dsimp only [r]
    exact routeTCommonModeReferenceRelativeWidth_pos hx
  have hR0 : 0 < R := mul_pos hlambda0 hr0
  have hz0 : 0 < z := by dsimp only [z]; linarith
  have htheta0 : 0 ≤ theta := by
    dsimp only [theta]
    exact routeTPhysicalSliceHandoffTheta_pos.le
  have htheta1 : theta ≤ 1 := by
    dsimp only [theta]
    exact (routeTPhysicalSliceHandoffTheta_lt_three_fourths.trans (by norm_num)).le
  have hRle : R ≤ lambda / 2 := by
    dsimp only [R]
    have hwidth' : r ≤ 1 / 2 := by simpa only [r] using hwidth
    have := mul_le_mul_of_nonneg_left hwidth' hlambda0.le
    linarith
  have hzle : z ≤ 4 * x := by
    dsimp only [z]
    linarith [hlambda.2]
  have htwoPow : (2 : ℝ) ^ theta ≤ 2 := by
    have hpow := Real.rpow_le_rpow_of_exponent_le
      (by norm_num : (1 : ℝ) ≤ 2) htheta1
    simpa only [Real.rpow_one] using hpow
  have hzPowUpper : z ^ theta ≤ 2 * (2 * x) ^ theta := by
    calc
      z ^ theta ≤ (4 * x) ^ theta :=
        Real.rpow_le_rpow hz0.le hzle htheta0
      _ = (2 : ℝ) ^ theta * (2 * x) ^ theta := by
        rw [show (4 : ℝ) * x = 2 * (2 * x) by ring,
          Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (by positivity : 0 ≤ 2 * x)]
      _ ≤ 2 * (2 * x) ^ theta :=
        mul_le_mul_of_nonneg_right htwoPow (Real.rpow_nonneg (by positivity) _)
  have hRlower : 4 * (2 * x) ^ theta ≤ R := by
    dsimp only [R, r, routeTCommonModeReferenceRelativeWidth]
    have hmul := mul_le_mul_of_nonneg_right hlambda.1
      (by positivity : 0 ≤ 4 * (2 * x) ^ theta / x)
    calc
      4 * (2 * x) ^ theta = x * (4 * (2 * x) ^ theta / x) := by field_simp
      _ ≤ lambda * (4 * (2 * x) ^ theta / x) := hmul
  have hcontain : z + 3 * z ^ theta / 2 ≤ lambda + 3 * R / 2 := by
    dsimp only [z]
    have hzR : 3 * z ^ theta ≤ 2 * R := by
      linarith [hzPowUpper, hRlower]
    linarith
  have hRupper : R ≤ 8 * (2 * x) ^ theta := by
    dsimp only [R, r, routeTCommonModeReferenceRelativeWidth]
    have hmul := mul_le_mul_of_nonneg_right hlambda.2
      (by positivity : 0 ≤ 4 * (2 * x) ^ theta / x)
    calc
      lambda * (4 * (2 * x) ^ theta / x) ≤
          (2 * x) * (4 * (2 * x) ^ theta / x) := hmul
      _ = 8 * (2 * x) ^ theta := by field_simp; norm_num
  have hxPowLe : x ^ theta ≤ z ^ theta := by
    apply Real.rpow_le_rpow hx.le
    · dsimp only [z]
      exact hlambda.1.trans (by linarith [hR0])
    · exact htheta0
  have htwoXpow : (2 * x) ^ theta ≤ 2 * x ^ theta := by
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hx.le]
    exact mul_le_mul_of_nonneg_right htwoPow (Real.rpow_nonneg hx.le _)
  have hRz : R ≤ 16 * z ^ theta := by
    linarith [hRupper, htwoXpow, hxPowLe]
  have htargetTheta :
      routeTCommonModeReferenceDensity * R <
        Chebyshev.theta (lambda + 3 * R / 2) -
          Chebyshev.theta (lambda + R / 2) := by
    have hzPow0 : 0 ≤ z ^ theta := Real.rpow_nonneg hz0.le _
    have hleft := Chebyshev.theta_mono
      (show z ≤ z + z ^ theta / 2 by linarith)
    have hright := Chebyshev.theta_mono hcontain
    have hscale : routeTCommonModeReferenceDensity * R ≤
        z ^ theta / 16384 := by
      unfold routeTCommonModeReferenceDensity
      linarith
    dsimp only [theta, r, R, z] at htheta hleft hright hscale ⊢
    linarith
  have hinject := routeT_theta_window_mul_margin_le_smooth_vonMangoldt_mass
    hlambda0.le hR0
  have hlower := mul_lt_mul_of_pos_left htargetTheta
    routeTSmoothWindowCentralMargin_pos
  dsimp only [r, R] at hinject hlower ⊢
  exact hlower.trans_le hinject

/-- Every base in one dyadic block shares a single relative reference width whose physical
reference window carries a uniform positive fraction of its width. -/
theorem eventually_routeT_commonMode_fixedReference_smooth_vonMangoldt_mass_lower :
    ∀ᶠ x : ℝ in atTop, ∀ lambda ∈ Set.Icc x (2 * x),
      routeTSmoothWindowCentralMargin *
          (routeTCommonModeReferenceDensity *
            (lambda * routeTCommonModeReferenceRelativeWidth x)) <
        ∑' n : ℕ, (vonMangoldt n : ℝ) *
          routeTSmoothWindowWeight lambda
            (lambda * routeTCommonModeReferenceRelativeWidth x) n := by
  rcases eventually_atTop.1 eventually_routeT_handoff_central_theta_mass with
    ⟨Q, hQ⟩
  filter_upwards [eventually_routeTCommonModeReferenceRelativeWidth_le_one_half,
      eventually_ge_atTop (max 1 Q)] with x hwidth hx
  intro lambda hlambda
  have hx0 : 0 < x := by linarith [le_max_left (1 : ℝ) Q]
  apply routeT_commonMode_fixedReference_smooth_vonMangoldt_mass_lower
    hx0 hlambda hwidth
  let R : ℝ := lambda * routeTCommonModeReferenceRelativeWidth x
  let z : ℝ := lambda + R / 2
  have hlambda0 : 0 < lambda := hx0.trans_le hlambda.1
  have hR0 : 0 < R := mul_pos hlambda0
    (routeTCommonModeReferenceRelativeWidth_pos hx0)
  apply hQ z
  dsimp only [z]
  have hQx : Q ≤ x := (le_max_right (1 : ℝ) Q).trans hx
  linarith [hlambda.1]

private theorem routeT_commonMode_centralCost_eq
    {P x : ℝ} (hx : 0 < x) :
    16 * P * routeTCommonModeCutoff x ^ 2 *
        routeTCommonModeReferenceRelativeWidth x =
      (64 * 2 ^ routeTPhysicalSliceHandoffTheta) * P *
        x ^ (-(3 / 4 - routeTPhysicalSliceHandoffTheta)) := by
  unfold routeTCommonModeCutoff routeTCommonModeReferenceRelativeWidth
  rw [← Real.rpow_natCast (x ^ (1 / 8 : ℝ)) 2, ← Real.rpow_mul hx.le]
  norm_num only [Nat.cast_ofNat]
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hx.le]
  have hpows : x ^ (1 / 4 : ℝ) * x ^ routeTPhysicalSliceHandoffTheta / x =
      x ^ (-(3 / 4 - routeTPhysicalSliceHandoffTheta)) := by
    rw [← Real.rpow_add hx]
    have hexp : (1 / 4 : ℝ) + routeTPhysicalSliceHandoffTheta =
        1 + (-(3 / 4 - routeTPhysicalSliceHandoffTheta)) := by ring
    rw [hexp, Real.rpow_add hx, Real.rpow_one]
    field_simp
  calc
    16 * P * x ^ (1 / 4 : ℝ) *
          (4 * (2 ^ routeTPhysicalSliceHandoffTheta *
            x ^ routeTPhysicalSliceHandoffTheta) / x) =
        (64 * 2 ^ routeTPhysicalSliceHandoffTheta) * P *
          (x ^ (1 / 4 : ℝ) * x ^ routeTPhysicalSliceHandoffTheta / x) := by ring
    _ = _ := by rw [hpows]

private theorem tendsto_routeT_commonMode_scalar_zero :
    Tendsto (fun T : ℝ =>
      (64 * 2 ^ routeTPhysicalSliceHandoffTheta) *
        T ^ (3 / 4 - routeTPhysicalSliceHandoffTheta) *
        routeTPrimeGapPacketBase T ^
          (-(3 / 4 - routeTPhysicalSliceHandoffTheta)))
      atTop (nhds 0) := by
  let g : ℝ := 3 / 4 - routeTPhysicalSliceHandoffTheta
  have hg : 0 < g := by
    dsimp only [g]
    linarith [routeTPhysicalSliceHandoffTheta_lt_three_fourths]
  have hdecay := (tendsto_rpow_neg_atTop
    (show 0 < (3 / 5 : ℝ) * g by positivity)).const_mul
      ((64 * 2 ^ routeTPhysicalSliceHandoffTheta) * 4 ^ g)
  have heq : ∀ᶠ T : ℝ in atTop,
      (64 * 2 ^ routeTPhysicalSliceHandoffTheta) * T ^ g *
          routeTPrimeGapPacketBase T ^ (-g) =
        ((64 * 2 ^ routeTPhysicalSliceHandoffTheta) * 4 ^ g) *
          T ^ (-((3 / 5 : ℝ) * g)) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
    unfold routeTPrimeGapPacketBase
    rw [Real.div_rpow (Real.rpow_nonneg hT.le _) (by norm_num : (0 : ℝ) ≤ 4),
      Real.rpow_neg (Real.rpow_nonneg hT.le _),
      Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 4),
      div_inv_eq_mul, ← Real.rpow_mul hT.le, ← Real.rpow_neg hT.le]
    have hpows : T ^ g * T ^ (-(8 / 5 * g)) = T ^ (-(3 / 5 * g)) := by
      rw [← Real.rpow_add hT]
      congr 1
      ring
    rw [show (64 * 2 ^ routeTPhysicalSliceHandoffTheta) * T ^ g *
        (T ^ (-(8 / 5 * g)) * 4 ^ g) =
      ((64 * 2 ^ routeTPhysicalSliceHandoffTheta) * 4 ^ g) *
        (T ^ g * T ^ (-(8 / 5 * g))) by ring, hpows]
  have ht : Tendsto (fun T : ℝ =>
      (64 * 2 ^ routeTPhysicalSliceHandoffTheta) * T ^ g *
        routeTPrimeGapPacketBase T ^ (-g)) atTop
      (nhds (((64 * 2 ^ routeTPhysicalSliceHandoffTheta) * 4 ^ g) * 0)) := by
    apply hdecay.congr'
    filter_upwards [heq] with T hT
    exact hT.symm
  simpa only [mul_zero, g] using ht

/-- The complete frozen-source central replacement cost vanishes on the canonical Route-T
schedule.  This is the scale gap which makes the two-tail cover unconditional. -/
theorem eventually_routeT_commonMode_centralCost_le :
    ∀ᶠ T : ℝ in atTop, ∀ L : ℕ,
      1 ≤ L → L ≤ routeTPrimeGapPacketSupport T →
      16 * heathBrownWindowRelevantFixedPolylogBound
            L (routeTPrimeGapPacketSupport T) 60
            (routeTPrimeGapPacketBase T) 1 *
          routeTCommonModeCutoff (routeTPrimeGapPacketBase T) ^ 2 *
          routeTCommonModeReferenceRelativeWidth (routeTPrimeGapPacketBase T) ≤
        ((2 * Real.pi) *
          (routeTSmoothWindowCentralMargin * routeTCommonModeReferenceDensity / 2)) / 2 := by
  let g : ℝ := 3 / 4 - routeTPhysicalSliceHandoffTheta
  let B : ℝ := ((2 * Real.pi) *
    (routeTSmoothWindowCentralMargin * routeTCommonModeReferenceDensity / 2)) / 2
  have hg : 0 < g := by
    dsimp only [g]
    linarith [routeTPhysicalSliceHandoffTheta_lt_three_fourths]
  have hB : 0 < B := by
    dsimp only [B]
    positivity [routeTCommonModeReferenceDensity_pos,
      routeTSmoothWindowCentralMargin_pos]
  have hpoly :=
    eventually_heathBrownWindowRelevantFixedPolylogBound_sixty_routeT_absorbed_leftCutoff hg
  have hscalar := Tendsto.eventually_le_const hB tendsto_routeT_commonMode_scalar_zero
  have hbaseTop : Tendsto routeTPrimeGapPacketBase atTop atTop := by
    unfold routeTPrimeGapPacketBase
    exact (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 8 / 5)).atTop_div_const
      (by norm_num)
  have hbaseLarge : ∀ᶠ T : ℝ in atTop, 1 ≤ routeTPrimeGapPacketBase T :=
    hbaseTop.eventually_ge_atTop 1
  filter_upwards [hpoly, hscalar, hbaseLarge,
      eventually_gt_atTop (0 : ℝ)] with T hpolyT hscalarT hx1 hT
  intro L hL hLX
  let x : ℝ := routeTPrimeGapPacketBase T
  let X : ℕ := routeTPrimeGapPacketSupport T
  let P : ℝ := heathBrownWindowRelevantFixedPolylogBound L X 60 x 1
  have hx0 : 0 < x := by dsimp only [x]; linarith
  have hx1' : 1 ≤ x := by simpa only [x] using hx1
  have hX : 1 ≤ X := by
    apply Nat.ceil_pos.mpr
    change 0 < 3 * x
    positivity
  have hceilUpper : (X : ℝ) < 3 * x + 1 := by
    dsimp only [X, routeTPrimeGapPacketSupport]
    exact Nat.ceil_lt_add_one (by positivity)
  have hXx : (X : ℝ) ≤ 4 * x := by
    linarith
  have hxscale : 4 * x = T ^ (8 / 5 : ℝ) := by
    dsimp only [x, routeTPrimeGapPacketBase]
    field_simp
  have hXscale : (X : ℝ) ≤ T ^ (8 / 5 : ℝ) := by
    rw [← hxscale]
    exact hXx
  have hP : P ≤ T ^ g := by
    exact hpolyT x L X hx1' hL hX hLX hXx hXscale
  rw [routeT_commonMode_centralCost_eq hx0]
  have hC0 : 0 ≤ (64 : ℝ) * 2 ^ routeTPhysicalSliceHandoffTheta := by positivity
  have hxpow0 : 0 ≤ x ^ (-g) := Real.rpow_nonneg hx0.le _
  calc
    (64 * 2 ^ routeTPhysicalSliceHandoffTheta) * P * x ^ (-g) ≤
        (64 * 2 ^ routeTPhysicalSliceHandoffTheta) * T ^ g * x ^ (-g) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hP hC0) hxpow0
    _ ≤ B := by simpa only [x, g] using hscalarT
    _ = _ := rfl

theorem routeTPrimeGapPacketWidth_le_commonModeReference
    {x lambda : ℝ} (hx : 1 ≤ x) (hlambda : lambda ∈ Set.Icc x (2 * x)) :
    routeTPrimeGapPacketWidth lambda ≤
      routeTCommonModeReferenceRelativeWidth x := by
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hlambda0 : 0 < lambda := hx0.trans_le hlambda.1
  have hanti : lambda ^ (-(49 / 80 : ℝ)) ≤ x ^ (-(49 / 80 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos hx0 hlambda.1 (by norm_num)
  have hexp : (-(49 / 80 : ℝ)) ≤ routeTPhysicalSliceHandoffTheta - 1 := by
    dsimp only [routeTPhysicalSliceHandoffTheta]
    linarith [maynardLongGlobalAmplitudeDeficit_lt_one_hundredth]
  have hpow := Real.rpow_le_rpow_of_exponent_le hx hexp
  have htheta0 : 0 ≤ routeTPhysicalSliceHandoffTheta :=
    routeTPhysicalSliceHandoffTheta_pos.le
  have htwo : 1 ≤ (2 : ℝ) ^ routeTPhysicalSliceHandoffTheta :=
    Real.one_le_rpow (by norm_num) htheta0
  have hrefEq : routeTCommonModeReferenceRelativeWidth x =
      (4 * 2 ^ routeTPhysicalSliceHandoffTheta) *
        x ^ (routeTPhysicalSliceHandoffTheta - 1) := by
    unfold routeTCommonModeReferenceRelativeWidth
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hx0.le,
      Real.rpow_sub hx0, Real.rpow_one]
    field_simp
  have hcoeff : 1 ≤ (4 : ℝ) * 2 ^ routeTPhysicalSliceHandoffTheta := by
    nlinarith
  have hlast : x ^ (routeTPhysicalSliceHandoffTheta - 1) ≤
      (4 * 2 ^ routeTPhysicalSliceHandoffTheta) *
        x ^ (routeTPhysicalSliceHandoffTheta - 1) := by
    exact le_mul_of_one_le_left (Real.rpow_nonneg hx0.le _) hcoeff
  unfold routeTPrimeGapPacketWidth
  rw [hrefEq]
  exact hanti.trans (hpow.trans hlast)

private theorem tendsto_routeTCommonModeCutoff_mul_reference_zero :
    Tendsto (fun x : ℝ => routeTCommonModeCutoff x *
      (2 * routeTCommonModeReferenceRelativeWidth x)) atTop (nhds 0) := by
  let delta : ℝ := 7 / 8 - routeTPhysicalSliceHandoffTheta
  have hdelta : 0 < delta := by
    dsimp only [delta]
    linarith [routeTPhysicalSliceHandoffTheta_lt_three_fourths]
  have hdecay := (tendsto_rpow_neg_atTop hdelta).const_mul
    (8 * 2 ^ routeTPhysicalSliceHandoffTheta)
  have heq : ∀ᶠ x : ℝ in atTop,
      routeTCommonModeCutoff x *
          (2 * routeTCommonModeReferenceRelativeWidth x) =
        (8 * 2 ^ routeTPhysicalSliceHandoffTheta) * x ^ (-delta) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    unfold routeTCommonModeCutoff routeTCommonModeReferenceRelativeWidth
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hx.le]
    have hpows : x ^ (1 / 8 : ℝ) * x ^ routeTPhysicalSliceHandoffTheta / x =
        x ^ (-delta) := by
      rw [← Real.rpow_add hx]
      have hexp : (1 / 8 : ℝ) + routeTPhysicalSliceHandoffTheta =
          1 + (-delta) := by dsimp only [delta]; ring
      rw [hexp, Real.rpow_add hx, Real.rpow_one]
      field_simp
    calc
      x ^ (1 / 8 : ℝ) *
          (2 * (4 * (2 ^ routeTPhysicalSliceHandoffTheta *
            x ^ routeTPhysicalSliceHandoffTheta) / x)) =
        (8 * 2 ^ routeTPhysicalSliceHandoffTheta) *
          (x ^ (1 / 8 : ℝ) * x ^ routeTPhysicalSliceHandoffTheta / x) := by ring
      _ = _ := by rw [hpows]
  have ht : Tendsto (fun x : ℝ => routeTCommonModeCutoff x *
      (2 * routeTCommonModeReferenceRelativeWidth x)) atTop
      (nhds ((8 * 2 ^ routeTPhysicalSliceHandoffTheta) * 0)) := by
    apply hdecay.congr'
    filter_upwards [heq] with x hx
    exact hx.symm
  simpa only [mul_zero] using ht

/-- On the canonical packet, both the common reference and every target width have small central
kernel error, and their combined error is below half the fixed Perron defect. -/
theorem eventually_routeT_commonMode_centralErrors_le :
    ∀ᶠ T : ℝ in atTop, ∀ L : ℕ,
      1 ≤ L → L ≤ routeTPrimeGapPacketSupport T →
      ∀ lambda ∈ Set.Icc (routeTPrimeGapPacketBase T)
          (2 * routeTPrimeGapPacketBase T),
        ‖maynardCentralWidthError
          (fun y : ℝ =>
            heathBrownWindowRelevantEligibleDyadicAggregate
              L (routeTPrimeGapPacketSupport T) 60 T (1 / 75)
                (routeTPrimeGapPacketBase T)
              ((1 : ℂ) + (y : ℝ) * Complex.I))
          lambda
          (lambda * routeTCommonModeReferenceRelativeWidth
            (routeTPrimeGapPacketBase T))
          (routeTCommonModeCutoff (routeTPrimeGapPacketBase T))‖ +
        ‖maynardCentralWidthError
          (fun y : ℝ =>
            heathBrownWindowRelevantEligibleDyadicAggregate
              L (routeTPrimeGapPacketSupport T) 60 T (1 / 75)
                (routeTPrimeGapPacketBase T)
              ((1 : ℂ) + (y : ℝ) * Complex.I))
          lambda (lambda * routeTPrimeGapPacketWidth lambda)
          (routeTCommonModeCutoff (routeTPrimeGapPacketBase T))‖ ≤
        ((2 * Real.pi) *
          (routeTSmoothWindowCentralMargin * routeTCommonModeReferenceDensity / 2)) / 2 := by
  have hbaseTop : Tendsto routeTPrimeGapPacketBase atTop atTop := by
    unfold routeTPrimeGapPacketBase
    exact (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 8 / 5)).atTop_div_const
      (by norm_num)
  have hsmall := Tendsto.eventually_le_const (by norm_num : (0 : ℝ) < 1)
    (tendsto_routeTCommonModeCutoff_mul_reference_zero.comp hbaseTop)
  have hcost := eventually_routeT_commonMode_centralCost_le
  have hbaseLarge : ∀ᶠ T : ℝ in atTop, 1 ≤ routeTPrimeGapPacketBase T :=
    hbaseTop.eventually_ge_atTop 1
  filter_upwards [hsmall, hcost, hbaseLarge,
      eventually_gt_atTop (0 : ℝ)] with T hsmallT hcostT hx1 hT
  intro L hL hLX lambda hlambda
  let x : ℝ := routeTPrimeGapPacketBase T
  let X : ℕ := routeTPrimeGapPacketSupport T
  let P : ℝ := heathBrownWindowRelevantFixedPolylogBound L X 60 x 1
  let U : ℝ := routeTCommonModeCutoff x
  let R : ℝ := routeTCommonModeReferenceRelativeWidth x
  let H : ℝ := routeTPrimeGapPacketWidth lambda
  have hx1' : 1 ≤ x := by simpa only [x] using hx1
  have hx0 : 0 < x := zero_lt_one.trans_le hx1'
  have hlambda0 : 0 < lambda := hx0.trans_le hlambda.1
  have hX : 1 ≤ X := by
    apply Nat.ceil_pos.mpr
    change 0 < 3 * x
    positivity
  have hP0 : 0 ≤ P := by
    dsimp only [P]
    exact (norm_nonneg
      (heathBrownWindowRelevantEligibleDyadicAggregate L X 60 T (1 / 75) x
        ((1 : ℂ) + (0 : ℝ) * Complex.I))).trans
      (norm_heathBrownWindowRelevantEligibleDyadicAggregate_le_fixedPolylog
        L X 60 hX T (1 / 75) x 1 0 hx0 (by norm_num))
  have hU0 : 0 ≤ U := by
    dsimp only [U, routeTCommonModeCutoff]
    positivity
  have hR0 : 0 < R := by
    dsimp only [R]
    exact routeTCommonModeReferenceRelativeWidth_pos hx0
  have hH0 : 0 < H := by
    dsimp only [H, routeTPrimeGapPacketWidth]
    positivity
  have hHR : H ≤ R := by
    dsimp only [H, R]
    exact routeTPrimeGapPacketWidth_le_commonModeReference hx1' hlambda
  have hsmallR : U * (2 * (lambda * R) / lambda) ≤ 1 := by
    have hs : U * (2 * R) ≤ 1 := by
      simpa only [Function.comp_apply, U, R, x] using hsmallT
    field_simp [hlambda0.ne']
    simpa only [mul_assoc] using hs
  have hsmallH : U * (2 * (lambda * H) / lambda) ≤ 1 := by
    have hs : U * (2 * H) ≤ U * (2 * R) := by
      gcongr
    have hsR : U * (2 * R) ≤ 1 := by
      simpa only [Function.comp_apply, U, R, x] using hsmallT
    exact (by field_simp [hlambda0.ne']; simpa only [mul_assoc] using hs.trans hsR)
  let a : ℝ → ℂ := fun y : ℝ =>
    heathBrownWindowRelevantEligibleDyadicAggregate L X 60 T (1 / 75) x
      ((1 : ℂ) + (y : ℝ) * Complex.I)
  have haBound : ∀ y, ‖a y‖ ≤ P := by
    intro y
    dsimp only [a, P]
    exact norm_heathBrownWindowRelevantEligibleDyadicAggregate_le_fixedPolylog
      L X 60 hX T (1 / 75) x 1 y hx0 (by norm_num)
  have herrorR := norm_maynardCentralWidthError_le
    a hP0 haBound hlambda0 (mul_pos hlambda0 hR0) hU0 hsmallR
  have herrorH := norm_maynardCentralWidthError_le
    a hP0 haBound hlambda0 (mul_pos hlambda0 hH0) hU0 hsmallH
  have herrorR' : ‖maynardCentralWidthError a lambda (lambda * R) U‖ ≤
      8 * P * U ^ 2 * R := by
    convert herrorR using 1
    field_simp [hlambda0.ne']
  have herrorH' : ‖maynardCentralWidthError a lambda (lambda * H) U‖ ≤
      8 * P * U ^ 2 * H := by
    convert herrorH using 1
    field_simp [hlambda0.ne']
  have hfactor0 : 0 ≤ 8 * P * U ^ 2 := by positivity
  have hsum : ‖maynardCentralWidthError a lambda (lambda * R) U‖ +
      ‖maynardCentralWidthError a lambda (lambda * H) U‖ ≤
      16 * P * U ^ 2 * R := by
    calc
      _ ≤ 8 * P * U ^ 2 * R + 8 * P * U ^ 2 * H :=
        add_le_add herrorR' herrorH'
      _ ≤ 8 * P * U ^ 2 * R + 8 * P * U ^ 2 * R := by
        exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hHR hfactor0)
      _ = 16 * P * U ^ 2 * R := by ring
  exact hsum.trans (by simpa only [P, U, R, x, X] using hcostT L hL hLX)

/-- Prime-freeness at any physical base in a dyadic block forces one of two high tails after the
Heath--Brown source has been frozen at the block's left endpoint.  No width ladder or selected
intermediate rung remains. -/
theorem primeFree_forces_fixedSource_commonMode_highTail
    (L X k : ℕ) (hXL : X < (L + 1) ^ k) {T0 t x lambda H R U rho : ℝ}
    (hx : 0 < x) (hlambda : lambda ∈ Set.Icc x (2 * x))
    (hT0 : 1 < T0)
    (hscale : ((2 ^ (2 * k) : ℕ) : ℝ) * T0 ^ t ≤ lambda)
    (hlambda2 : 2 ≤ lambda) (hH : 0 < H) (hR : 0 < R) (hrho : 0 < rho)
    (hwidthH : 1 ≤ 2 * (lambda * H))
    (hsupportH : lambda + 2 * (lambda * H) ≤ X)
    (hsupportR : lambda + 2 * (lambda * R) ≤ X)
    (hprimeFree :
      Chebyshev.theta (lambda + 2 * (lambda * H)) -
        Chebyshev.theta lambda = 0)
    (href : routeTSmoothWindowCentralMargin * (rho * (lambda * R)) ≤
      ∑' n : ℕ, (vonMangoldt n : ℝ) *
        routeTSmoothWindowWeight lambda (lambda * R) n)
    (hleakage :
      (Real.log (lambda + 2 * (lambda * H)) / Real.log 2) *
          (Real.sqrt (2 * (lambda * H)) + 1) *
            Real.log (lambda + 2 * (lambda * H)) / (lambda * H) ≤
        routeTSmoothWindowCentralMargin * rho / 2)
    (hlow :
      ‖maynardCentralWidthError
          (fun y : ℝ =>
            heathBrownWindowRelevantEligibleDyadicAggregate L X k T0 t x
              ((1 : ℂ) + (y : ℝ) * Complex.I))
          lambda (lambda * R) U‖ +
        ‖maynardCentralWidthError
          (fun y : ℝ =>
            heathBrownWindowRelevantEligibleDyadicAggregate L X k T0 t x
              ((1 : ℂ) + (y : ℝ) * Complex.I))
          lambda (lambda * H) U‖ ≤
          ((2 * Real.pi) * (routeTSmoothWindowCentralMargin * rho / 2)) / 2) :
    ((2 * Real.pi) * (routeTSmoothWindowCentralMargin * rho / 2)) / 4 ≤
        ‖maynardWidthHighTail
          (fun y : ℝ =>
            heathBrownWindowRelevantEligibleDyadicAggregate L X k T0 t x
              ((1 : ℂ) + (y : ℝ) * Complex.I))
          lambda (lambda * R) U‖ ∨
      ((2 * Real.pi) * (routeTSmoothWindowCentralMargin * rho / 2)) / 4 ≤
        ‖maynardWidthHighTail
          (fun y : ℝ =>
            heathBrownWindowRelevantEligibleDyadicAggregate L X k T0 t x
              ((1 : ℂ) + (y : ℝ) * Complex.I))
          lambda (lambda * H) U‖ := by
  have hlambda0 : 0 < lambda := by linarith
  have hHphysical : 0 < lambda * H := mul_pos hlambda0 hH
  have hRphysical : 0 < lambda * R := mul_pos hlambda0 hR
  let a : ℝ → ℂ := fun y : ℝ =>
    heathBrownWindowRelevantEligibleDyadicAggregate L X k T0 t x
      ((1 : ℂ) + (y : ℝ) * Complex.I)
  have ha : Continuous a := by
    dsimp only [a]
    exact continuous_heathBrownWindowRelevantEligibleDyadicAggregate_line
      L X k T0 t x 1
  have hintR0 :=
    integrable_LSeries_mul_routeTNormalizedSmoothWindowMellin_of_upperSupported
      (upperSupported_heathBrownWindowRelevantEligiblePacket L X k T0 t x)
      hlambda0 hRphysical (by norm_num : (0 : ℝ) < 1)
  have hintH0 :=
    integrable_LSeries_mul_routeTNormalizedSmoothWindowMellin_of_upperSupported
      (upperSupported_heathBrownWindowRelevantEligiblePacket L X k T0 t x)
      hlambda0 hHphysical (by norm_num : (0 : ℝ) < 1)
  have hintR : Integrable (fun y : ℝ =>
      a y * routeTNormalizedSmoothWindowMellin lambda (lambda * R)
        ((1 : ℂ) + (y : ℝ) * Complex.I)) := by
    refine hintR0.congr (Eventually.of_forall fun y => ?_)
    exact congrArg
      (fun z : ℂ => z * routeTNormalizedSmoothWindowMellin lambda (lambda * R)
        ((1 : ℂ) + (y : ℝ) * Complex.I))
      (LSeries_heathBrownWindowRelevantEligiblePacket L X k T0 t x
        ((1 : ℂ) + (y : ℝ) * Complex.I))
  have hintH : Integrable (fun y : ℝ =>
      a y * routeTNormalizedSmoothWindowMellin lambda (lambda * H)
        ((1 : ℂ) + (y : ℝ) * Complex.I)) := by
    refine hintH0.congr (Eventually.of_forall fun y => ?_)
    exact congrArg
      (fun z : ℂ => z * routeTNormalizedSmoothWindowMellin lambda (lambda * H)
        ((1 : ℂ) + (y : ℝ) * Complex.I))
      (LSeries_heathBrownWindowRelevantEligiblePacket L X k T0 t x
        ((1 : ℂ) + (y : ℝ) * Complex.I))
  have hphysical := norm_integral_normalizedKernelDefect_ge_of_primeFree_of_fraction
    L X k hXL hT0 hscale hlambda2 hHphysical hRphysical hrho hwidthH
      hsupportH hsupportR (by norm_num : (0 : ℝ) < 1) hprimeFree href hleakage
  have hrecut :=
    integral_windowRelevant_mul_scaled_adjacentNormalizedMellin_eq_leftWindowRelevant
      L X k T0 t (x := x) (lambda := lambda) (N := 1) (R := R) (H := H)
        (sigma := 1) hx hlambda (by norm_num) hR hH (by norm_num)
  have hlarge :
      (2 * Real.pi) * (routeTSmoothWindowCentralMargin * rho / 2) ≤
        ‖∫ y : ℝ, a y *
          (routeTNormalizedSmoothWindowMellin lambda (lambda * R)
              ((1 : ℂ) + (y : ℝ) * Complex.I) -
            routeTNormalizedSmoothWindowMellin lambda (lambda * H)
              ((1 : ℂ) + (y : ℝ) * Complex.I))‖ := by
    dsimp only [a]
    have hrecut' := hrecut
    norm_num at hrecut'
    exact hphysical.trans_eq (congrArg norm hrecut')
  exact large_adjacentNormalizedMellin_forces_commonMode_highTail
    a ha hlambda0 hHphysical hRphysical hintR hintH hlarge (by simpa only [a] using hlow)

/-- Canonical Route-T prime-free cover with no width ladder.  One common reference tail and the
literal target tail are the only survivors above the central cutoff `x^(1/8)`. -/
theorem exists_eventually_routeT_primeFree_fixedSource_commonMode_twoTail :
    ∀ᶠ T : ℝ in atTop,
      ∃ L : ℕ, 1 ≤ L ∧
        routeTPrimeGapPacketSupport T < (L + 1) ^ (60 : ℕ) ∧
        (L : ℝ) ≤ T ^ (2 / 75 : ℝ) ∧
        ∀ lambda ∈ Set.Icc (routeTPrimeGapPacketBase T)
            (2 * routeTPrimeGapPacketBase T),
          Chebyshev.theta
                (lambda + 2 * (lambda * routeTPrimeGapPacketWidth lambda)) -
              Chebyshev.theta lambda = 0 →
          ((2 * Real.pi) *
              (routeTSmoothWindowCentralMargin *
                routeTCommonModeReferenceDensity / 2)) / 4 ≤
              ‖maynardWidthHighTail
                (fun y : ℝ =>
                  heathBrownWindowRelevantEligibleDyadicAggregate
                    L (routeTPrimeGapPacketSupport T) 60 T (1 / 75)
                      (routeTPrimeGapPacketBase T)
                    ((1 : ℂ) + (y : ℝ) * Complex.I))
                lambda
                (lambda * routeTCommonModeReferenceRelativeWidth
                  (routeTPrimeGapPacketBase T))
                (routeTCommonModeCutoff (routeTPrimeGapPacketBase T))‖ ∨
            ((2 * Real.pi) *
              (routeTSmoothWindowCentralMargin *
                routeTCommonModeReferenceDensity / 2)) / 4 ≤
              ‖maynardWidthHighTail
                (fun y : ℝ =>
                  heathBrownWindowRelevantEligibleDyadicAggregate
                    L (routeTPrimeGapPacketSupport T) 60 T (1 / 75)
                      (routeTPrimeGapPacketBase T)
                    ((1 : ℂ) + (y : ℝ) * Complex.I))
                lambda (lambda * routeTPrimeGapPacketWidth lambda)
                (routeTCommonModeCutoff (routeTPrimeGapPacketBase T))‖ := by
  have hbaseTop : Tendsto routeTPrimeGapPacketBase atTop atTop := by
    unfold routeTPrimeGapPacketBase
    exact (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 8 / 5)).atTop_div_const
      (by norm_num)
  have hmass := hbaseTop.eventually
    eventually_routeT_commonMode_fixedReference_smooth_vonMangoldt_mass_lower
  have hcentral := eventually_routeT_commonMode_centralErrors_le
  have hrefSmall := hbaseTop.eventually
    eventually_routeTCommonModeReferenceRelativeWidth_le_one_fourth
  have hbaseLarge : ∀ᶠ T : ℝ in atTop, 16 ≤ routeTPrimeGapPacketBase T :=
    hbaseTop.eventually_ge_atTop 16
  have htargetSmall : ∀ᶠ T : ℝ in atTop,
      routeTPrimeGapPacketBase T ^ (-(49 / 80 : ℝ)) ≤ 1 / 4 := by
    have hlim := (tendsto_rpow_neg_atTop
      (by norm_num : (0 : ℝ) < 49 / 80)).comp hbaseTop
    exact Tendsto.eventually_le_const (by norm_num : (0 : ℝ) < 1 / 4) hlim
  have hscale : ∀ᶠ T : ℝ in atTop,
      4 * (((2 ^ 120 : ℕ) : ℝ)) ≤ T ^ (119 / 75 : ℝ) :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 119 / 75)).eventually_ge_atTop
      (4 * (((2 ^ 120 : ℕ) : ℝ)))
  have hleftScale : ∀ᶠ T : ℝ in atTop,
      4 ≤ T ^ (118 / 75 : ℝ) :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 118 / 75)).eventually_ge_atTop 4
  have hleakAll := eventually_routeT_primePowerLeakage_le_of_power_width_const
    (theta := (31 / 80 : ℝ)) (epsilon :=
      routeTSmoothWindowCentralMargin * routeTCommonModeReferenceDensity / 2)
      (by norm_num) (by positivity [routeTSmoothWindowCentralMargin_pos,
        routeTCommonModeReferenceDensity_pos])
  rcases eventually_atTop.1 hleakAll with ⟨Q, hQ⟩
  have hleakThreshold : ∀ᶠ T : ℝ in atTop,
      Q ≤ routeTPrimeGapPacketBase T := hbaseTop.eventually_ge_atTop Q
  filter_upwards [hmass, hcentral, hrefSmall, hbaseLarge, htargetSmall,
      hscale, hleftScale, hleakThreshold,
      eventually_ge_atTop (2 : ℝ)] with T hmassT hcentralT hrefSmallT
        hbase16 htargetBase hscaleT hleftScaleT hthreshold hT
  let x : ℝ := routeTPrimeGapPacketBase T
  let X : ℕ := routeTPrimeGapPacketSupport T
  have hT0 : 0 < T := by linarith
  have hTone : 1 < T := by linarith
  have hx0 : 0 < x := by
    dsimp only [x, routeTPrimeGapPacketBase]
    positivity
  have hx1 : 1 ≤ x := by
    dsimp only [x] at hbase16 ⊢
    linarith
  have hX : 1 ≤ X := by
    apply Nat.ceil_pos.mpr
    change 0 < 3 * x
    positivity
  have hceilLower : 3 * x ≤ (X : ℝ) := by
    dsimp only [X, routeTPrimeGapPacketSupport]
    exact Nat.le_ceil _
  have hceilUpper : (X : ℝ) < 3 * x + 1 := by
    dsimp only [X, routeTPrimeGapPacketSupport]
    exact Nat.ceil_lt_add_one (by positivity)
  have hXx : (X : ℝ) ≤ 4 * x := by linarith
  have hxscale : 4 * x = T ^ (8 / 5 : ℝ) := by
    dsimp only [x, routeTPrimeGapPacketBase]
    field_simp
  have hXscale : (X : ℝ) ≤ T ^ (8 / 5 : ℝ) := by
    rw [← hxscale]
    exact hXx
  have hXscale' : (X : ℝ) ≤ T ^ (120 * (1 / 75 : ℝ)) := by
    convert hXscale using 1 <;> norm_num
  obtain ⟨L, hL, hXL, hLscale⟩ :=
    exists_maynardMoebiusCutoff_sixty (T0 := T) (t := (1 / 75 : ℝ)) (X := X)
      hTone (by norm_num) hXscale'
  have hLscale' : (L : ℝ) ≤ T ^ (2 / 75 : ℝ) := by
    convert hLscale using 1 <;> norm_num
  have hleftMul :
      T ^ (2 / 75 : ℝ) ≤ T ^ (118 / 75 : ℝ) * (T ^ (2 / 75 : ℝ) / 4) := by
    have hmul := mul_le_mul_of_nonneg_right hleftScaleT
      (div_nonneg (Real.rpow_nonneg hT0.le (2 / 75 : ℝ))
        (by norm_num : (0 : ℝ) ≤ 4))
    calc
      T ^ (2 / 75 : ℝ) = 4 * (T ^ (2 / 75 : ℝ) / 4) := by ring
      _ ≤ T ^ (118 / 75 : ℝ) * (T ^ (2 / 75 : ℝ) / 4) := hmul
  have hleftBase : T ^ (2 / 75 : ℝ) ≤ x := by
    calc
      T ^ (2 / 75 : ℝ) ≤
          T ^ (118 / 75 : ℝ) * (T ^ (2 / 75 : ℝ) / 4) := hleftMul
      _ = T ^ (8 / 5 : ℝ) / 4 := by
        rw [show T ^ (118 / 75 : ℝ) * (T ^ (2 / 75 : ℝ) / 4) =
          (T ^ (118 / 75 : ℝ) * T ^ (2 / 75 : ℝ)) / 4 by ring,
          ← Real.rpow_add hT0]
        congr 2
        norm_num
      _ = x := by rfl
  have hLXreal : (L : ℝ) ≤ (X : ℝ) := by
    exact hLscale'.trans (hleftBase.trans (by linarith [hceilLower, hx0]))
  have hLX : L ≤ X := by exact_mod_cast hLXreal
  refine ⟨L, hL, by simpa only [X] using hXL, hLscale', ?_⟩
  intro lambda hlambda hprimeFree
  let H : ℝ := routeTPrimeGapPacketWidth lambda
  let R : ℝ := routeTCommonModeReferenceRelativeWidth x
  let U : ℝ := routeTCommonModeCutoff x
  have hlambda0 : 0 < lambda := hx0.trans_le hlambda.1
  have hlambda2 : 2 ≤ lambda := by linarith [hlambda.1, hbase16]
  have hH0 : 0 < H := by
    dsimp only [H, routeTPrimeGapPacketWidth]
    positivity
  have hR0 : 0 < R := by
    dsimp only [R]
    exact routeTCommonModeReferenceRelativeWidth_pos hx0
  have hHquarter : H ≤ 1 / 4 := by
    have hanti := Real.rpow_le_rpow_of_nonpos hx0 hlambda.1
      (by norm_num : (-(49 / 80 : ℝ)) ≤ 0)
    dsimp only [H, routeTPrimeGapPacketWidth]
    exact hanti.trans (by simpa only [x] using htargetBase)
  have hRquarter : R ≤ 1 / 4 := by simpa only [R, x] using hrefSmallT
  have hscaleLambda :
      (((2 ^ (2 * 60) : ℕ) : ℝ)) * T ^ (1 / 75 : ℝ) ≤ lambda := by
    have hmul :
        (4 * (((2 ^ 120 : ℕ) : ℝ))) * (T ^ (1 / 75 : ℝ) / 4) ≤
          T ^ (119 / 75 : ℝ) * (T ^ (1 / 75 : ℝ) / 4) :=
      mul_le_mul_of_nonneg_right hscaleT
        (div_nonneg (Real.rpow_nonneg hT0.le (1 / 75 : ℝ)) (by norm_num))
    calc
      (((2 ^ (2 * 60) : ℕ) : ℝ)) * T ^ (1 / 75 : ℝ) =
          (4 * (((2 ^ 120 : ℕ) : ℝ))) * (T ^ (1 / 75 : ℝ) / 4) := by
            norm_num; ring
      _ ≤ T ^ (119 / 75 : ℝ) * (T ^ (1 / 75 : ℝ) / 4) := hmul
      _ = T ^ (8 / 5 : ℝ) / 4 := by
        rw [show T ^ (119 / 75 : ℝ) * (T ^ (1 / 75 : ℝ) / 4) =
          (T ^ (119 / 75 : ℝ) * T ^ (1 / 75 : ℝ)) / 4 by ring,
          ← Real.rpow_add hT0]
        congr 2
        norm_num
      _ = x := by rfl
      _ ≤ lambda := hlambda.1
  have hpowerEq : lambda ^ (31 / 80 : ℝ) = lambda * H := by
    dsimp only [H, routeTPrimeGapPacketWidth]
    calc
      lambda ^ (31 / 80 : ℝ) = lambda ^ (1 + (-(49 / 80 : ℝ))) := by
        congr 1
        norm_num
      _ = lambda ^ (1 : ℝ) * lambda ^ (-(49 / 80 : ℝ)) :=
        Real.rpow_add hlambda0 1 (-(49 / 80 : ℝ))
      _ = lambda * lambda ^ (-(49 / 80 : ℝ)) := by rw [Real.rpow_one]
  have hphysicalH1 : 1 ≤ lambda * H := by
    rw [← hpowerEq]
    exact Real.one_le_rpow (by linarith) (by norm_num)
  have hphysicalHle : lambda * H ≤ lambda := by
    calc
      lambda * H ≤ lambda * 1 :=
        mul_le_mul_of_nonneg_left (hHquarter.trans (by norm_num)) hlambda0.le
      _ = lambda := by ring
  have hwidthH : 1 ≤ 2 * (lambda * H) := by linarith
  have hsupportQuarter : lambda + 2 * (lambda / 4) ≤ (X : ℝ) := by
    calc
      lambda + 2 * (lambda / 4) = (3 / 2 : ℝ) * lambda := by ring
      _ ≤ (3 / 2 : ℝ) * (2 * x) :=
        mul_le_mul_of_nonneg_left hlambda.2 (by norm_num)
      _ = 3 * x := by ring
      _ ≤ (X : ℝ) := hceilLower
  have hHmul : lambda * H ≤ lambda / 4 := by
    calc
      lambda * H ≤ lambda * (1 / 4) :=
        mul_le_mul_of_nonneg_left hHquarter hlambda0.le
      _ = lambda / 4 := by ring
  have hRmul : lambda * R ≤ lambda / 4 := by
    calc
      lambda * R ≤ lambda * (1 / 4) :=
        mul_le_mul_of_nonneg_left hRquarter hlambda0.le
      _ = lambda / 4 := by ring
  have hsupportH : lambda + 2 * (lambda * H) ≤ (X : ℝ) := by
    calc
      lambda + 2 * (lambda * H) ≤ lambda + 2 * (lambda / 4) :=
        add_le_add_right
          (mul_le_mul_of_nonneg_left hHmul (by norm_num : (0 : ℝ) ≤ 2)) lambda
      _ ≤ (X : ℝ) := hsupportQuarter
  have hsupportR : lambda + 2 * (lambda * R) ≤ (X : ℝ) := by
    calc
      lambda + 2 * (lambda * R) ≤ lambda + 2 * (lambda / 4) :=
        add_le_add_right
          (mul_le_mul_of_nonneg_left hRmul (by norm_num : (0 : ℝ) ≤ 2)) lambda
      _ ≤ (X : ℝ) := hsupportQuarter
  have hleakage := hQ lambda (hthreshold.trans hlambda.1) (lambda * H)
    (by rw [← hpowerEq]) hphysicalHle
  have href := hmassT lambda (by simpa only [x] using hlambda)
  have hlow := hcentralT L hL (by simpa only [X] using hLX) lambda
    (by simpa only [x] using hlambda)
  have hresult := primeFree_forces_fixedSource_commonMode_highTail
    L X 60 hXL (T0 := T) (t := (1 / 75 : ℝ)) (x := x) (lambda := lambda)
      (H := H) (R := R) (U := U) (rho := routeTCommonModeReferenceDensity)
      hx0 hlambda hTone hscaleLambda hlambda2 hH0 hR0
      routeTCommonModeReferenceDensity_pos hwidthH hsupportH hsupportR
      hprimeFree href.le hleakage (by simpa only [x, X, H, R, U] using hlow)
  simpa only [x, X, H, R, U] using hresult

end

end RHTower.Sieve
