import GaloisForLFunctions.RHTower.CompactL2FourierRootDivision
import GaloisForLFunctions.RHTower.Suzuki.SuzukiH01FormDomain

/-!
# Route U compact-root admission to Suzuki's logarithmic form domain

The exact two-root factorization supplies a reciprocal-frequency tail for the divided odd
descendant.  Together with its compact time support, this gives finite Suzuki logarithmic Fourier
energy and hence membership in the exact aperture form domain.
-/

open Complex MeasureTheory Set
open scoped ENNReal FourierTransform

noncomputable section

namespace RHTower

theorem routeURealFourier_neg_two_pi_eq_fourier
    (h : ℝ → ℂ) (ξ : ℝ) :
    routeURealFourier h (-2 * Real.pi * ξ) = 𝓕 h ξ := by
  rw [routeURealFourier, Real.fourier_real_eq_integral_exp_smul]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with x
  change h x * Complex.exp (Complex.I * ((-2 * Real.pi * ξ : ℝ) : ℂ) * (x : ℂ)) =
    Complex.exp ((-2 * Real.pi * x * ξ : ℝ) * Complex.I) * h x
  rw [mul_comm]
  congr 1
  push_cast
  ring_nf

theorem norm_routeURealFourier_le_integral_norm
    {h : ℝ → ℂ} (w : ℝ) :
    ‖routeURealFourier h w‖ ≤ ∫ x : ℝ, ‖h x‖ := by
  rw [routeURealFourier]
  calc
    ‖∫ x : ℝ, h x * routeURealFourierPhase w x‖ ≤
        ∫ x : ℝ, ‖h x * routeURealFourierPhase w x‖ :=
      norm_integral_le_integral_norm _
    _ = ∫ x : ℝ, ‖h x‖ := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards with x
      rw [norm_mul, norm_routeURealFourierPhase, mul_one]

theorem norm_routeURealOddRootDividedTime_fourier_le_tail
    {b d c : ℝ} (hbd : b ≤ d) {h : ℝ → ℂ} (hh : Integrable h)
    (hsupp : ∀ y, y ≤ b ∨ d ≤ y → h y = 0)
    (hc : routeURealFourier h c = 0) (hnegc : routeURealFourier h (-c) = 0)
    (hc0 : c ≠ 0) {w : ℝ} (hw : 2 * |c| ≤ |w|) :
    ‖routeURealFourier (routeURealOddRootDividedTime b c h) w‖ ≤
      2 * (∫ x : ℝ, ‖h x‖) / |w| := by
  have hwpos : 0 < |w| := by
    have hcpos : 0 < |c| := abs_pos.mpr hc0
    linarith
  have hfac := routeURealOddRootDividedTime_fourier_factor
    hbd hh hsupp hc hnegc hc0 w
  have hnorm := congrArg norm hfac
  rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs] at hnorm
  have hc_sq : 4 * c ^ 2 ≤ w ^ 2 := by
    have hsquare := (sq_le_sq₀
      (mul_nonneg (by norm_num) (abs_nonneg c)) (abs_nonneg w)).2 hw
    nlinarith [sq_abs c, sq_abs w]
  have hdiff_nonneg : 0 ≤ w ^ 2 - c ^ 2 := by nlinarith
  have hden : w ^ 2 / 2 ≤ |w ^ 2 - c ^ 2| := by
    rw [abs_of_nonneg hdiff_nonneg]
    nlinarith
  have hhbound := norm_routeURealFourier_le_integral_norm (h := h) w
  have hHint : 0 ≤ ∫ x : ℝ, ‖h x‖ := integral_nonneg fun _ => norm_nonneg _
  have hq0 : 0 ≤ ‖routeURealFourier
      (routeURealOddRootDividedTime b c h) w‖ := norm_nonneg _
  have hmul : |w| * ‖routeURealFourier
      (routeURealOddRootDividedTime b c h) w‖ ≤
      2 * (∫ x : ℝ, ‖h x‖) := by
    have hleft : (w ^ 2 / 2) * ‖routeURealFourier
        (routeURealOddRootDividedTime b c h) w‖ ≤
        |w ^ 2 - c ^ 2| * ‖routeURealFourier
          (routeURealOddRootDividedTime b c h) w‖ :=
      mul_le_mul_of_nonneg_right hden hq0
    have hright : |w| * ‖routeURealFourier h w‖ ≤
        |w| * (∫ x : ℝ, ‖h x‖) :=
      mul_le_mul_of_nonneg_left hhbound (abs_nonneg w)
    rw [hnorm] at hleft
    have hw_sq : w ^ 2 = |w| ^ 2 := by nlinarith [sq_abs w]
    rw [hw_sq] at hleft
    nlinarith
  exact (le_div_iff₀ hwpos).2 (by simpa [mul_comm] using hmul)

def routeURealOddRootFourierGlobalBound (b c : ℝ) (h : ℝ → ℂ) : ℝ :=
  ∫ x : ℝ, ‖routeURealOddRootDividedTime b c h x‖

def routeURealOddRootFourierReciprocalBound (b c : ℝ) (h : ℝ → ℂ) : ℝ :=
  max (2 * |c| * routeURealOddRootFourierGlobalBound b c h)
    (2 * ∫ x : ℝ, ‖h x‖)

theorem routeURealOddRootFourierGlobalBound_nonneg
    (b c : ℝ) (h : ℝ → ℂ) :
    0 ≤ routeURealOddRootFourierGlobalBound b c h := by
  exact integral_nonneg fun _ => norm_nonneg _

theorem routeURealOddRootFourierReciprocalBound_nonneg
    (b c : ℝ) (h : ℝ → ℂ) :
    0 ≤ routeURealOddRootFourierReciprocalBound b c h := by
  unfold routeURealOddRootFourierReciprocalBound
  exact le_trans
    (mul_nonneg (mul_nonneg (by norm_num) (abs_nonneg c))
      (routeURealOddRootFourierGlobalBound_nonneg b c h))
    (le_max_left _ _)

theorem norm_routeURealOddRootDividedTime_fourier_le_global
    (b c : ℝ) (h : ℝ → ℂ) (w : ℝ) :
    ‖routeURealFourier (routeURealOddRootDividedTime b c h) w‖ ≤
      routeURealOddRootFourierGlobalBound b c h := by
  exact norm_routeURealFourier_le_integral_norm
    (h := routeURealOddRootDividedTime b c h) w

theorem norm_routeURealOddRootDividedTime_fourier_le_reciprocal
    {b d c : ℝ} (hbd : b ≤ d) {h : ℝ → ℂ} (hh : Integrable h)
    (hsupp : ∀ y, y ≤ b ∨ d ≤ y → h y = 0)
    (hc : routeURealFourier h c = 0) (hnegc : routeURealFourier h (-c) = 0)
    (hc0 : c ≠ 0) {w : ℝ} (hw0 : w ≠ 0) :
    ‖routeURealFourier (routeURealOddRootDividedTime b c h) w‖ ≤
      routeURealOddRootFourierReciprocalBound b c h / |w| := by
  let C := routeURealOddRootFourierGlobalBound b c h
  let H := ∫ x : ℝ, ‖h x‖
  let M := routeURealOddRootFourierReciprocalBound b c h
  have hC0 : 0 ≤ C := routeURealOddRootFourierGlobalBound_nonneg b c h
  have hH0 : 0 ≤ H := integral_nonneg fun _ => norm_nonneg _
  have hM0 : 0 ≤ M := routeURealOddRootFourierReciprocalBound_nonneg b c h
  have hwpos : 0 < |w| := abs_pos.mpr hw0
  by_cases htail : 2 * |c| ≤ |w|
  · have hq := norm_routeURealOddRootDividedTime_fourier_le_tail
      hbd hh hsupp hc hnegc hc0 htail
    have hHM : 2 * H ≤ M := by
      dsimp [M, routeURealOddRootFourierReciprocalBound]
      exact le_max_right _ _
    exact hq.trans (div_le_div_of_nonneg_right hHM hwpos.le)
  · have hq := norm_routeURealOddRootDividedTime_fourier_le_global
      b c h w
    have hwsmall : |w| ≤ 2 * |c| := le_of_not_ge htail
    have hCM : C * |w| ≤ M := by
      calc
        C * |w| ≤ C * (2 * |c|) :=
          mul_le_mul_of_nonneg_left hwsmall hC0
        _ = 2 * |c| * C := by ring
        _ ≤ M := by
          dsimp [M, routeURealOddRootFourierReciprocalBound]
          exact le_max_left _ _
    exact hq.trans ((le_div_iff₀ hwpos).2 hCM)

theorem norm_fourier_routeURealOddRootDividedTime_le_envelope
    {b d c : ℝ} (hbd : b ≤ d) {h : ℝ → ℂ} (hh : Integrable h)
    (hsupp : ∀ y, y ≤ b ∨ d ≤ y → h y = 0)
    (hc : routeURealFourier h c = 0) (hnegc : routeURealFourier h (-c) = 0)
    (hc0 : c ≠ 0) {ξ : ℝ} (hξ0 : ξ ≠ 0) :
    ‖𝓕 (routeURealOddRootDividedTime b c h) ξ‖ ≤
      min |routeURealOddRootFourierGlobalBound b c h|
        (|routeURealOddRootFourierReciprocalBound b c h| / |ξ|) := by
  let q := routeURealOddRootDividedTime b c h
  let C := routeURealOddRootFourierGlobalBound b c h
  let M := routeURealOddRootFourierReciprocalBound b c h
  have hC0 : 0 ≤ C := routeURealOddRootFourierGlobalBound_nonneg b c h
  have hM0 : 0 ≤ M := routeURealOddRootFourierReciprocalBound_nonneg b c h
  rw [le_min_iff]
  constructor
  · rw [← routeURealFourier_neg_two_pi_eq_fourier]
    simpa [C, abs_of_nonneg hC0] using
      norm_routeURealOddRootDividedTime_fourier_le_global
        b c h (-2 * Real.pi * ξ)
  · rw [← routeURealFourier_neg_two_pi_eq_fourier]
    have hw0 : -2 * Real.pi * ξ ≠ 0 := by
      exact mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) hξ0
    have htail := norm_routeURealOddRootDividedTime_fourier_le_reciprocal
      hbd hh hsupp hc hnegc hc0 hw0
    have hscale : |(-2 * Real.pi * ξ : ℝ)| = 2 * Real.pi * |ξ| := by
      rw [abs_mul, abs_mul, abs_neg, abs_of_pos Real.pi_pos]
      norm_num
    rw [hscale] at htail
    rw [abs_of_nonneg hM0]
    refine htail.trans ?_
    apply div_le_div_of_nonneg_left hM0 (abs_pos.mpr hξ0)
    nlinarith [Real.pi_gt_three, abs_pos.mpr hξ0]

theorem integrable_routeURealOddRootDividedTime_hlogEnergy
    {b d c : ℝ} (hbd : b ≤ d) {h : ℝ → ℂ} (hh : Integrable h)
    (hsupp : ∀ y, y ≤ b ∨ d ≤ y → h y = 0)
    (hc : routeURealFourier h c = 0) (hnegc : routeURealFourier h (-c) = 0)
    (hc0 : c ≠ 0) :
    Integrable (fun ξ : ℝ => suzukiLogWeight ξ *
      ‖𝓕 (routeURealOddRootDividedTime b c h) ξ‖ ^ 2) := by
  let q := routeURealOddRootDividedTime b c h
  have hq1 : Integrable q :=
    integrable_routeURealOddRootDividedTime hbd hh hsupp hc hnegc hc0
  exact integrable_suzukiLogWeight_norm_sq_of_general_fourier_envelope
    (𝓕 q)
    (routeURealOddRootFourierGlobalBound b c h)
    (routeURealOddRootFourierReciprocalBound b c h)
    (GaloisForLFunctions.RHTower.continuous_fourier_of_integrable hq1).aestronglyMeasurable
    (fun ξ hξ => norm_fourier_routeURealOddRootDividedTime_le_envelope
      hbd hh hsupp hc hnegc hc0 hξ)

/-! ## Even symmetric-root quotient -/

def routeURealTwiceRootFourierGlobalBound (b c : ℝ) (h : ℝ → ℂ) : ℝ :=
  ∫ x : ℝ, ‖routeURealTwiceRootDividedTime b c h x‖

def routeURealTwiceRootFourierRadius (c : ℝ) : ℝ :=
  max (2 * |c|) 1

def routeURealTwiceRootFourierReciprocalBound (b c : ℝ) (h : ℝ → ℂ) : ℝ :=
  max (routeURealTwiceRootFourierRadius c *
      routeURealTwiceRootFourierGlobalBound b c h)
    (2 * ∫ x : ℝ, ‖h x‖)

theorem routeURealTwiceRootFourierGlobalBound_nonneg
    (b c : ℝ) (h : ℝ → ℂ) :
    0 ≤ routeURealTwiceRootFourierGlobalBound b c h := by
  exact integral_nonneg fun _ => norm_nonneg _

theorem routeURealTwiceRootFourierRadius_pos (c : ℝ) :
    0 < routeURealTwiceRootFourierRadius c := by
  unfold routeURealTwiceRootFourierRadius
  exact lt_of_lt_of_le zero_lt_one (le_max_right _ _)

theorem routeURealTwiceRootFourierReciprocalBound_nonneg
    (b c : ℝ) (h : ℝ → ℂ) :
    0 ≤ routeURealTwiceRootFourierReciprocalBound b c h := by
  unfold routeURealTwiceRootFourierReciprocalBound
  exact le_trans
    (mul_nonneg (routeURealTwiceRootFourierRadius_pos c).le
      (routeURealTwiceRootFourierGlobalBound_nonneg b c h))
    (le_max_left _ _)

theorem norm_routeURealTwiceRootDividedTime_fourier_le_global
    (b c : ℝ) (h : ℝ → ℂ) (w : ℝ) :
    ‖routeURealFourier (routeURealTwiceRootDividedTime b c h) w‖ ≤
      routeURealTwiceRootFourierGlobalBound b c h := by
  exact norm_routeURealFourier_le_integral_norm
    (h := routeURealTwiceRootDividedTime b c h) w

theorem norm_routeURealTwiceRootDividedTime_fourier_le_tail
    {b d c : ℝ} (hbd : b ≤ d) {h : ℝ → ℂ} (hh : Integrable h)
    (hsupp : ∀ y, y ≤ b ∨ d ≤ y → h y = 0)
    (hc : routeURealFourier h c = 0) (hnegc : routeURealFourier h (-c) = 0)
    (hc0 : c ≠ 0) {w : ℝ}
    (hw : routeURealTwiceRootFourierRadius c ≤ |w|) :
    ‖routeURealFourier (routeURealTwiceRootDividedTime b c h) w‖ ≤
      2 * (∫ x : ℝ, ‖h x‖) / |w| := by
  have htwo : 2 * |c| ≤ |w| :=
    le_trans (le_max_left _ _) hw
  have hone : 1 ≤ |w| :=
    le_trans (le_max_right _ _) hw
  have hwpos : 0 < |w| := lt_of_lt_of_le zero_lt_one hone
  have hfac := routeURealTwiceRootDividedTime_fourier_factor
    hbd hh hsupp hc hnegc hc0 w
  have hnorm := congrArg norm hfac
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs] at hnorm
  have hc_sq : 4 * c ^ 2 ≤ w ^ 2 := by
    have hsquare := (sq_le_sq₀
      (mul_nonneg (by norm_num) (abs_nonneg c)) (abs_nonneg w)).2 htwo
    nlinarith [sq_abs c, sq_abs w]
  have hdiff_nonneg : 0 ≤ w ^ 2 - c ^ 2 := by nlinarith
  have hden : w ^ 2 / 2 ≤ |w ^ 2 - c ^ 2| := by
    rw [abs_of_nonneg hdiff_nonneg]
    nlinarith
  have hhbound := norm_routeURealFourier_le_integral_norm (h := h) w
  have hHint : 0 ≤ ∫ x : ℝ, ‖h x‖ := integral_nonneg fun _ => norm_nonneg _
  have hq0 : 0 ≤ ‖routeURealFourier
      (routeURealTwiceRootDividedTime b c h) w‖ := norm_nonneg _
  have hleft : (w ^ 2 / 2) * ‖routeURealFourier
      (routeURealTwiceRootDividedTime b c h) w‖ ≤
      |w ^ 2 - c ^ 2| * ‖routeURealFourier
        (routeURealTwiceRootDividedTime b c h) w‖ :=
    mul_le_mul_of_nonneg_right hden hq0
  rw [hnorm] at hleft
  have hw_sq : w ^ 2 = |w| ^ 2 := by nlinarith [sq_abs w]
  rw [hw_sq] at hleft
  have hmul : |w| * ‖routeURealFourier
      (routeURealTwiceRootDividedTime b c h) w‖ ≤
      2 * (∫ x : ℝ, ‖h x‖) := by
    nlinarith
  exact (le_div_iff₀ hwpos).2 (by simpa [mul_comm] using hmul)

theorem norm_routeURealTwiceRootDividedTime_fourier_le_reciprocal
    {b d c : ℝ} (hbd : b ≤ d) {h : ℝ → ℂ} (hh : Integrable h)
    (hsupp : ∀ y, y ≤ b ∨ d ≤ y → h y = 0)
    (hc : routeURealFourier h c = 0) (hnegc : routeURealFourier h (-c) = 0)
    (hc0 : c ≠ 0) {w : ℝ} (hw0 : w ≠ 0) :
    ‖routeURealFourier (routeURealTwiceRootDividedTime b c h) w‖ ≤
      routeURealTwiceRootFourierReciprocalBound b c h / |w| := by
  let C := routeURealTwiceRootFourierGlobalBound b c h
  let R := routeURealTwiceRootFourierRadius c
  let H := ∫ x : ℝ, ‖h x‖
  let M := routeURealTwiceRootFourierReciprocalBound b c h
  have hC0 : 0 ≤ C := routeURealTwiceRootFourierGlobalBound_nonneg b c h
  have hM0 : 0 ≤ M := routeURealTwiceRootFourierReciprocalBound_nonneg b c h
  have hwpos : 0 < |w| := abs_pos.mpr hw0
  by_cases htail : R ≤ |w|
  · have hq := norm_routeURealTwiceRootDividedTime_fourier_le_tail
      hbd hh hsupp hc hnegc hc0 htail
    have hHM : 2 * H ≤ M := by
      dsimp [M, H, routeURealTwiceRootFourierReciprocalBound]
      exact le_max_right _ _
    exact hq.trans (div_le_div_of_nonneg_right hHM hwpos.le)
  · have hq := norm_routeURealTwiceRootDividedTime_fourier_le_global b c h w
    have hwsmall : |w| ≤ R := le_of_not_ge htail
    have hCM : C * |w| ≤ M := by
      calc
        C * |w| ≤ C * R := mul_le_mul_of_nonneg_left hwsmall hC0
        _ = R * C := by ring
        _ ≤ M := by
          dsimp [M, R, C, routeURealTwiceRootFourierReciprocalBound]
          exact le_max_left _ _
    exact hq.trans ((le_div_iff₀ hwpos).2 hCM)

theorem norm_fourier_routeURealTwiceRootDividedTime_le_envelope
    {b d c : ℝ} (hbd : b ≤ d) {h : ℝ → ℂ} (hh : Integrable h)
    (hsupp : ∀ y, y ≤ b ∨ d ≤ y → h y = 0)
    (hc : routeURealFourier h c = 0) (hnegc : routeURealFourier h (-c) = 0)
    (hc0 : c ≠ 0) {ξ : ℝ} (hξ0 : ξ ≠ 0) :
    ‖𝓕 (routeURealTwiceRootDividedTime b c h) ξ‖ ≤
      min |routeURealTwiceRootFourierGlobalBound b c h|
        (|routeURealTwiceRootFourierReciprocalBound b c h| / |ξ|) := by
  let C := routeURealTwiceRootFourierGlobalBound b c h
  let M := routeURealTwiceRootFourierReciprocalBound b c h
  have hC0 : 0 ≤ C := routeURealTwiceRootFourierGlobalBound_nonneg b c h
  have hM0 : 0 ≤ M := routeURealTwiceRootFourierReciprocalBound_nonneg b c h
  rw [le_min_iff]
  constructor
  · rw [← routeURealFourier_neg_two_pi_eq_fourier]
    simpa [C, abs_of_nonneg hC0] using
      norm_routeURealTwiceRootDividedTime_fourier_le_global
        b c h (-2 * Real.pi * ξ)
  · rw [← routeURealFourier_neg_two_pi_eq_fourier]
    have hw0 : -2 * Real.pi * ξ ≠ 0 := by
      exact mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) hξ0
    have htail := norm_routeURealTwiceRootDividedTime_fourier_le_reciprocal
      hbd hh hsupp hc hnegc hc0 hw0
    have hscale : |(-2 * Real.pi * ξ : ℝ)| = 2 * Real.pi * |ξ| := by
      rw [abs_mul, abs_mul, abs_neg, abs_of_pos Real.pi_pos]
      norm_num
    rw [hscale] at htail
    rw [abs_of_nonneg hM0]
    refine htail.trans ?_
    apply div_le_div_of_nonneg_left hM0 (abs_pos.mpr hξ0)
    nlinarith [Real.pi_gt_three, abs_pos.mpr hξ0]

theorem integrable_routeURealTwiceRootDividedTime_hlogEnergy
    {b d c : ℝ} (hbd : b ≤ d) {h : ℝ → ℂ} (hh : Integrable h)
    (hsupp : ∀ y, y ≤ b ∨ d ≤ y → h y = 0)
    (hc : routeURealFourier h c = 0) (hnegc : routeURealFourier h (-c) = 0)
    (hc0 : c ≠ 0) :
    Integrable (fun ξ : ℝ => suzukiLogWeight ξ *
      ‖𝓕 (routeURealTwiceRootDividedTime b c h) ξ‖ ^ 2) := by
  let q := routeURealTwiceRootDividedTime b c h
  have hq1 : Integrable q :=
    integrable_routeURealTwiceRootDividedTime hbd hh hsupp hc hnegc hc0
  exact integrable_suzukiLogWeight_norm_sq_of_general_fourier_envelope
    (𝓕 q)
    (routeURealTwiceRootFourierGlobalBound b c h)
    (routeURealTwiceRootFourierReciprocalBound b c h)
    (GaloisForLFunctions.RHTower.continuous_fourier_of_integrable hq1).aestronglyMeasurable
    (fun ξ hξ => norm_fourier_routeURealTwiceRootDividedTime_le_envelope
      hbd hh hsupp hc hnegc hc0 hξ)

theorem fourier_routeURealTwiceRootDividedTime_factor
    {b d c : ℝ} (hbd : b ≤ d) {h : ℝ → ℂ} (hh : Integrable h)
    (hsupp : ∀ y, y ≤ b ∨ d ≤ y → h y = 0)
    (hc : routeURealFourier h c = 0) (hnegc : routeURealFourier h (-c) = 0)
    (hc0 : c ≠ 0) (ξ : ℝ) :
    ((((-2 * Real.pi * ξ) ^ 2 - c ^ 2 : ℝ) : ℂ) *
      𝓕 (routeURealTwiceRootDividedTime b c h) ξ) = 𝓕 h ξ := by
  rw [← routeURealFourier_neg_two_pi_eq_fourier,
    ← routeURealFourier_neg_two_pi_eq_fourier]
  exact routeURealTwiceRootDividedTime_fourier_factor
    hbd hh hsupp hc hnegc hc0 (-2 * Real.pi * ξ)

theorem indicator_routeURealTwiceRootDividedTime
    (a : SuzukiPositiveAperture) {c : ℝ} {h : ℝ → ℂ} (hh : Integrable h)
    (hsupp : ∀ y, y ≤ -a.1 ∨ a.1 ≤ y → h y = 0)
    (hc : routeURealFourier h c = 0) (hnegc : routeURealFourier h (-c) = 0)
    (hc0 : c ≠ 0) :
    (Icc (-a.1) a.1).indicator
        (routeURealTwiceRootDividedTime (-a.1) c h) =
      routeURealTwiceRootDividedTime (-a.1) c h := by
  funext x
  by_cases hx : x ∈ Icc (-a.1) a.1
  · rw [indicator_of_mem hx]
  · rw [indicator_of_notMem hx]
    apply (routeURealTwiceRootDividedTime_support
      (by linarith [a.2]) hh hsupp hc hnegc hc0 x ?_).symm
    simp only [mem_Icc, not_and_or, not_le] at hx
    exact hx.imp le_of_lt le_of_lt

/-- The even quotient after removing the symmetric roots is also an actual vector in Suzuki's
exact form domain at unchanged aperture. -/
def routeURealTwiceRootDividedSuzukiFormVector
    (a : SuzukiPositiveAperture) (c : ℝ) (h : ℝ → ℂ) (hh : Integrable h)
    (hsupp : ∀ y, y ≤ -a.1 ∨ a.1 ≤ y → h y = 0)
    (hc : routeURealFourier h c = 0) (hnegc : routeURealFourier h (-c) = 0)
    (hc0 : c ≠ 0) : SuzukiHlogFormDomain a :=
  let hbd : -a.1 ≤ a.1 := by linarith [a.2]
  let q := routeURealTwiceRootDividedTime (-a.1) c h
  let hq1 : Integrable q :=
    integrable_routeURealTwiceRootDividedTime hbd hh hsupp hc hnegc hc0
  let hq2 : MemLp q 2 (volume : Measure ℝ) :=
    memLp_routeURealTwiceRootDividedTime hbd hh hsupp hc hnegc hc0
  let henergy : Integrable (fun ξ : ℝ => suzukiLogWeight ξ * ‖𝓕 q ξ‖ ^ 2) :=
    integrable_routeURealTwiceRootDividedTime_hlogEnergy
      hbd hh hsupp hc hnegc hc0
  suzukiHlogFormVectorOfFunction a q hq1 hq2 henergy
    (indicator_routeURealTwiceRootDividedTime a hh hsupp hc hnegc hc0)

theorem suzukiHlogFormEmbedding_routeURealTwiceRootDividedSuzukiFormVector
    (a : SuzukiPositiveAperture) (c : ℝ) (h : ℝ → ℂ) (hh : Integrable h)
    (hsupp : ∀ y, y ≤ -a.1 ∨ a.1 ≤ y → h y = 0)
    (hc : routeURealFourier h c = 0) (hnegc : routeURealFourier h (-c) = 0)
    (hc0 : c ≠ 0) :
    suzukiHlogFormEmbedding a
        (routeURealTwiceRootDividedSuzukiFormVector
          a c h hh hsupp hc hnegc hc0) =
      (memLp_routeURealTwiceRootDividedTime (by linarith [a.2])
        hh hsupp hc hnegc hc0).toLp
        (routeURealTwiceRootDividedTime (-a.1) c h) := by
  unfold routeURealTwiceRootDividedSuzukiFormVector
  apply suzukiHlogFormEmbedding_formVectorOfFunction

theorem routeURealTwiceRootDividedSuzukiFormVector_coeFn
    (a : SuzukiPositiveAperture) (c : ℝ) (h : ℝ → ℂ) (hh : Integrable h)
    (hsupp : ∀ y, y ≤ -a.1 ∨ a.1 ≤ y → h y = 0)
    (hc : routeURealFourier h c = 0) (hnegc : routeURealFourier h (-c) = 0)
    (hc0 : c ≠ 0) :
    (((routeURealTwiceRootDividedSuzukiFormVector
      a c h hh hsupp hc hnegc hc0).1 : SuzukiHlogFourierL2) : ℝ → ℂ)
      =ᵐ[suzukiHlogMeasure]
        𝓕 (routeURealTwiceRootDividedTime (-a.1) c h) := by
  unfold routeURealTwiceRootDividedSuzukiFormVector
  exact suzukiHlogFourierVector_coeFn
    (routeURealTwiceRootDividedTime (-a.1) c h)
    (integrable_routeURealTwiceRootDividedTime
      (by linarith [a.2]) hh hsupp hc hnegc hc0)
    (integrable_routeURealTwiceRootDividedTime_hlogEnergy
      (by linarith [a.2]) hh hsupp hc hnegc hc0)

theorem routeURealTwiceRootDividedSuzukiFormVector_factor_ae
    (a : SuzukiPositiveAperture) (c : ℝ) (h : ℝ → ℂ) (hh : Integrable h)
    (hsupp : ∀ y, y ≤ -a.1 ∨ a.1 ≤ y → h y = 0)
    (hc : routeURealFourier h c = 0) (hnegc : routeURealFourier h (-c) = 0)
    (hc0 : c ≠ 0) :
    ∀ᵐ ξ ∂suzukiHlogMeasure,
      (((-2 * Real.pi * ξ) ^ 2 - c ^ 2 : ℝ) : ℂ) *
          (routeURealTwiceRootDividedSuzukiFormVector
            a c h hh hsupp hc hnegc hc0).1 ξ = 𝓕 h ξ := by
  filter_upwards [routeURealTwiceRootDividedSuzukiFormVector_coeFn
    a c h hh hsupp hc hnegc hc0] with ξ hξ
  rw [hξ]
  exact fourier_routeURealTwiceRootDividedTime_factor
    (by linarith [a.2]) hh hsupp hc hnegc hc0 ξ

theorem fourier_routeURealOddRootDividedTime_factor
    {b d c : ℝ} (hbd : b ≤ d) {h : ℝ → ℂ} (hh : Integrable h)
    (hsupp : ∀ y, y ≤ b ∨ d ≤ y → h y = 0)
    (hc : routeURealFourier h c = 0) (hnegc : routeURealFourier h (-c) = 0)
    (hc0 : c ≠ 0) (ξ : ℝ) :
    ((((-2 * Real.pi * ξ) ^ 2 - c ^ 2 : ℝ) : ℂ) *
      𝓕 (routeURealOddRootDividedTime b c h) ξ) =
        ((-2 * Real.pi * ξ : ℝ) : ℂ) * 𝓕 h ξ := by
  rw [← routeURealFourier_neg_two_pi_eq_fourier,
    ← routeURealFourier_neg_two_pi_eq_fourier]
  exact routeURealOddRootDividedTime_fourier_factor
    hbd hh hsupp hc hnegc hc0 (-2 * Real.pi * ξ)

theorem indicator_routeURealOddRootDividedTime
    (a : SuzukiPositiveAperture) {c : ℝ} {h : ℝ → ℂ} (hh : Integrable h)
    (hsupp : ∀ y, y ≤ -a.1 ∨ a.1 ≤ y → h y = 0)
    (hc : routeURealFourier h c = 0) (hnegc : routeURealFourier h (-c) = 0)
    (hc0 : c ≠ 0) :
    (Icc (-a.1) a.1).indicator
        (routeURealOddRootDividedTime (-a.1) c h) =
      routeURealOddRootDividedTime (-a.1) c h := by
  funext x
  by_cases hx : x ∈ Icc (-a.1) a.1
  · rw [indicator_of_mem hx]
  · rw [indicator_of_notMem hx]
    apply (routeURealOddRootDividedTime_support
      (by linarith [a.2]) hh hsupp hc hnegc hc0 x ?_).symm
    simp only [mem_Icc, not_and_or, not_le] at hx
    exact hx.imp le_of_lt le_of_lt

/-- The symmetric real-root odd descendant is an actual vector in Suzuki's exact critical
aperture form domain.  No smoothness or prior logarithmic-energy premise is required. -/
def routeURealOddRootDividedSuzukiFormVector
    (a : SuzukiPositiveAperture) (c : ℝ) (h : ℝ → ℂ) (hh : Integrable h)
    (hsupp : ∀ y, y ≤ -a.1 ∨ a.1 ≤ y → h y = 0)
    (hc : routeURealFourier h c = 0) (hnegc : routeURealFourier h (-c) = 0)
    (hc0 : c ≠ 0) : SuzukiHlogFormDomain a :=
  let hbd : -a.1 ≤ a.1 := by linarith [a.2]
  let q := routeURealOddRootDividedTime (-a.1) c h
  let hq1 : Integrable q :=
    integrable_routeURealOddRootDividedTime hbd hh hsupp hc hnegc hc0
  let hq2 : MemLp q 2 (volume : Measure ℝ) :=
    memLp_routeURealOddRootDividedTime hbd hh hsupp hc hnegc hc0
  let henergy : Integrable (fun ξ : ℝ => suzukiLogWeight ξ * ‖𝓕 q ξ‖ ^ 2) :=
    integrable_routeURealOddRootDividedTime_hlogEnergy
      hbd hh hsupp hc hnegc hc0
  suzukiHlogFormVectorOfFunction a q hq1 hq2 henergy
    (indicator_routeURealOddRootDividedTime a hh hsupp hc hnegc hc0)

theorem suzukiHlogFormEmbedding_routeURealOddRootDividedSuzukiFormVector
    (a : SuzukiPositiveAperture) (c : ℝ) (h : ℝ → ℂ) (hh : Integrable h)
    (hsupp : ∀ y, y ≤ -a.1 ∨ a.1 ≤ y → h y = 0)
    (hc : routeURealFourier h c = 0) (hnegc : routeURealFourier h (-c) = 0)
    (hc0 : c ≠ 0) :
    suzukiHlogFormEmbedding a
        (routeURealOddRootDividedSuzukiFormVector
          a c h hh hsupp hc hnegc hc0) =
      (memLp_routeURealOddRootDividedTime (by linarith [a.2])
        hh hsupp hc hnegc hc0).toLp
        (routeURealOddRootDividedTime (-a.1) c h) := by
  unfold routeURealOddRootDividedSuzukiFormVector
  apply suzukiHlogFormEmbedding_formVectorOfFunction

theorem routeURealOddRootDividedSuzukiFormVector_coeFn
    (a : SuzukiPositiveAperture) (c : ℝ) (h : ℝ → ℂ) (hh : Integrable h)
    (hsupp : ∀ y, y ≤ -a.1 ∨ a.1 ≤ y → h y = 0)
    (hc : routeURealFourier h c = 0) (hnegc : routeURealFourier h (-c) = 0)
    (hc0 : c ≠ 0) :
    (((routeURealOddRootDividedSuzukiFormVector
      a c h hh hsupp hc hnegc hc0).1 : SuzukiHlogFourierL2) : ℝ → ℂ)
      =ᵐ[suzukiHlogMeasure]
        𝓕 (routeURealOddRootDividedTime (-a.1) c h) := by
  unfold routeURealOddRootDividedSuzukiFormVector
  exact suzukiHlogFourierVector_coeFn
    (routeURealOddRootDividedTime (-a.1) c h)
    (integrable_routeURealOddRootDividedTime
      (by linarith [a.2]) hh hsupp hc hnegc hc0)
    (integrable_routeURealOddRootDividedTime_hlogEnergy
      (by linarith [a.2]) hh hsupp hc hnegc hc0)

/-- The admitted form vector represents the exact odd two-root quotient almost everywhere. -/
theorem routeURealOddRootDividedSuzukiFormVector_factor_ae
    (a : SuzukiPositiveAperture) (c : ℝ) (h : ℝ → ℂ) (hh : Integrable h)
    (hsupp : ∀ y, y ≤ -a.1 ∨ a.1 ≤ y → h y = 0)
    (hc : routeURealFourier h c = 0) (hnegc : routeURealFourier h (-c) = 0)
    (hc0 : c ≠ 0) :
    ∀ᵐ ξ ∂suzukiHlogMeasure,
      (((-2 * Real.pi * ξ) ^ 2 - c ^ 2 : ℝ) : ℂ) *
          (routeURealOddRootDividedSuzukiFormVector
            a c h hh hsupp hc hnegc hc0).1 ξ =
        ((-2 * Real.pi * ξ : ℝ) : ℂ) * 𝓕 h ξ := by
  filter_upwards [routeURealOddRootDividedSuzukiFormVector_coeFn
    a c h hh hsupp hc hnegc hc0] with ξ hξ
  rw [hξ]
  exact fourier_routeURealOddRootDividedTime_factor
    (by linarith [a.2]) hh hsupp hc hnegc hc0 ξ

end RHTower
