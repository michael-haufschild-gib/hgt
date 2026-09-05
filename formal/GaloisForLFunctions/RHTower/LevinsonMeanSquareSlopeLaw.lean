import Mathlib

/-!
# The slope law of the Levinson mean square

Young's formula for the mean square of `ζ·Ψ_P` on the line `Re s = ½ − R/log T` with a mollifier of
length `T^θ` and profile `P` (`P(0) = 0`, `P(1) = 1`) is

  `c_P(R) = 1 + (1/θ) · E(R) · ∫₀¹ (RθP(u) + P'(u))² du`,   `E(R) = ∫₀¹ e^{2Rv} dv = (e^{2R} − 1)/(2R)`.

**Slope law**: `c_P'(0) = c_P(0)` for every profile — the left-shifted mean square grows at first
order exactly like `e^{R}`, independently of `P` and `θ`. Consequently the first-order net gain of
the Levinson shift, `(1+κ)R/2 − (c_P'(0)/c_P(0))·R/2 = κR/2`, is universal, and no mollifier
profile can reopen the mollified-Littlewood family through the slope.
-/

open intervalIntegral

namespace RHTower

noncomputable section

/-- `E(R) = ∫₀¹ e^{2Rv} dv`. -/
def youngE (R : ℝ) : ℝ := ∫ v in (0 : ℝ)..1, Real.exp (2 * R * v)

theorem youngE_zero : youngE 0 = 1 := by
  simp [youngE]

theorem youngE_eq {R : ℝ} (hR : R ≠ 0) :
    youngE R = (Real.exp (2 * R) - 1) / (2 * R) := by
  unfold youngE
  have h2R : (2 * R) ≠ 0 := mul_ne_zero two_ne_zero hR
  rw [intervalIntegral.integral_comp_mul_left (fun x => Real.exp x) h2R]
  simp [integral_exp, div_eq_inv_mul]

/-- `E'(0) = 1`, from the third-order exponential bound. -/
theorem hasDerivAt_youngE_zero : HasDerivAt youngE 1 0 := by
  rw [hasDerivAt_iff_isLittleO]
  refine Asymptotics.IsLittleO.of_bound fun c hc => ?_
  have hδ : 0 < min (1 / 2 : ℝ) (9 * c / 8) := lt_min (by norm_num) (by positivity)
  filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hδ] with R hR
  rw [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs] at hR
  have hR1 : |R| < 1 / 2 := lt_of_lt_of_le hR (min_le_left _ _)
  have hRc : |R| < 9 * c / 8 := lt_of_lt_of_le hR (min_le_right _ _)
  simp only [sub_zero, smul_eq_mul, mul_one, youngE_zero, Real.norm_eq_abs]
  rcases eq_or_ne R 0 with h0 | h0
  · subst h0
    simp [youngE_zero]
  · rw [youngE_eq h0]
    have hx : |2 * R| ≤ 1 := by
      rw [abs_mul, abs_two]
      linarith
    have hb := Real.exp_bound hx (n := 3) (by norm_num)
    have hsum : ∑ m ∈ Finset.range 3, (2 * R) ^ m / (m.factorial : ℝ)
        = 1 + 2 * R + 2 * R ^ 2 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      ring
    rw [hsum] at hb
    have hcoef : |2 * R| ^ 3 * (((3 : ℕ).succ : ℝ) / (((3 : ℕ).factorial : ℝ) * (3 : ℕ)))
        = (16 / 9) * |R| ^ 3 := by
      rw [abs_mul, abs_two]
      norm_num [Nat.factorial]
      ring
    rw [hcoef] at hb
    have hnum : (Real.exp (2 * R) - 1) / (2 * R) - 1 - R
        = (Real.exp (2 * R) - (1 + 2 * R + 2 * R ^ 2)) / (2 * R) := by
      field_simp
      ring
    rw [hnum, abs_div, abs_mul, abs_two]
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 * |R|)]
    have hR0 : 0 < |R| := abs_pos.mpr h0
    have hkey : (16 / 9) * |R| ^ 3 ≤ c * |R| * (2 * |R|) := by
      have h1 : (16 / 9) * |R| ≤ 2 * c := by linarith
      have h2 : 0 ≤ |R| ^ 2 := sq_nonneg _
      nlinarith [mul_le_mul_of_nonneg_right h1 h2]
    linarith

/-- The Levinson/Young mean-square functional. -/
def youngMeanSquare (θ : ℝ) (P P' : ℝ → ℝ) (R : ℝ) : ℝ :=
  1 + (1 / θ) * (youngE R * ∫ u in (0 : ℝ)..1, (R * θ * P u + P' u) ^ 2)

/-- The mollifier integral is a quadratic polynomial in the shift. -/
theorem integral_shiftedProfile_sq {θ : ℝ} {P P' : ℝ → ℝ} (hPc : Continuous P)
    (hP' : Continuous P') (R : ℝ) :
    (∫ u in (0 : ℝ)..1, (R * θ * P u + P' u) ^ 2)
      = (∫ u in (0 : ℝ)..1, P' u ^ 2) + (∫ u in (0 : ℝ)..1, 2 * θ * (P u * P' u)) * R
        + (∫ u in (0 : ℝ)..1, θ ^ 2 * P u ^ 2) * R ^ 2 := by
  have hfun : (fun u => (R * θ * P u + P' u) ^ 2)
      = fun u => (P' u ^ 2 + 2 * θ * (P u * P' u) * R) + θ ^ 2 * P u ^ 2 * R ^ 2 := by
    funext u
    ring
  have h1 : IntervalIntegrable (fun u => P' u ^ 2) MeasureTheory.volume 0 1 :=
    (hP'.pow 2).intervalIntegrable 0 1
  have h2 : IntervalIntegrable (fun u => 2 * θ * (P u * P' u) * R) MeasureTheory.volume 0 1 :=
    (((hPc.mul hP').const_mul (2 * θ)).mul_const R).intervalIntegrable 0 1
  have h3 : IntervalIntegrable (fun u => θ ^ 2 * P u ^ 2 * R ^ 2) MeasureTheory.volume 0 1 :=
    (((hPc.pow 2).const_mul (θ ^ 2)).mul_const (R ^ 2)).intervalIntegrable 0 1
  rw [hfun, intervalIntegral.integral_add (h1.add h2) h3, intervalIntegral.integral_add h1 h2,
    intervalIntegral.integral_mul_const, intervalIntegral.integral_mul_const]

/-- `∫₀¹ 2θ P P' = θ (P(1)² − P(0)²)`. -/
theorem integral_two_theta_mul_profile_deriv {θ : ℝ} {P P' : ℝ → ℝ}
    (hP : ∀ x, HasDerivAt P (P' x) x) (hPc : Continuous P) (hP' : Continuous P') :
    (∫ u in (0 : ℝ)..1, 2 * θ * (P u * P' u)) = θ * (P 1 ^ 2 - P 0 ^ 2) := by
  have hsq : ∀ x, HasDerivAt (fun x => P x ^ 2) (2 * (P x * P' x)) x := by
    intro x
    have h := (hP x).pow 2
    have h2 : ((2 : ℕ) : ℝ) * P x ^ (2 - 1) * P' x = 2 * (P x * P' x) := by
      first
        | (norm_num [mul_assoc])
        | (norm_num; ring)
    rw [h2] at h
    exact h
  have hint : IntervalIntegrable (fun u => 2 * (P u * P' u)) MeasureTheory.volume 0 1 :=
    ((hPc.mul hP').const_mul 2).intervalIntegrable 0 1
  have hfund := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hsq x) hint
  have hfun : (fun u => 2 * θ * (P u * P' u)) = fun u => θ * (2 * (P u * P' u)) := by
    funext u
    ring
  rw [hfun, intervalIntegral.integral_const_mul, hfund]

/-- **The slope law.** For every profile with `P(0) = 0`, `P(1) = 1`, the Levinson mean square
satisfies `c_P'(0) = c_P(0)`. -/
theorem youngMeanSquare_slope_law {θ : ℝ} (hθ : θ ≠ 0) {P P' : ℝ → ℝ}
    (hP : ∀ x, HasDerivAt P (P' x) x) (hP' : Continuous P') (hP0 : P 0 = 0) (hP1 : P 1 = 1) :
    HasDerivAt (youngMeanSquare θ P P') (youngMeanSquare θ P P' 0) 0 := by
  have hPc : Continuous P := continuous_iff_continuousAt.2 fun x => (hP x).continuousAt
  set A : ℝ := ∫ u in (0 : ℝ)..1, P' u ^ 2 with hA
  set B : ℝ := ∫ u in (0 : ℝ)..1, 2 * θ * (P u * P' u) with hB
  set C : ℝ := ∫ u in (0 : ℝ)..1, θ ^ 2 * P u ^ 2 with hC
  have hBθ : B = θ := by
    rw [hB, integral_two_theta_mul_profile_deriv hP hPc hP', hP0, hP1]
    ring
  have hfun : youngMeanSquare θ P P'
      = fun R => 1 + (1 / θ) * (youngE R * (A + B * R + C * R ^ 2)) := by
    funext R
    simp only [youngMeanSquare]
    rw [integral_shiftedProfile_sq hPc hP' R]
  rw [hfun]
  show HasDerivAt _ (1 + 1 / θ * (youngE 0 * (A + B * 0 + C * 0 ^ 2))) 0
  have hpoly : HasDerivAt (fun R : ℝ => A + B * R + C * R ^ 2)
      (B * 1 + C * ((2 : ℕ) * (0 : ℝ) ^ (2 - 1))) 0 :=
    (((hasDerivAt_id' (0 : ℝ)).const_mul B).const_add A).add
      ((hasDerivAt_pow 2 (0 : ℝ)).const_mul C)
  have hprod := ((hasDerivAt_youngE_zero.mul hpoly).const_mul (1 / θ)).const_add 1
  refine hprod.congr_deriv ?_
  simp only [youngE_zero, hBθ]
  field_simp
  ring

end

end RHTower
