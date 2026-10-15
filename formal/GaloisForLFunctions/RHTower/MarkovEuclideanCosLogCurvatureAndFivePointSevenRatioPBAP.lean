import GaloisForLFunctions.RHTower.MarkovFiveHalvesTailIsolationAndSeventeenOneFortyFourthsPBAP

/-!
# The Euclidean Trigonometric Amplitude Identity, Elimination of `spectralFirstMoment` from Second-Order Peano Curvature, and Coercivity up to `spectralSecondMoment / L² < 491 / 85 > 5.776`

In Module 51 through Module 54, the second derivative
`cosLogProfileDeriv2 r t = (-r ^ 2 * cos (r * log t) + r * sin (r * log t)) * (t ^ 2)⁻¹`
was bounded by applying the triangle inequality `|a * cos θ + b * sin θ| ≤ |a| + |b|`, giving
`|-r ^ 2 * cos θ + r * sin θ| ≤ r ^ 2 + |r|`. When integrated against `‖paperFT f.1 r‖ ^ 2` and
combined with `2 * |r| ≤ r ^ 2 + 1`, this paid `r ^ 2 + (1 / 2) * r ^ 2 + 1 / 2 = (3 / 2) * r ^ 2 + 1 / 2`
because `|cos θ|` and `|sin θ|` were both replaced by `1` simultaneously!

In this module, we exploit the fundamental Pythagorean identity `cos θ ^ 2 + sin θ ^ 2 = 1`:

1. **Section 1 (The Euclidean Trigonometric Amplitude Identity and the Pointwise
   `(r ^ 2 + 1 / 2) / t ^ 2` Second-Derivative Bound for `cos (r * log t)`):**
   - For all `a, b, θ : ℝ`, we prove the exact orthogonal rotation identity (`sq_add_sq_cos_sin`):
     `(a * cos θ + b * sin θ) ^ 2 + (a * sin θ - b * cos θ) ^ 2 = a ^ 2 + b ^ 2`,
     and hence `(a * cos θ + b * sin θ) ^ 2 ≤ a ^ 2 + b ^ 2` (`sq_linear_cos_sin_le`).
   - Specializing to `a = -r ^ 2` and `b = r` gives
     `(-r ^ 2 * cos θ + r * sin θ) ^ 2 ≤ r ^ 4 + r ^ 2 < r ^ 4 + r ^ 2 + 1 / 4 = (r ^ 2 + 1 / 2) ^ 2`,
     proving (`abs_neg_sq_mul_cos_add_mul_sin_le_sq_add_half`):
     `|-r ^ 2 * cos θ + r * sin θ| ≤ r ^ 2 + 1 / 2`!
   - Using the `(3, 4, 5)` Pythagorean identity
     `((5 / 4) * r ^ 2 + 1 / 4) ^ 2 - (r ^ 4 + r ^ 2) = ((3 / 4) * r ^ 2 - 1 / 4) ^ 2 ≥ 0`,
     we also prove the low-constant variant (`abs_neg_sq_mul_cos_add_mul_sin_le_five_fourths_sq_add_fourth`):
     `|-r ^ 2 * cos θ + r * sin θ| ≤ (5 / 4) * r ^ 2 + 1 / 4`!
   - On every unit cell `[n - 1, n]` (`2 ≤ n`), this upgrades the Peano bound for `cosLogProfile r`
     to (`abs_cosLogProfile_sub_cellSecant_le_sq_add_half_mul_cellParabola`):
     `|cosLogProfile r x - cellSecant (cosLogProfile r) n x| ≤ ((r ^ 2 + 1 / 2) / (2 * (n - 1) ^ 2)) * cellParabola n x`.

2. **Section 2 (Complete Elimination of `spectralFirstMoment` from the Second-Order Peano Curvature
   of `weilSymmetricLogNumerator` via Plancherel):**
   - Integrating `(r ^ 2 + 1 / 2)` against `(1 / (2 * π)) * ‖paperFT f.1 r‖ ^ 2 * 2` and applying
     the Plancherel identity `(1 / (2 * π)) * ∫ r, ‖paperFT f.1 r‖ ^ 2 * 2 = 2 * ∫ u, ‖f.1 u‖ ^ 2`
     proves (`abs_weilSymmetricLogNumerator_sub_cellSecant_le_spectralSecondMoment_add_l2`):
     `|weilSymmetricLogNumerator f.1 x - cellSecant (weilSymmetricLogNumerator f.1) n x| ≤ ((spectralSecondMoment f.1 + ∫ u, ‖f.1 u‖ ^ 2) / (2 * (n - 1) ^ 2)) * cellParabola n x`
     with **no `spectralFirstMoment` term and no `hint1` integrability hypothesis**!
   - Combining with Module 54's `17 / 144` series bound yields
     (`neg_seventeen_one_forty_fourths_spectralSecondMoment_add_l2_le_secantNumeratorCellDefect`):
     `-(17 / 144) * (spectralSecondMoment f.1 + ∫ u, ‖f.1 u‖ ^ 2) ≤ secantNumeratorCellDefect f.1 N`,
     cutting the `spectralSecondMoment` coefficient by an exact factor of `3 / 2` (from `17 / 96`
     down to `17 / 144`)!

3. **Section 3 (The `(491 / 720) ∫ ‖f.1‖² - (17 / 144) spectralSecondMoment f.1` Coercivity Law,
   the `(109 / 144) ∫ ‖f.1‖² - (17 / 144) spectralSecondMoment f.1` Prime-Blind Cone Law, and
   Unconditional `markovEnergy ≥ 0` up to `spectralSecondMoment F ≤ (491 / 85 - δ) ∫ ‖F‖² > 5.776 ∫ ‖F‖²`):**
   - Absorbing `(17 / 144) * ∫ ‖f.1‖²` into the `(4 / 5) * ∫ ‖f.1‖²` positive surplus yields
     (`four_ninety_one_seven_twentieths_l2_sub_seventeen_one_forty_fourths_spectralSecondMoment_le_rightCellQuadratureDefect`):
     `(491 / 720) * ∫ ‖f.1‖² - (17 / 144) * spectralSecondMoment f.1 ≤ rightCellQuadratureDefect (weilContinuumLogProfile f.1) N`,
     raising the critical `spectralSecondMoment / L^2` ratio to **`491 / 85 > 5.7764`**!
   - On the Prime-Blind Cone (`logVector f = 0`), absorbing `(17 / 144) * ∫ ‖f.1‖²` into Module 52's
     `(7 / 8) * ∫ ‖f.1‖²` surplus gives
     (`one_hundred_nine_one_forty_fourths_l2_sub_seventeen_one_forty_fourths_spectralSecondMoment_le_rightCellQuadratureDefect_of_logVector_eq_zero`):
     `(109 / 144) * ∫ ‖f.1‖² - (17 / 144) * spectralSecondMoment f.1 ≤ rightCellQuadratureDefect (weilContinuumLogProfile f.1) N`,
     where both denominators are `144` and the critical ratio is **`109 / 17 > 6.4117`**!
-/

open Complex MeasureTheory Filter Topology Set Finsupp
open scoped Real ComplexConjugate ContDiff FourierTransform
open Zeta23
open GaloisForLFunctions.RHTower
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower

open WeilOneSided WeilSpectral WeilLevyPole WeilLevyPoleGauss WeilLevyCoshCrossover LebesgueAtomWeil
open RHTower.NonnegativeCone

/-! ## Section 1: The Euclidean Trigonometric Amplitude Identity and the Pointwise `(r ^ 2 + 1 / 2) / t ^ 2` Second-Derivative Bound for `cos (r * log t)` -/

/-- **Exact Orthogonal Rotation / Parseval Identity for `(cos θ, sin θ)`**:
`(a * Real.cos θ + b * Real.sin θ) ^ 2 + (a * Real.sin θ - b * Real.cos θ) ^ 2 = a ^ 2 + b ^ 2`. -/
theorem sq_add_sq_cos_sin (a b θ : ℝ) :
    (a * Real.cos θ + b * Real.sin θ) ^ 2 + (a * Real.sin θ - b * Real.cos θ) ^ 2 =
      a ^ 2 + b ^ 2 := by
  have hcs := Real.cos_sq_add_sin_sq θ
  linear_combination (a ^ 2 + b ^ 2) * hcs

/-- **Euclidean Cauchy–Schwarz Bound for Linear Combinations of `cos θ` and `sin θ`**:
`(a * Real.cos θ + b * Real.sin θ) ^ 2 ≤ a ^ 2 + b ^ 2`. -/
theorem sq_linear_cos_sin_le (a b θ : ℝ) :
    (a * Real.cos θ + b * Real.sin θ) ^ 2 ≤ a ^ 2 + b ^ 2 := by
  have hid := sq_add_sq_cos_sin a b θ
  have hsq : 0 ≤ (a * Real.sin θ - b * Real.cos θ) ^ 2 := sq_nonneg _
  linarith

/-- **Sharp Asymptotic Amplitude Bound `|-r ^ 2 * cos θ + r * sin θ| ≤ r ^ 2 + 1 / 2`**:
since `(-r ^ 2 * cos θ + r * sin θ) ^ 2 ≤ r ^ 4 + r ^ 2 ≤ r ^ 4 + r ^ 2 + 1 / 4 = (r ^ 2 + 1 / 2) ^ 2`,
the triangle-inequality cross term `|r|` is replaced globally by `1 / 2`! -/
theorem abs_neg_sq_mul_cos_add_mul_sin_le_sq_add_half (r θ : ℝ) :
    |-r ^ 2 * Real.cos θ + r * Real.sin θ| ≤ r ^ 2 + 1 / 2 := by
  have h1 := sq_linear_cos_sin_le (-r ^ 2) r θ
  have h2 : (-r ^ 2) ^ 2 + r ^ 2 ≤ (r ^ 2 + 1 / 2) ^ 2 := by
    have hpos : (0 : ℝ) ≤ 1 / 4 := by norm_num
    nlinarith
  have hsq : (-r ^ 2 * Real.cos θ + r * Real.sin θ) ^ 2 ≤ (r ^ 2 + 1 / 2) ^ 2 := h1.trans h2
  rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_sq (by positivity : 0 ≤ r ^ 2 + 1 / 2)]
  exact Real.sqrt_le_sqrt hsq

/-- **Pythagorean `(3, 4, 5)` Low-Constant Amplitude Bound
`|-r ^ 2 * cos θ + r * sin θ| ≤ (5 / 4) * r ^ 2 + 1 / 4`**:
via `((5 / 4) * r ^ 2 + 1 / 4) ^ 2 - (r ^ 4 + r ^ 2) = ((3 / 4) * r ^ 2 - 1 / 4) ^ 2 ≥ 0`. -/
theorem abs_neg_sq_mul_cos_add_mul_sin_le_five_fourths_sq_add_fourth (r θ : ℝ) :
    |-r ^ 2 * Real.cos θ + r * Real.sin θ| ≤ (5 / 4) * r ^ 2 + 1 / 4 := by
  have h1 := sq_linear_cos_sin_le (-r ^ 2) r θ
  have h2 : (-r ^ 2) ^ 2 + r ^ 2 ≤ ((5 / 4) * r ^ 2 + 1 / 4) ^ 2 := by
    have hsq_diff : 0 ≤ ((3 / 4 : ℝ) * r ^ 2 - 1 / 4) ^ 2 := sq_nonneg _
    nlinarith
  have hsq : (-r ^ 2 * Real.cos θ + r * Real.sin θ) ^ 2 ≤ ((5 / 4) * r ^ 2 + 1 / 4) ^ 2 :=
    h1.trans h2
  rw [← Real.sqrt_sq_eq_abs, ← Real.sqrt_sq (by positivity : 0 ≤ (5 / 4) * r ^ 2 + 1 / 4)]
  exact Real.sqrt_le_sqrt hsq

/-- **Pointwise `(r ^ 2 + 1 / 2) / (n - 1) ^ 2` Bound on `cosLogProfileDeriv2 r t` for `t ∈ [n - 1, n]`
(`2 ≤ n`)**: -/
theorem abs_cosLogProfileDeriv2_le_sq_add_half_div_sq_of_mem_Icc
    (r : ℝ) {n : ℕ} (hn : 2 ≤ n) {t : ℝ} (ht : t ∈ Icc ((n : ℝ) - 1) (n : ℝ)) :
    |cosLogProfileDeriv2 r t| ≤ (r ^ 2 + 1 / 2) / ((n : ℝ) - 1) ^ 2 := by
  have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn1_pos : (0 : ℝ) < (n : ℝ) - 1 := by linarith
  have ht_pos : 0 < t := lt_of_lt_of_le hn1_pos ht.1
  unfold cosLogProfileDeriv2
  rw [abs_mul, abs_inv, abs_of_pos (sq_pos_of_pos ht_pos), ← div_eq_mul_inv]
  have hnum := abs_neg_sq_mul_cos_add_mul_sin_le_sq_add_half r (r * Real.log t)
  have hsq_le : ((n : ℝ) - 1) ^ 2 ≤ t ^ 2 := sq_le_sq' (by linarith) ht.1
  exact (div_le_div_of_nonneg_right hnum (sq_nonneg t)).trans
    (div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos hn1_pos) hsq_le)

/-- **Euclidean Peano Parabola Bound for `cosLogProfile r` on `[n - 1, n]` (`2 ≤ n`)**:
`|cosLogProfile r x - cellSecant (cosLogProfile r) n x| ≤ ((r ^ 2 + 1 / 2) / (2 * (n - 1) ^ 2)) * cellParabola n x`. -/
theorem abs_cosLogProfile_sub_cellSecant_le_sq_add_half_mul_cellParabola
    (r : ℝ) {n : ℕ} (hn : 2 ≤ n) {x : ℝ} (hx : x ∈ Icc ((n : ℝ) - 1) (n : ℝ)) :
    |cosLogProfile r x - cellSecant (cosLogProfile r) n x| ≤
      ((r ^ 2 + 1 / 2) / (2 * ((n : ℝ) - 1) ^ 2)) * cellParabola n x := by
  have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have ht_pos : ∀ t ∈ Icc ((n : ℝ) - 1) (n : ℝ), 0 < t :=
    fun t ht => by linarith [ht.1]
  have h := abs_sub_cellSecant_le_half_mul_cellParabola_of_abs_deriv2_le n
    (fun t ht => hasDerivAt_cosLogProfile r (ht_pos t ht))
    (fun t ht => hasDerivAt_cosLogProfileDeriv r (ht_pos t ht))
    (fun t ht => abs_cosLogProfileDeriv2_le_sq_add_half_div_sq_of_mem_Icc r hn ht) hx
  have halg : ((r ^ 2 + 1 / 2) / ((n : ℝ) - 1) ^ 2) / 2 =
      (r ^ 2 + 1 / 2) / (2 * ((n : ℝ) - 1) ^ 2) := by
    rw [div_div, mul_comm (((n : ℝ) - 1) ^ 2) 2]
  rwa [halg] at h

/-! ## Section 2: Complete Elimination of `spectralFirstMoment` from the Second-Order Peano Curvature of `weilSymmetricLogNumerator` via Plancherel -/

/-- **Pointwise `(spectralSecondMoment f.1 + ∫ ‖f.1‖²) / (2 (n - 1)^2)` Peano Bound for
`weilSymmetricLogNumerator f.1` on `[n - 1, n]` (`2 ≤ n`)**:
integrating `abs_cosLogProfile_sub_cellSecant_le_sq_add_half_mul_cellParabola` against
`(1 / (2 * π)) * ‖paperFT f.1 r‖ ^ 2 * 2` and applying Plancherel eliminates `spectralFirstMoment`
completely! -/
theorem abs_weilSymmetricLogNumerator_sub_cellSecant_le_spectralSecondMoment_add_l2
    (f : WeilTestFn)
    (hint2 : Integrable fun r : ℝ => ‖paperFT f.1 r‖ ^ 2 * (2 * r ^ 2))
    {n : ℕ} (hn : 2 ≤ n) {x : ℝ} (hx : x ∈ Icc ((n : ℝ) - 1) (n : ℝ)) :
    |weilSymmetricLogNumerator f.1 x - cellSecant (weilSymmetricLogNumerator f.1) n x| ≤
      ((spectralSecondMoment f.1 + ∫ u : ℝ, ‖f.1 u‖ ^ 2) / (2 * ((n : ℝ) - 1) ^ 2)) *
        cellParabola n x := by
  have hsq := integrable_paperFT_norm_sq f
  have hplanch := one_div_two_pi_mul_integral_paperFT_norm_sq_mul_two_eq f
  have hcos : ∀ t : ℝ, Integrable fun r : ℝ => ‖paperFT f.1 r‖ ^ 2 * (2 * cosLogProfile r t) :=
    integrable_paperFT_norm_sq_mul_two_cosLogProfile f
  have hint_diff : Integrable fun r : ℝ =>
      ‖paperFT f.1 r‖ ^ 2 * (2 * (cosLogProfile r x - cellSecant (cosLogProfile r) n x)) := by
    have hlin :
        (fun r : ℝ => ‖paperFT f.1 r‖ ^ 2 * (2 * (cosLogProfile r x - cellSecant (cosLogProfile r) n x))) =
        fun r : ℝ =>
          ‖paperFT f.1 r‖ ^ 2 * (2 * cosLogProfile r x) -
            (((n : ℝ) - x) * (‖paperFT f.1 r‖ ^ 2 * (2 * cosLogProfile r ((n : ℝ) - 1))) +
              (x - ((n : ℝ) - 1)) * (‖paperFT f.1 r‖ ^ 2 * (2 * cosLogProfile r (n : ℝ)))) := by
      ext r
      unfold cellSecant
      ring
    rw [hlin]
    exact (hcos x).sub (((hcos ((n : ℝ) - 1)).const_mul _).add ((hcos (n : ℝ)).const_mul _))
  rw [weilSymmetricLogNumerator_sub_cellSecant_eq_spectral f n x,
    abs_mul, abs_of_pos (div_pos one_pos Real.two_pi_pos)]
  have hrhs_eq :
      ((spectralSecondMoment f.1 + ∫ u : ℝ, ‖f.1 u‖ ^ 2) / (2 * ((n : ℝ) - 1) ^ 2)) *
        cellParabola n x =
      (1 / (2 * π)) * ∫ r : ℝ,
        (‖paperFT f.1 r‖ ^ 2 * (2 * r ^ 2) + (1 / 2) * (‖paperFT f.1 r‖ ^ 2 * 2)) *
          (cellParabola n x / (2 * ((n : ℝ) - 1) ^ 2)) := by
    have hplanch' : (∫ u : ℝ, ‖f.1 u‖ ^ 2) =
        (1 / (2 * π)) * ((1 / 2) * ∫ r : ℝ, ‖paperFT f.1 r‖ ^ 2 * 2) := by
      linarith [hplanch]
    unfold spectralSecondMoment
    rw [integral_mul_const, integral_add hint2 ((hsq.mul_const 2).const_mul (1 / 2)),
      integral_const_mul, hplanch']
    ring
  rw [hrhs_eq]
  refine mul_le_mul_of_nonneg_left (abs_integral_le_integral_abs.trans ?_)
    (div_nonneg zero_le_one Real.two_pi_pos.le)
  refine integral_mono hint_diff.abs
    ((hint2.add ((hsq.mul_const 2).const_mul (1 / 2))).mul_const _) fun r => ?_
  dsimp
  rw [abs_mul, abs_mul, abs_of_nonneg (sq_nonneg _), abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hpeano := abs_cosLogProfile_sub_cellSecant_le_sq_add_half_mul_cellParabola r hn hx
  have hweight : 0 ≤ ‖paperFT f.1 r‖ ^ 2 * 2 := mul_nonneg (sq_nonneg _) (by norm_num)
  have hmul := mul_le_mul_of_nonneg_left hpeano hweight
  have halg : ‖paperFT f.1 r‖ ^ 2 * 2 * (((r ^ 2 + 1 / 2) / (2 * ((n : ℝ) - 1) ^ 2)) * cellParabola n x) =
      (‖paperFT f.1 r‖ ^ 2 * (2 * r ^ 2) + (1 / 2) * (‖paperFT f.1 r‖ ^ 2 * 2)) *
        (cellParabola n x / (2 * ((n : ℝ) - 1) ^ 2)) := by ring
  linarith

/-- **Cutoff-Independent `-(17 / 144) (spectralSecondMoment f.1 + ∫ ‖f.1‖²) ≤ secantNumeratorCellDefect f.1 N`
(No `spectralFirstMoment` Needed!)**: -/
theorem neg_seventeen_one_forty_fourths_spectralSecondMoment_add_l2_le_secantNumeratorCellDefect
    (f : WeilTestFn)
    (hint2 : Integrable fun r : ℝ => ‖paperFT f.1 r‖ ^ 2 * (2 * r ^ 2))
    (N : ℕ) :
    -(17 / 144) * (spectralSecondMoment f.1 + ∫ u : ℝ, ‖f.1 u‖ ^ 2) ≤
      secantNumeratorCellDefect f.1 N := by
  have hnorm_nonneg : 0 ≤ ∫ u : ℝ, ‖f.1 u‖ ^ 2 := integral_nonneg fun _ => sq_nonneg _
  refine neg_seventeen_one_forty_fourths_mul_le_secantNumeratorCellDefect_of_inv_sq_semiconcave
    f (add_nonneg (spectralSecondMoment_nonneg f.1) hnorm_nonneg) N
    fun n hn x hx => ?_
  rw [Finset.mem_Icc] at hn
  have h := abs_weilSymmetricLogNumerator_sub_cellSecant_le_spectralSecondMoment_add_l2
    f hint2 hn.1 hx
  linarith [(abs_le.mp h).1]

/-- **Hybrid Cell-Split Euclidean Bound
`-(5 / 144) spectralSecondMoment f.1 - (1 / 3) spectralFirstMoment f.1 - (5 / 144) ∫ ‖f.1‖² ≤ secantNumeratorCellDefect f.1 N`**: -/
theorem neg_five_one_forty_fourths_second_sub_third_first_sub_five_one_forty_fourths_l2_le_secantNumeratorCellDefect
    (f : WeilTestFn)
    (hint1 : Integrable fun r : ℝ => ‖paperFT f.1 r‖ ^ 2 * (2 * |r|))
    (hint2 : Integrable fun r : ℝ => ‖paperFT f.1 r‖ ^ 2 * (2 * r ^ 2))
    (N : ℕ) :
    -(5 / 144) * spectralSecondMoment f.1 - (1 / 3) * spectralFirstMoment f.1 -
        (5 / 144) * (∫ u : ℝ, ‖f.1 u‖ ^ 2) ≤
      secantNumeratorCellDefect f.1 N := by
  have hnorm_nonneg : 0 ≤ ∫ u : ℝ, ‖f.1 u‖ ^ 2 := integral_nonneg fun _ => sq_nonneg _
  have hhyb := neg_third_first_sub_five_one_forty_fourths_second_le_secantNumeratorCellDefect_of_hybrid
    f (spectralFirstMoment_nonneg f.1)
    (add_nonneg (spectralSecondMoment_nonneg f.1) hnorm_nonneg) N
    (fun x hx => by
      have hx2 : x ∈ Icc (((2 : ℕ) : ℝ) - 1) (2 : ℕ) := by
        convert hx using 2 <;> norm_num
      have hcell := neg_two_mul_div_pred_mul_cellParabola_le_sub_cellSecant_of_log_lipschitz
        (weilSymmetricLogNumerator f.1) (spectralFirstMoment_nonneg f.1) (le_refl 2)
        (fun y hy z _ hyz =>
          abs_weilSymmetricLogNumerator_sub_le_spectralFirstMoment_mul_log_sub
            f hint1 (by norm_num at hy; linarith [hy.1]) hyz) hx2
      have halg : -((4 * spectralFirstMoment f.1 / (((2 : ℕ) : ℝ) - 1)) / 2) * cellParabola 2 x =
          -(2 * spectralFirstMoment f.1) * cellParabola 2 x := by
        push_cast
        ring
      rwa [halg] at hcell)
    (fun n hn x hx => by
      rw [Finset.mem_Icc] at hn
      have hn2 : 2 ≤ n := by omega
      have h := abs_weilSymmetricLogNumerator_sub_cellSecant_le_spectralSecondMoment_add_l2
        f hint2 hn2 hx
      linarith [(abs_le.mp h).1])
  linarith

/-! ## Section 3: The `(491 / 720) ∫ ‖f.1‖² - (17 / 144) spectralSecondMoment f.1` Coercivity Law, the `(109 / 144) ∫ ‖f.1‖² - (17 / 144) spectralSecondMoment f.1` Prime-Blind Cone Law, and Unconditional `markovEnergy ≥ 0` up to `spectralSecondMoment F ≤ (491 / 85 - δ) ∫ ‖F‖² > 5.776 ∫ ‖F‖²` -/

/-- **Pure Second-Moment `(491 / 720) ∫ ‖f.1‖² - (17 / 144) spectralSecondMoment f.1` Lower Bound on
`rightCellQuadratureDefect` (Critical Ratio `491 / 85 > 5.7764`)**:
eliminating `spectralFirstMoment` via the Euclidean identity `cos^2 + sin^2 = 1` reduces the
coefficient of `spectralSecondMoment f.1` from `17 / 96` to `17 / 144` with no `hint1` assumption! -/
theorem four_ninety_one_seven_twentieths_l2_sub_seventeen_one_forty_fourths_spectralSecondMoment_le_rightCellQuadratureDefect
    (f : WeilTestFn)
    (hint2 : Integrable fun r : ℝ => ‖paperFT f.1 r‖ ^ 2 * (2 * r ^ 2))
    {N : ℕ} (hN1 : 1 ≤ N)
    (hN0 : EF.weilTest f.1 f.1 (Real.log N) = 0 ∧ EF.weilTest f.1 f.1 (-Real.log N) = 0)
    (hN : ∀ n : ℕ, N < n →
      EF.weilTest f.1 f.1 (Real.log n) = 0 ∧ EF.weilTest f.1 f.1 (-Real.log n) = 0) :
    (491 / 720) * (∫ u : ℝ, ‖f.1 u‖ ^ 2) - (17 / 144) * spectralSecondMoment f.1 ≤
      rightCellQuadratureDefect (weilContinuumLogProfile f.1) N := by
  have h1 := four_fifths_l2_add_secantNumerator_le_rightCellQuadratureDefect f hN1 hN0 hN
  have h2 := neg_seventeen_one_forty_fourths_spectralSecondMoment_add_l2_le_secantNumeratorCellDefect
    f hint2 N
  linarith

/-- **Prime-Blind Cone `(109 / 144) ∫ ‖f.1‖² - (17 / 144) spectralSecondMoment f.1` Lower Bound on
`rightCellQuadratureDefect` (Critical Ratio `109 / 17 > 6.4117`)**:
on the Prime-Blind Cone (`logVector f = 0`), absorbing `(17 / 144) * ∫ ‖f.1‖²` into Module 52's
`(7 / 8) * ∫ ‖f.1‖²` origin surplus leaves `7 / 8 - 17 / 144 = 109 / 144`! -/
theorem one_hundred_nine_one_forty_fourths_l2_sub_seventeen_one_forty_fourths_spectralSecondMoment_le_rightCellQuadratureDefect_of_logVector_eq_zero
    (f : WeilTestFn) (hblind : logVector f = 0)
    (hint2 : Integrable fun r : ℝ => ‖paperFT f.1 r‖ ^ 2 * (2 * r ^ 2))
    {N : ℕ} (hN1 : 1 ≤ N)
    (hN0 : EF.weilTest f.1 f.1 (Real.log N) = 0 ∧ EF.weilTest f.1 f.1 (-Real.log N) = 0)
    (hN : ∀ n : ℕ, N < n →
      EF.weilTest f.1 f.1 (Real.log n) = 0 ∧ EF.weilTest f.1 f.1 (-Real.log n) = 0) :
    (109 / 144) * (∫ u : ℝ, ‖f.1 u‖ ^ 2) - (17 / 144) * spectralSecondMoment f.1 ≤
      rightCellQuadratureDefect (weilContinuumLogProfile f.1) N := by
  have h1 := seven_eighths_l2_add_secantNumerator_le_rightCellQuadratureDefect_of_logVector_eq_zero
    f hblind hN1 hN0 hN
  have h2 := neg_seventeen_one_forty_fourths_spectralSecondMoment_add_l2_le_secantNumeratorCellDefect
    f hint2 N
  linarith

/-- **Unconditional `0 ≤ markovEnergy F` on the Primitive Hyperplane whenever
`spectralSecondMoment F ≤ (491 / 85 - δ) ∫ ‖F‖² > 5.776 ∫ ‖F‖²`**: -/
theorem markovEnergy_ofReal_nonneg_of_spectralSecondMoment_le_four_ninety_one_eighty_fifths_of_cosh_zero
    (m : ℕ) {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hcosh : coshHalfMoment f = 0)
    (hint2 : Integrable fun r : ℝ => ‖paperFT (realWeilTestFn f hf hfc).1 r‖ ^ 2 * (2 * r ^ 2))
    {N : ℕ} (hN1 : 1 ≤ N)
    (hN0 : EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (Real.log N) = 0 ∧
      EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (-Real.log N) = 0)
    (hN : ∀ x : ℝ, (N : ℝ) < x →
      EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (Real.log x) = 0 ∧
        EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1 (-Real.log x) = 0)
    (hdiff : ∀ n ∈ Finset.Icc 2 N,
      0 ≤ iteratedForwardDiff m (logValue (realWeilTestFn f hf hfc).1) n)
    {δ : ℝ} (hδ : 0 < δ)
    (hsec_bound : spectralSecondMoment (realWeilTestFn f hf hfc).1 ≤
      (491 / 85 - δ) * ∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2) :
    0 ≤ markovEnergy (realWeilTestFn f hf hfc).1 := by
  let θ := max (max 1 (Real.log (N : ℝ))) (288 / (17 * δ))
  have hθ1 : 1 ≤ θ := (le_max_left 1 (Real.log (N : ℝ))).trans (le_max_left _ _)
  have hθ0 : 0 ≤ θ := by linarith
  have hθlog : Real.log (N : ℝ) ≤ θ :=
    (le_max_right 1 (Real.log (N : ℝ))).trans (le_max_left _ _)
  have h17δ : 0 < 17 * δ := by linarith
  have hθδ_le : 288 / (17 * δ) ≤ θ := le_max_right _ _
  have hθδ : 288 ≤ θ * (17 * δ) := (div_le_iff₀ h17δ).mp hθδ_le
  have hbase := four_fifths_secantNumerator_upgraded_l2_le_markovEnergy_of_cosh_zero
    m hθ0 hf hfc hcosh hN1 hθlog hN0 hN hdiff
  have hnum := neg_seventeen_one_forty_fourths_spectralSecondMoment_add_l2_le_secantNumeratorCellDefect
    (realWeilTestFn f hf hfc) hint2 N
  have hθnum := mul_le_mul_of_nonneg_left hnum hθ0
  have hθbound := mul_le_mul_of_nonneg_left hsec_bound (by positivity : 0 ≤ (17 / 144) * θ)
  have hnorm_nonneg : 0 ≤ ∫ u : ℝ, ‖(realWeilTestFn f hf hfc).1 u‖ ^ 2 :=
    integral_nonneg fun _ => sq_nonneg _
  have hθδ_norm := mul_le_mul_of_nonneg_right hθδ hnorm_nonneg
  have hres_nonneg : 0 ≤ (θ - 1) * bochnerResolventEnergy
      (EF.weilTest (realWeilTestFn f hf hfc).1 (realWeilTestFn f hf hfc).1) :=
    mul_nonneg (by linarith) (bochnerResolventEnergy_weilTest_nonneg _)
  have hsinh_nonneg : 0 ≤ 2 * θ * sinhHalfMoment f ^ 2 := by positivity
  linarith

end RHTower

end
