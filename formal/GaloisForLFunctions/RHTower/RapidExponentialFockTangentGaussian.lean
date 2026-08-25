import GaloisForLFunctions.RHTower.PolynomialFockTangentGaussian
import GaloisForLFunctions.RHTower.RapidExponentialFockPotentialGeometry
import GaloisForLFunctions.HTGeometry.ExponentialDividedDifference

/-!
# Tangent Gaussian for the rapid exponential Fock potential

A global radial Bregman estimate with an explicit polynomial loss dominates the holomorphic tangent
density by a centered Gaussian.  Sharp rapid-Fock kernel asymptotics are unnecessary for the
compactness application: the polynomial loss is absorbed by exponential prime-window decay.
-/

open MeasureTheory Set

namespace RHTower

noncomputable section

/-- Conservative global curvature retained after tangent gauging. -/
def rapidExponentialFockTangentCurvature (a x : ℝ) : ℝ :=
  a ^ 2 * Real.exp (2 * a * x) /
    (4 * (1 + max 1 (2 * a * x)) ^ 2)

theorem rapidExponentialFockTangentCurvature_pos
    {a x : ℝ} (ha : 0 < a) (_hx : 0 ≤ x) :
    0 < rapidExponentialFockTangentCurvature a x := by
  unfold rapidExponentialFockTangentCurvature
  have : 0 < 1 + max 1 (2 * a * x) := by linarith [le_max_left 1 (2 * a * x)]
  positivity

private theorem one_fourth_lt_exp_neg_one :
    (1 / 4 : ℝ) < Real.exp (-1) := by
  have he : Real.exp 1 < 3 := Real.exp_one_lt_d9.trans (by norm_num)
  have hprod : Real.exp 1 * Real.exp (-1) = 1 := by
    rw [← Real.exp_add]
    norm_num
  nlinarith [Real.exp_pos 1, Real.exp_pos (-1)]

private theorem one_sixteenth_lt_exp_neg_two :
    (1 / 16 : ℝ) < Real.exp (-2) := by
  have he : Real.exp 1 < 3 := Real.exp_one_lt_d9.trans (by norm_num)
  have he2 : Real.exp 2 < 9 := by
    rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
    nlinarith [Real.exp_pos 1]
  have hprod : Real.exp 2 * Real.exp (-2) = 1 := by
    rw [← Real.exp_add]
    norm_num
  nlinarith [Real.exp_pos 2, Real.exp_pos (-2)]

private theorem expDivTwo_one_half_le_of_nonneg
    {t : ℝ} (ht : 0 ≤ t) :
    1 / 2 ≤ GaloisForLFunctions.HTGeometry.expDivTwo t := by
  rw [← GaloisForLFunctions.HTGeometry.expDivTwo_zero]
  unfold GaloisForLFunctions.HTGeometry.expDivTwo
  apply intervalIntegral.integral_mono_on (by norm_num)
    (GaloisForLFunctions.HTGeometry.intervalIntegrable_expMulTwo 0 0 1)
    (GaloisForLFunctions.HTGeometry.intervalIntegrable_expMulTwo t 0 1)
  intro s hs
  have hfac : 0 ≤ 1 - s := by linarith [hs.2]
  have hexp : 1 ≤ Real.exp (s * t) := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (mul_nonneg hs.1 ht)
  simp only [mul_zero, Real.exp_zero, mul_one]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hexp hfac

private theorem exp_remainder_lower_of_nonneg
    {t : ℝ} (ht : 0 ≤ t) :
    t ^ 2 / 2 ≤ Real.exp t - 1 - t := by
  by_cases ht0 : t = 0
  · subst t
    norm_num
  · have hid := GaloisForLFunctions.HTGeometry.expDivTwo_eq_of_ne ht0
    have hdiv := expDivTwo_one_half_le_of_nonneg ht
    have hsq : 0 ≤ t ^ 2 := sq_nonneg t
    calc
      t ^ 2 / 2 = t ^ 2 * (1 / 2) := by ring
      _ ≤ t ^ 2 * GaloisForLFunctions.HTGeometry.expDivTwo t :=
        mul_le_mul_of_nonneg_left hdiv hsq
      _ = Real.exp t - 1 - t := by
        rw [hid]
        field_simp [pow_ne_zero 2 ht0]

private theorem exp_neg_remainder_lower
    {b u : ℝ} (hb : 1 ≤ b) (hu0 : 0 ≤ u) (hub : u ≤ b) :
    u ^ 2 / (16 * (1 + b) ^ 2) ≤ Real.exp (-u) - 1 + u := by
  have hden : 0 < 16 * (1 + b) ^ 2 := by positivity
  have hcoef : u ^ 2 / (16 * (1 + b) ^ 2) ≤ 1 / 16 := by
    apply (div_le_iff₀ hden).2
    have hsq : u ^ 2 ≤ (1 + b) ^ 2 := by
      have hu : u ≤ 1 + b := hub.trans (by linarith)
      exact (sq_le_sq₀ hu0 (by linarith : 0 ≤ 1 + b)).2 hu
    nlinarith
  by_cases hu1 : u ≤ 1
  · by_cases huZero : u = 0
    · subst u
      norm_num
    · have hneg : -u ≤ 0 := by linarith
      have hdiv := GaloisForLFunctions.HTGeometry.exp_div_two_le_expDivTwo hneg
      have hexp : Real.exp (-1) ≤ Real.exp (-u) :=
        Real.exp_le_exp.mpr (by linarith)
      have hdivLower : 1 / 8 ≤ GaloisForLFunctions.HTGeometry.expDivTwo (-u) := by
        nlinarith [one_fourth_lt_exp_neg_one]
      have hid := GaloisForLFunctions.HTGeometry.expDivTwo_eq_of_ne
        (neg_ne_zero.mpr huZero)
      have hcoefSmall : 1 / (16 * (1 + b) ^ 2) ≤ 1 / 8 := by
        have : 4 ≤ (1 + b) ^ 2 := by nlinarith
        apply (div_le_iff₀ hden).2
        nlinarith
      calc
        u ^ 2 / (16 * (1 + b) ^ 2) =
            u ^ 2 * (1 / (16 * (1 + b) ^ 2)) := by ring
        _ ≤ u ^ 2 * (1 / 8) :=
          mul_le_mul_of_nonneg_left hcoefSmall (sq_nonneg u)
        _ ≤ u ^ 2 * GaloisForLFunctions.HTGeometry.expDivTwo (-u) := by
          gcongr
        _ = Real.exp (-u) - 1 + u := by
          rw [hid]
          field_simp [pow_ne_zero 2 (neg_ne_zero.mpr huZero)]
          ring
  · have hu1' : 1 < u := lt_of_not_ge hu1
    have hrem : 1 / 16 ≤ Real.exp (-u) - 1 + u := by
      by_cases hbig : 17 / 16 ≤ u
      · have hpos := Real.exp_pos (-u)
        nlinarith
      · have huTwo : u < 2 := by
          have : u < 17 / 16 := lt_of_not_ge hbig
          norm_num at this ⊢
          linarith
        have hexp : Real.exp (-2) < Real.exp (-u) :=
          Real.exp_lt_exp.mpr (by linarith)
        nlinarith [one_sixteenth_lt_exp_neg_two]
    exact hcoef.trans hrem

private theorem rapidExponentialFock_radial_bregman_lower
    {a x r : ℝ} (ha : 0 < a) (hr : 0 ≤ r) :
    rapidExponentialFockTangentCurvature a x * (r - x) ^ 2 ≤
      rapidExponentialFockPotential a r - rapidExponentialFockPotential a x -
        rapidExponentialFockRadialSlope a x * (r - x) := by
  let b : ℝ := max 1 (2 * a * x)
  let t : ℝ := 2 * a * (r - x)
  have hb : 1 ≤ b := le_max_left _ _
  have hphi : 0 < rapidExponentialFockPotential a x := by
    unfold rapidExponentialFockPotential
    positivity
  have hidentity :
      rapidExponentialFockPotential a r - rapidExponentialFockPotential a x -
          rapidExponentialFockRadialSlope a x * (r - x) =
        rapidExponentialFockPotential a x * (Real.exp t - 1 - t) := by
    unfold rapidExponentialFockPotential rapidExponentialFockRadialSlope
    rw [show Real.exp (2 * a * r) =
        Real.exp (2 * a * x) * Real.exp t by
      rw [← Real.exp_add]
      congr 1
      dsimp [t]
      ring]
    dsimp [t]
    ring
  rw [hidentity]
  by_cases htx : x ≤ r
  · have ht0 : 0 ≤ t := by dsimp [t]; nlinarith
    have hrem := exp_remainder_lower_of_nonneg ht0
    have hcurv : rapidExponentialFockTangentCurvature a x ≤
        2 * a ^ 2 * rapidExponentialFockPotential a x := by
      unfold rapidExponentialFockTangentCurvature rapidExponentialFockPotential
      have hdenOne : 1 ≤ 4 * (1 + max 1 (2 * a * x)) ^ 2 := by
        nlinarith [sq_nonneg (1 + max 1 (2 * a * x)),
          le_max_left 1 (2 * a * x)]
      have hnum : 0 ≤ a ^ 2 * Real.exp (2 * a * x) := by positivity
      calc
        a ^ 2 * Real.exp (2 * a * x) /
              (4 * (1 + max 1 (2 * a * x)) ^ 2) ≤
            a ^ 2 * Real.exp (2 * a * x) := div_le_self hnum hdenOne
        _ ≤ 2 * a ^ 2 * Real.exp (2 * a * x) := by nlinarith
    have hrem' :
        2 * a ^ 2 * rapidExponentialFockPotential a x * (r - x) ^ 2 ≤
          rapidExponentialFockPotential a x * (Real.exp t - 1 - t) := by
      have := mul_le_mul_of_nonneg_left hrem hphi.le
      dsimp [t] at this
      nlinarith
    exact (mul_le_mul_of_nonneg_right hcurv (sq_nonneg _)).trans hrem'
  · have hrx : r < x := lt_of_not_ge htx
    let u : ℝ := 2 * a * (x - r)
    have hu0 : 0 ≤ u := by dsimp [u]; positivity
    have hub : u ≤ b := by
      have hbase : 2 * a * x ≤ b := le_max_right _ _
      dsimp [u]
      nlinarith
    have hrem := exp_neg_remainder_lower hb hu0 hub
    have htNeg : t = -u := by dsimp [t, u]; ring
    have hscaled := mul_le_mul_of_nonneg_left hrem hphi.le
    dsimp [b] at hscaled
    rw [htNeg]
    have hcurvIdentity :
        rapidExponentialFockTangentCurvature a x * (r - x) ^ 2 =
          rapidExponentialFockPotential a x *
            (u ^ 2 / (16 * (1 + max 1 (2 * a * x)) ^ 2)) := by
      unfold rapidExponentialFockTangentCurvature rapidExponentialFockPotential
      dsimp [u]
      have hden : 1 + max 1 (2 * a * x) ≠ 0 := by
        linarith [le_max_left 1 (2 * a * x)]
      field_simp [hden]
      ring
    rw [hcurvIdentity]
    simpa [htNeg] using hscaled

/-- Global rapid radial Bregman lower bound at a positive real base point. -/
theorem rapidExponentialFockPotential_bregman_lower
    {a x : ℝ} (ha : 0 < a) (hx : 0 ≤ x) (z : ℂ) :
    rapidExponentialFockPotential a x +
        rapidExponentialFockRadialSlope a x * (z.re - x) +
        rapidExponentialFockTangentCurvature a x * ‖z - (x : ℂ)‖ ^ 2 ≤
      rapidExponentialFockPotential a ‖z‖ := by
  let r : ℝ := ‖z‖
  let c : ℝ := rapidExponentialFockTangentCurvature a x
  have hr : 0 ≤ r := norm_nonneg z
  have hrad := rapidExponentialFock_radial_bregman_lower (x := x) ha hr
  have hre : z.re ≤ r := by
    dsimp [r]
    exact (le_abs_self z.re).trans (Complex.abs_re_le_norm z)
  have hgeom : ‖z - (x : ℂ)‖ ^ 2 =
      (r - x) ^ 2 + 2 * x * (r - z.re) := by
    rw [Complex.sq_norm]
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.ofReal_re,
      Complex.sub_im, Complex.ofReal_im, sub_zero]
    have hzsq : r ^ 2 = z.re ^ 2 + z.im ^ 2 := by
      dsimp [r]
      rw [Complex.sq_norm]
      simp [Complex.normSq]
      ring
    nlinarith
  have hc : 0 ≤ c := (rapidExponentialFockTangentCurvature_pos ha hx).le
  have hslope : c * (2 * x) ≤ rapidExponentialFockRadialSlope a x := by
    unfold c rapidExponentialFockTangentCurvature rapidExponentialFockRadialSlope
    have hden : 0 < 4 * (1 + max 1 (2 * a * x)) ^ 2 := by positivity
    have hmax : 2 * a * x ≤ max 1 (2 * a * x) := le_max_right _ _
    have hratio : a * x / (4 * (1 + max 1 (2 * a * x)) ^ 2) ≤ 1 := by
      apply (div_le_one hden).2
      nlinarith [sq_nonneg (1 + max 1 (2 * a * x))]
    have hscale : 0 ≤ 2 * a * Real.exp (2 * a * x) := by positivity
    calc
      (a ^ 2 * Real.exp (2 * a * x) /
            (4 * (1 + max 1 (2 * a * x)) ^ 2)) * (2 * x) =
          (2 * a * Real.exp (2 * a * x)) *
            (a * x / (4 * (1 + max 1 (2 * a * x)) ^ 2)) := by ring
      _ ≤ (2 * a * Real.exp (2 * a * x)) * 1 :=
        mul_le_mul_of_nonneg_left hratio hscale
      _ = 2 * a * Real.exp (2 * a * x) := by ring
  rw [hgeom]
  have htangent := mul_le_mul_of_nonneg_right hslope (sub_nonneg.mpr hre)
  nlinarith

/-- Squared modulus of the tangent exponential against the rapid Fock weight. -/
def rapidExponentialFockTangentDensity (a x : ℝ) (z : ℂ) : ℝ :=
  Real.exp (2 * rapidExponentialFockRadialSlope a x * (z.re - x) -
    2 * rapidExponentialFockPotential a ‖z‖)

theorem rapidExponentialFockTangentDensity_le_gaussian
    {a x : ℝ} (ha : 0 < a) (hx : 0 ≤ x) (z : ℂ) :
    rapidExponentialFockTangentDensity a x z ≤
      Real.exp (-2 * rapidExponentialFockPotential a x) *
        Real.exp (-(2 * rapidExponentialFockTangentCurvature a x *
          ‖z - (x : ℂ)‖ ^ 2)) := by
  have h := rapidExponentialFockPotential_bregman_lower ha hx z
  have hexp :
      2 * rapidExponentialFockRadialSlope a x * (z.re - x) -
          2 * rapidExponentialFockPotential a ‖z‖ ≤
        -2 * rapidExponentialFockPotential a x -
          2 * rapidExponentialFockTangentCurvature a x * ‖z - (x : ℂ)‖ ^ 2 := by
    linarith
  rw [rapidExponentialFockTangentDensity, ← Real.exp_add]
  exact Real.exp_le_exp.mpr (by simpa [sub_eq_add_neg] using hexp)

theorem integrable_rapidExponentialFockTangentDensity
    {a x : ℝ} (ha : 0 < a) (hx : 0 ≤ x) :
    Integrable (rapidExponentialFockTangentDensity a x) := by
  let c : ℝ := 2 * rapidExponentialFockTangentCurvature a x
  have hc : 0 < c := mul_pos (by norm_num) (rapidExponentialFockTangentCurvature_pos ha hx)
  let g : ℂ → ℝ := fun z =>
    Real.exp (-2 * rapidExponentialFockPotential a x) *
      Real.exp (-c * ‖z - (x : ℂ)‖ ^ 2)
  have hg : Integrable g := by
    simpa [g] using (integrable_complex_gaussian_sub_real c x hc).const_mul
      (Real.exp (-2 * rapidExponentialFockPotential a x))
  apply hg.mono
  · have hcont : Continuous (rapidExponentialFockTangentDensity a x) := by
      unfold rapidExponentialFockTangentDensity rapidExponentialFockPotential
      fun_prop
    exact hcont.aestronglyMeasurable
  · filter_upwards [] with z
    rw [Real.norm_of_nonneg (by unfold rapidExponentialFockTangentDensity; positivity),
      Real.norm_of_nonneg (by dsimp [g]; positivity)]
    simpa [g, c] using rapidExponentialFockTangentDensity_le_gaussian ha hx z

/-- Plane-norm upper bound for the rapid tangent exponential. -/
theorem integral_rapidExponentialFockTangentDensity_le
    {a x : ℝ} (ha : 0 < a) (hx : 0 ≤ x) :
    (∫ z : ℂ, rapidExponentialFockTangentDensity a x z) ≤
      Real.exp (-2 * rapidExponentialFockPotential a x) *
        (Real.pi / (2 * rapidExponentialFockTangentCurvature a x)) := by
  let c : ℝ := 2 * rapidExponentialFockTangentCurvature a x
  have hc : 0 < c := mul_pos (by norm_num) (rapidExponentialFockTangentCurvature_pos ha hx)
  let g : ℂ → ℝ := fun z =>
    Real.exp (-2 * rapidExponentialFockPotential a x) *
      Real.exp (-c * ‖z - (x : ℂ)‖ ^ 2)
  have hg : Integrable g := by
    simpa [g] using (integrable_complex_gaussian_sub_real c x hc).const_mul
      (Real.exp (-2 * rapidExponentialFockPotential a x))
  have hf := integrable_rapidExponentialFockTangentDensity ha hx
  calc
    (∫ z : ℂ, rapidExponentialFockTangentDensity a x z) ≤ ∫ z : ℂ, g z := by
      apply MeasureTheory.integral_mono_ae hf hg
      filter_upwards [] with z
      simpa [g, c] using rapidExponentialFockTangentDensity_le_gaussian ha hx z
    _ = Real.exp (-2 * rapidExponentialFockPotential a x) * (Real.pi / c) := by
      rw [MeasureTheory.integral_const_mul, integral_complex_gaussian_sub_real c x hc]
    _ = _ := by rfl

end

end RHTower
