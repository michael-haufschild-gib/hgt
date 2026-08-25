import GaloisForLFunctions.HTGeometry.ExponentialDividedDifference
import GaloisForLFunctions.HTGeometry.HolomorphicBallMeanSq
import GaloisForLFunctions.RHTower.RapidExponentialMomentFockNorm
import GaloisForLFunctions.RHTower.RapidExponentialFockPotentialGeometry

/-!
# Local weighted evaluation for the rapid exponential moment-Fock carrier

An explicit radius comparable to `exp (-a x)` keeps the radial exponential potential within a
uniform tangent Bregman error.  Holomorphic mean-square control then bounds evaluation by weighted
mass on this shrinking ball.  No diagonal-kernel lower bound is asserted in this file.
-/

open MeasureTheory Set Metric
open scoped Real

namespace RHTower

noncomputable section

/-- A conservative explicit rapid-Fock radius on the positive real tail. -/
def rapidExponentialFockLocalRadius (a x : ℝ) : ℝ :=
  (8 * (a + 1))⁻¹ * Real.exp (-a * x)

theorem rapidExponentialFockLocalRadius_pos
    {a x : ℝ} (ha : 0 < a) :
    0 < rapidExponentialFockLocalRadius a x := by
  unfold rapidExponentialFockLocalRadius
  positivity

theorem rapidExponentialFockLocalRadius_le_one_eighth
    {a x : ℝ} (ha : 0 < a) (hx : 0 ≤ x) :
    rapidExponentialFockLocalRadius a x ≤ 1 / 8 := by
  have hden : 8 ≤ 8 * (a + 1) := by nlinarith
  have hinv : (8 * (a + 1))⁻¹ ≤ (8 : ℝ)⁻¹ := by
    exact inv_anti₀ (by norm_num) hden
  have hexp : Real.exp (-a * x) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    have : -(a * x) ≤ 0 := neg_nonpos.mpr (mul_nonneg ha.le hx)
    nlinarith
  unfold rapidExponentialFockLocalRadius
  calc
    (8 * (a + 1))⁻¹ * Real.exp (-a * x) ≤
        (8 : ℝ)⁻¹ * Real.exp (-a * x) := by gcongr
    _ ≤ (8 : ℝ)⁻¹ * 1 := by gcongr
    _ = 1 / 8 := by norm_num

theorem rapidExponentialFockPotential_mul_localRadius_sq
    {a x : ℝ} (ha : 0 < a) :
    rapidExponentialFockPotential a x * rapidExponentialFockLocalRadius a x ^ 2 =
      (8 * (a + 1))⁻¹ ^ 2 := by
  have hden : 8 * (a + 1) ≠ 0 := by positivity
  unfold rapidExponentialFockPotential rapidExponentialFockLocalRadius
  rw [mul_pow, ← Real.exp_nat_mul]
  calc
    Real.exp (2 * a * x) *
        ((8 * (a + 1))⁻¹ ^ 2 * Real.exp ((2 : ℕ) * (-a * x))) =
        (8 * (a + 1))⁻¹ ^ 2 *
          (Real.exp (2 * a * x) * Real.exp ((2 : ℕ) * (-a * x))) := by ring
    _ = (8 * (a + 1))⁻¹ ^ 2 *
          Real.exp (2 * a * x + (2 : ℕ) * (-a * x)) := by rw [Real.exp_add]
    _ = (8 * (a + 1))⁻¹ ^ 2 := by
      ring_nf
      simp

private theorem expDivTwo_le_exp_abs (v : ℝ) :
    GaloisForLFunctions.HTGeometry.expDivTwo v ≤ Real.exp |v| := by
  by_cases hv : v ≤ 0
  · have hhalf := GaloisForLFunctions.HTGeometry.expDivTwo_le_half hv
    have hone : 1 / 2 ≤ Real.exp |v| := by
      have : 1 ≤ Real.exp |v| := by
        rw [← Real.exp_zero]
        exact Real.exp_le_exp.mpr (abs_nonneg v)
      linarith
    exact hhalf.trans hone
  · have hv0 : 0 ≤ v := le_of_not_ge hv
    have hmono :
        GaloisForLFunctions.HTGeometry.expDivTwo v ≤
          ∫ _t in (0 : ℝ)..1, Real.exp v := by
      unfold GaloisForLFunctions.HTGeometry.expDivTwo
      apply intervalIntegral.integral_mono_on (by norm_num)
        (GaloisForLFunctions.HTGeometry.intervalIntegrable_expMulTwo v 0 1)
        intervalIntegrable_const
      intro t ht
      have hfac : 0 ≤ 1 - t := by linarith [ht.2]
      have hexp : Real.exp (t * v) ≤ Real.exp v := by
        exact Real.exp_le_exp.mpr (by nlinarith [ht.2])
      calc
        (1 - t) * Real.exp (t * v) ≤ 1 * Real.exp (t * v) := by
          gcongr
          linarith [ht.1]
        _ ≤ Real.exp v := by simpa using hexp
    simpa [abs_of_nonneg hv0] using hmono

private theorem exp_le_tangent_add_sq (v : ℝ) :
    Real.exp v ≤ 1 + v + v ^ 2 * Real.exp |v| := by
  by_cases hv : v = 0
  · subst v
    norm_num
  · have hid := GaloisForLFunctions.HTGeometry.expDivTwo_eq_of_ne hv
    have hdiv := expDivTwo_le_exp_abs v
    calc
      Real.exp v = 1 + v + v ^ 2 *
          GaloisForLFunctions.HTGeometry.expDivTwo v := by
        rw [hid]
        field_simp [pow_ne_zero 2 hv]
        ring
      _ ≤ 1 + v + v ^ 2 * Real.exp |v| := by gcongr

/-- Radial displacement differs from real displacement only quadratically on the positive tail. -/
theorem norm_real_add_le_real_add_re_add_two_mul_normSq
    {x : ℝ} (hx : 1 / 2 ≤ x) (w : ℂ) (hw : ‖w‖ ≤ 1 / 8) :
    ‖(x : ℂ) + w‖ ≤ x + w.re + 2 * ‖w‖ ^ 2 := by
  let A : ℝ := x + w.re
  let q : ℝ := 2 * ‖w‖ ^ 2
  have hre : -‖w‖ ≤ w.re := by
    have h := Complex.abs_re_le_norm w
    rw [abs_le] at h
    exact h.1
  have hA : 3 / 8 ≤ A := by
    dsimp [A]
    linarith
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have him : w.im ^ 2 ≤ ‖w‖ ^ 2 := by
    have h := Complex.abs_im_le_norm w
    have hsq := (sq_le_sq₀ (abs_nonneg w.im) (norm_nonneg w)).2 h
    simpa [sq_abs] using hsq
  have hnormSq : ‖(x : ℂ) + w‖ ^ 2 = A ^ 2 + w.im ^ 2 := by
    rw [Complex.sq_norm]
    simp [Complex.normSq, A]
    ring
  have hsquare : ‖(x : ℂ) + w‖ ^ 2 ≤ (A + q) ^ 2 := by
    rw [hnormSq]
    dsimp [q]
    nlinarith [sq_nonneg ‖w‖]
  have hright : 0 ≤ A + q := by linarith
  exact (sq_le_sq₀ (norm_nonneg _) hright).mp (by simpa [A, q] using hsquare)

/-- Uniform tangent Bregman bound on the explicit rapid local ball. -/
theorem rapidExponentialFockPotential_bregman_upper_local
    {a x : ℝ} (ha : 0 < a) (hx : 1 / 2 ≤ x) (w : ℂ)
    (hw : ‖w‖ ≤ rapidExponentialFockLocalRadius a x) :
    rapidExponentialFockPotential a ‖(x : ℂ) + w‖ ≤
      rapidExponentialFockPotential a x +
        rapidExponentialFockRadialSlope a x * w.re + 1 := by
  let δ : ℝ := rapidExponentialFockLocalRadius a x
  let r : ℝ := ‖(x : ℂ) + w‖
  let v : ℝ := 2 * a * (r - x)
  have hx0 : 0 ≤ x := by linarith
  have hδ : δ ≤ 1 / 8 := rapidExponentialFockLocalRadius_le_one_eighth ha hx0
  have hrUpper : r ≤ x + w.re + 2 * ‖w‖ ^ 2 :=
    norm_real_add_le_real_add_re_add_two_mul_normSq hx w (hw.trans hδ)
  have hrAbs : |r - x| ≤ ‖w‖ := by
    dsimp [r]
    rw [abs_le]
    constructor
    · have h := norm_sub_norm_le (x : ℂ) ((x : ℂ) + w)
      simpa [abs_of_nonneg hx0, add_comm] using h
    · have h := norm_sub_norm_le ((x : ℂ) + w) (x : ℂ)
      simpa [abs_of_nonneg hx0] using h
  have hvAbs : |v| ≤ 1 / 4 := by
    have hax : Real.exp (-a * x) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have : -(a * x) ≤ 0 := neg_nonpos.mpr (mul_nonneg ha.le hx0)
      nlinarith
    have haFrac : a / (a + 1) ≤ 1 := by
      have hden : 0 < a + 1 := by positivity
      rw [div_le_one hden]
      linarith
    calc
      |v| = 2 * a * |r - x| := by simp [v, abs_mul, abs_of_pos ha]
      _ ≤ 2 * a * ‖w‖ := by gcongr
      _ ≤ 2 * a * δ := by gcongr
      _ = (a / (4 * (a + 1))) * Real.exp (-a * x) := by
        dsimp [δ, rapidExponentialFockLocalRadius]
        field_simp
        ring
      _ ≤ (a / (4 * (a + 1))) * 1 := by gcongr
      _ ≤ 1 / 4 := by
        have hid : a / (4 * (a + 1)) = (a / (a + 1)) / 4 := by
          field_simp
        rw [hid, mul_one]
        exact div_le_div_of_nonneg_right haFrac (by norm_num)
  have hexpAbs : Real.exp |v| < 3 := by
    calc
      Real.exp |v| ≤ Real.exp 1 := Real.exp_le_exp.mpr (hvAbs.trans (by norm_num))
      _ < 2.7182818286 := Real.exp_one_lt_d9
      _ < 3 := by norm_num
  have hexp := exp_le_tangent_add_sq v
  have hpotentialIdentity :
      rapidExponentialFockPotential a r =
        rapidExponentialFockPotential a x * Real.exp v := by
    unfold rapidExponentialFockPotential
    rw [← Real.exp_add]
    congr 1
    dsimp [v]
    ring
  have hvUpper : v ≤ 2 * a * w.re + 4 * a * ‖w‖ ^ 2 := by
    dsimp [v]
    nlinarith
  have hlocalSq :
      rapidExponentialFockPotential a x * ‖w‖ ^ 2 ≤
        (8 * (a + 1))⁻¹ ^ 2 := by
    have hsq : ‖w‖ ^ 2 ≤ δ ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) (rapidExponentialFockLocalRadius_pos ha).le).2 hw
    calc
      rapidExponentialFockPotential a x * ‖w‖ ^ 2 ≤
          rapidExponentialFockPotential a x * δ ^ 2 := by
            exact mul_le_mul_of_nonneg_left hsq
              (by unfold rapidExponentialFockPotential; positivity)
      _ = (8 * (a + 1))⁻¹ ^ 2 := by
        simpa [δ] using rapidExponentialFockPotential_mul_localRadius_sq ha
  have hvSq : v ^ 2 ≤ 4 * a ^ 2 * ‖w‖ ^ 2 := by
    have hvAbs' : |v| ≤ 2 * a * ‖w‖ := by
      calc
        |v| = 2 * a * |r - x| := by simp [v, abs_mul, abs_of_pos ha]
        _ ≤ 2 * a * ‖w‖ := by gcongr
    have hright : 0 ≤ 2 * a * ‖w‖ := by positivity
    have hsq := (sq_le_sq₀ (abs_nonneg v) hright).2 hvAbs'
    have hsq' : v ^ 2 ≤ (2 * a * ‖w‖) ^ 2 := by
      simpa [sq_abs] using hsq
    nlinarith
  rw [hpotentialIdentity]
  calc
    rapidExponentialFockPotential a x * Real.exp v ≤
        rapidExponentialFockPotential a x *
          (1 + v + v ^ 2 * Real.exp |v|) := by
            exact mul_le_mul_of_nonneg_left hexp
              (by unfold rapidExponentialFockPotential; positivity)
    _ ≤ rapidExponentialFockPotential a x +
          rapidExponentialFockRadialSlope a x * w.re +
          rapidExponentialFockPotential a x *
            ((4 * a + 12 * a ^ 2) * ‖w‖ ^ 2) := by
      have hphi : 0 ≤ rapidExponentialFockPotential a x := by
        unfold rapidExponentialFockPotential
        positivity
      have hvExp : v ^ 2 * Real.exp |v| ≤
          12 * a ^ 2 * ‖w‖ ^ 2 := by
        calc
          v ^ 2 * Real.exp |v| ≤
              (4 * a ^ 2 * ‖w‖ ^ 2) * Real.exp |v| := by
                gcongr
          _ ≤ (4 * a ^ 2 * ‖w‖ ^ 2) * 3 := by gcongr
          _ = 12 * a ^ 2 * ‖w‖ ^ 2 := by ring
      have hlinear := mul_le_mul_of_nonneg_left hvUpper hphi
      have hquadratic := mul_le_mul_of_nonneg_left hvExp hphi
      calc
        rapidExponentialFockPotential a x *
            (1 + v + v ^ 2 * Real.exp |v|) =
            rapidExponentialFockPotential a x +
              rapidExponentialFockPotential a x * v +
              rapidExponentialFockPotential a x *
                (v ^ 2 * Real.exp |v|) := by ring
        _ ≤ rapidExponentialFockPotential a x +
              rapidExponentialFockPotential a x *
                (2 * a * w.re + 4 * a * ‖w‖ ^ 2) +
              rapidExponentialFockPotential a x *
                (12 * a ^ 2 * ‖w‖ ^ 2) := by gcongr
        _ = rapidExponentialFockPotential a x +
              rapidExponentialFockRadialSlope a x * w.re +
              rapidExponentialFockPotential a x *
                ((4 * a + 12 * a ^ 2) * ‖w‖ ^ 2) := by
          unfold rapidExponentialFockPotential rapidExponentialFockRadialSlope
          ring
    _ ≤ rapidExponentialFockPotential a x +
          rapidExponentialFockRadialSlope a x * w.re + 1 := by
      have hcoef :
          (4 * a + 12 * a ^ 2) * (8 * (a + 1))⁻¹ ^ 2 ≤ 1 := by
        have hden : 0 < 8 * (a + 1) := by positivity
        rw [inv_pow]
        apply (div_le_iff₀ (sq_pos_of_pos hden)).2
        nlinarith [sq_nonneg (a + 1)]
      have hrem :
          rapidExponentialFockPotential a x *
              ((4 * a + 12 * a ^ 2) * ‖w‖ ^ 2) ≤ 1 := by
        calc
          rapidExponentialFockPotential a x *
              ((4 * a + 12 * a ^ 2) * ‖w‖ ^ 2) =
              (4 * a + 12 * a ^ 2) *
                (rapidExponentialFockPotential a x * ‖w‖ ^ 2) := by ring
          _ ≤ (4 * a + 12 * a ^ 2) * (8 * (a + 1))⁻¹ ^ 2 := by
            gcongr
          _ ≤ 1 := hcoef
      linarith

/-- Holomorphic tangent gauge cancelling first-order rapid-weight variation. -/
def rapidExponentialFockTangentGauge
    (a x : ℝ) (F : ℂ → ℂ) (z : ℂ) : ℂ :=
  F z * Complex.exp (-(rapidExponentialFockRadialSlope a x : ℂ) * (z - x))

theorem differentiable_rapidExponentialFockTangentGauge
    (a x : ℝ) (F : ℂ → ℂ) (hF : Differentiable ℂ F) :
    Differentiable ℂ (rapidExponentialFockTangentGauge a x F) := by
  unfold rapidExponentialFockTangentGauge
  fun_prop

theorem normSq_rapidExponentialFockTangentGauge
    (a x : ℝ) (F : ℂ → ℂ) (z : ℂ) :
    ‖rapidExponentialFockTangentGauge a x F z‖ ^ 2 =
      ‖F z‖ ^ 2 *
        Real.exp (-2 * rapidExponentialFockRadialSlope a x * (z.re - x)) := by
  unfold rapidExponentialFockTangentGauge
  rw [norm_mul, Complex.norm_exp, mul_pow]
  congr 1
  rw [← Real.exp_nat_mul]
  congr 1
  simp
  ring

/-- Gauged square density is controlled by the original rapid weighted density on a local ball. -/
theorem normSq_rapidExponentialFockTangentGauge_le_weighted
    {a x : ℝ} (ha : 0 < a) (hx : 1 / 2 ≤ x) (F : ℂ → ℂ) (z : ℂ)
    (hz : z ∈ Metric.ball (x : ℂ) (rapidExponentialFockLocalRadius a x)) :
    ‖rapidExponentialFockTangentGauge a x F z‖ ^ 2 ≤
      Real.exp (2 * rapidExponentialFockPotential a x + 2) *
        (‖F z‖ ^ 2 * Real.exp (-2 * rapidExponentialFockPotential a ‖z‖)) := by
  let w : ℂ := z - x
  have hw : ‖w‖ ≤ rapidExponentialFockLocalRadius a x := by
    exact le_of_lt (by simpa [w, Metric.mem_ball, dist_eq_norm] using hz)
  have hzadd : (x : ℂ) + w = z := by dsimp [w]; abel
  have hphi := rapidExponentialFockPotential_bregman_upper_local ha hx w hw
  rw [hzadd] at hphi
  have hexp :
      -2 * rapidExponentialFockRadialSlope a x * (z.re - x) ≤
        2 * rapidExponentialFockPotential a x + 2 -
          2 * rapidExponentialFockPotential a ‖z‖ := by
    have hwre : w.re = z.re - x := by simp [w]
    rw [hwre] at hphi
    linarith
  rw [normSq_rapidExponentialFockTangentGauge]
  calc
    ‖F z‖ ^ 2 *
          Real.exp (-2 * rapidExponentialFockRadialSlope a x * (z.re - x)) ≤
        ‖F z‖ ^ 2 * Real.exp
          (2 * rapidExponentialFockPotential a x + 2 -
            2 * rapidExponentialFockPotential a ‖z‖) := by
      exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) (sq_nonneg _)
    _ = Real.exp (2 * rapidExponentialFockPotential a x + 2) *
        (‖F z‖ ^ 2 * Real.exp (-2 * rapidExponentialFockPotential a ‖z‖)) := by
      rw [show 2 * rapidExponentialFockPotential a x + 2 -
          2 * rapidExponentialFockPotential a ‖z‖ =
        (2 * rapidExponentialFockPotential a x + 2) +
          (-2 * rapidExponentialFockPotential a ‖z‖) by ring, Real.exp_add]
      ring

/-- Local weighted mean-value estimate for the rapid carrier on the positive real tail. -/
theorem rapidExponentialFock_local_weighted_mean
    {a x : ℝ} (ha : 0 < a) (hx : 1 / 2 ≤ x)
    (F : ℂ → ℂ) (hF : Differentiable ℂ F) :
    Real.pi * rapidExponentialFockLocalRadius a x ^ 2 * ‖F (x : ℂ)‖ ^ 2 ≤
      Real.exp (2 * rapidExponentialFockPotential a x + 2) *
        ∫ z in Metric.ball (x : ℂ) (rapidExponentialFockLocalRadius a x),
          ‖F z‖ ^ 2 * Real.exp (-2 * rapidExponentialFockPotential a ‖z‖) := by
  let G : ℂ → ℂ := rapidExponentialFockTangentGauge a x F
  have hG := differentiable_rapidExponentialFockTangentGauge a x F hF
  have hmean := GaloisForLFunctions.HTGeometry.normSq_value_mul_area_le_integral_ball
    (R := rapidExponentialFockLocalRadius a x) G hG (x : ℂ)
      (rapidExponentialFockLocalRadius_pos ha)
  have hGx : G (x : ℂ) = F (x : ℂ) := by
    simp [G, rapidExponentialFockTangentGauge]
  rw [hGx] at hmean
  let W : ℂ → ℝ := fun z =>
    Real.exp (2 * rapidExponentialFockPotential a x + 2) *
      (‖F z‖ ^ 2 * Real.exp (-2 * rapidExponentialFockPotential a ‖z‖))
  have hGint : IntegrableOn (fun z => ‖G z‖ ^ 2)
      (Metric.ball (x : ℂ) (rapidExponentialFockLocalRadius a x)) := by
    apply ((hG.continuous.norm.pow 2).continuousOn.integrableOn_compact
      (isCompact_closedBall (x : ℂ) (rapidExponentialFockLocalRadius a x))).mono_set
    exact Metric.ball_subset_closedBall
  have hWcont : Continuous W := by
    unfold W
    exact continuous_const.mul ((hF.continuous.norm.pow 2).mul
      (Real.continuous_exp.comp
        (continuous_const.mul
          ((continuous_rapidExponentialFockPotential a).comp continuous_norm))))
  have hWint : IntegrableOn W
      (Metric.ball (x : ℂ) (rapidExponentialFockLocalRadius a x)) := by
    apply (hWcont.continuousOn.integrableOn_compact
      (isCompact_closedBall (x : ℂ) (rapidExponentialFockLocalRadius a x))).mono_set
    exact Metric.ball_subset_closedBall
  have hint :
      (∫ z in Metric.ball (x : ℂ) (rapidExponentialFockLocalRadius a x), ‖G z‖ ^ 2) ≤
        ∫ z in Metric.ball (x : ℂ) (rapidExponentialFockLocalRadius a x), W z := by
    change Integrable (fun z => ‖G z‖ ^ 2)
      (volume.restrict (Metric.ball (x : ℂ) (rapidExponentialFockLocalRadius a x))) at hGint
    change Integrable W
      (volume.restrict (Metric.ball (x : ℂ) (rapidExponentialFockLocalRadius a x))) at hWint
    apply MeasureTheory.integral_mono_ae hGint hWint
    filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
    exact normSq_rapidExponentialFockTangentGauge_le_weighted ha hx F z hz
  calc
    Real.pi * rapidExponentialFockLocalRadius a x ^ 2 * ‖F (x : ℂ)‖ ^ 2 ≤
        ∫ z in Metric.ball (x : ℂ) (rapidExponentialFockLocalRadius a x),
          ‖G z‖ ^ 2 := hmean
    _ ≤ ∫ z in Metric.ball (x : ℂ) (rapidExponentialFockLocalRadius a x), W z := hint
    _ = Real.exp (2 * rapidExponentialFockPotential a x + 2) *
        ∫ z in Metric.ball (x : ℂ) (rapidExponentialFockLocalRadius a x),
          ‖F z‖ ^ 2 * Real.exp (-2 * rapidExponentialFockPotential a ‖z‖) := by
      rw [MeasureTheory.integral_const_mul]

end

end RHTower
