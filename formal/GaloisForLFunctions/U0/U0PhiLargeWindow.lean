/-
# The window branch at the SHARP threshold: `phiB b` on the disk, `‖b‖ > 2+√2`

Sharp-threshold parameterization of the window construction.  Two b-dependent radii replace the
crude `‖b‖ − 23/20` far field of the `‖b‖ ≥ 4` pass:

* the far field is everything beyond the escape fixed point:  `farB b = {‖w‖ > xStar ‖b‖}`
  with `xStar B = (1+√(1+4B))/2`.  The fixed-point identity `xStar² = xStar + B` makes this set
  EXACTLY forward invariant and bounds the series ratio uniformly by
  `rMax b = ‖b‖/(‖b‖ + xStar ‖b‖) < 1` — no margin inequalities, no escape-rate constant;

* the window disk is `ball 0 (rB b)` with `rB b = min(21/20, √(1 + (‖b‖−1−xStar ‖b‖)/2))`.
  For `‖b‖ > 2+√2` the clearance `‖b‖ − 1 > xStar ‖b‖` (`xStar_lt_of_sharp`) is positive, so
  `rB b > 1` — the disk crosses the unit circle — and one quadratic step from it lands in
  `farB b`.  The threshold is exactly where the clearance vanishes.

The series ratio may exceed `1/2` near the threshold, so the log estimate is the general-radius
`‖log(1+u)‖ ≤ (1−r)⁻¹‖u‖` (`U0LogBoundGeneral`).  For complex `b` the branch stays rotated
through the parameter:

  `phiB b z := exp(½·(log b + log(1 + z²/b) + tail(z² + b)))`

— `1 + z²/b` stays in the right half-plane on the disk, so `phiB` is analytic across the unit
circle, and `phiB² = bottcherCoord b ∘ (z ↦ z² + b)` branch-free at the `exp` level.  The
functional equation, dyadic pullback chain, and the window engine instance parameterize as
before; the annulus preconnectedness is proven for every radius `r > 1`.
-/
import GaloisForLFunctions.U0.U0PhiFourWindow
import GaloisForLFunctions.U0.U0WindowNormalization
import GaloisForLFunctions.U0.U0MonotoneEscape
import GaloisForLFunctions.U0.U0LogBoundGeneral

open Complex Filter Topology Metric Set Polynomial Bottcher
open U0 U0NaturalBoundary U0WindowNormalization U0MonotoneEscape U0LogBoundGeneral

namespace U0PhiLargeWindow

/-- **The sharp far field**: everything beyond the escape fixed point `xStar ‖b‖`. -/
def farB (b : ℂ) : Set ℂ := {w : ℂ | xStar ‖b‖ < ‖w‖}

/-- The uniform series-ratio bound on the sharp far field: `‖b/w²‖ ≤ rMax b < 1`. -/
noncomputable def rMax (b : ℂ) : ℝ := ‖b‖ / (‖b‖ + xStar ‖b‖)

/-- **The b-dependent window radius** `min(21/20, √(1 + clearance/2))`, where the clearance is
`‖b‖ − 1 − xStar ‖b‖ > 0` exactly above the sharp threshold. -/
noncomputable def rB (b : ℂ) : ℝ :=
  min (21 / 20) (Real.sqrt (1 + (‖b‖ - 1 - xStar ‖b‖) / 2))

theorem norm_gt_two {b : ℂ} (hb : 2 + Real.sqrt 2 < ‖b‖) : 2 < ‖b‖ := by
  linarith [Real.sqrt_nonneg 2]

theorem isOpen_farB (b : ℂ) : IsOpen (farB b) := isOpen_lt continuous_const continuous_norm

theorem farB_ne_zero {b w : ℂ} (hb : 2 < ‖b‖) (hw : w ∈ farB b) : w ≠ 0 := by
  intro h0
  have h1 : xStar ‖b‖ < ‖w‖ := hw
  have hxs1 : 1 < xStar ‖b‖ := one_lt_xStar (by linarith)
  rw [h0] at h1
  simp at h1
  linarith

/-- **Exact forward invariance** of the sharp far field, from the fixed-point identity
`xStar² = xStar + ‖b‖`. -/
theorem farB_invariant {b w : ℂ} (hb : 2 < ‖b‖) (hw : w ∈ farB b) :
    quadratic b w ∈ farB b := by
  have hx : xStar ‖b‖ < ‖w‖ := hw
  have hxs1 : 1 < xStar ‖b‖ := one_lt_xStar (by linarith)
  have hfix : xStar ‖b‖ ^ 2 - xStar ‖b‖ - ‖b‖ = 0 := xStar_fixed (by linarith)
  show xStar ‖b‖ < ‖w ^ 2 + b‖
  have htri : ‖w ^ 2‖ ≤ ‖w ^ 2 + b‖ + ‖b‖ := norm_le_add_norm_add _ _
  have hp : ‖w ^ 2‖ = ‖w‖ ^ 2 := norm_pow w 2
  nlinarith [hx, htri, hxs1, hfix,
    mul_pos (sub_pos.mpr hx) (show (0:ℝ) < ‖w‖ + xStar ‖b‖ by linarith)]

theorem farB_iterate {b : ℂ} (hb : 2 < ‖b‖) (k : ℕ) {w : ℂ} (hw : w ∈ farB b) :
    (quadratic b)^[k] w ∈ farB b := by
  induction k with
  | zero => simpa using hw
  | succ m ih =>
    rw [Function.iterate_succ_apply']
    exact farB_invariant hb ih

theorem rMax_nonneg {b : ℂ} (hb : 2 < ‖b‖) : 0 ≤ rMax b := by
  have hxs1 : 1 < xStar ‖b‖ := one_lt_xStar (by linarith)
  exact div_nonneg (norm_nonneg b) (by linarith)

theorem rMax_lt_one {b : ℂ} (hb : 2 < ‖b‖) : rMax b < 1 := by
  have hxs1 : 1 < xStar ‖b‖ := one_lt_xStar (by linarith)
  rw [rMax, div_lt_one (by linarith)]
  linarith

/-- The series ratio is uniformly bounded by `rMax b` on the sharp far field. -/
theorem farB_ratio_le {b w : ℂ} (hb : 2 < ‖b‖) (hw : w ∈ farB b) :
    ‖b / w ^ 2‖ ≤ rMax b := by
  have hx : xStar ‖b‖ < ‖w‖ := hw
  have hxs1 : 1 < xStar ‖b‖ := one_lt_xStar (by linarith)
  have hfix : xStar ‖b‖ ^ 2 - xStar ‖b‖ - ‖b‖ = 0 := xStar_fixed (by linarith)
  have hw2 : ‖b‖ + xStar ‖b‖ ≤ ‖w‖ ^ 2 := by
    nlinarith [mul_pos (sub_pos.mpr hx) (show (0:ℝ) < ‖w‖ + xStar ‖b‖ by linarith), hfix]
  have hwpos : (0 : ℝ) < ‖w‖ := by linarith
  rw [norm_div, norm_pow, rMax,
    div_le_div_iff₀ (pow_pos hwpos 2) (by linarith : (0:ℝ) < ‖b‖ + xStar ‖b‖)]
  exact mul_le_mul_of_nonneg_left hw2 (norm_nonneg b)

theorem farB_ratio_lt_one {b w : ℂ} (hb : 2 < ‖b‖) (hw : w ∈ farB b) :
    ‖b / w ^ 2‖ < 1 :=
  lt_of_le_of_lt (farB_ratio_le hb hw) (rMax_lt_one hb)

/-- Geometric term bound on the sharp far field, with the general-radius log constant. -/
theorem norm_term_le_B {b w : ℂ} (hb : 2 < ‖b‖) (hw : w ∈ farB b) (k : ℕ) :
    ‖bottcherLogTerm b w k‖ ≤ (1 - rMax b)⁻¹ * rMax b * (1 / 2 : ℝ) ^ (k + 1) := by
  have hA : (quadratic b)^[k] w ∈ farB b := farB_iterate hb k hw
  have hq : ‖b / ((quadratic b)^[k] w) ^ 2‖ ≤ rMax b := farB_ratio_le hb hA
  have hlog := norm_clog_one_add_le_of_le (rMax_lt_one hb) hq
  have hCpos : (0 : ℝ) < (1 - rMax b)⁻¹ := by
    have := rMax_lt_one hb
    exact inv_pos.mpr (by linarith)
  unfold bottcherLogTerm
  rw [norm_mul, norm_inv, norm_pow, Complex.norm_ofNat]
  calc ((2 : ℝ) ^ (k + 1))⁻¹ * ‖Complex.log (1 + b / ((quadratic b)^[k] w) ^ 2)‖
      ≤ ((2 : ℝ) ^ (k + 1))⁻¹ * ((1 - rMax b)⁻¹ * rMax b) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        calc ‖Complex.log (1 + b / ((quadratic b)^[k] w) ^ 2)‖
            ≤ (1 - rMax b)⁻¹ * ‖b / ((quadratic b)^[k] w) ^ 2‖ := hlog
          _ ≤ (1 - rMax b)⁻¹ * rMax b := mul_le_mul_of_nonneg_left hq hCpos.le
    _ = (1 - rMax b)⁻¹ * rMax b * (1 / 2 : ℝ) ^ (k + 1) := by
        rw [one_div, inv_pow]
        ring

theorem summable_term_B {b w : ℂ} (hb : 2 < ‖b‖) (hw : w ∈ farB b) :
    Summable (fun k => bottcherLogTerm b w k) := by
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun k => norm_nonneg _) (fun k => norm_term_le_B hb hw k)
  have h := summable_geometric_of_lt_one (r := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
  exact (h.mul_left ((1 - rMax b)⁻¹ * rMax b * (1 / 2))).congr fun k => by ring

/-- The Böttcher log-series tail is differentiable on the sharp far field. -/
theorem tail_differentiableOn_B {b : ℂ} (hb : 2 < ‖b‖) :
    DifferentiableOn ℂ (fun w => ∑' k, bottcherLogTerm b w k) (farB b) := by
  have hqd : Differentiable ℂ (quadratic b) := by
    have : (quadratic b) = fun z => z ^ 2 + b := by
      funext z; exact quadratic_apply b z
    rw [this]
    exact (differentiable_pow 2).add_const b
  refine differentiableOn_tsum_of_summable_norm
    (u := fun k => (1 - rMax b)⁻¹ * rMax b * (1 / 2 : ℝ) ^ (k + 1)) ?_ ?_ (isOpen_farB b) ?_
  · have hgeom : Summable
        (fun k : ℕ => ((1 - rMax b)⁻¹ * rMax b * (1 / 2)) * (1 / 2 : ℝ) ^ k) :=
      (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _
    refine hgeom.congr fun k => ?_
    ring
  · intro k w hw
    apply DifferentiableAt.differentiableWithinAt
    have hA : (quadratic b)^[k] w ∈ farB b := farB_iterate hb k hw
    have hAne : ((quadratic b)^[k] w) ^ 2 ≠ 0 := pow_ne_zero 2 (farB_ne_zero hb hA)
    have hiter : DifferentiableAt ℂ ((quadratic b)^[k]) w := (hqd.iterate k).differentiableAt
    have hinner : DifferentiableAt ℂ (fun v => 1 + b / ((quadratic b)^[k] v) ^ 2) w := by
      have hdiv : DifferentiableAt ℂ (fun v => b / ((quadratic b)^[k] v) ^ 2) w :=
        (differentiableAt_const _).div (hiter.pow 2) hAne
      exact (differentiableAt_const (1 : ℂ)).add hdiv
    have hslit : (1 + b / ((quadratic b)^[k] w) ^ 2) ∈ slitPlane := by
      refine Or.inl ?_
      have hre : |(b / ((quadratic b)^[k] w) ^ 2).re|
          ≤ ‖b / ((quadratic b)^[k] w) ^ 2‖ := Complex.abs_re_le_norm _
      have hq := farB_ratio_le hb hA
      have hlt := rMax_lt_one hb
      have : (1 + b / ((quadratic b)^[k] w) ^ 2).re
          = 1 + (b / ((quadratic b)^[k] w) ^ 2).re := by
        simp [Complex.add_re]
      rw [this]
      have habs := abs_le.mp (le_trans hre hq)
      linarith [habs.1]
    exact (hinner.clog hslit).const_mul _
  · intro k w hw
    exact norm_term_le_B hb hw k

/-! ## The b-dependent window radius -/

theorem rB_le (b : ℂ) : rB b ≤ 21 / 20 := min_le_left _ _

/-- Above the sharp threshold the window disk crosses the unit circle. -/
theorem one_lt_rB {b : ℂ} (hb : 2 + Real.sqrt 2 < ‖b‖) : 1 < rB b := by
  have hcl := xStar_lt_of_sharp hb
  refine lt_min (by norm_num) ?_
  have h1 : (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
  rw [h1]
  exact Real.sqrt_lt_sqrt (by norm_num) (by linarith)

theorem rB_sq_le {b : ℂ} (hb : 2 + Real.sqrt 2 < ‖b‖) :
    rB b ^ 2 ≤ 1 + (‖b‖ - 1 - xStar ‖b‖) / 2 := by
  have hcl := xStar_lt_of_sharp hb
  have harg : (0 : ℝ) ≤ 1 + (‖b‖ - 1 - xStar ‖b‖) / 2 := by linarith
  have h1 : rB b ≤ Real.sqrt (1 + (‖b‖ - 1 - xStar ‖b‖) / 2) := min_le_right _ _
  have h0 : (0 : ℝ) ≤ rB b := le_min (by norm_num) (Real.sqrt_nonneg _)
  calc rB b ^ 2 ≤ Real.sqrt (1 + (‖b‖ - 1 - xStar ‖b‖) / 2) ^ 2 := by nlinarith [h1, h0]
    _ = 1 + (‖b‖ - 1 - xStar ‖b‖) / 2 := Real.sq_sqrt harg

/-! ## The parameterized branch -/

/-- **The window branch at parameter `b`**: the branch is rotated through `log b`, so it is
well defined for every complex `b` above the sharp threshold — no slit-plane condition on
`z² + b`. -/
noncomputable def phiB (b z : ℂ) : ℂ :=
  Complex.exp ((2 : ℂ)⁻¹ * (Complex.log b + Complex.log (1 + z ^ 2 / b)
    + ∑' k, bottcherLogTerm b (quadratic b z) k))

theorem phiB_ne_zero (b z : ℂ) : phiB b z ≠ 0 := Complex.exp_ne_zero _

theorem b_ne_zero {b : ℂ} (hb : 2 < ‖b‖) : b ≠ 0 := by
  intro h0
  rw [h0] at hb
  simp at hb
  linarith

/-- On the window disk the normalized ratio stays in the right half-plane. -/
theorem ratio_re_ge {b z : ℂ} (hb : 2 + Real.sqrt 2 < ‖b‖) (hz : z ∈ ball (0 : ℂ) (rB b)) :
    (1 / 2 : ℝ) ≤ (1 + z ^ 2 / b).re := by
  have hz' : ‖z‖ < rB b := by simpa [mem_ball, dist_zero_right] using hz
  have hz21 : ‖z‖ < 21 / 20 := lt_of_lt_of_le hz' (rB_le b)
  have hs1 : (1 : ℝ) ≤ Real.sqrt 2 := by
    nlinarith [Real.sq_sqrt (show (0:ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
  have hb0 : (0 : ℝ) < ‖b‖ := by linarith
  have hnorm : ‖z ^ 2 / b‖ ≤ 1 / 2 := by
    rw [norm_div, norm_pow, div_le_iff₀ hb0]
    nlinarith [hz21, norm_nonneg z, hs1, hb]
  have hre : |(z ^ 2 / b).re| ≤ ‖z ^ 2 / b‖ := Complex.abs_re_le_norm _
  have habs := abs_le.mp (le_trans hre hnorm)
  have h1 : (1 + z ^ 2 / b).re = 1 + (z ^ 2 / b).re := by
    simp [Complex.add_re]
  rw [h1]
  linarith [habs.1]

theorem ratio_ne_zero {b z : ℂ} (hb : 2 + Real.sqrt 2 < ‖b‖) (hz : z ∈ ball (0 : ℂ) (rB b)) :
    (1 : ℂ) + z ^ 2 / b ≠ 0 := by
  intro h0
  have := ratio_re_ge hb hz
  rw [h0] at this
  simp at this
  linarith

theorem ratio_mem_slitPlane {b z : ℂ} (hb : 2 + Real.sqrt 2 < ‖b‖)
    (hz : z ∈ ball (0 : ℂ) (rB b)) :
    (1 : ℂ) + z ^ 2 / b ∈ slitPlane := by
  refine Or.inl ?_
  have := ratio_re_ge hb hz
  linarith

/-- **One quadratic step from the window disk lands in the sharp far field** — this is exactly
the clearance `‖b‖ − rB² ≥ xStar + clearance/2 > xStar`, available above the sharp threshold. -/
theorem quadB_mem_farB {b z : ℂ} (hb : 2 + Real.sqrt 2 < ‖b‖) (hz : z ∈ ball (0 : ℂ) (rB b)) :
    quadratic b z ∈ farB b := by
  have hz' : ‖z‖ < rB b := by simpa [mem_ball, dist_zero_right] using hz
  have hrsq := rB_sq_le hb
  have hcl := xStar_lt_of_sharp hb
  show xStar ‖b‖ < ‖z ^ 2 + b‖
  have htri : ‖b‖ ≤ ‖z ^ 2 + b‖ + ‖z ^ 2‖ := by
    calc ‖b‖ = ‖z ^ 2 + b - z ^ 2‖ := by ring_nf
      _ ≤ ‖z ^ 2 + b‖ + ‖z ^ 2‖ := norm_sub_le _ _
  have hp : ‖z ^ 2‖ = ‖z‖ ^ 2 := norm_pow z 2
  have hzr : ‖z‖ ^ 2 < rB b ^ 2 := by
    nlinarith [hz', norm_nonneg z, one_lt_rB hb]
  nlinarith [htri, hzr, hrsq, hcl]

theorem quadB_ne_zero {b z : ℂ} (hb : 2 + Real.sqrt 2 < ‖b‖) (hz : z ∈ ball (0 : ℂ) (rB b)) :
    z ^ 2 + b ≠ 0 := by
  have hfar : quadratic b z ∈ farB b := quadB_mem_farB hb hz
  have := farB_ne_zero (norm_gt_two hb) hfar
  simpa [quadratic_apply] using this

/-- The branch squares to the genuine Böttcher coordinate one step ahead — branch-free at the
`exp` level, for every `‖b‖` above the sharp threshold. -/
theorem phiB_sq {b z : ℂ} (hb : 2 + Real.sqrt 2 < ‖b‖) (hz : z ∈ ball (0 : ℂ) (rB b)) :
    phiB b z ^ 2 = bottcherCoord b (quadratic b z) := by
  have hb0 : b ≠ 0 := b_ne_zero (norm_gt_two hb)
  have hrne : (1 : ℂ) + z ^ 2 / b ≠ 0 := ratio_ne_zero hb hz
  have hzsq : z ^ 2 + b ≠ 0 := quadB_ne_zero hb hz
  have hδ : Complex.exp (Complex.log b + Complex.log (1 + z ^ 2 / b)
      - Complex.log (z ^ 2 + b)) = 1 := by
    rw [Complex.exp_sub, Complex.exp_add, Complex.exp_log hb0, Complex.exp_log hrne,
      Complex.exp_log hzsq]
    rw [div_eq_one_iff_eq hzsq]
    field_simp
    ring
  have hqz : quadratic b z = z ^ 2 + b := rfl
  unfold phiB bottcherCoord bottcherLog
  rw [pow_two, ← Complex.exp_add]
  calc Complex.exp ((2 : ℂ)⁻¹ * (Complex.log b + Complex.log (1 + z ^ 2 / b)
        + ∑' k, bottcherLogTerm b (quadratic b z) k)
      + (2 : ℂ)⁻¹ * (Complex.log b + Complex.log (1 + z ^ 2 / b)
        + ∑' k, bottcherLogTerm b (quadratic b z) k))
      = Complex.exp ((Complex.log (quadratic b z)
          + ∑' k, bottcherLogTerm b (quadratic b z) k)
        + (Complex.log b + Complex.log (1 + z ^ 2 / b) - Complex.log (z ^ 2 + b))) := by
        rw [hqz]
        congr 1
        ring
    _ = Complex.exp (Complex.log (quadratic b z)
          + ∑' k, bottcherLogTerm b (quadratic b z) k)
        * Complex.exp (Complex.log b + Complex.log (1 + z ^ 2 / b)
          - Complex.log (z ^ 2 + b)) := Complex.exp_add _ _
    _ = Complex.exp (Complex.log (quadratic b z)
          + ∑' k, bottcherLogTerm b (quadratic b z) k) := by
        rw [hδ, mul_one]

/-- **`phiB b` is analytic on the whole disk `ball 0 (rB b)` — across the unit circle.** -/
theorem phiB_analytic {b : ℂ} (hb : 2 + Real.sqrt 2 < ‖b‖) :
    AnalyticOnNhd ℂ (phiB b) (ball (0 : ℂ) (rB b)) := by
  apply DifferentiableOn.analyticOnNhd _ isOpen_ball
  intro z hz
  apply DifferentiableAt.differentiableWithinAt
  have hqd : DifferentiableAt ℂ (quadratic b) z := by
    have : (quadratic b) = fun v => v ^ 2 + b := by
      funext v; exact quadratic_apply b v
    rw [this]
    exact ((differentiable_pow 2).add_const b).differentiableAt
  have hratio : DifferentiableAt ℂ (fun v => Complex.log (1 + v ^ 2 / b)) z := by
    have hin : DifferentiableAt ℂ (fun v : ℂ => 1 + v ^ 2 / b) z := by
      have : DifferentiableAt ℂ (fun v : ℂ => v ^ 2 / b) z :=
        (differentiableAt_pow 2).div_const b
      exact (differentiableAt_const (1 : ℂ)).add this
    exact hin.clog (ratio_mem_slitPlane hb hz)
  have htail : DifferentiableAt ℂ (fun v => ∑' k, bottcherLogTerm b (quadratic b v) k) z := by
    have hT : DifferentiableAt ℂ (fun w => ∑' k, bottcherLogTerm b w k) (quadratic b z) :=
      (tail_differentiableOn_B (norm_gt_two hb)).differentiableAt
        ((isOpen_farB b).mem_nhds (quadB_mem_farB hb hz))
    exact hT.comp z hqd
  have hsum : DifferentiableAt ℂ (fun v => Complex.log b + Complex.log (1 + v ^ 2 / b)
      + ∑' k, bottcherLogTerm b (quadratic b v) k) z :=
    ((differentiableAt_const _).add hratio).add htail
  exact (hsum.const_mul _).cexp

/-! ## The functional equation on the sharp far field -/

/-- **The Böttcher functional equation on the sharp far field** — branch-free at the `exp`
level: `φ(z² + b) = φ(z)²` for every `‖z‖ > xStar ‖b‖`. -/
theorem bottcherCoord_quadratic_farB {b z : ℂ} (hb : 2 < ‖b‖) (hz : z ∈ farB b) :
    bottcherCoord b (quadratic b z) = (bottcherCoord b z) ^ 2 := by
  have hz0 : z ≠ 0 := farB_ne_zero hb hz
  have hzsq : z ^ 2 + b ≠ 0 := by
    have hfar : quadratic b z ∈ farB b := farB_invariant hb hz
    have := farB_ne_zero hb hfar
    simpa [quadratic_apply] using this
  have hratio : (1 : ℂ) + b / z ^ 2 ≠ 0 := by
    intro h0
    have h1 : ‖b / z ^ 2‖ = 1 := by
      rw [show b / z ^ 2 = -1 from by linear_combination h0]
      simp
    have h2 := farB_ratio_lt_one hb hz
    rw [h1] at h2
    linarith
  have hshift : ∀ k, bottcherLogTerm b (quadratic b z) k = 2 * bottcherLogTerm b z (k + 1) := by
    intro k
    unfold bottcherLogTerm
    have hiter : (quadratic b)^[k] (quadratic b z) = (quadratic b)^[k + 1] z := by
      rw [Function.iterate_succ_apply]
    rw [hiter]
    have h2 : ((2 : ℂ) ^ (k + 1 + 1))⁻¹ * 2 = ((2 : ℂ) ^ (k + 1))⁻¹ := by
      rw [pow_succ]
      field_simp
    rw [← h2]
    ring
  have hsum : ∑' k, bottcherLogTerm b (quadratic b z) k
      = 2 * (∑' k, bottcherLogTerm b z k) - 2 * bottcherLogTerm b z 0 := by
    have hsummable := summable_term_B hb hz
    have h1 : ∑' k, bottcherLogTerm b (quadratic b z) k
        = ∑' k, 2 * bottcherLogTerm b z (k + 1) := tsum_congr hshift
    rw [h1, tsum_mul_left]
    have h2 : ∑' k, bottcherLogTerm b z (k + 1)
        = (∑' k, bottcherLogTerm b z k) - bottcherLogTerm b z 0 := by
      have := hsummable.tsum_eq_zero_add
      linear_combination -this
    rw [h2]
    ring
  unfold bottcherCoord bottcherLog
  rw [hsum]
  have hterm0 : bottcherLogTerm b z 0 = (2 : ℂ)⁻¹ * Complex.log (1 + b / z ^ 2) := by
    unfold bottcherLogTerm
    simp
  rw [hterm0]
  have hqz : quadratic b z = z ^ 2 + b := rfl
  have hδ : Complex.exp (Complex.log (z ^ 2 + b) - Complex.log (1 + b / z ^ 2)
      - 2 * Complex.log z) = 1 := by
    rw [sub_sub, Complex.exp_sub, Complex.exp_add, Complex.exp_log hzsq,
      Complex.exp_log hratio]
    rw [show (2 : ℂ) * Complex.log z = Complex.log z + Complex.log z from by ring,
      Complex.exp_add, Complex.exp_log hz0]
    rw [div_eq_one_iff_eq (by
      intro h0
      rcases mul_eq_zero.mp h0 with h1 | h1
      · exact hratio h1
      · exact hz0 (by rcases mul_eq_zero.mp h1 with h2 | h2 <;> exact h2))]
    field_simp
  calc Complex.exp (Complex.log (quadratic b z)
        + (2 * (∑' k, bottcherLogTerm b z k) - 2 * ((2 : ℂ)⁻¹
            * Complex.log (1 + b / z ^ 2))))
      = Complex.exp ((2 : ℂ) * (Complex.log z + ∑' k, bottcherLogTerm b z k)
          + (Complex.log (z ^ 2 + b) - Complex.log (1 + b / z ^ 2)
            - 2 * Complex.log z)) := by
        rw [hqz]
        congr 1
        ring
    _ = Complex.exp ((2 : ℂ) * (Complex.log z + ∑' k, bottcherLogTerm b z k))
          * Complex.exp (Complex.log (z ^ 2 + b) - Complex.log (1 + b / z ^ 2)
            - 2 * Complex.log z) := Complex.exp_add _ _
    _ = Complex.exp ((2 : ℂ) * (Complex.log z + ∑' k, bottcherLogTerm b z k)) := by
        rw [hδ, mul_one]
    _ = Complex.exp (Complex.log z + ∑' k, bottcherLogTerm b z k) ^ 2 := by
        rw [pow_two, ← Complex.exp_add]
        congr 1
        ring

/-- **The dyadic pullback chain at parameter `b`**: on the window,
`phiB^(2^(m+1))` is the genuine Böttcher coordinate `m + 1` quadratic steps ahead. -/
theorem phiB_pow_iterate {b z : ℂ} (hb : 2 + Real.sqrt 2 < ‖b‖)
    (hz : z ∈ Metric.ball (0 : ℂ) (rB b)) (m : ℕ) :
    phiB b z ^ (2 ^ (m + 1)) = bottcherCoord b ((quadratic b)^[m] (quadratic b z)) := by
  induction m with
  | zero =>
    simpa using phiB_sq hb hz
  | succ m ihm =>
    have hmem : (quadratic b)^[m] (quadratic b z) ∈ farB b :=
      farB_iterate (norm_gt_two hb) m (quadB_mem_farB hb hz)
    have hpow : phiB b z ^ (2 ^ (m + 1 + 1)) = (phiB b z ^ (2 ^ (m + 1))) ^ 2 := by
      rw [← pow_mul, ← pow_succ]
    rw [hpow, ihm, Function.iterate_succ_apply',
      bottcherCoord_quadratic_farB (norm_gt_two hb) hmem]

/-! ## The window engine instance at parameter `b` -/

/-- The annulus `{1 < ‖z‖ < r}` is preconnected for EVERY radius `r > 1` (polar image of
`Ioo (1, r) × 𝕊¹`) — the parameterized form of `U0PhiFourWindow.isPreconnected_annulus`. -/
theorem isPreconnected_annulus_of_one_lt {r : ℝ} (hr : 1 < r) :
    IsPreconnected (ball (0 : ℂ) r ∩ Ext) := by
  have hprod : IsConnected ((Ioo (1 : ℝ) r) ×ˢ Metric.sphere (0 : ℂ) 1) := by
    refine IsConnected.prod ⟨⟨(1 + r) / 2, by linarith, by linarith⟩, isPreconnected_Ioo⟩ ?_
    exact isConnected_sphere
      (by rw [← Module.finrank_eq_rank, Complex.finrank_real_complex]; norm_num) 0 (by norm_num)
  have hcont : Continuous (fun p : ℝ × ℂ => (p.1 : ℂ) • p.2) := by fun_prop
  have himg := hprod.image _ hcont.continuousOn
  have hset : ball (0 : ℂ) r ∩ Ext
      = (fun p : ℝ × ℂ => (p.1 : ℂ) • p.2) '' ((Ioo (1 : ℝ) r) ×ˢ Metric.sphere (0 : ℂ) 1) := by
    ext z
    simp only [Ext, Set.mem_inter_iff, mem_ball, dist_zero_right, mem_setOf_eq, Set.mem_image,
      Set.mem_prod, mem_Ioo, mem_sphere_zero_iff_norm]
    constructor
    · rintro ⟨hlt, hgt⟩
      have hz0 : ‖z‖ ≠ 0 := by positivity
      refine ⟨⟨‖z‖, (‖z‖⁻¹ : ℝ) • z⟩, ⟨⟨hgt, hlt⟩, ?_⟩, ?_⟩
      · show ‖(‖z‖⁻¹ : ℝ) • z‖ = 1
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity), inv_mul_cancel₀ hz0]
      · show (↑‖z‖ : ℂ) • ((‖z‖⁻¹ : ℝ) • z) = z
        rw [Complex.real_smul, smul_eq_mul, ← mul_assoc, ← Complex.ofReal_mul,
          mul_inv_cancel₀ hz0, Complex.ofReal_one, one_mul]
    · rintro ⟨⟨t, w⟩, ⟨⟨ht1, ht2⟩, hw⟩, rfl⟩
      have hnorm : ‖(↑t : ℂ) • w‖ = t := by
        rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, hw, mul_one,
          abs_of_pos (by linarith)]
      constructor
      · rw [hnorm]; exact ht2
      · show 1 < ‖(↑t : ℂ) • w‖
        rw [hnorm]; exact ht1
  rw [hset]
  exact himg.isPreconnected

/-- **`u₀ ⟂ phiB b`, separability-free, for every `‖b‖ > 2+√2`.**  A polynomial relation
`P(z, phiB b z, u₀ z) = 0` on a nonempty open subset of the annulus `{1 < ‖z‖ < rB b}` with
some positive-index coefficient not identically zero is impossible.  The natural-boundary
window engine is φ-generic; only the constructed branch and its disk were parameter-specific. -/
theorem u0_phiB_no_relation_nondegenerate {b : ℂ} (hb : 2 + Real.sqrt 2 < ‖b‖)
    (P : (Polynomial (Polynomial ℂ))[X]) {i₀ : ℕ} (hi₀ : 1 ≤ i₀)
    (hnondeg : ∃ z ∈ Metric.ball (0 : ℂ) (rB b) ∩ Ext,
      coeffFun (phiB b) (P.coeff i₀) z ≠ 0)
    {V : Set ℂ} (hVo : IsOpen V) (hVne : V.Nonempty)
    (hVD : V ⊆ Metric.ball (0 : ℂ) (rB b) ∩ Ext)
    (hrel : ∀ z ∈ V, P.eval₂ (eval₂RingHom (evalRingHom z) (phiB b z)) (u0 z) = 0) :
    False := by
  refine u0_windowed_no_relation_nondegenerate isOpen_ball
    ((convex_ball (0 : ℂ) (rB b)).isPreconnected)
    (isPreconnected_annulus_of_one_lt (one_lt_rB hb))
    (phiB_analytic hb) (z₁ := 1) ?_ ?_ P hi₀ hnondeg hVo hVne hVD hrel
  · show (1 : ℂ) ∈ Metric.ball (0 : ℂ) (rB b)
    simp only [Metric.mem_ball, dist_zero_right, norm_one]
    exact one_lt_rB hb
  · simp

end U0PhiLargeWindow
