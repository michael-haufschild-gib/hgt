import GaloisForLFunctions.RHTower.RandomEulerAbscissa
import Mathlib.Analysis.Complex.MeanValue
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

/-!
# The Euler logarithmic factor of a single random phase

The random Euler observable is a sum of independent factors, one per prime,

`ℓ_p = -log (1 - X_p p^{-σ})`,

each reading a single uniform phase.  This file analyses one such factor as a function of its
phase parameter `x ∈ [0,1]` and radius `r = p^{-σ} ∈ [0,1)`:

* `norm_randomEulerLogFactor_le` — the elementary Taylor bound `‖ℓ‖ ≤ r²/(2(1-r)) + r`;
* `integral_randomEulerLogFactor` — the factor is centred, by the mean value property of the
  holomorphic function `w ↦ -log (1 - w)` on the disc of radius `r`;
* `norm_randomEulerLogFactor_ge` — on the far arc, where the phase has `cos ≤ -1/2`, the factor
  has modulus at least `r/4`, because there `|1 - r e(x)|² ≥ 1 + r`.

The last two give matching two-sided bounds for the second moment of one factor, which is what
places the abscissa of almost sure convergence of the whole observable at `σ = 1/2`.
-/

noncomputable section

open MeasureTheory Filter Topology Metric

namespace GaloisForLFunctions.RHTower

/-- The Euler logarithmic factor at radius `r` and phase parameter `x`. -/
def randomEulerLogFactor (r x : ℝ) : ℂ :=
  -Complex.log (1 - (r : ℂ) * Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I))

/-- The circle phase is unimodular. -/
theorem norm_randomEulerPhase (x : ℝ) :
    ‖Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)‖ = 1 := by
  rw [Complex.norm_exp]
  simp

/-- The argument of the logarithm has modulus `|r|`. -/
theorem norm_randomEulerLogArg (r x : ℝ) :
    ‖(r : ℂ) * Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)‖ = |r| := by
  rw [norm_mul, norm_randomEulerPhase, mul_one]
  simp

/-- **The Taylor bound for one Euler factor.** -/
theorem norm_randomEulerLogFactor_le {r : ℝ} (hr0 : 0 ≤ r) (hr : r < 1) (x : ℝ) :
    ‖randomEulerLogFactor r x‖ ≤ r ^ (2 : ℕ) * (1 - r)⁻¹ / 2 + r := by
  set w : ℂ := (r : ℂ) * Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I) with hw
  have hnw : ‖-w‖ = r := by
    rw [norm_neg, hw, norm_randomEulerLogArg, abs_of_nonneg hr0]
  have hlt : ‖-w‖ < 1 := by rw [hnw]; exact hr
  have h := Complex.norm_log_one_add_le hlt
  rw [hnw] at h
  have hrw : (1 : ℂ) - w = 1 + (-w) := by ring
  rw [randomEulerLogFactor, ← hw, hrw, norm_neg]
  exact h

/-- **The linear approximation of one Euler factor.** -/
theorem norm_randomEulerLogFactor_sub_linear_le {r : ℝ} (hr0 : 0 ≤ r) (hr : r < 1) (x : ℝ) :
    ‖randomEulerLogFactor r x
        - (r : ℂ) * Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)‖
      ≤ r ^ (2 : ℕ) * (1 - r)⁻¹ / 2 := by
  set w : ℂ := (r : ℂ) * Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I) with hw
  have hnw : ‖-w‖ = r := by
    rw [norm_neg, hw, norm_randomEulerLogArg, abs_of_nonneg hr0]
  have hlt : ‖-w‖ < 1 := by rw [hnw]; exact hr
  have h := Complex.norm_log_one_add_sub_self_le hlt
  rw [hnw] at h
  have hrw : (1 : ℂ) - w = 1 + (-w) := by ring
  rw [randomEulerLogFactor, ← hw, hrw]
  have hneg : -Complex.log (1 + -w) - w = -(Complex.log (1 + -w) - (-w)) := by ring
  rw [hneg, norm_neg]
  exact h

/-! ### The mean value property -/

/-- The function whose circle averages give the Euler factor. -/
def negLogOneSub (z : ℂ) : ℂ := -Complex.log (1 - z)

theorem differentiableAt_negLogOneSub {z : ℂ} (hz : ‖z‖ < 1) :
    DifferentiableAt ℂ negLogOneSub z := by
  have hmem : (1 : ℂ) - z ∈ Complex.slitPlane := by
    have := Complex.mem_slitPlane_of_norm_lt_one (z := -z) (by rwa [norm_neg])
    simpa [sub_eq_add_neg] using this
  have hlog : DifferentiableAt ℂ Complex.log ((1 : ℂ) - z) := Complex.differentiableAt_log hmem
  have hsub : DifferentiableAt ℂ (fun w : ℂ => (1 : ℂ) - w) z :=
    (differentiableAt_const _).sub differentiableAt_id
  exact ((hlog.comp z hsub).neg)

/-- **The Euler factor is centred.**  The mean value property of `w ↦ -log (1 - w)` on the disc of
radius `r` gives mean `-log 1 = 0`. -/
theorem integral_randomEulerLogFactor {r : ℝ} (hr : |r| < 1) :
    ∫ x, randomEulerLogFactor r x ∂(volume.restrict (Set.Icc (0 : ℝ) 1)) = 0 := by
  have hdiff : ∀ z : ℂ, ‖z‖ ≤ |r| → DifferentiableAt ℂ negLogOneSub z := fun z hz =>
    differentiableAt_negLogOneSub (lt_of_le_of_lt hz hr)
  have hcont : ContinuousOn negLogOneSub (closedBall (0 : ℂ) |r|) := by
    intro z hz
    refine ((hdiff z ?_).continuousAt).continuousWithinAt
    simpa [Metric.mem_closedBall, dist_eq_norm] using hz
  have hball : ∀ z ∈ ball (0 : ℂ) |r| \ (∅ : Set ℂ), DifferentiableAt ℂ negLogOneSub z := by
    intro z hz
    refine hdiff z (le_of_lt ?_)
    simpa [Metric.mem_ball, dist_eq_norm] using hz.1
  have hmv : Real.circleAverage negLogOneSub 0 r = negLogOneSub 0 :=
    circleAverage_of_differentiable_on_off_countable Set.countable_empty hcont hball
  have hzero : negLogOneSub 0 = 0 := by simp [negLogOneSub]
  have hmap : ∀ θ : ℝ, negLogOneSub (circleMap 0 r θ)
      = -Complex.log (1 - (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)) := by
    intro θ
    simp [negLogOneSub, circleMap]
  have hpi : (2 * Real.pi) ≠ 0 := by positivity
  have hsub : ∀ x : ℝ, randomEulerLogFactor r x = negLogOneSub (circleMap 0 r (2 * Real.pi * x)) := by
    intro x
    rw [hmap, randomEulerLogFactor]
  have hchange : (∫ x in (0 : ℝ)..1, negLogOneSub (circleMap 0 r (2 * Real.pi * x)))
      = (2 * Real.pi)⁻¹ • ∫ θ in (2 * Real.pi * 0)..(2 * Real.pi * 1),
          negLogOneSub (circleMap 0 r θ) :=
    intervalIntegral.integral_comp_mul_left
      (fun θ => negLogOneSub (circleMap 0 r θ)) hpi
  calc ∫ x, randomEulerLogFactor r x ∂(volume.restrict (Set.Icc (0 : ℝ) 1))
      = ∫ x in Set.Icc (0 : ℝ) 1, negLogOneSub (circleMap 0 r (2 * Real.pi * x)) := by
        exact integral_congr_ae (Filter.Eventually.of_forall fun x => hsub x)
    _ = ∫ x in Set.Ioc (0 : ℝ) 1, negLogOneSub (circleMap 0 r (2 * Real.pi * x)) :=
        integral_Icc_eq_integral_Ioc
    _ = ∫ x in (0 : ℝ)..1, negLogOneSub (circleMap 0 r (2 * Real.pi * x)) :=
        (intervalIntegral.integral_of_le (by norm_num)).symm
    _ = (2 * Real.pi)⁻¹ • ∫ θ in (2 * Real.pi * 0)..(2 * Real.pi * 1),
          negLogOneSub (circleMap 0 r θ) := hchange
    _ = Real.circleAverage negLogOneSub 0 r := by
        rw [Real.circleAverage]
        norm_num
    _ = 0 := by rw [hmv, hzero]

/-! ### The far arc -/

/-- On the middle third of the period the circle phase has cosine at most `-1/2`. -/
theorem cos_twoPi_le_neg_half {x : ℝ} (hx1 : 1 / 3 ≤ x) (hx2 : x ≤ 2 / 3) :
    Real.cos (2 * Real.pi * x) ≤ -(1 / 2) := by
  have hpi := Real.pi_pos
  have hue : 2 * Real.pi * x = (2 * Real.pi * x - Real.pi) + Real.pi := by ring
  have habs : |2 * Real.pi * x - Real.pi| ≤ Real.pi / 3 := by
    rw [abs_le]
    constructor <;> nlinarith
  have hcos : Real.cos (Real.pi / 3) ≤ Real.cos |2 * Real.pi * x - Real.pi| :=
    Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) (by linarith) habs
  rw [Real.cos_abs, Real.cos_pi_div_three] at hcos
  rw [hue, Real.cos_add_pi]
  linarith

/-- The squared modulus of the Euler argument. -/
theorem normSq_one_sub_randomEulerLogArg (r x : ℝ) :
    ‖(1 : ℂ) - (r : ℂ) * Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I)‖ ^ (2 : ℕ)
      = 1 - 2 * r * Real.cos (2 * Real.pi * x) + r ^ (2 : ℕ) := by
  set θ : ℝ := 2 * Real.pi * x with hθ
  have hexre : (Complex.exp ((θ : ℂ) * Complex.I)).re = Real.cos θ :=
    Complex.exp_ofReal_mul_I_re θ
  have hexim : (Complex.exp ((θ : ℂ) * Complex.I)).im = Real.sin θ :=
    Complex.exp_ofReal_mul_I_im θ
  have hre : ((1 : ℂ) - (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)).re
      = 1 - r * Real.cos θ := by
    rw [Complex.sub_re, Complex.one_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      hexre, hexim]
    ring
  have him : ((1 : ℂ) - (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I)).im
      = -(r * Real.sin θ) := by
    rw [Complex.sub_im, Complex.one_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      hexre, hexim]
    ring
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, hre, him]
  have hpy := Real.sin_sq_add_cos_sq θ
  nlinarith [hpy]

/-- **The Euler factor is large on the far arc.** -/
theorem norm_randomEulerLogFactor_ge {r x : ℝ} (hr0 : 0 ≤ r) (hr : r ≤ 1)
    (hx : Real.cos (2 * Real.pi * x) ≤ -(1 / 2)) :
    r / 4 ≤ ‖randomEulerLogFactor r x‖ := by
  set w : ℂ := (r : ℂ) * Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * Complex.I) with hw
  have hnormsq : ‖(1 : ℂ) - w‖ ^ (2 : ℕ) = 1 - 2 * r * Real.cos (2 * Real.pi * x) + r ^ (2 : ℕ) :=
    normSq_one_sub_randomEulerLogArg r x
  have hge : 1 + r ≤ ‖(1 : ℂ) - w‖ ^ (2 : ℕ) := by
    rw [hnormsq]; nlinarith
  have hpos : (0 : ℝ) < ‖(1 : ℂ) - w‖ := by nlinarith [norm_nonneg ((1 : ℂ) - w)]
  have hlog : Real.log (1 + r) ≤ 2 * Real.log ‖(1 : ℂ) - w‖ := by
    have h1 : Real.log (1 + r) ≤ Real.log (‖(1 : ℂ) - w‖ ^ (2 : ℕ)) :=
      Real.log_le_log (by linarith) hge
    rwa [Real.log_pow] at h1
    
  have hre : (randomEulerLogFactor r x).re = -Real.log ‖(1 : ℂ) - w‖ := by
    rw [randomEulerLogFactor, ← hw, Complex.neg_re, Complex.log_re]
  have hlogge : r / 2 ≤ Real.log (1 + r) := by
    have h0 : (0 : ℝ) < 1 + r := by linarith
    have h1 : Real.log ((1 + r)⁻¹) ≤ (1 + r)⁻¹ - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    rw [Real.log_inv] at h1
    have h0' : (1 + r) ≠ 0 := ne_of_gt h0
    have h2 : r / (1 + r) ≤ Real.log (1 + r) := by
      have heq : (1 + r)⁻¹ - 1 = -(r / (1 + r)) := by field_simp; ring
      rw [heq] at h1
      linarith
    have h3 : r / 2 ≤ r / (1 + r) := by
      apply div_le_div_of_nonneg_left hr0 h0
      linarith
    linarith
  have habs : |(randomEulerLogFactor r x).re| ≤ ‖randomEulerLogFactor r x‖ :=
    Complex.abs_re_le_norm _
  have hneg : (randomEulerLogFactor r x).re ≤ -(r / 4) := by
    rw [hre]
    linarith
  have : r / 4 ≤ |(randomEulerLogFactor r x).re| := by
    rw [abs_of_nonpos (by linarith)]
    linarith
  linarith

end GaloisForLFunctions.RHTower
