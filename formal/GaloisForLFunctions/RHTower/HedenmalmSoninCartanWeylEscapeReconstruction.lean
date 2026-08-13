import GaloisForLFunctions.RHTower.HedenmalmSoninEscapeAnalyticGaugeCuspNoGo
import GaloisForLFunctions.RHTower.RouteRHyperbolicGaugePolarReductionNoGo

/-!
# Sonin escape as Weyl reduction of a holomorphic Cartan orientation pair

The scalar cusp excluded by P-G130 has a canonical rank-two survivor.  Two reciprocal holomorphic
Cartan legs have determinant one, while selecting their smaller norm produces exactly the
two-sided escape-cancelling cusp.  Burnol's actual forward/inverse Mellin dilation characters are
this Cartan orbit, not merely an analogous model.

At an actual Xi divisor, completed radial work is the square of the normalized negative logarithm
of the smaller Cartan leg times completed first-divided source energy.  Thus the nonsmooth scalar
detector is the Weyl-chamber quotient of regular vector-valued source data.
-/

open Complex Real

noncomputable section

namespace RHTower

/-- Holomorphic determinant-one Cartan orbit carrying the two Sonin orientations. -/
def soninComplexCartanOrientationOrbit (z : ℂ) : RouteRHyperbolicSourcePlane :=
  (Complex.exp z, Complex.exp (-z))

theorem differentiable_soninComplexCartanOrientationOrbit :
    Differentiable ℂ soninComplexCartanOrientationOrbit := by
  exact Complex.differentiable_exp.prodMk
    (Complex.differentiable_exp.comp differentiable_neg)

theorem soninComplexCartanOrientationOrbit_mul_eq_one (z : ℂ) :
    (soninComplexCartanOrientationOrbit z).1 *
        (soninComplexCartanOrientationOrbit z).2 = 1 := by
  rw [soninComplexCartanOrientationOrbit, ← Complex.exp_add]
  simp

/-- On the real Cartan axis, the complex orbit is the literal Route-R horizontal gauge. -/
theorem soninComplexCartanOrientationOrbit_real_eq_routeRGauge (a : ℝ) :
    soninComplexCartanOrientationOrbit (a : ℂ) =
      routeRHyperbolicSourceGauge a (1, 1) := by
  apply Prod.ext <;>
    simp [soninComplexCartanOrientationOrbit, ← Complex.ofReal_exp]
  rw [show -(a : ℂ) = ((-a : ℝ) : ℂ) by simp, ← Complex.ofReal_exp]

/-- Weyl-chamber reduction of the two reciprocal Cartan gains. -/
theorem soninComplexCartanOrientationOrbit_lower_gain (a : ℝ) :
    min ‖(soninComplexCartanOrientationOrbit (a : ℂ)).1‖
        ‖(soninComplexCartanOrientationOrbit (a : ℂ)).2‖ =
      Real.exp (-|a|) := by
  rw [soninComplexCartanOrientationOrbit, Complex.norm_exp, Complex.norm_exp]
  simp only [ofReal_re, neg_re]
  by_cases ha : 0 ≤ a
  · rw [abs_of_nonneg ha, min_eq_right]
    exact Real.exp_le_exp.mpr (by linarith)
  · have ha' : a ≤ 0 := le_of_not_ge ha
    rw [abs_of_nonpos ha', neg_neg, min_eq_left]
    exact Real.exp_le_exp.mpr (by linarith)

theorem soninComplexCartanOrientationOrbit_lower_gain_complex (z : ℂ) :
    min ‖(soninComplexCartanOrientationOrbit z).1‖
        ‖(soninComplexCartanOrientationOrbit z).2‖ =
      Real.exp (-|z.re|) := by
  rw [soninComplexCartanOrientationOrbit, Complex.norm_exp, Complex.norm_exp]
  simp only [neg_re]
  by_cases hz : 0 ≤ z.re
  · rw [abs_of_nonneg hz, min_eq_right]
    exact Real.exp_le_exp.mpr (by linarith)
  · have hz' : z.re ≤ 0 := le_of_not_ge hz
    rw [abs_of_nonpos hz', neg_neg, min_eq_left]
    exact Real.exp_le_exp.mpr (by linarith)

/-- The exact scalar cancellation cusp is the lower gain of a regular rank-two Cartan orbit. -/
theorem soninEscapeCancellingGaugeModulus_eq_cartan_lower_gain
    {c : ℝ} (hc : 0 ≤ c) (x : ℝ) :
    soninEscapeCancellingGaugeModulus c x =
      min ‖(soninComplexCartanOrientationOrbit ((c * x : ℝ) : ℂ)).1‖
        ‖(soninComplexCartanOrientationOrbit ((c * x : ℝ) : ℂ)).2‖ := by
  rw [soninComplexCartanOrientationOrbit_lower_gain]
  simp [soninEscapeCancellingGaugeModulus, abs_mul, abs_of_nonneg hc]

/-- Holomorphic Cartan legs remain regular, but Weyl-chamber minimization creates precisely the
critical-wall cusp. -/
theorem not_differentiableAt_soninComplexCartanOrientationOrbit_lower_gain
    {c : ℝ} (hc : 0 < c) :
    ¬ DifferentiableAt ℝ
      (fun x : ℝ =>
        min ‖(soninComplexCartanOrientationOrbit ((c * x : ℝ) : ℂ)).1‖
          ‖(soninComplexCartanOrientationOrbit ((c * x : ℝ) : ℂ)).2‖) 0 := by
  intro h
  apply not_differentiableAt_soninEscapeCancellingGaugeModulus hc
  apply h.congr_of_eventuallyEq
  filter_upwards with x
  exact soninEscapeCancellingGaugeModulus_eq_cartan_lower_gain hc.le x

/-- Actual forward/inverse Burnol Mellin characters as an ordered orientation pair. -/
def burnolSoninMellinOrientationPair (r : ℝ) (w : ℂ) :
    RouteRHyperbolicSourcePlane :=
  (burnolMellinDilationCharacter r w,
    (burnolMellinDilationCharacter r w)⁻¹)

/-- Burnol's actual orientation pair is exactly the complex Cartan orbit. -/
theorem burnolSoninMellinOrientationPair_eq_complexCartanOrbit
    {r : ℝ} (hr : 0 < r) (w : ℂ) :
    burnolSoninMellinOrientationPair r w =
      soninComplexCartanOrientationOrbit
        ((Real.log r : ℂ) * (w - 1 / 2)) := by
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  apply Prod.ext
  · simp only [burnolSoninMellinOrientationPair,
      soninComplexCartanOrientationOrbit, burnolMellinDilationCharacter]
    rw [Complex.cpow_def_of_ne_zero hrC, ← Complex.ofReal_log hr.le]
  · simp only [burnolSoninMellinOrientationPair,
      soninComplexCartanOrientationOrbit, burnolMellinDilationCharacter]
    rw [Complex.cpow_def_of_ne_zero hrC, ← Complex.ofReal_log hr.le,
      Complex.exp_neg]

theorem differentiable_burnolSoninMellinOrientationPair
    {r : ℝ} (hr : 0 < r) :
    Differentiable ℂ (burnolSoninMellinOrientationPair r) := by
  have heq : burnolSoninMellinOrientationPair r =
      fun w : ℂ => soninComplexCartanOrientationOrbit
        ((Real.log r : ℂ) * (w - 1 / 2)) := by
    funext w
    exact burnolSoninMellinOrientationPair_eq_complexCartanOrbit hr w
  rw [heq]
  apply differentiable_soninComplexCartanOrientationOrbit.comp
  fun_prop

theorem burnolSoninMellinOrientationPair_mul_eq_one
    {r : ℝ} (hr : 0 < r) (w : ℂ) :
    (burnolSoninMellinOrientationPair r w).1 *
        (burnolSoninMellinOrientationPair r w).2 = 1 := by
  rw [burnolSoninMellinOrientationPair_eq_complexCartanOrbit hr]
  exact soninComplexCartanOrientationOrbit_mul_eq_one _

/-- The smaller actual Burnol orientation gain is exactly the scalar escape-cancelling cusp. -/
theorem burnolSoninMellinOrientationPair_lower_gain
    {r : ℝ} (hr : 1 < r) (w : ℂ) :
    min ‖(burnolSoninMellinOrientationPair r w).1‖
        ‖(burnolSoninMellinOrientationPair r w).2‖ =
      soninEscapeCancellingGaugeModulus (Real.log r) (w.re - 1 / 2) := by
  rw [burnolSoninMellinOrientationPair_eq_complexCartanOrbit (zero_lt_one.trans hr),
    soninComplexCartanOrientationOrbit_lower_gain_complex]
  simp [soninEscapeCancellingGaugeModulus, abs_mul, abs_of_pos (Real.log_pos hr)]

/-- On the canonically right-oriented actual Xi fibre, the smaller Cartan leg has exponential
decay rate equal to the P-G129 Sonin Lyapunov rate. -/
theorem burnolSoninMellinOrientationPair_lower_gain_xi
    (q : XiZeroCopy) (hoff : (xiSpectralPoint q).im ≠ 0)
    {r : ℝ} (hr : 1 < r) :
    min
        ‖(burnolSoninMellinOrientationPair r
          (((xiSoninRightOrientedCopy q).1 : ℂ))).1‖
        ‖(burnolSoninMellinOrientationPair r
          (((xiSoninRightOrientedCopy q).1 : ℂ))).2‖ =
      Real.exp (-Real.log r * thetaXiSoninApertureLyapunovRate q) := by
  rw [burnolSoninMellinOrientationPair_lower_gain hr,
    soninEscapeCancellingGaugeModulus]
  have hneg := xiSpectralPoint_im_xiSoninRightOrientedCopy_neg q hoff
  have habs := xiSpectralPoint_im_xiSoninRightOrientedCopy_abs q
  rw [abs_of_neg hneg] at habs
  have hw :
      (((xiSoninRightOrientedCopy q).1 : ℂ)).re - 1 / 2 =
        thetaXiSoninApertureLyapunovRate q := by
    rw [← criticalAffine_xiSoninRightOrientedCopy, re_centeredSpectralPoint]
    linarith
  rw [hw, abs_of_nonneg]
  exact abs_nonneg _

/-- **Cartan reconstruction of completed radial work.**  On every off-line Xi copy, radial source
work is squared normalized negative log of the smaller actual orientation gain, multiplied by
literal completed first-divided source energy. -/
theorem burnolCompletedRadialSourceWork_eq_cartan_log_lower_gain_sq_mul_norm_sq
    (q : XiZeroCopy) (hoff : (xiSpectralPoint q).im ≠ 0)
    {r : ℝ} (hr : 1 < r) :
    burnolCompletedRadialSourceWork q.1 =
      ((-Real.log
          (min
            ‖(burnolSoninMellinOrientationPair r
              (((xiSoninRightOrientedCopy q).1 : ℂ))).1‖
            ‖(burnolSoninMellinOrientationPair r
              (((xiSoninRightOrientedCopy q).1 : ℂ))).2‖)) /
        Real.log r) ^ 2 * ‖completedXiFirstDividedL2 q.1‖ ^ 2 := by
  rw [burnolSoninMellinOrientationPair_lower_gain_xi q hoff hr,
    Real.log_exp,
    burnolCompletedRadialSourceWork_eq_soninLyapunovRate_sq_mul_norm_sq]
  have hlog : Real.log r ≠ 0 := (Real.log_pos hr).ne'
  congr 1
  field_simp

/-- The Weyl-reduced orientation pair is neutral exactly on the critical wall. -/
theorem burnolSoninMellinOrientationPair_lower_gain_eq_one_iff
    {r : ℝ} (hr : 1 < r) (w : ℂ) :
    min ‖(burnolSoninMellinOrientationPair r w).1‖
        ‖(burnolSoninMellinOrientationPair r w).2‖ = 1 ↔
      w.re = 1 / 2 := by
  rw [burnolSoninMellinOrientationPair_lower_gain hr,
    soninEscapeCancellingGaugeModulus, Real.exp_eq_one_iff]
  have hlog : Real.log r ≠ 0 := (Real.log_pos hr).ne'
  constructor
  · intro h
    have habs : |w.re - 1 / 2| = 0 := by
      rcases mul_eq_zero.mp h with hneg | habs
      · exact absurd (neg_eq_zero.mp hneg) hlog
      · exact habs
    exact sub_eq_zero.mp (abs_eq_zero.mp habs)
  · intro h
    rw [h, sub_self, abs_zero, mul_zero]

end RHTower
