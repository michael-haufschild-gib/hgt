import GaloisForLFunctions.RHTower.IntervalAutocorrelation
import GaloisForLFunctions.RHTower.CCMPolarPrimeStieltjesAutocorrelation
import GaloisForLFunctions.RHTower.CCMRectangularTwoEdge

/-!
# The two-edge rectangular window and its autocorrelation

The corpus carries the *transform* of the two-edge rectangular window,
`rectangularTwoEdgeTransform L a w = exp(a w) A_L(w) + exp(-a w) A_L(-w)` with
`A_L(w) = ∫₀^L exp(-w t) dt`.  Since `exp(a w) A_L(w) = ∫_(a-L)^a exp(w u) du` and
`exp(-a w) A_L(-w) = ∫_(-a)^(-a+L) exp(w u) du`, the physical vector behind it is the indicator of
two length-`L` blocks placed at the two edges of the aperture:

`v = 1_[a-L, a] + 1_[-a, -a+L]`.

This module defines that vector and computes the aperture autocorrelation the polar--prime carrier
consumes.  The autocorrelation splits into four interval overlaps: two self terms, each the
triangle `(L - |h|)⁺`, and two cross terms between the opposite edges.  For `L ≤ a` and `h ≥ 0`
one cross term vanishes identically and the other is supported in `[2a-2L, 2a]`, so the
autocorrelation is a triangle at the origin plus a trapezoidal bump at the far lag.

Everything here is exact and elementary: no asymptotics, no prolate theory, no oscillatory analysis.
-/

open MeasureTheory Set Complex

namespace RHTower

/-- The physical two-edge rectangular window: two length-`L` blocks at the aperture edges. -/
noncomputable def twoEdgeIndicator (L a : ℝ) (x : ℝ) : ℂ :=
  (Icc (a - L) a).indicator (fun _ => (1 : ℂ)) x +
    (Icc (-a) (-a + L)).indicator (fun _ => (1 : ℂ)) x

@[simp] theorem conj_twoEdgeIndicator (L a x : ℝ) :
    (starRingEnd ℂ) (twoEdgeIndicator L a x) = twoEdgeIndicator L a x := by
  by_cases hx : x ∈ Icc (a - L) a <;> by_cases hy : x ∈ Icc (-a) (-a + L) <;>
    simp [twoEdgeIndicator, Set.indicator_of_mem, Set.indicator_of_notMem, hx, hy]

/-- The four interval overlaps appearing in the two-edge autocorrelation. -/
noncomputable def twoEdgeOverlap (L a h : ℝ) : ℝ :=
  max ((L : ℝ) - |h|) 0 + max ((L : ℝ) - |h|) 0
    + max (min (-a + L) (a - h) - max (-a) (a - L - h)) 0
    + max (min a (-a + L - h) - max (a - L) (-a - h)) 0

/-- **Two-edge autocorrelation, exact four-term form.**  No hypotheses on `L`, `a`, `h`. -/
theorem twoEdge_apertureAutocorrelation_eq (L a h : ℝ) :
    apertureAutocorrelation (twoEdgeIndicator L a) h = ((twoEdgeOverlap L a h : ℝ) : ℂ) := by
  have hAA := integrable_indicator_shift_mul_complex (a - L) a (a - L) a h
  have hAB := integrable_indicator_shift_mul_complex (a - L) a (-a) (-a + L) h
  have hBA := integrable_indicator_shift_mul_complex (-a) (-a + L) (a - L) a h
  have hBB := integrable_indicator_shift_mul_complex (-a) (-a + L) (-a) (-a + L) h
  have hpt : ∀ x : ℝ,
      twoEdgeIndicator L a (x + h) * (starRingEnd ℂ) (twoEdgeIndicator L a x)
        = ((Icc (a - L) a).indicator (fun _ => (1 : ℂ)) (x + h) *
            (Icc (a - L) a).indicator (fun _ => (1 : ℂ)) x
          + (Icc (a - L) a).indicator (fun _ => (1 : ℂ)) (x + h) *
            (Icc (-a) (-a + L)).indicator (fun _ => (1 : ℂ)) x)
          + ((Icc (-a) (-a + L)).indicator (fun _ => (1 : ℂ)) (x + h) *
              (Icc (a - L) a).indicator (fun _ => (1 : ℂ)) x
            + (Icc (-a) (-a + L)).indicator (fun _ => (1 : ℂ)) (x + h) *
              (Icc (-a) (-a + L)).indicator (fun _ => (1 : ℂ)) x) := by
    intro x
    rw [conj_twoEdgeIndicator]
    unfold twoEdgeIndicator
    ring
  have h12 : Integrable (fun x : ℝ =>
      (Icc (a - L) a).indicator (fun _ => (1 : ℂ)) (x + h) *
          (Icc (a - L) a).indicator (fun _ => (1 : ℂ)) x
        + (Icc (a - L) a).indicator (fun _ => (1 : ℂ)) (x + h) *
          (Icc (-a) (-a + L)).indicator (fun _ => (1 : ℂ)) x) := by
    simpa using hAA.add hAB
  have h34 : Integrable (fun x : ℝ =>
      (Icc (-a) (-a + L)).indicator (fun _ => (1 : ℂ)) (x + h) *
          (Icc (a - L) a).indicator (fun _ => (1 : ℂ)) x
        + (Icc (-a) (-a + L)).indicator (fun _ => (1 : ℂ)) (x + h) *
          (Icc (-a) (-a + L)).indicator (fun _ => (1 : ℂ)) x) := by
    simpa using hBA.add hBB
  rw [apertureAutocorrelation, funext hpt,
    integral_add h12 h34, integral_add hAA hAB, integral_add hBA hBB,
    integral_indicator_Icc_shift_mul_Icc_complex (a - L) a (a - L) a h,
    integral_indicator_Icc_shift_mul_Icc_complex (a - L) a (-a) (-a + L) h,
    integral_indicator_Icc_shift_mul_Icc_complex (-a) (-a + L) (a - L) a h,
    integral_indicator_Icc_shift_mul_Icc_complex (-a) (-a + L) (-a) (-a + L) h]
  rw [twoEdgeOverlap, min_sub_max_eq (a - L) a h, min_sub_max_eq (-a) (-a + L) h]
  push_cast
  ring_nf

/-- For `L ≤ a` and nonnegative lag, the near-edge-to-far-edge overlap vanishes: the shifted left
block lies strictly left of the right block. -/
theorem twoEdge_backward_cross_eq_zero {L a h : ℝ} (hLa : L ≤ a) (hh : 0 ≤ h) :
    max (min a (-a + L - h) - max (a - L) (-a - h)) 0 = 0 := by
  have hle : min a (-a + L - h) - max (a - L) (-a - h) ≤ 0 := by
    have h1 : min a (-a + L - h) ≤ -a + L - h := min_le_right _ _
    have h2 : a - L ≤ max (a - L) (-a - h) := le_max_left _ _
    linarith
  exact max_eq_right hle

/-- **Two-edge autocorrelation in the aperture regime.**  For `0 < L ≤ a` and `h ≥ 0` the profile is
the origin triangle `2(L - h)⁺` plus one far-lag cross term. -/
theorem twoEdge_apertureAutocorrelation_eq_of_le
    {L a h : ℝ} (hLa : L ≤ a) (hh : 0 ≤ h) :
    apertureAutocorrelation (twoEdgeIndicator L a) h
      = (((2 * max (L - h) 0
            + max (min (-a + L) (a - h) - max (-a) (a - L - h)) 0 : ℝ)) : ℂ) := by
  rw [twoEdge_apertureAutocorrelation_eq L a h, twoEdgeOverlap,
    twoEdge_backward_cross_eq_zero hLa hh, abs_of_nonneg hh]
  push_cast
  ring

/-- **Endpoint lag.**  At the full lag `2a` the two-edge autocorrelation vanishes.  The window is
not literally zero at `x = ±a` — it is `1` there — so this is proved from the exact overlap formula
rather than from a support hypothesis. -/
theorem twoEdge_apertureAutocorrelation_two_mul_eq_zero
    {L a : ℝ} (hL : 0 < L) (hLa : L ≤ a) :
    apertureAutocorrelation (twoEdgeIndicator L a) (2 * a) = 0 := by
  rw [twoEdge_apertureAutocorrelation_eq L a (2 * a), twoEdgeOverlap]
  have h1 : max (L - |2 * a|) 0 = 0 := by
    have : L - |2 * a| ≤ 0 := by
      rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ 2 * a)]
      linarith
    exact max_eq_right this
  have h2 : max (min (-a + L) (a - 2 * a) - max (-a) (a - L - 2 * a)) 0 = 0 := by
    have hmin : min (-a + L) (a - 2 * a) = -a := by
      rw [min_eq_right (by linarith)]
      ring
    have hmax : max (-a) (a - L - 2 * a) = -a := max_eq_left (by linarith)
    rw [hmin, hmax]
    simp
  have h3 : max (min a (-a + L - 2 * a) - max (a - L) (-a - 2 * a)) 0 = 0 := by
    have hle : min a (-a + L - 2 * a) - max (a - L) (-a - 2 * a) ≤ 0 := by
      have hA : min a (-a + L - 2 * a) ≤ -a + L - 2 * a := min_le_right _ _
      have hB : a - L ≤ max (a - L) (-a - 2 * a) := le_max_left _ _
      linarith
    exact max_eq_right hle
  rw [h1, h2, h3]
  norm_num

/-! ## Identification with the transform already in the corpus

The corpus defines `rectangularTwoEdgeTransform` on the transform side only.  The theorem below
identifies it as the bilateral transform of `twoEdgeIndicator`, which is the load-bearing link
between the physical and transform sides of the rectangular family. -/

/-- The bilateral transform of a single interval indicator. -/
theorem integral_indicator_Icc_mul_exp {c d : ℝ} (hcd : c ≤ d) {w : ℂ} (hw : w ≠ 0) :
    ∫ x : ℝ, (Icc c d).indicator (fun _ => (1 : ℂ)) x * Complex.exp (w * x)
      = (Complex.exp (w * d) - Complex.exp (w * c)) / w := by
  have hpt : ∀ x : ℝ,
      (Icc c d).indicator (fun _ => (1 : ℂ)) x * Complex.exp (w * x)
        = (Icc c d).indicator (fun y : ℝ => Complex.exp (w * y)) x := by
    intro x
    by_cases hx : x ∈ Icc c d
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, one_mul]
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, zero_mul]
  rw [funext hpt, MeasureTheory.integral_indicator measurableSet_Icc,
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hcd,
    integral_exp_mul_complex hw]

/-- **Physical/transform identification.**  `rectangularTwoEdgeTransform L a` is the bilateral
transform of the two-edge window. -/
theorem integral_twoEdgeIndicator_mul_exp {L a : ℝ} (hL : 0 ≤ L) {w : ℂ} (hw : w ≠ 0) :
    ∫ x : ℝ, twoEdgeIndicator L a x * Complex.exp (w * x)
      = rectangularTwoEdgeTransform L a w := by
  have hA : (a - L) ≤ a := by linarith
  have hB : (-a) ≤ (-a + L) := by linarith
  have hsplit : ∀ x : ℝ, twoEdgeIndicator L a x * Complex.exp (w * x)
      = (Icc (a - L) a).indicator (fun _ => (1 : ℂ)) x * Complex.exp (w * x)
        + (Icc (-a) (-a + L)).indicator (fun _ => (1 : ℂ)) x * Complex.exp (w * x) := by
    intro x
    unfold twoEdgeIndicator
    ring
  have hIA : Integrable (fun x : ℝ =>
      (Icc (a - L) a).indicator (fun _ => (1 : ℂ)) x * Complex.exp (w * x)) := by
    have hpt : (fun x : ℝ => (Icc (a - L) a).indicator (fun _ => (1 : ℂ)) x * Complex.exp (w * x))
        = (Icc (a - L) a).indicator (fun y : ℝ => Complex.exp (w * y)) := by
      funext x
      by_cases hx : x ∈ Icc (a - L) a
      · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, one_mul]
      · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, zero_mul]
    rw [hpt]
    refine (Continuous.integrableOn_Icc ?_).integrable_indicator measurableSet_Icc
    exact Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)
  have hIB : Integrable (fun x : ℝ =>
      (Icc (-a) (-a + L)).indicator (fun _ => (1 : ℂ)) x * Complex.exp (w * x)) := by
    have hpt : (fun x : ℝ =>
        (Icc (-a) (-a + L)).indicator (fun _ => (1 : ℂ)) x * Complex.exp (w * x))
        = (Icc (-a) (-a + L)).indicator (fun y : ℝ => Complex.exp (w * y)) := by
      funext x
      by_cases hx : x ∈ Icc (-a) (-a + L)
      · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, one_mul]
      · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, zero_mul]
    rw [hpt]
    refine (Continuous.integrableOn_Icc ?_).integrable_indicator measurableSet_Icc
    exact Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)
  rw [funext hsplit, integral_add hIA hIB,
    integral_indicator_Icc_mul_exp hA hw, integral_indicator_Icc_mul_exp hB hw,
    rectangularTwoEdgeTransform, rectangularWindowAmplitude_eq_div hw,
    rectangularWindowAmplitude_eq_div (neg_ne_zero.mpr hw)]
  push_cast
  have h1 : w * ((a : ℂ) - (L : ℂ)) = w * (a : ℂ) + -(w * (L : ℂ)) := by ring
  have h2 : w * (-(a : ℂ) + (L : ℂ)) = -(w * (a : ℂ)) + w * (L : ℂ) := by ring
  have h3 : w * (-(a : ℂ)) = -(w * (a : ℂ)) := by ring
  have h4 : (a : ℂ) * w = w * (a : ℂ) := by ring
  have h5 : -(a : ℂ) * w = -(w * (a : ℂ)) := by ring
  have h6 : -(L : ℂ) * w = -(w * (L : ℂ)) := by ring
  have h7 : -(L : ℂ) * -w = w * (L : ℂ) := by ring
  rw [h1, h2, h3, h4, h5, h6, h7, Complex.exp_add, Complex.exp_add]
  field_simp
  ring


/-! ## Pairing against the polar--prime carrier

The corpus's carrier theorem needs one integrability hypothesis.  For the two-edge window the
autocorrelation is the explicit piecewise-linear `twoEdgeOverlap`, which is continuous, so the
hypothesis is automatic and the carrier specializes to a finite explicit expression: two elementary
`cosh` integrals minus two von Mangoldt blocks. -/

theorem continuous_twoEdgeOverlap (L a : ℝ) : Continuous (twoEdgeOverlap L a) := by
  unfold twoEdgeOverlap
  fun_prop

theorem integrable_twoEdge_autocorrelation_mul_cosh (L a : ℝ) :
    Integrable (fun h => apertureAutocorrelation (twoEdgeIndicator L a) h *
        (2 * Real.cosh (h / 2) : ℂ)) (volume.restrict (Set.Ioc (0 : ℝ) (2 * a))) := by
  have hfun : (fun h : ℝ => apertureAutocorrelation (twoEdgeIndicator L a) h *
      (2 * Real.cosh (h / 2) : ℂ))
      = fun h : ℝ => ((twoEdgeOverlap L a h : ℝ) : ℂ) * (2 * Real.cosh (h / 2) : ℂ) := by
    funext h
    rw [twoEdge_apertureAutocorrelation_eq L a h]
  rw [hfun]
  have hcont : Continuous (fun h : ℝ => ((twoEdgeOverlap L a h : ℝ) : ℂ) *
      (2 * Real.cosh (h / 2) : ℂ)) := by
    have h1 : Continuous (fun h : ℝ => ((twoEdgeOverlap L a h : ℝ) : ℂ)) :=
      Complex.continuous_ofReal.comp (continuous_twoEdgeOverlap L a)
    have h2 : Continuous (fun h : ℝ => (2 * Real.cosh (h / 2) : ℂ)) := by
      fun_prop
    exact h1.mul h2
  exact hcont.integrableOn_Ioc

/-- **The rectangular polar--prime carrier in closed form.**  The continuous part is an elementary
integral of the explicit triangle-plus-trapezoid profile against `2cosh(h/2)`; the arithmetic part
is the von Mangoldt sum of the same profile sampled at the logarithms of the integers up to the
aperture cutoff. -/
theorem twoEdge_polarPrimeAutocorrelationQuadratic_eq (L a : ℝ) :
    polarPrimeAutocorrelationQuadratic a (twoEdgeIndicator L a)
      = 2 * (∫ h in Set.Ioc (0 : ℝ) (2 * a),
            twoEdgeOverlap L a h * (2 * Real.cosh (h / 2)))
        - 2 * ∑ k ∈ Finset.Icc 2 ⌊Real.exp (2 * a)⌋₊,
            criticalMellinAtomWeight k * twoEdgeOverlap L a (Real.log k) := by
  have hre : ∀ h : ℝ, (apertureAutocorrelation (twoEdgeIndicator L a) h).re
      = twoEdgeOverlap L a h := by
    intro h
    rw [twoEdge_apertureAutocorrelation_eq L a h, Complex.ofReal_re]
  rw [polarPrimeAutocorrelationQuadratic_eq_integral_sub_sum
      (integrable_twoEdge_autocorrelation_mul_cosh L a)]
  congr 1
  · congr 1
    apply MeasureTheory.integral_congr_ae
    filter_upwards with h
    rw [hre h]
  · congr 1
    apply Finset.sum_congr rfl
    intro k _
    rw [hre (Real.log k)]

end RHTower
