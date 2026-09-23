import GaloisForLFunctions.RHTower.PrimeArchThetaGaussianApertureBalance
import GaloisForLFunctions.HTGeometry.HalfLineSteinRobertson
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-!
# The forced Gaussian-aperture composite window

The two weighted Turan windows consumed by the Gaussian-aperture balance should not be estimated
separately.  Their forced composite has a much more rigid derivative.  If `M_j` denotes the
half-line moment of the tilted completed theta source, its derivative is the positive density
factor `2 f(t) t^(2 : ℕ)` times the quadratic

`M_2^(2 : ℕ) - (M_1 M_2 + M_0 M_3 / 5) t^(2 : ℕ) + (M_0 M_2 / 5) t^(4 : ℕ)`.

This file constructs that literal source window.  It proves the derivative identity, its two
zero-endpoint laws, positivity of every tilted half-moment, and nonnegativity of the quadratic
discriminant from source log-convexity.  These are the dependency-closed ingredients behind the
one-crossing theorem; no independent pointwise estimate on either Turan window is assumed.
-/

open Complex Real MeasureTheory Set Filter Topology Polynomial

namespace RHTower

noncomputable section

/-- The completed theta density after the physical Gaussian contraction `lambda ≤ 0`. -/
def thetaCuspGaussianApertureDensity (lambda x : ℝ) : ℝ :=
  Real.exp (lambda * x ^ (2 : ℕ)) * thetaCuspFullSource x

/-- Half of the existing even Gaussian-aperture moment. -/
def thetaCuspGaussianApertureHalfMoment (lambda : ℝ) (j : ℕ) : ℝ :=
  ∫ x : ℝ in Ioi 0, x ^ (2 * j) * thetaCuspGaussianApertureDensity lambda x

/-- The moment prefix used to split a crossing window at height `t`. -/
def thetaCuspGaussianApertureMomentPrefix (lambda : ℝ) (j : ℕ) (t : ℝ) : ℝ :=
  ∫ x : ℝ in (0 : ℝ)..t,
    x ^ (2 * j) * thetaCuspGaussianApertureDensity lambda x

/-- The positive crossing window, already reduced from the double integral to prefix moments. -/
def thetaCuspGaussianApertureCrossingWindow
    (lambda : ℝ) (m : ℕ) (t : ℝ) : ℝ :=
  thetaCuspGaussianApertureMomentPrefix lambda m t *
      thetaCuspGaussianApertureHalfMoment lambda (m + 1) -
    thetaCuspGaussianApertureMomentPrefix lambda (m + 1) t *
      thetaCuspGaussianApertureHalfMoment lambda m

/-- The single forced window in the curvature representation of the aperture balance. -/
def thetaCuspGaussianApertureCompositeWindow (lambda t : ℝ) : ℝ :=
  thetaCuspGaussianApertureMoment lambda 2 *
      thetaCuspGaussianApertureCrossingWindow lambda 1 t -
    thetaCuspGaussianApertureMoment lambda 0 / 5 *
      thetaCuspGaussianApertureCrossingWindow lambda 2 t

/-- The exact quadratic controlling the height derivative of the composite window. -/
def thetaCuspGaussianApertureWindowDerivativePolynomial (lambda y : ℝ) : ℝ :=
  thetaCuspGaussianApertureHalfMoment lambda 2 ^ (2 : ℕ) -
      (thetaCuspGaussianApertureHalfMoment lambda 1 *
          thetaCuspGaussianApertureHalfMoment lambda 2 +
        thetaCuspGaussianApertureHalfMoment lambda 0 *
          thetaCuspGaussianApertureHalfMoment lambda 3 / 5) * y +
    thetaCuspGaussianApertureHalfMoment lambda 0 *
      thetaCuspGaussianApertureHalfMoment lambda 2 / 5 * y ^ (2 : ℕ)

/-- The discriminant of the exact height-derivative quadratic. -/
def thetaCuspGaussianApertureWindowDerivativeDiscriminant (lambda : ℝ) : ℝ :=
  (thetaCuspGaussianApertureHalfMoment lambda 1 *
        thetaCuspGaussianApertureHalfMoment lambda 2 +
      thetaCuspGaussianApertureHalfMoment lambda 0 *
        thetaCuspGaussianApertureHalfMoment lambda 3 / 5) ^ (2 : ℕ) -
    4 * (thetaCuspGaussianApertureHalfMoment lambda 0 *
      thetaCuspGaussianApertureHalfMoment lambda 2 / 5) *
        thetaCuspGaussianApertureHalfMoment lambda 2 ^ (2 : ℕ)

theorem continuous_thetaCuspGaussianApertureDensity (lambda : ℝ) :
    Continuous (thetaCuspGaussianApertureDensity lambda) := by
  unfold thetaCuspGaussianApertureDensity
  exact (Real.continuous_exp.comp
    (continuous_const.mul (continuous_id.pow 2))).mul
      contDiff_thetaCuspFullSource.continuous

theorem continuous_thetaCuspGaussianApertureMomentIntegrand
    (lambda : ℝ) (j : ℕ) :
    Continuous (fun x : ℝ =>
      x ^ (2 * j) * thetaCuspGaussianApertureDensity lambda x) := by
  exact (continuous_id.pow _).mul
    (continuous_thetaCuspGaussianApertureDensity lambda)

/-- The existing full moment is exactly twice the half moment used by the crossing calculus. -/
theorem thetaCuspGaussianApertureMoment_eq_two_mul_halfMoment
    (lambda : ℝ) (j : ℕ) :
    thetaCuspGaussianApertureMoment lambda j =
      2 * thetaCuspGaussianApertureHalfMoment lambda j := by
  unfold thetaCuspGaussianApertureMoment thetaCuspGaussianApertureHalfMoment
    thetaCuspGaussianApertureDensity
  congr 2
  funext x
  ring

/-- Gaussian contraction preserves integrability of every completed-source polynomial moment. -/
theorem integrableOn_thetaCuspGaussianApertureMomentIntegrand
    {lambda : ℝ} (hlambda : lambda ≤ 0) (j : ℕ) :
    IntegrableOn (fun x : ℝ =>
      x ^ (2 * j) * thetaCuspGaussianApertureDensity lambda x) (Ioi 0) := by
  have hbase := integrableOn_thetaCuspRawMoment (2 * j)
  refine MeasureTheory.Integrable.mono hbase ?_ ?_
  · exact Continuous.aestronglyMeasurable
      (continuous_thetaCuspGaussianApertureMomentIntegrand lambda j)
      (μ := volume.restrict (Ioi 0))
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hpow : 0 ≤ x ^ (2 * j) := pow_nonneg hx.le _
    have hsource : 0 ≤ thetaCuspFullSource x :=
      (thetaCuspFullSource_pos_of_pos hx).le
    have hexpNonneg : 0 ≤ Real.exp (lambda * x ^ (2 : ℕ)) := Real.exp_nonneg _
    have hexpLe : Real.exp (lambda * x ^ (2 : ℕ)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg hlambda (sq_nonneg x))
    rw [thetaCuspGaussianApertureDensity, Real.norm_eq_abs, Real.norm_eq_abs]
    rw [abs_of_nonneg (mul_nonneg hpow (mul_nonneg hexpNonneg hsource)),
      abs_of_nonneg (mul_nonneg hpow hsource)]
    nlinarith [mul_nonneg hpow hsource]

/-- Every contracted half moment is strictly positive. -/
theorem thetaCuspGaussianApertureHalfMoment_pos
    {lambda : ℝ} (hlambda : lambda ≤ 0) (j : ℕ) :
    0 < thetaCuspGaussianApertureHalfMoment lambda j := by
  let f : ℝ → ℝ := fun x =>
    x ^ (2 * j) * thetaCuspGaussianApertureDensity lambda x
  have hfcont : Continuous f := by
    simpa only [f] using
      continuous_thetaCuspGaussianApertureMomentIntegrand lambda j
  have hfint : IntegrableOn f (Ioi 0) := by
    simpa only [f] using
      integrableOn_thetaCuspGaussianApertureMomentIntegrand hlambda j
  have hfnn : 0 ≤ᵐ[volume.restrict (Ioi 0)] f := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    dsimp [f, thetaCuspGaussianApertureDensity]
    exact mul_nonneg (pow_nonneg hx.le _)
      (mul_nonneg (Real.exp_nonneg _) (thetaCuspFullSource_pos_of_pos hx).le)
  rw [thetaCuspGaussianApertureHalfMoment]
  apply (setIntegral_pos_iff_support_of_nonneg_ae hfnn hfint).2
  have hopen : IsOpen (Function.support f ∩ Ioi (0 : ℝ)) :=
    hfcont.isOpen_support.inter isOpen_Ioi
  apply hopen.measure_pos (volume : Measure ℝ)
  refine ⟨1, ?_, by norm_num⟩
  change f 1 ≠ 0
  dsimp [f, thetaCuspGaussianApertureDensity]
  exact ne_of_gt (mul_pos (by positivity)
    (mul_pos (Real.exp_pos _)
      (thetaCuspFullSource_pos_of_pos (x := 1) (by norm_num))))

/-- Cauchy--Schwarz log-convexity of the four contracted moments used by the window. -/
theorem thetaCuspGaussianApertureHalfMoment_two_sq_le_one_mul_three
    {lambda : ℝ} (hlambda : lambda ≤ 0) :
    thetaCuspGaussianApertureHalfMoment lambda 2 ^ (2 : ℕ) ≤
      thetaCuspGaussianApertureHalfMoment lambda 1 *
        thetaCuspGaussianApertureHalfMoment lambda 3 := by
  let mu : Measure ℝ := volume.restrict (Ioi 0)
  let f : ℝ → ℝ := fun x =>
    x * Real.sqrt (thetaCuspGaussianApertureDensity lambda x)
  let g : ℝ → ℝ := fun x =>
    x ^ (3 : ℕ) * Real.sqrt (thetaCuspGaussianApertureDensity lambda x)
  have hdensity : 0 ≤ᵐ[mu] thetaCuspGaussianApertureDensity lambda := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    rw [thetaCuspGaussianApertureDensity]
    positivity [thetaCuspFullSource_pos_of_pos hx]
  have hfmeas : AEStronglyMeasurable f mu := by
    exact Continuous.aestronglyMeasurable
      (continuous_id.mul (Real.continuous_sqrt.comp
        (continuous_thetaCuspGaussianApertureDensity lambda))) (μ := mu)
  have hgmeas : AEStronglyMeasurable g mu := by
    exact Continuous.aestronglyMeasurable
      ((continuous_id.pow 3).mul (Real.continuous_sqrt.comp
        (continuous_thetaCuspGaussianApertureDensity lambda))) (μ := mu)
  have hfSq : Integrable (fun x => f x ^ (2 : ℕ)) mu := by
    have h := integrableOn_thetaCuspGaussianApertureMomentIntegrand hlambda 1
    apply h.congr
    filter_upwards [hdensity] with x hx
    dsimp [f]
    rw [mul_pow, Real.sq_sqrt hx]
  have hgSq : Integrable (fun x => g x ^ (2 : ℕ)) mu := by
    have h := integrableOn_thetaCuspGaussianApertureMomentIntegrand hlambda 3
    apply h.congr
    filter_upwards [hdensity] with x hx
    dsimp [g]
    rw [mul_pow, Real.sq_sqrt hx]
    ring
  have hcs := HTGeometry.sq_integral_mul_le_integral_sq_mul_integral_sq
    hfmeas hgmeas hfSq hgSq
  have hfg : (∫ x, f x * g x ∂mu) =
      thetaCuspGaussianApertureHalfMoment lambda 2 := by
    rw [thetaCuspGaussianApertureHalfMoment]
    apply integral_congr_ae
    filter_upwards [hdensity, ae_restrict_mem measurableSet_Ioi] with x hx hxi
    dsimp [f, g]
    calc
      x * √(thetaCuspGaussianApertureDensity lambda x) *
          (x ^ (3 : ℕ) * √(thetaCuspGaussianApertureDensity lambda x)) =
          x ^ (4 : ℕ) * (√(thetaCuspGaussianApertureDensity lambda x)) ^ (2 : ℕ) := by ring
      _ = x ^ (4 : ℕ) * thetaCuspGaussianApertureDensity lambda x := by
        rw [Real.sq_sqrt hx]
  have hf2 : (∫ x, f x ^ (2 : ℕ) ∂mu) =
      thetaCuspGaussianApertureHalfMoment lambda 1 := by
    rw [thetaCuspGaussianApertureHalfMoment]
    apply integral_congr_ae
    filter_upwards [hdensity] with x hx
    dsimp [f]
    rw [mul_pow, Real.sq_sqrt hx]
  have hg2 : (∫ x, g x ^ (2 : ℕ) ∂mu) =
      thetaCuspGaussianApertureHalfMoment lambda 3 := by
    rw [thetaCuspGaussianApertureHalfMoment]
    apply integral_congr_ae
    filter_upwards [hdensity] with x hx
    dsimp [g]
    rw [mul_pow, Real.sq_sqrt hx]
    ring
  rwa [hfg, hf2, hg2] at hcs

/-- Prefix differentiation is literal FTC differentiation of the contracted moment density. -/
theorem hasDerivAt_thetaCuspGaussianApertureMomentPrefix
    (lambda : ℝ) (j : ℕ) (t : ℝ) :
    HasDerivAt (thetaCuspGaussianApertureMomentPrefix lambda j)
      (t ^ (2 * j) * thetaCuspGaussianApertureDensity lambda t) t := by
  let f : ℝ → ℝ := fun x =>
    x ^ (2 * j) * thetaCuspGaussianApertureDensity lambda x
  have hfcont : Continuous f := by
    simpa only [f] using
      continuous_thetaCuspGaussianApertureMomentIntegrand lambda j
  have h := intervalIntegral.integral_hasDerivAt_right
    (hfcont.intervalIntegrable 0 t)
    (hfcont.stronglyMeasurableAtFilter volume (nhds t)) hfcont.continuousAt
  exact h

/-- Exact derivative of one positive crossing window. -/
theorem hasDerivAt_thetaCuspGaussianApertureCrossingWindow
    (lambda : ℝ) (m : ℕ) (t : ℝ) :
    HasDerivAt (thetaCuspGaussianApertureCrossingWindow lambda m)
      (thetaCuspGaussianApertureDensity lambda t * t ^ (2 * m) *
        (thetaCuspGaussianApertureHalfMoment lambda (m + 1) -
          t ^ (2 : ℕ) * thetaCuspGaussianApertureHalfMoment lambda m)) t := by
  have h₀ := (hasDerivAt_thetaCuspGaussianApertureMomentPrefix lambda m t).const_mul
    (thetaCuspGaussianApertureHalfMoment lambda (m + 1))
  have h₁ := (hasDerivAt_thetaCuspGaussianApertureMomentPrefix lambda (m + 1) t).const_mul
    (thetaCuspGaussianApertureHalfMoment lambda m)
  have hfun : (fun y : ℝ =>
      thetaCuspGaussianApertureHalfMoment lambda (m + 1) *
          thetaCuspGaussianApertureMomentPrefix lambda m y -
        thetaCuspGaussianApertureHalfMoment lambda m *
          thetaCuspGaussianApertureMomentPrefix lambda (m + 1) y) =
      thetaCuspGaussianApertureCrossingWindow lambda m := by
    funext y
    simp only [thetaCuspGaussianApertureCrossingWindow]
    ring
  have hval : thetaCuspGaussianApertureHalfMoment lambda (m + 1) *
        (t ^ (2 * m) * thetaCuspGaussianApertureDensity lambda t) -
      thetaCuspGaussianApertureHalfMoment lambda m *
        (t ^ (2 * (m + 1)) * thetaCuspGaussianApertureDensity lambda t) =
      thetaCuspGaussianApertureDensity lambda t * t ^ (2 * m) *
        (thetaCuspGaussianApertureHalfMoment lambda (m + 1) -
          t ^ (2 : ℕ) * thetaCuspGaussianApertureHalfMoment lambda m) := by
    rw [show 2 * (m + 1) = 2 * m + 2 by omega, pow_add]
    ring
  rw [← hfun, ← hval]
  exact h₀.sub h₁

/-- **Exact derivative collapse.**  The forced two-window composite has a quadratic height
derivative; no separate estimate on either component remains. -/
theorem hasDerivAt_thetaCuspGaussianApertureCompositeWindow
    (lambda t : ℝ) :
    HasDerivAt (thetaCuspGaussianApertureCompositeWindow lambda)
      (2 * thetaCuspGaussianApertureDensity lambda t * t ^ (2 : ℕ) *
        thetaCuspGaussianApertureWindowDerivativePolynomial lambda (t ^ (2 : ℕ))) t := by
  have h₁ := (hasDerivAt_thetaCuspGaussianApertureCrossingWindow lambda 1 t).const_mul
    (thetaCuspGaussianApertureMoment lambda 2)
  have h₂ := (hasDerivAt_thetaCuspGaussianApertureCrossingWindow lambda 2 t).const_mul
    (thetaCuspGaussianApertureMoment lambda 0 / 5)
  have hval : thetaCuspGaussianApertureMoment lambda 2 *
        (thetaCuspGaussianApertureDensity lambda t * t ^ (2 * 1) *
          (thetaCuspGaussianApertureHalfMoment lambda (1 + 1) -
            t ^ (2 : ℕ) * thetaCuspGaussianApertureHalfMoment lambda 1)) -
      thetaCuspGaussianApertureMoment lambda 0 / 5 *
        (thetaCuspGaussianApertureDensity lambda t * t ^ (2 * 2) *
          (thetaCuspGaussianApertureHalfMoment lambda (2 + 1) -
            t ^ (2 : ℕ) * thetaCuspGaussianApertureHalfMoment lambda 2)) =
      2 * thetaCuspGaussianApertureDensity lambda t * t ^ (2 : ℕ) *
        thetaCuspGaussianApertureWindowDerivativePolynomial lambda (t ^ (2 : ℕ)) := by
    rw [thetaCuspGaussianApertureMoment_eq_two_mul_halfMoment,
      thetaCuspGaussianApertureMoment_eq_two_mul_halfMoment]
    simp only [thetaCuspGaussianApertureWindowDerivativePolynomial,
      Nat.reduceMul, Nat.reduceAdd, pow_two]
    ring
  rw [← hval]
  exact h₁.sub h₂

/-- Every moment prefix converges to its full half moment as the height tends to infinity. -/
theorem tendsto_thetaCuspGaussianApertureMomentPrefix_atTop
    {lambda : ℝ} (hlambda : lambda ≤ 0) (j : ℕ) :
    Tendsto (thetaCuspGaussianApertureMomentPrefix lambda j) atTop
      (nhds (thetaCuspGaussianApertureHalfMoment lambda j)) := by
  exact MeasureTheory.intervalIntegral_tendsto_integral_Ioi 0
    (integrableOn_thetaCuspGaussianApertureMomentIntegrand hlambda j) tendsto_id

/-- Each crossing window vanishes at the far endpoint. -/
theorem tendsto_thetaCuspGaussianApertureCrossingWindow_atTop
    {lambda : ℝ} (hlambda : lambda ≤ 0) (m : ℕ) :
    Tendsto (thetaCuspGaussianApertureCrossingWindow lambda m) atTop (nhds 0) := by
  have hcNext : Tendsto
      (fun _ : ℝ => thetaCuspGaussianApertureHalfMoment lambda (m + 1)) atTop
      (nhds (thetaCuspGaussianApertureHalfMoment lambda (m + 1))) := tendsto_const_nhds
  have hc : Tendsto
      (fun _ : ℝ => thetaCuspGaussianApertureHalfMoment lambda m) atTop
      (nhds (thetaCuspGaussianApertureHalfMoment lambda m)) := tendsto_const_nhds
  have h₀ := (tendsto_thetaCuspGaussianApertureMomentPrefix_atTop hlambda m).mul
    hcNext
  have h₁ := (tendsto_thetaCuspGaussianApertureMomentPrefix_atTop hlambda (m + 1)).mul
    hc
  have h := h₀.sub h₁
  rw [show thetaCuspGaussianApertureHalfMoment lambda m *
        thetaCuspGaussianApertureHalfMoment lambda (m + 1) -
      thetaCuspGaussianApertureHalfMoment lambda (m + 1) *
        thetaCuspGaussianApertureHalfMoment lambda m = 0 by ring] at h
  exact h

/-- The forced composite also vanishes at the far endpoint. -/
theorem tendsto_thetaCuspGaussianApertureCompositeWindow_atTop
    {lambda : ℝ} (hlambda : lambda ≤ 0) :
    Tendsto (thetaCuspGaussianApertureCompositeWindow lambda) atTop (nhds 0) := by
  have hc₂ : Tendsto (fun _ : ℝ => thetaCuspGaussianApertureMoment lambda 2) atTop
      (nhds (thetaCuspGaussianApertureMoment lambda 2)) := tendsto_const_nhds
  have hc₀ : Tendsto (fun _ : ℝ => thetaCuspGaussianApertureMoment lambda 0 / 5) atTop
      (nhds (thetaCuspGaussianApertureMoment lambda 0 / 5)) := tendsto_const_nhds
  have h₁ := hc₂.mul
    (tendsto_thetaCuspGaussianApertureCrossingWindow_atTop hlambda 1)
  have h₂ := hc₀.mul
    (tendsto_thetaCuspGaussianApertureCrossingWindow_atTop hlambda 2)
  have h := h₁.sub h₂
  rw [show thetaCuspGaussianApertureMoment lambda 2 * 0 -
      thetaCuspGaussianApertureMoment lambda 0 / 5 * 0 = 0 by ring] at h
  exact h

/-- The forced composite starts at zero. -/
theorem thetaCuspGaussianApertureCompositeWindow_zero (lambda : ℝ) :
    thetaCuspGaussianApertureCompositeWindow lambda 0 = 0 := by
  simp [thetaCuspGaussianApertureCompositeWindow,
    thetaCuspGaussianApertureCrossingWindow,
    thetaCuspGaussianApertureMomentPrefix]

/-- Source log-convexity puts the exact derivative quadratic in the real-root chamber. -/
theorem thetaCuspGaussianApertureWindowDerivativeDiscriminant_nonneg
    {lambda : ℝ} (hlambda : lambda ≤ 0) :
    0 ≤ thetaCuspGaussianApertureWindowDerivativeDiscriminant lambda := by
  have hlog :=
    thetaCuspGaussianApertureHalfMoment_two_sq_le_one_mul_three hlambda
  have h0 := thetaCuspGaussianApertureHalfMoment_pos hlambda 0
  have h1 := thetaCuspGaussianApertureHalfMoment_pos hlambda 1
  have h2 := thetaCuspGaussianApertureHalfMoment_pos hlambda 2
  have h3 := thetaCuspGaussianApertureHalfMoment_pos hlambda 3
  have hamgm : 0 ≤
      (thetaCuspGaussianApertureHalfMoment lambda 1 *
          thetaCuspGaussianApertureHalfMoment lambda 2 -
        thetaCuspGaussianApertureHalfMoment lambda 0 *
          thetaCuspGaussianApertureHalfMoment lambda 3 / 5) ^ (2 : ℕ) := sq_nonneg _
  rw [thetaCuspGaussianApertureWindowDerivativeDiscriminant]
  nlinarith [mul_pos h0 h2, mul_pos h1 h3]

/-- The positive linear coefficient of the derivative quadratic. -/
def thetaCuspGaussianApertureWindowDerivativeLinearCoefficient (lambda : ℝ) : ℝ :=
  thetaCuspGaussianApertureHalfMoment lambda 1 *
      thetaCuspGaussianApertureHalfMoment lambda 2 +
    thetaCuspGaussianApertureHalfMoment lambda 0 *
      thetaCuspGaussianApertureHalfMoment lambda 3 / 5

/-- A canonical height lying strictly inside the initial positive-derivative chamber. -/
def thetaCuspGaussianApertureWindowInitialHeight (lambda : ℝ) : ℝ :=
  Real.sqrt
    (thetaCuspGaussianApertureHalfMoment lambda 2 ^ (2 : ℕ) /
      (2 * thetaCuspGaussianApertureWindowDerivativeLinearCoefficient lambda))

theorem thetaCuspGaussianApertureWindowDerivativeLinearCoefficient_pos
    {lambda : ℝ} (hlambda : lambda ≤ 0) :
    0 < thetaCuspGaussianApertureWindowDerivativeLinearCoefficient lambda := by
  have h0 := thetaCuspGaussianApertureHalfMoment_pos hlambda 0
  have h1 := thetaCuspGaussianApertureHalfMoment_pos hlambda 1
  have h2 := thetaCuspGaussianApertureHalfMoment_pos hlambda 2
  have h3 := thetaCuspGaussianApertureHalfMoment_pos hlambda 3
  rw [thetaCuspGaussianApertureWindowDerivativeLinearCoefficient]
  positivity

theorem thetaCuspGaussianApertureWindowInitialHeight_pos
    {lambda : ℝ} (hlambda : lambda ≤ 0) :
    0 < thetaCuspGaussianApertureWindowInitialHeight lambda := by
  rw [thetaCuspGaussianApertureWindowInitialHeight]
  apply Real.sqrt_pos.mpr
  exact div_pos (sq_pos_of_pos (thetaCuspGaussianApertureHalfMoment_pos hlambda 2))
    (mul_pos (by norm_num)
      (thetaCuspGaussianApertureWindowDerivativeLinearCoefficient_pos hlambda))

/-- Before the canonical initial height, the derivative quadratic is strictly positive. -/
theorem thetaCuspGaussianApertureWindowDerivativePolynomial_pos_of_lt_initialHeight
    {lambda t : ℝ} (hlambda : lambda ≤ 0) (ht : 0 < t)
    (htInitial : t < thetaCuspGaussianApertureWindowInitialHeight lambda) :
    0 < thetaCuspGaussianApertureWindowDerivativePolynomial lambda (t ^ (2 : ℕ)) := by
  let m0 := thetaCuspGaussianApertureHalfMoment lambda 0
  let m1 := thetaCuspGaussianApertureHalfMoment lambda 1
  let m2 := thetaCuspGaussianApertureHalfMoment lambda 2
  let m3 := thetaCuspGaussianApertureHalfMoment lambda 3
  let b := thetaCuspGaussianApertureWindowDerivativeLinearCoefficient lambda
  have hm0 : 0 < m0 := thetaCuspGaussianApertureHalfMoment_pos hlambda 0
  have hm2 : 0 < m2 := thetaCuspGaussianApertureHalfMoment_pos hlambda 2
  have hb : 0 < b := thetaCuspGaussianApertureWindowDerivativeLinearCoefficient_pos hlambda
  have hyPos : 0 < m2 ^ (2 : ℕ) / (2 * b) :=
    div_pos (sq_pos_of_pos hm2) (mul_pos (by norm_num) hb)
  have hheightSq : thetaCuspGaussianApertureWindowInitialHeight lambda ^ (2 : ℕ) =
      m2 ^ (2 : ℕ) / (2 * b) := by
    rw [thetaCuspGaussianApertureWindowInitialHeight, Real.sq_sqrt]
    exact hyPos.le
  have htSq : t ^ (2 : ℕ) < m2 ^ (2 : ℕ) / (2 * b) := by
    rw [← hheightSq]
    exact (sq_lt_sq₀ ht.le (thetaCuspGaussianApertureWindowInitialHeight_pos hlambda).le).2
      htInitial
  have hcross : b * t ^ (2 : ℕ) < m2 ^ (2 : ℕ) / 2 := by
    have hden : 0 < 2 * b := mul_pos (by norm_num) hb
    rw [lt_div_iff₀ hden] at htSq
    nlinarith
  have hlead : 0 ≤ m0 * m2 / 5 * (t ^ (2 : ℕ)) ^ (2 : ℕ) := by positivity
  change 0 < m2 ^ (2 : ℕ) -
      (m1 * m2 + m0 * m3 / 5) * t ^ (2 : ℕ) +
        m0 * m2 / 5 * (t ^ (2 : ℕ)) ^ (2 : ℕ)
  have hbEq : b = m1 * m2 + m0 * m3 / 5 := by
    rfl
  rw [← hbEq]
  nlinarith [sq_pos_of_pos hm2]

/-- The literal composite window is strictly positive at a canonical source-derived height. -/
theorem thetaCuspGaussianApertureCompositeWindow_initialHeight_pos
    {lambda : ℝ} (hlambda : lambda ≤ 0) :
    0 < thetaCuspGaussianApertureCompositeWindow lambda
      (thetaCuspGaussianApertureWindowInitialHeight lambda) := by
  let T := thetaCuspGaussianApertureWindowInitialHeight lambda
  have hT : 0 < T := thetaCuspGaussianApertureWindowInitialHeight_pos hlambda
  have hcont : ContinuousOn (thetaCuspGaussianApertureCompositeWindow lambda) (Icc 0 T) := by
    intro t ht
    exact (hasDerivAt_thetaCuspGaussianApertureCompositeWindow lambda t).continuousAt.continuousWithinAt
  have hstrict : StrictMonoOn (thetaCuspGaussianApertureCompositeWindow lambda) (Icc 0 T) := by
    apply strictMonoOn_of_deriv_pos (convex_Icc 0 T) hcont
    intro t ht
    rw [interior_Icc] at ht
    rw [(hasDerivAt_thetaCuspGaussianApertureCompositeWindow lambda t).deriv]
    have hdensity : 0 < thetaCuspGaussianApertureDensity lambda t := by
      rw [thetaCuspGaussianApertureDensity]
      exact mul_pos (Real.exp_pos _) (thetaCuspFullSource_pos_of_pos ht.1)
    exact mul_pos (mul_pos (mul_pos (by norm_num) hdensity) (sq_pos_of_pos ht.1))
      (thetaCuspGaussianApertureWindowDerivativePolynomial_pos_of_lt_initialHeight
        hlambda ht.1 ht.2)
  have hrise := hstrict (show 0 ∈ Icc (0 : ℝ) T by exact ⟨le_rfl, hT.le⟩)
    (show T ∈ Icc (0 : ℝ) T by exact ⟨hT.le, le_rfl⟩) hT
  rwa [thetaCuspGaussianApertureCompositeWindow_zero] at hrise

/-- **No degenerate derivative chamber.**  The endpoint return to zero rules out a double root,
so the exact derivative quadratic has two distinct real roots for every physical aperture. -/
theorem thetaCuspGaussianApertureWindowDerivativeDiscriminant_pos
    {lambda : ℝ} (hlambda : lambda ≤ 0) :
    0 < thetaCuspGaussianApertureWindowDerivativeDiscriminant lambda := by
  have hdiscNonneg :=
    thetaCuspGaussianApertureWindowDerivativeDiscriminant_nonneg hlambda
  by_contra hdiscNotPos
  have hdiscZero : thetaCuspGaussianApertureWindowDerivativeDiscriminant lambda = 0 :=
    le_antisymm (le_of_not_gt hdiscNotPos) hdiscNonneg
  let m0 := thetaCuspGaussianApertureHalfMoment lambda 0
  let m1 := thetaCuspGaussianApertureHalfMoment lambda 1
  let m2 := thetaCuspGaussianApertureHalfMoment lambda 2
  let m3 := thetaCuspGaussianApertureHalfMoment lambda 3
  let a := m0 * m2 / 5
  let b := m1 * m2 + m0 * m3 / 5
  have hm0 : 0 < m0 := thetaCuspGaussianApertureHalfMoment_pos hlambda 0
  have hm2 : 0 < m2 := thetaCuspGaussianApertureHalfMoment_pos hlambda 2
  have ha : 0 < a := by positivity
  have hdiscEq : b ^ (2 : ℕ) - 4 * a * m2 ^ (2 : ℕ) = 0 := by
    simpa only [thetaCuspGaussianApertureWindowDerivativeDiscriminant, m0, m1, m2,
      m3, a, b] using hdiscZero
  have hpolyNonneg : ∀ y : ℝ,
      0 ≤ thetaCuspGaussianApertureWindowDerivativePolynomial lambda y := by
    intro y
    have hsquare : 0 ≤ (2 * a * y - b) ^ (2 : ℕ) := sq_nonneg _
    change 0 ≤ m2 ^ (2 : ℕ) - b * y + a * y ^ (2 : ℕ)
    nlinarith
  have hcont : ContinuousOn (thetaCuspGaussianApertureCompositeWindow lambda) (Ici 0) := by
    intro t ht
    exact (hasDerivAt_thetaCuspGaussianApertureCompositeWindow lambda t).continuousAt.continuousWithinAt
  have hdiff : DifferentiableOn ℝ
      (thetaCuspGaussianApertureCompositeWindow lambda) (interior (Ici 0)) := by
    intro t ht
    exact (hasDerivAt_thetaCuspGaussianApertureCompositeWindow lambda t).differentiableAt.differentiableWithinAt
  have hmono : MonotoneOn (thetaCuspGaussianApertureCompositeWindow lambda) (Ici 0) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 0) hcont hdiff
    intro t ht
    rw [interior_Ici] at ht
    rw [(hasDerivAt_thetaCuspGaussianApertureCompositeWindow lambda t).deriv]
    exact mul_nonneg
      (mul_nonneg (mul_nonneg (by norm_num)
        (by
          rw [thetaCuspGaussianApertureDensity]
          exact mul_nonneg (Real.exp_nonneg _)
            (thetaCuspFullSource_pos_of_pos ht).le))
        (sq_nonneg t))
      (hpolyNonneg (t ^ (2 : ℕ)))
  let T := thetaCuspGaussianApertureWindowInitialHeight lambda
  have hT : 0 < T := thetaCuspGaussianApertureWindowInitialHeight_pos hlambda
  have hlimit := tendsto_thetaCuspGaussianApertureCompositeWindow_atTop hlambda
  have hTnonpos : thetaCuspGaussianApertureCompositeWindow lambda T ≤ 0 := by
    exact ge_of_tendsto hlimit (by
      filter_upwards [eventually_ge_atTop T] with t ht
      have htmem : t ∈ Ici (0 : ℝ) := le_trans hT.le ht
      exact hmono hT.le htmem ht)
  have hTpos := thetaCuspGaussianApertureCompositeWindow_initialHeight_pos hlambda
  exact (not_lt_of_ge hTnonpos hTpos)

/-- Positive leading coefficient of the derivative quadratic. -/
def thetaCuspGaussianApertureWindowDerivativeLeadingCoefficient (lambda : ℝ) : ℝ :=
  thetaCuspGaussianApertureHalfMoment lambda 0 *
    thetaCuspGaussianApertureHalfMoment lambda 2 / 5

/-- Smaller root square of the exact derivative quadratic. -/
def thetaCuspGaussianApertureWindowLowerRootSq (lambda : ℝ) : ℝ :=
  (thetaCuspGaussianApertureWindowDerivativeLinearCoefficient lambda -
      Real.sqrt (thetaCuspGaussianApertureWindowDerivativeDiscriminant lambda)) /
    (2 * thetaCuspGaussianApertureWindowDerivativeLeadingCoefficient lambda)

/-- Larger root square of the exact derivative quadratic. -/
def thetaCuspGaussianApertureWindowUpperRootSq (lambda : ℝ) : ℝ :=
  (thetaCuspGaussianApertureWindowDerivativeLinearCoefficient lambda +
      Real.sqrt (thetaCuspGaussianApertureWindowDerivativeDiscriminant lambda)) /
    (2 * thetaCuspGaussianApertureWindowDerivativeLeadingCoefficient lambda)

theorem thetaCuspGaussianApertureWindowDerivativeLeadingCoefficient_pos
    {lambda : ℝ} (hlambda : lambda ≤ 0) :
    0 < thetaCuspGaussianApertureWindowDerivativeLeadingCoefficient lambda := by
  rw [thetaCuspGaussianApertureWindowDerivativeLeadingCoefficient]
  positivity [thetaCuspGaussianApertureHalfMoment_pos hlambda 0,
    thetaCuspGaussianApertureHalfMoment_pos hlambda 2]

/-- The discriminant differs from the squared linear coefficient by the strictly positive
`4ac` term. -/
theorem thetaCuspGaussianApertureWindowDerivativeDiscriminant_lt_linear_sq
    {lambda : ℝ} (hlambda : lambda ≤ 0) :
    thetaCuspGaussianApertureWindowDerivativeDiscriminant lambda <
      thetaCuspGaussianApertureWindowDerivativeLinearCoefficient lambda ^ (2 : ℕ) := by
  have ha := thetaCuspGaussianApertureWindowDerivativeLeadingCoefficient_pos hlambda
  have hm2 := thetaCuspGaussianApertureHalfMoment_pos hlambda 2
  simp only [thetaCuspGaussianApertureWindowDerivativeDiscriminant,
    thetaCuspGaussianApertureWindowDerivativeLinearCoefficient,
    thetaCuspGaussianApertureWindowDerivativeLeadingCoefficient] at ha ⊢
  nlinarith [mul_pos ha (sq_pos_of_pos hm2)]

theorem thetaCuspGaussianApertureWindowLowerRootSq_pos
    {lambda : ℝ} (hlambda : lambda ≤ 0) :
    0 < thetaCuspGaussianApertureWindowLowerRootSq lambda := by
  have hdisc := thetaCuspGaussianApertureWindowDerivativeDiscriminant_pos hlambda
  have hlin := thetaCuspGaussianApertureWindowDerivativeLinearCoefficient_pos hlambda
  have hdiscLt :=
    thetaCuspGaussianApertureWindowDerivativeDiscriminant_lt_linear_sq hlambda
  have hsqrtSq :
      Real.sqrt (thetaCuspGaussianApertureWindowDerivativeDiscriminant lambda) ^ (2 : ℕ) =
        thetaCuspGaussianApertureWindowDerivativeDiscriminant lambda :=
    Real.sq_sqrt hdisc.le
  have hsqrtLt :
      Real.sqrt (thetaCuspGaussianApertureWindowDerivativeDiscriminant lambda) <
        thetaCuspGaussianApertureWindowDerivativeLinearCoefficient lambda := by
    apply (sq_lt_sq₀ (Real.sqrt_nonneg _) hlin.le).mp
    rwa [hsqrtSq]
  rw [thetaCuspGaussianApertureWindowLowerRootSq]
  exact div_pos (sub_pos.mpr hsqrtLt)
    (mul_pos (by norm_num)
      (thetaCuspGaussianApertureWindowDerivativeLeadingCoefficient_pos hlambda))

theorem thetaCuspGaussianApertureWindowLowerRootSq_lt_upperRootSq
    {lambda : ℝ} (hlambda : lambda ≤ 0) :
    thetaCuspGaussianApertureWindowLowerRootSq lambda <
      thetaCuspGaussianApertureWindowUpperRootSq lambda := by
  have hdisc := thetaCuspGaussianApertureWindowDerivativeDiscriminant_pos hlambda
  have ha := thetaCuspGaussianApertureWindowDerivativeLeadingCoefficient_pos hlambda
  rw [thetaCuspGaussianApertureWindowLowerRootSq,
    thetaCuspGaussianApertureWindowUpperRootSq]
  exact div_lt_div_of_pos_right (by nlinarith [Real.sqrt_pos.mpr hdisc])
    (mul_pos (by norm_num) ha)

theorem thetaCuspGaussianApertureWindowUpperRootSq_pos
    {lambda : ℝ} (hlambda : lambda ≤ 0) :
    0 < thetaCuspGaussianApertureWindowUpperRootSq lambda :=
  lt_trans (thetaCuspGaussianApertureWindowLowerRootSq_pos hlambda)
    (thetaCuspGaussianApertureWindowLowerRootSq_lt_upperRootSq hlambda)

/-- Exact factorization by the two source-derived root squares. -/
theorem thetaCuspGaussianApertureWindowDerivativePolynomial_factor
    {lambda : ℝ} (hlambda : lambda ≤ 0) (y : ℝ) :
    thetaCuspGaussianApertureWindowDerivativePolynomial lambda y =
      thetaCuspGaussianApertureWindowDerivativeLeadingCoefficient lambda *
        (y - thetaCuspGaussianApertureWindowLowerRootSq lambda) *
        (y - thetaCuspGaussianApertureWindowUpperRootSq lambda) := by
  let a := thetaCuspGaussianApertureWindowDerivativeLeadingCoefficient lambda
  let b := thetaCuspGaussianApertureWindowDerivativeLinearCoefficient lambda
  let c := thetaCuspGaussianApertureHalfMoment lambda 2 ^ (2 : ℕ)
  let d := thetaCuspGaussianApertureWindowDerivativeDiscriminant lambda
  have ha : a ≠ 0 :=
    (thetaCuspGaussianApertureWindowDerivativeLeadingCoefficient_pos hlambda).ne'
  have hd : 0 ≤ d :=
    (thetaCuspGaussianApertureWindowDerivativeDiscriminant_pos hlambda).le
  have hsqrt : Real.sqrt d ^ (2 : ℕ) = d := Real.sq_sqrt hd
  have hdEq : d = b ^ (2 : ℕ) - 4 * a * c := by
    simp only [d, b, a, c, thetaCuspGaussianApertureWindowDerivativeDiscriminant,
      thetaCuspGaussianApertureWindowDerivativeLinearCoefficient,
      thetaCuspGaussianApertureWindowDerivativeLeadingCoefficient]
  change c - b * y + a * y ^ (2 : ℕ) =
    a * (y - (b - Real.sqrt d) / (2 * a)) *
      (y - (b + Real.sqrt d) / (2 * a))
  field_simp [ha]
  nlinarith

/-- The derivative polynomial is positive below its first positive root square. -/
theorem thetaCuspGaussianApertureWindowDerivativePolynomial_pos_below_lowerRoot
    {lambda y : ℝ} (hlambda : lambda ≤ 0)
    (hyLower : y < thetaCuspGaussianApertureWindowLowerRootSq lambda) :
    0 < thetaCuspGaussianApertureWindowDerivativePolynomial lambda y := by
  rw [thetaCuspGaussianApertureWindowDerivativePolynomial_factor hlambda]
  have hUpper := lt_trans hyLower
    (thetaCuspGaussianApertureWindowLowerRootSq_lt_upperRootSq hlambda)
  exact mul_pos_of_neg_of_neg (mul_neg_of_pos_of_neg
      (thetaCuspGaussianApertureWindowDerivativeLeadingCoefficient_pos hlambda)
      (sub_neg.mpr hyLower))
    (sub_neg.mpr hUpper)

/-- The derivative polynomial is negative between its two positive root squares. -/
theorem thetaCuspGaussianApertureWindowDerivativePolynomial_neg_between_roots
    {lambda y : ℝ} (hlambda : lambda ≤ 0)
    (hLower : thetaCuspGaussianApertureWindowLowerRootSq lambda < y)
    (hUpper : y < thetaCuspGaussianApertureWindowUpperRootSq lambda) :
    thetaCuspGaussianApertureWindowDerivativePolynomial lambda y < 0 := by
  rw [thetaCuspGaussianApertureWindowDerivativePolynomial_factor hlambda]
  exact mul_neg_of_pos_of_neg
    (mul_pos (thetaCuspGaussianApertureWindowDerivativeLeadingCoefficient_pos hlambda)
      (sub_pos.mpr hLower))
    (sub_neg.mpr hUpper)

/-- The derivative polynomial is positive above its second positive root square. -/
theorem thetaCuspGaussianApertureWindowDerivativePolynomial_pos_above_upperRoot
    {lambda y : ℝ} (hlambda : lambda ≤ 0)
    (hUpper : thetaCuspGaussianApertureWindowUpperRootSq lambda < y) :
    0 < thetaCuspGaussianApertureWindowDerivativePolynomial lambda y := by
  rw [thetaCuspGaussianApertureWindowDerivativePolynomial_factor hlambda]
  have hLower := lt_trans
    (thetaCuspGaussianApertureWindowLowerRootSq_lt_upperRootSq hlambda) hUpper
  exact mul_pos (mul_pos
      (thetaCuspGaussianApertureWindowDerivativeLeadingCoefficient_pos hlambda)
      (sub_pos.mpr hLower))
    (sub_pos.mpr hUpper)

/-- **Three-phase derivative law.**  Along positive height the literal composite window rises,
falls, and rises again, with the two phase boundaries fixed by source moments. -/
theorem thetaCuspGaussianApertureCompositeWindow_deriv_threePhase
    {lambda t : ℝ} (hlambda : lambda ≤ 0) (ht : 0 < t) :
    (t ^ (2 : ℕ) < thetaCuspGaussianApertureWindowLowerRootSq lambda →
        0 < deriv (thetaCuspGaussianApertureCompositeWindow lambda) t) ∧
      (thetaCuspGaussianApertureWindowLowerRootSq lambda < t ^ (2 : ℕ) →
        t ^ (2 : ℕ) < thetaCuspGaussianApertureWindowUpperRootSq lambda →
          deriv (thetaCuspGaussianApertureCompositeWindow lambda) t < 0) ∧
      (thetaCuspGaussianApertureWindowUpperRootSq lambda < t ^ (2 : ℕ) →
        0 < deriv (thetaCuspGaussianApertureCompositeWindow lambda) t) := by
  rw [(hasDerivAt_thetaCuspGaussianApertureCompositeWindow lambda t).deriv]
  have hdensity : 0 < thetaCuspGaussianApertureDensity lambda t := by
    rw [thetaCuspGaussianApertureDensity]
    exact mul_pos (Real.exp_pos _) (thetaCuspFullSource_pos_of_pos ht)
  have hprefactor : 0 < 2 * thetaCuspGaussianApertureDensity lambda t * t ^ (2 : ℕ) := by
    positivity
  constructor
  · intro hLower
    exact mul_pos hprefactor
      (thetaCuspGaussianApertureWindowDerivativePolynomial_pos_below_lowerRoot
        hlambda hLower)
  constructor
  · intro hLower hUpper
    exact mul_neg_of_pos_of_neg hprefactor
      (thetaCuspGaussianApertureWindowDerivativePolynomial_neg_between_roots
        hlambda hLower hUpper)
  · intro hUpper
    exact mul_pos hprefactor
      (thetaCuspGaussianApertureWindowDerivativePolynomial_pos_above_upperRoot
        hlambda hUpper)

/-- First positive turning height of the composite window. -/
def thetaCuspGaussianApertureWindowLowerTurningHeight (lambda : ℝ) : ℝ :=
  Real.sqrt (thetaCuspGaussianApertureWindowLowerRootSq lambda)

/-- Second positive turning height of the composite window. -/
def thetaCuspGaussianApertureWindowUpperTurningHeight (lambda : ℝ) : ℝ :=
  Real.sqrt (thetaCuspGaussianApertureWindowUpperRootSq lambda)

theorem thetaCuspGaussianApertureWindowLowerTurningHeight_pos
    {lambda : ℝ} (hlambda : lambda ≤ 0) :
    0 < thetaCuspGaussianApertureWindowLowerTurningHeight lambda := by
  rw [thetaCuspGaussianApertureWindowLowerTurningHeight]
  exact Real.sqrt_pos.mpr
    (thetaCuspGaussianApertureWindowLowerRootSq_pos hlambda)

theorem thetaCuspGaussianApertureWindowLowerTurningHeight_sq
    {lambda : ℝ} (hlambda : lambda ≤ 0) :
    thetaCuspGaussianApertureWindowLowerTurningHeight lambda ^ (2 : ℕ) =
      thetaCuspGaussianApertureWindowLowerRootSq lambda := by
  rw [thetaCuspGaussianApertureWindowLowerTurningHeight, Real.sq_sqrt]
  exact (thetaCuspGaussianApertureWindowLowerRootSq_pos hlambda).le

theorem thetaCuspGaussianApertureWindowUpperTurningHeight_sq
    {lambda : ℝ} (hlambda : lambda ≤ 0) :
    thetaCuspGaussianApertureWindowUpperTurningHeight lambda ^ (2 : ℕ) =
      thetaCuspGaussianApertureWindowUpperRootSq lambda := by
  rw [thetaCuspGaussianApertureWindowUpperTurningHeight, Real.sq_sqrt]
  exact (thetaCuspGaussianApertureWindowUpperRootSq_pos hlambda).le

theorem thetaCuspGaussianApertureWindowLowerTurningHeight_lt_upper
    {lambda : ℝ} (hlambda : lambda ≤ 0) :
    thetaCuspGaussianApertureWindowLowerTurningHeight lambda <
      thetaCuspGaussianApertureWindowUpperTurningHeight lambda := by
  rw [thetaCuspGaussianApertureWindowLowerTurningHeight,
    thetaCuspGaussianApertureWindowUpperTurningHeight]
  exact Real.sqrt_lt_sqrt
    (thetaCuspGaussianApertureWindowLowerRootSq_pos hlambda).le
    (thetaCuspGaussianApertureWindowLowerRootSq_lt_upperRootSq hlambda)

/-- The composite window rises strictly from the seam to its first turning height. -/
theorem thetaCuspGaussianApertureCompositeWindow_strictMonoOn_initial
    {lambda : ℝ} (hlambda : lambda ≤ 0) :
    StrictMonoOn (thetaCuspGaussianApertureCompositeWindow lambda)
      (Icc 0 (thetaCuspGaussianApertureWindowLowerTurningHeight lambda)) := by
  let L := thetaCuspGaussianApertureWindowLowerTurningHeight lambda
  have hL : 0 < L := thetaCuspGaussianApertureWindowLowerTurningHeight_pos hlambda
  have hcont : ContinuousOn (thetaCuspGaussianApertureCompositeWindow lambda) (Icc 0 L) := by
    intro t ht
    exact (hasDerivAt_thetaCuspGaussianApertureCompositeWindow lambda t).continuousAt.continuousWithinAt
  apply strictMonoOn_of_deriv_pos (convex_Icc 0 L) hcont
  intro t ht
  rw [interior_Icc] at ht
  have htSq : t ^ (2 : ℕ) < thetaCuspGaussianApertureWindowLowerRootSq lambda := by
    rw [← thetaCuspGaussianApertureWindowLowerTurningHeight_sq hlambda]
    exact (sq_lt_sq₀ ht.1.le hL.le).2 ht.2
  exact (thetaCuspGaussianApertureCompositeWindow_deriv_threePhase hlambda ht.1).1 htSq

/-- Between the two turning heights, the composite window falls strictly. -/
theorem thetaCuspGaussianApertureCompositeWindow_strictAntiOn_middle
    {lambda : ℝ} (hlambda : lambda ≤ 0) :
    StrictAntiOn (thetaCuspGaussianApertureCompositeWindow lambda)
      (Icc (thetaCuspGaussianApertureWindowLowerTurningHeight lambda)
        (thetaCuspGaussianApertureWindowUpperTurningHeight lambda)) := by
  let L := thetaCuspGaussianApertureWindowLowerTurningHeight lambda
  let U := thetaCuspGaussianApertureWindowUpperTurningHeight lambda
  have hL : 0 < L := thetaCuspGaussianApertureWindowLowerTurningHeight_pos hlambda
  have hcont : ContinuousOn (thetaCuspGaussianApertureCompositeWindow lambda) (Icc L U) := by
    intro t ht
    exact (hasDerivAt_thetaCuspGaussianApertureCompositeWindow lambda t).continuousAt.continuousWithinAt
  apply strictAntiOn_of_deriv_neg (convex_Icc L U) hcont
  intro t ht
  rw [interior_Icc] at ht
  have htpos : 0 < t := lt_trans hL ht.1
  have hLower : thetaCuspGaussianApertureWindowLowerRootSq lambda < t ^ (2 : ℕ) := by
    rw [← thetaCuspGaussianApertureWindowLowerTurningHeight_sq hlambda]
    exact (sq_lt_sq₀ hL.le htpos.le).2 ht.1
  have hUpper : t ^ (2 : ℕ) < thetaCuspGaussianApertureWindowUpperRootSq lambda := by
    rw [← thetaCuspGaussianApertureWindowUpperTurningHeight_sq hlambda]
    exact (sq_lt_sq₀ htpos.le
      (le_trans hL.le
        (thetaCuspGaussianApertureWindowLowerTurningHeight_lt_upper hlambda).le)).2 ht.2
  exact (thetaCuspGaussianApertureCompositeWindow_deriv_threePhase hlambda htpos).2.1
    hLower hUpper

/-- Beyond the second turning height, the composite window rises strictly back to zero. -/
theorem thetaCuspGaussianApertureCompositeWindow_strictMonoOn_tail
    {lambda : ℝ} (hlambda : lambda ≤ 0) :
    StrictMonoOn (thetaCuspGaussianApertureCompositeWindow lambda)
      (Ici (thetaCuspGaussianApertureWindowUpperTurningHeight lambda)) := by
  let U := thetaCuspGaussianApertureWindowUpperTurningHeight lambda
  have hU : 0 < U := lt_trans
    (thetaCuspGaussianApertureWindowLowerTurningHeight_pos hlambda)
    (thetaCuspGaussianApertureWindowLowerTurningHeight_lt_upper hlambda)
  have hcont : ContinuousOn (thetaCuspGaussianApertureCompositeWindow lambda) (Ici U) := by
    intro t ht
    exact (hasDerivAt_thetaCuspGaussianApertureCompositeWindow lambda t).continuousAt.continuousWithinAt
  apply strictMonoOn_of_deriv_pos (convex_Ici U) hcont
  intro t ht
  rw [interior_Ici] at ht
  have htpos : 0 < t := lt_trans hU ht
  have hUpper : thetaCuspGaussianApertureWindowUpperRootSq lambda < t ^ (2 : ℕ) := by
    rw [← thetaCuspGaussianApertureWindowUpperTurningHeight_sq hlambda]
    exact (sq_lt_sq₀ hU.le htpos.le).2 ht
  exact (thetaCuspGaussianApertureCompositeWindow_deriv_threePhase hlambda htpos).2.2
    hUpper

theorem thetaCuspGaussianApertureCompositeWindow_lowerTurningHeight_pos
    {lambda : ℝ} (hlambda : lambda ≤ 0) :
    0 < thetaCuspGaussianApertureCompositeWindow lambda
      (thetaCuspGaussianApertureWindowLowerTurningHeight lambda) := by
  have hL := thetaCuspGaussianApertureWindowLowerTurningHeight_pos hlambda
  have hrise := thetaCuspGaussianApertureCompositeWindow_strictMonoOn_initial hlambda
    (show 0 ∈ Icc (0 : ℝ) (thetaCuspGaussianApertureWindowLowerTurningHeight lambda) by
      exact ⟨le_rfl, hL.le⟩)
    (show thetaCuspGaussianApertureWindowLowerTurningHeight lambda ∈
        Icc (0 : ℝ) (thetaCuspGaussianApertureWindowLowerTurningHeight lambda) by
      exact ⟨hL.le, le_rfl⟩) hL
  rwa [thetaCuspGaussianApertureCompositeWindow_zero] at hrise

theorem thetaCuspGaussianApertureCompositeWindow_upperTurningHeight_neg
    {lambda : ℝ} (hlambda : lambda ≤ 0) :
    thetaCuspGaussianApertureCompositeWindow lambda
      (thetaCuspGaussianApertureWindowUpperTurningHeight lambda) < 0 := by
  let U := thetaCuspGaussianApertureWindowUpperTurningHeight lambda
  let V := U + 1
  have hU : 0 < U := lt_trans
    (thetaCuspGaussianApertureWindowLowerTurningHeight_pos hlambda)
    (thetaCuspGaussianApertureWindowLowerTurningHeight_lt_upper hlambda)
  have hUV : U < V := by dsimp [V]; linarith
  have htail := thetaCuspGaussianApertureCompositeWindow_strictMonoOn_tail hlambda
  have hrise : thetaCuspGaussianApertureCompositeWindow lambda U <
      thetaCuspGaussianApertureCompositeWindow lambda V :=
    htail (show U ∈ Ici U by exact le_refl U)
      (show V ∈ Ici U by exact hUV.le) hUV
  have hVnonpos : thetaCuspGaussianApertureCompositeWindow lambda V ≤ 0 := by
    exact ge_of_tendsto
      (tendsto_thetaCuspGaussianApertureCompositeWindow_atTop hlambda) (by
        filter_upwards [eventually_ge_atTop V] with t ht
        exact htail.monotoneOn (show V ∈ Ici U by exact hUV.le)
          (show t ∈ Ici U by exact le_trans hUV.le ht) ht)
  exact lt_of_lt_of_le hrise hVnonpos

/-- **Exact one-crossing theorem.**  For every physical Gaussian aperture there is exactly one
positive height where the forced composite window vanishes.  It lies strictly between the two
source-derived turning heights. -/
theorem existsUnique_thetaCuspGaussianApertureCompositeWindow_pos_zero
    {lambda : ℝ} (hlambda : lambda ≤ 0) :
    ∃! t : ℝ,
      t ∈ Ioo (thetaCuspGaussianApertureWindowLowerTurningHeight lambda)
          (thetaCuspGaussianApertureWindowUpperTurningHeight lambda) ∧
        thetaCuspGaussianApertureCompositeWindow lambda t = 0 := by
  let L := thetaCuspGaussianApertureWindowLowerTurningHeight lambda
  let U := thetaCuspGaussianApertureWindowUpperTurningHeight lambda
  have hLU : L ≤ U :=
    (thetaCuspGaussianApertureWindowLowerTurningHeight_lt_upper hlambda).le
  have hcont : ContinuousOn (thetaCuspGaussianApertureCompositeWindow lambda) (Icc L U) := by
    intro t ht
    exact (hasDerivAt_thetaCuspGaussianApertureCompositeWindow lambda t).continuousAt.continuousWithinAt
  have hzeroMem : (0 : ℝ) ∈ Icc
      (thetaCuspGaussianApertureCompositeWindow lambda U)
      (thetaCuspGaussianApertureCompositeWindow lambda L) := by
    exact ⟨(thetaCuspGaussianApertureCompositeWindow_upperTurningHeight_neg hlambda).le,
      (thetaCuspGaussianApertureCompositeWindow_lowerTurningHeight_pos hlambda).le⟩
  rcases intermediate_value_Icc' hLU hcont hzeroMem with ⟨t, htIcc, htZero⟩
  have htL : L < t := lt_of_le_of_ne htIcc.1 (by
    intro heq
    subst t
    exact (thetaCuspGaussianApertureCompositeWindow_lowerTurningHeight_pos hlambda).ne'
      htZero)
  have htU : t < U := lt_of_le_of_ne htIcc.2 (by
    intro heq
    subst t
    exact (thetaCuspGaussianApertureCompositeWindow_upperTurningHeight_neg hlambda).ne
      htZero)
  refine ⟨t, ⟨⟨htL, htU⟩, htZero⟩, ?_⟩
  intro u hu
  have hanti := thetaCuspGaussianApertureCompositeWindow_strictAntiOn_middle hlambda
  exact (hanti.injOn htIcc ⟨hu.1.1.le, hu.1.2.le⟩
    (htZero.trans hu.2.symm)).symm

theorem thetaCuspGaussianApertureCompositeWindow_pos_of_pos_le_lowerTurningHeight
    {lambda t : ℝ} (hlambda : lambda ≤ 0) (ht : 0 < t)
    (htLower : t ≤ thetaCuspGaussianApertureWindowLowerTurningHeight lambda) :
    0 < thetaCuspGaussianApertureCompositeWindow lambda t := by
  have hL := thetaCuspGaussianApertureWindowLowerTurningHeight_pos hlambda
  have hrise := thetaCuspGaussianApertureCompositeWindow_strictMonoOn_initial hlambda
    (show 0 ∈ Icc (0 : ℝ) (thetaCuspGaussianApertureWindowLowerTurningHeight lambda) by
      exact ⟨le_rfl, hL.le⟩)
    (show t ∈ Icc (0 : ℝ) (thetaCuspGaussianApertureWindowLowerTurningHeight lambda) by
      exact ⟨ht.le, htLower⟩) ht
  rwa [thetaCuspGaussianApertureCompositeWindow_zero] at hrise

theorem thetaCuspGaussianApertureCompositeWindow_neg_of_upperTurningHeight_le
    {lambda t : ℝ} (hlambda : lambda ≤ 0)
    (hUpper : thetaCuspGaussianApertureWindowUpperTurningHeight lambda ≤ t) :
    thetaCuspGaussianApertureCompositeWindow lambda t < 0 := by
  let U := thetaCuspGaussianApertureWindowUpperTurningHeight lambda
  let v := t + 1
  have htv : t < v := by dsimp [v]; linarith
  have htail := thetaCuspGaussianApertureCompositeWindow_strictMonoOn_tail hlambda
  have hrise : thetaCuspGaussianApertureCompositeWindow lambda t <
      thetaCuspGaussianApertureCompositeWindow lambda v :=
    htail (show t ∈ Ici U by exact hUpper)
      (show v ∈ Ici U by exact le_trans hUpper htv.le) htv
  have hvNonpos : thetaCuspGaussianApertureCompositeWindow lambda v ≤ 0 := by
    exact ge_of_tendsto
      (tendsto_thetaCuspGaussianApertureCompositeWindow_atTop hlambda) (by
        filter_upwards [eventually_ge_atTop v] with x hx
        exact htail.monotoneOn (show v ∈ Ici U by exact le_trans hUpper htv.le)
          (show x ∈ Ici U by exact le_trans (le_trans hUpper htv.le) hx) hx)
  exact lt_of_lt_of_le hrise hvNonpos

/-- Global form of the one-crossing law: the literal forced window has exactly one positive
zero, and the turning-height theorem locates it inside the falling phase. -/
theorem existsUnique_pos_thetaCuspGaussianApertureCompositeWindow_eq_zero
    {lambda : ℝ} (hlambda : lambda ≤ 0) :
    ∃! t : ℝ, 0 < t ∧ thetaCuspGaussianApertureCompositeWindow lambda t = 0 := by
  rcases existsUnique_thetaCuspGaussianApertureCompositeWindow_pos_zero hlambda with
    ⟨t, ht, htUnique⟩
  have hLpos := thetaCuspGaussianApertureWindowLowerTurningHeight_pos hlambda
  refine ⟨t, ⟨lt_trans hLpos ht.1.1, ht.2⟩, ?_⟩
  intro u hu
  by_cases huLower : u ≤ thetaCuspGaussianApertureWindowLowerTurningHeight lambda
  · have hupos :=
      thetaCuspGaussianApertureCompositeWindow_pos_of_pos_le_lowerTurningHeight
        hlambda hu.1 huLower
    exact False.elim (hupos.ne' hu.2)
  by_cases hUpper : thetaCuspGaussianApertureWindowUpperTurningHeight lambda ≤ u
  · have huneg :=
      thetaCuspGaussianApertureCompositeWindow_neg_of_upperTurningHeight_le
        hlambda hUpper
    exact False.elim (huneg.ne hu.2)
  · exact htUnique u ⟨⟨lt_of_not_ge huLower, lt_of_not_ge hUpper⟩, hu.2⟩

end

end RHTower
