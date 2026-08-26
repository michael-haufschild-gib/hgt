import GaloisForLFunctions.HTGeometry.BoundedZeroFreeLogHerglotz
import GaloisForLFunctions.HTGeometry.BoundedInvertibleWeakPhase
import GaloisForLFunctions.HTGeometry.AnalyticCircleMean
import GaloisForLFunctions.HTGeometry.HausdorffCDDPhaseKernel
import GaloisForLFunctions.HTGeometry.MakarovPoltoratskiWeakPhaseBigO
import GaloisForLFunctions.HTGeometry.PoissonBoundaryPositivity
import GaloisForLFunctions.HTGeometry.SchurOneSubOuter
import GaloisForLFunctions.HTGeometry.DiskSmirnovAnalyticValue
import GaloisForLFunctions.HTGeometry.SzegoLowerBoundGeneral
import GaloisForLFunctions.RHTower.XiShiftedHardEdgeComplexCayleyGeometry

/-!
# Weak type `(1,1)` for conjugate Herglotz transforms

Davis's positive harmonic majorant gives a direct, quantitative Kolmogorov estimate for every
probability-measure Herglotz transform on the disk.  No absolute continuity of the representing
measure is needed.  The exact radial estimate is

`m {ζ : |Im H_μ(rζ)| > A} ≤ 4 / (π A)`.

This is the singular-measure-safe phase bound needed by canonical inner--outer factorization.
-/

open Complex Filter Metric MeasureTheory Set Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

def davisRatio (A : ℝ) (w : ℂ) : ℂ :=
  (w - (A : ℂ) * I) / (w + (A : ℂ) * I)

def davisWeakTypeAnalytic (A : ℝ) (w : ℂ) : ℂ :=
  1 + (-I / (Real.pi : ℂ)) * Complex.log (davisRatio A w)

theorem davisRatio_im {A : ℝ} (w : ℂ) :
    (davisRatio A w).im =
      (-2 * A * w.re) / Complex.normSq (w + (A : ℂ) * I) := by
  rw [davisRatio, Complex.div_im]
  simp only [Complex.sub_re, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, I_re,
    Complex.ofReal_im, I_im, mul_zero, sub_zero, Complex.add_re,
    add_zero, Complex.sub_im, mul_one, Complex.add_im]
  ring

theorem davisRatio_im_neg {A : ℝ} (hA : 0 < A) {w : ℂ} (hw : 0 < w.re) :
    (davisRatio A w).im < 0 := by
  rw [davisRatio_im]
  have hden : 0 < Complex.normSq (w + (A : ℂ) * I) := by
    rw [Complex.normSq_pos]
    intro hzero
    have hre := congrArg Complex.re hzero
    simp at hre
    linarith
  exact div_neg_of_neg_of_pos (by nlinarith) hden

theorem davisRatio_mem_slitPlane {A : ℝ} (hA : 0 < A) {w : ℂ} (hw : 0 < w.re) :
    davisRatio A w ∈ Complex.slitPlane := by
  exact Or.inr (ne_of_lt (davisRatio_im_neg hA hw))

theorem differentiableAt_davisWeakTypeAnalytic {A : ℝ} (hA : 0 < A)
    {w : ℂ} (hw : 0 < w.re) :
    DifferentiableAt ℂ (davisWeakTypeAnalytic A) w := by
  unfold davisWeakTypeAnalytic davisRatio
  have hplus : w + (A : ℂ) * I ≠ 0 := by
    intro hzero
    have hre := congrArg Complex.re hzero
    simp at hre
    linarith
  have hratio : DifferentiableAt ℂ
      (fun z : ℂ => (z - (A : ℂ) * I) / (z + (A : ℂ) * I)) w := by
    fun_prop (disch := exact hplus)
  exact (differentiableAt_const (c := (1 : ℂ))).add
    ((differentiableAt_const (c := (-I / (Real.pi : ℂ)))).mul
      ((Complex.differentiableAt_log (davisRatio_mem_slitPlane hA hw)).comp w hratio))

theorem davisWeakTypeAnalytic_re (A : ℝ) (w : ℂ) :
    (davisWeakTypeAnalytic A w).re =
      1 + (davisRatio A w).arg / Real.pi := by
  rw [davisWeakTypeAnalytic, Complex.add_re, Complex.mul_re, Complex.div_re,
    Complex.log_im]
  norm_num [Complex.normSq_ofReal]
  field_simp [Real.pi_ne_zero]

theorem davisRatio_re {A : ℝ} (w : ℂ) :
    (davisRatio A w).re =
      (Complex.normSq w - A ^ 2) / Complex.normSq (w + (A : ℂ) * I) := by
  rw [davisRatio, Complex.div_re]
  simp only [Complex.sub_re, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, I_re,
    Complex.ofReal_im, I_im, mul_zero, sub_zero, Complex.add_re,
    add_zero, Complex.sub_im, mul_one, Complex.add_im, Complex.normSq_apply]
  ring

theorem davisWeakTypeAnalytic_re_nonneg (A : ℝ) (w : ℂ) :
    0 ≤ (davisWeakTypeAnalytic A w).re := by
  rw [davisWeakTypeAnalytic_re]
  have harg := Complex.neg_pi_lt_arg (davisRatio A w)
  have hpi := Real.pi_pos
  rw [show 1 + (davisRatio A w).arg / Real.pi =
      (Real.pi + (davisRatio A w).arg) / Real.pi by
        field_simp [Real.pi_ne_zero]]
  exact div_nonneg (by linarith) hpi.le

theorem davisWeakTypeAnalytic_re_le_one {A : ℝ} (hA : 0 < A)
    {w : ℂ} (hw : 0 < w.re) :
    (davisWeakTypeAnalytic A w).re ≤ 1 := by
  rw [davisWeakTypeAnalytic_re]
  have harg : (davisRatio A w).arg < 0 :=
    Complex.arg_neg_iff.mpr (davisRatio_im_neg hA hw)
  have hpi := Real.pi_pos
  have : (davisRatio A w).arg / Real.pi < 0 := div_neg_of_neg_of_pos harg hpi
  linarith

theorem one_half_lt_davisWeakTypeAnalytic_re_of_norm_gt
    {A : ℝ} (hA : 0 < A) {w : ℂ} (hwre : 0 < w.re)
    (hwA : A < ‖w‖) :
    (1 / 2 : ℝ) < (davisWeakTypeAnalytic A w).re := by
  have hqre : 0 < (davisRatio A w).re := by
    rw [davisRatio_re]
    have hnum : 0 < Complex.normSq w - A ^ 2 := by
      rw [Complex.normSq_eq_norm_sq]
      nlinarith [norm_nonneg w]
    have hden : 0 < Complex.normSq (w + (A : ℂ) * I) := by
      rw [Complex.normSq_pos]
      intro hzero
      have hre := congrArg Complex.re hzero
      simp at hre
      linarith
    exact div_pos hnum hden
  have hargAbs : |(davisRatio A w).arg| < Real.pi / 2 :=
    Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hqre)
  have hargNeg : (davisRatio A w).arg < 0 :=
    Complex.arg_neg_iff.mpr (davisRatio_im_neg hA hwre)
  have hargLower : -Real.pi / 2 < (davisRatio A w).arg := by
    rw [abs_lt] at hargAbs
    linarith [hargAbs.1]
  rw [davisWeakTypeAnalytic_re]
  have hpi := Real.pi_pos
  have hdiv : -(1 / 2 : ℝ) < (davisRatio A w).arg / Real.pi := by
    rw [lt_div_iff₀ hpi]
    nlinarith
  linarith

theorem davisRatio_one_arg (A : ℝ) :
    (davisRatio A 1).arg = -2 * Real.arctan A := by
  let u : ℂ := 1 - (A : ℂ) * I
  let v : ℂ := 1 + (A : ℂ) * I
  have hu : 0 < u.re := by simp [u, Complex.mul_re]
  have hv : 0 < v.re := by simp [v, Complex.mul_re]
  rw [show davisRatio A 1 = u / v by rfl,
    RHTower.complex_arg_div_eq_sub_of_re_pos hu hv,
    complexArg_eq_arctan_of_re_pos hu,
    complexArg_eq_arctan_of_re_pos hv]
  simp [u, v, Complex.mul_re, Complex.mul_im, Real.arctan_neg]
  ring

theorem davisWeakTypeAnalytic_one_re_le {A : ℝ} (hA : 0 < A) :
    (davisWeakTypeAnalytic A 1).re ≤ 2 / (Real.pi * A) := by
  rw [davisWeakTypeAnalytic_re, davisRatio_one_arg A]
  have hInv : 0 ≤ A⁻¹ := (inv_pos.mpr hA).le
  have hatan := arctan_le_self hInv
  have hidentity := Real.arctan_inv_of_pos hA
  rw [hidentity] at hatan
  have hpi := Real.pi_pos
  have hmul : (2 / Real.pi) * Real.arctan A ≥
      (2 / Real.pi) * (Real.pi / 2 - A⁻¹) := by
    gcongr
    linarith
  field_simp [Real.pi_ne_zero, hA.ne'] at hmul ⊢
  nlinarith

theorem circleMeasureHerglotz_re_pos
    (μ : ProbabilityMeasure Circle) {w : ℂ} (hw : ‖w‖ < 1) :
    0 < (circleMeasureHerglotz μ w).re := by
  rw [circleMeasureHerglotz_re μ hw]
  let f : Circle → ℝ := fun ζ => _root_.poissonKernel 0 w (ζ : ℂ)
  have hwball : w ∈ ball (0 : ℂ) 1 := by
    simpa [Metric.mem_ball, dist_zero_right] using hw
  have hfpos : ∀ ζ, 0 < f ζ := by
    intro ζ
    apply poissonKernel_pos (R := 1)
    · simp
    · exact hwball
  have hfcont : Continuous f := continuous_poissonKernel_circle hwball
  have hfint : Integrable f (μ : Measure Circle) :=
    hfcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  apply (integral_pos_iff_support_of_nonneg (fun ζ => (hfpos ζ).le) hfint).2
  have hsupp : Function.support f = Set.univ := by
    ext ζ
    simp only [Function.mem_support, Set.mem_univ, iff_true]
    exact (hfpos ζ).ne'
  rw [hsupp]
  simp

/-- Davis's positive harmonic majorant composed with a circle Herglotz transform. -/
def circleHerglotzDavisTransform
    (μ : ProbabilityMeasure Circle) (A : ℝ) (z : ℂ) : ℂ :=
  davisWeakTypeAnalytic A (circleMeasureHerglotz μ z)

theorem analyticOnNhd_circleHerglotzDavisTransform
    (μ : ProbabilityMeasure Circle) {A : ℝ} (hA : 0 < A) :
    AnalyticOnNhd ℂ (circleHerglotzDavisTransform μ A) (ball (0 : ℂ) 1) := by
  have hdiff : DifferentiableOn ℂ (circleHerglotzDavisTransform μ A)
      (ball (0 : ℂ) 1) := by
    intro z hz
    change DifferentiableWithinAt ℂ
      (fun x : ℂ => davisWeakTypeAnalytic A (circleMeasureHerglotz μ x))
      (ball (0 : ℂ) 1) z
    have hzNorm : ‖z‖ < 1 := by
      simpa [Metric.mem_ball, dist_zero_right] using hz
    have hinner : DifferentiableAt ℂ (circleMeasureHerglotz μ) z :=
      (differentiableOn_circleMeasureHerglotz μ).differentiableAt
        (isOpen_ball.mem_nhds hz)
    exact ((differentiableAt_davisWeakTypeAnalytic hA
      (circleMeasureHerglotz_re_pos μ hzNorm)).comp z hinner).differentiableWithinAt
  exact hdiff.analyticOnNhd isOpen_ball

theorem circleAverage_circleHerglotzDavisTransform_re
    (μ : ProbabilityMeasure Circle) {A r : ℝ} (hA : 0 < A)
    (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ∫ ζ : Circle,
        (circleHerglotzDavisTransform μ A ((r : ℂ) * (ζ : ℂ))).re
          ∂circleLebesgue =
      (circleHerglotzDavisTransform μ A 0).re := by
  let q : ℂ → ℂ := circleHerglotzDavisTransform μ A
  change (∫ ζ : Circle, (q ((r : ℂ) * (ζ : ℂ))).re ∂circleLebesgue) =
    (q 0).re
  have hqAna : AnalyticOnNhd ℂ q (ball (0 : ℂ) 1) :=
    analyticOnNhd_circleHerglotzDavisTransform μ hA
  have harg : ∀ ζ : Circle, (r : ℂ) * (ζ : ℂ) ∈ ball (0 : ℂ) 1 := by
    intro ζ
    rw [Metric.mem_ball, dist_zero_right, norm_mul, norm_real, Real.norm_eq_abs,
      abs_of_nonneg hr0, Circle.norm_coe, mul_one]
    exact hr1
  have hqCont : Continuous fun ζ : Circle => q ((r : ℂ) * (ζ : ℂ)) :=
    hqAna.continuousOn.comp_continuous
      (continuous_const.mul continuous_subtype_val) harg
  rw [integral_circleLebesgue_eq_circleAverage
    (fun w : ℂ => (q ((r : ℂ) * w)).re)
    (Complex.continuous_re.comp hqCont).aestronglyMeasurable]
  rw [Real.circleAverage]
  have hqCircle : Continuous fun θ : ℝ => q (circleMap 0 r θ) :=
    hqAna.continuousOn.comp_continuous (continuous_circleMap 0 r) (fun θ => by
      rw [Metric.mem_ball, dist_zero_right, norm_circleMap_zero,
        abs_of_nonneg hr0]
      exact hr1)
  have hqIoc : Integrable (fun θ : ℝ => q (circleMap 0 r θ))
      (volume.restrict (Set.Ioc 0 (2 * Real.pi))) := by
    change IntegrableOn (fun θ : ℝ => q (circleMap 0 r θ))
      (Set.Ioc 0 (2 * Real.pi)) volume
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le (by positivity)).mp
      (hqCircle.intervalIntegrable _ _)
  have hmean := integral_circleMap_eq_center_of_analyticOnNhd_unitBall
    hqAna hr0 hr1
  rw [show (fun θ : ℝ =>
      (q ((r : ℂ) * circleMap 0 1 θ)).re) =
      fun θ : ℝ => (q (circleMap 0 r θ)).re by
        funext θ
        congr 2
        simp [circleMap]]
  rw [intervalIntegral.integral_of_le (by positivity)]
  rw [show ∫ θ in Set.Ioc (0 : ℝ) (2 * Real.pi),
      (q (circleMap 0 r θ)).re =
      (∫ θ in Set.Ioc (0 : ℝ) (2 * Real.pi),
        q (circleMap 0 r θ)).re by exact integral_re hqIoc]
  rw [← intervalIntegral.integral_of_le (by positivity)]
  rw [hmean]
  norm_num [Complex.mul_re, smul_eq_mul]
  field_simp [Real.pi_ne_zero]

theorem circleMeasureHerglotz_im_radial_weakType
    (μ : ProbabilityMeasure Circle) {A r : ℝ}
    (hA : 0 < A) (hr0 : 0 ≤ r) (hr1 : r < 1) :
    circleLebesgue.real {ζ : Circle |
        A < |(circleMeasureHerglotz μ ((r : ℂ) * (ζ : ℂ))).im|} ≤
      4 / (Real.pi * A) := by
  let F : Circle → ℂ := fun ζ =>
    circleMeasureHerglotz μ ((r : ℂ) * (ζ : ℂ))
  let g : Circle → ℝ := fun ζ => (davisWeakTypeAnalytic A (F ζ)).re
  have harg : ∀ ζ : Circle, ‖(r : ℂ) * (ζ : ℂ)‖ < 1 := by
    intro ζ
    rw [norm_mul, norm_real, Real.norm_eq_abs, abs_of_nonneg hr0,
      Circle.norm_coe, mul_one]
    exact hr1
  have hFre : ∀ ζ, 0 < (F ζ).re := fun ζ =>
    circleMeasureHerglotz_re_pos μ (harg ζ)
  have hgcont : Continuous g := by
    unfold g F
    have hinner : Continuous (fun ζ : Circle => (r : ℂ) * (ζ : ℂ)) :=
      continuous_const.mul continuous_subtype_val
    exact Complex.continuous_re.comp
      ((analyticOnNhd_circleHerglotzDavisTransform μ hA).continuousOn.comp_continuous
        hinner (fun ζ => by
          simpa [Metric.mem_ball, dist_zero_right] using harg ζ))
  have hg0 : ∀ ζ, 0 ≤ g ζ := fun ζ =>
    davisWeakTypeAnalytic_re_nonneg A (F ζ)
  have hg1 : ∀ ζ, g ζ ≤ 1 := fun ζ =>
    davisWeakTypeAnalytic_re_le_one hA (hFre ζ)
  have hgInt : Integrable g circleLebesgue :=
    hgcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hmark := MeasureTheory.mul_meas_ge_le_integral_of_nonneg
    (μ := circleLebesgue) (f := g)
    (Filter.Eventually.of_forall (Pi.le_def.mpr hg0)) hgInt (1 / 2 : ℝ)
  have hmean : (∫ ζ : Circle, g ζ ∂circleLebesgue) =
      (davisWeakTypeAnalytic A 1).re := by
    simpa [g, F, circleHerglotzDavisTransform] using
      circleAverage_circleHerglotzDavisTransform_re μ hA hr0 hr1
  have hsuper : circleLebesgue.real {ζ : Circle | (1 / 2 : ℝ) ≤ g ζ} ≤
      4 / (Real.pi * A) := by
    have hcenter := davisWeakTypeAnalytic_one_re_le hA
    rw [hmean] at hmark
    calc
      circleLebesgue.real {ζ : Circle | (1 / 2 : ℝ) ≤ g ζ} ≤
          2 * (davisWeakTypeAnalytic A 1).re := by
        nlinarith
      _ ≤ 2 * (2 / (Real.pi * A)) :=
        mul_le_mul_of_nonneg_left hcenter (by positivity)
      _ = 4 / (Real.pi * A) := by ring
  have hsubset : {ζ : Circle | A < |(F ζ).im|} ⊆
      {ζ : Circle | (1 / 2 : ℝ) ≤ g ζ} := by
    intro ζ hζ
    have hnorm : A < ‖F ζ‖ := lt_of_lt_of_le hζ (Complex.abs_im_le_norm (F ζ))
    exact (one_half_lt_davisWeakTypeAnalytic_re_of_norm_gt hA (hFre ζ) hnorm).le
  calc
    circleLebesgue.real {ζ : Circle |
        A < |(circleMeasureHerglotz μ ((r : ℂ) * (ζ : ℂ))).im|} =
        circleLebesgue.real {ζ : Circle | A < |(F ζ).im|} := by rfl
    _ ≤ circleLebesgue.real {ζ : Circle | (1 / 2 : ℝ) ≤ g ζ} := by
      exact ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hsubset)
    _ ≤ 4 / (Real.pi * A) := hsuper

/-- Schur transform of a probability-measure Herglotz transform. -/
def circleMeasureHerglotzSchur (μ : ProbabilityMeasure Circle) : DiskMultiplier where
  fn := fun z => (circleMeasureHerglotz μ z - 1) /
    (circleMeasureHerglotz μ z + 1)
  diff := by
    intro z hz
    have hzNorm : ‖z‖ < 1 := by
      simpa [Metric.mem_ball, dist_zero_right] using hz
    have hden : circleMeasureHerglotz μ z + 1 ≠ 0 := by
      intro hzero
      have hre := congrArg Complex.re hzero
      simp at hre
      linarith [circleMeasureHerglotz_re_pos μ hzNorm]
    exact ((differentiableOn_circleMeasureHerglotz μ z hz).sub
      (differentiableAt_const (c := (1 : ℂ))).differentiableWithinAt).div
        ((differentiableOn_circleMeasureHerglotz μ z hz).add
          (differentiableAt_const (c := (1 : ℂ))).differentiableWithinAt) hden
  bd := 1
  bd_nonneg := zero_le_one
  bd_le := by
    intro z hz
    have hzNorm : ‖z‖ < 1 := by
      simpa [Metric.mem_ball, dist_zero_right] using hz
    let w := circleMeasureHerglotz μ z
    have hw : 0 ≤ w.re := (circleMeasureHerglotz_re_pos μ hzNorm).le
    have hden : w + 1 ≠ 0 := by
      intro hzero
      have hre := congrArg Complex.re hzero
      simp at hre
      linarith
    change ‖(w - 1) / (w + 1)‖ ≤ 1
    rw [norm_div, div_le_one (norm_pos_iff.mpr hden)]
    have hsq : ‖w - 1‖ ^ 2 ≤ ‖w + 1‖ ^ 2 := by
      rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply,
        Complex.normSq_apply]
      simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im,
        sub_zero, Complex.add_re, Complex.add_im, add_zero]
      nlinarith
    nlinarith [norm_nonneg (w - 1), norm_nonneg (w + 1)]

@[simp] theorem circleMeasureHerglotzSchur_zero
    (μ : ProbabilityMeasure Circle) : (circleMeasureHerglotzSchur μ).fn 0 = 0 := by
  simp [circleMeasureHerglotzSchur]

theorem norm_circleMeasureHerglotzSchur_le_one
    (μ : ProbabilityMeasure Circle) (z : ℂ) (hz : z ∈ ball (0 : ℂ) 1) :
    ‖(circleMeasureHerglotzSchur μ).fn z‖ ≤ 1 :=
  (circleMeasureHerglotzSchur μ).bd_le z hz

/-- Smirnov quotient whose analytic value is the Herglotz transform. -/
def circleMeasureHerglotzSmirnovBoundary
    (μ : ProbabilityMeasure Circle) : DiskSmirnovBoundary where
  numerator := (DiskMultiplier.const 1).add (circleMeasureHerglotzSchur μ)
  denominator := (DiskMultiplier.const 1).sub (circleMeasureHerglotzSchur μ)
  denominator_outer := isOuterDiskMultiplier_one_sub_of_schur
    (circleMeasureHerglotzSchur μ)
    (norm_circleMeasureHerglotzSchur_le_one μ)
    ⟨0, by simp, by simp⟩

theorem circleMeasureHerglotzSmirnovBoundary_value
    (μ : ProbabilityMeasure Circle) (z : ℂ) (hz : ‖z‖ < 1) :
    (circleMeasureHerglotzSmirnovBoundary μ).value z =
      circleMeasureHerglotz μ z := by
  let H := circleMeasureHerglotz μ z
  have hden : H + 1 ≠ 0 := by
    intro hzero
    have hre := congrArg Complex.re hzero
    simp at hre
    linarith [circleMeasureHerglotz_re_pos μ hz]
  change (1 + (H - 1) / (H + 1)) / (1 - (H - 1) / (H + 1)) = H
  field_simp
  ring

theorem circleMeasureHerglotzSmirnovBoundary_radialBoundaryFun
    (μ : ProbabilityMeasure Circle) (n : ℕ) (ζ : Circle) :
    (circleMeasureHerglotzSmirnovBoundary μ).radialBoundaryFun n ζ =
      circleMeasureHerglotz μ
        ((hardyDiskAbelRadius n : ℂ) * (ζ : ℂ)) := by
  rw [DiskSmirnovBoundary.radialBoundaryFun]
  change (1 + (circleMeasureHerglotzSchur μ).fn
      ((hardyDiskAbelRadius n : ℂ) * (ζ : ℂ))) /
    (1 - (circleMeasureHerglotzSchur μ).fn
      ((hardyDiskAbelRadius n : ℂ) * (ζ : ℂ))) = _
  exact circleMeasureHerglotzSmirnovBoundary_value μ _
    (by
      rw [norm_mul, norm_real, Real.norm_eq_abs,
        abs_of_nonneg (hardyDiskAbelRadius_nonneg n), Circle.norm_coe, mul_one]
      exact hardyDiskAbelRadius_lt_one n)

/-- A.e. boundary value supplied by the exact Smirnov quotient model of the Herglotz transform. -/
def circleMeasureHerglotzBoundaryValue
    (μ : ProbabilityMeasure Circle) (ζ : Circle) : ℂ :=
  diskMultiplierBoundaryMeasurableRep
      (circleMeasureHerglotzSmirnovBoundary μ).numerator ζ /
    diskMultiplierBoundaryMeasurableRep
      (circleMeasureHerglotzSmirnovBoundary μ).denominator ζ

theorem measurable_circleMeasureHerglotzBoundaryValue
    (μ : ProbabilityMeasure Circle) :
    Measurable (circleMeasureHerglotzBoundaryValue μ) :=
  (measurable_diskMultiplierBoundaryMeasurableRep
      (circleMeasureHerglotzSmirnovBoundary μ).numerator).div
    (measurable_diskMultiplierBoundaryMeasurableRep
      (circleMeasureHerglotzSmirnovBoundary μ).denominator)

/-- Boundary conjugate Herglotz transform. -/
def circleMeasureHerglotzBoundaryIm
    (μ : ProbabilityMeasure Circle) (ζ : Circle) : ℝ :=
  (circleMeasureHerglotzBoundaryValue μ ζ).im

theorem exists_circleMeasureHerglotz_radial_subseq_ae
    (μ : ProbabilityMeasure Circle) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧
      ∀ᵐ ζ : Circle ∂circleLebesgue,
        Tendsto (fun i => circleMeasureHerglotz μ
          ((hardyDiskAbelRadius (ns i) : ℂ) * (ζ : ℂ))) atTop
          (𝓝 (circleMeasureHerglotzBoundaryValue μ ζ)) := by
  obtain ⟨ns, hns, hconv⟩ :=
    (circleMeasureHerglotzSmirnovBoundary μ).exists_radialBoundary_subseq_ae
  refine ⟨ns, hns, ?_⟩
  filter_upwards [hconv,
    diskMultiplierBoundaryMeasurableRep_ae
      (circleMeasureHerglotzSmirnovBoundary μ).numerator,
    diskMultiplierBoundaryMeasurableRep_ae
      (circleMeasureHerglotzSmirnovBoundary μ).denominator] with ζ hζ hnum hden
  simpa only [circleMeasureHerglotzSmirnovBoundary_radialBoundaryFun,
    circleMeasureHerglotzBoundaryValue, hnum, hden] using hζ

/-- Kolmogorov weak-type bound for the genuine boundary conjugate of a probability Herglotz
transform.  The factor two versus the radial bound comes only from passing a strict level through
an a.e. limit. -/
theorem circleMeasureHerglotzBoundaryIm_weakType
    (μ : ProbabilityMeasure Circle) {A : ℝ} (hA : 0 < A) :
    circleLebesgue.real {ζ : Circle |
        A < |circleMeasureHerglotzBoundaryIm μ ζ|} ≤
      8 / (Real.pi * A) := by
  obtain ⟨ns, hns, hconv⟩ := exists_circleMeasureHerglotz_radial_subseq_ae μ
  let f : ℕ → Circle → ℝ := fun i ζ =>
    (circleMeasureHerglotz μ
      ((hardyDiskAbelRadius (ns i) : ℂ) * (ζ : ℂ))).im
  let h : Circle → ℝ := circleMeasureHerglotzBoundaryIm μ
  let E : Set Circle := {ζ | A < |h ζ|}
  let Ehalf : ℕ → Set Circle := fun i => {ζ | A / 2 < |f i ζ|}
  let B : ℕ → Set Circle := fun N => {ζ | ∀ n, N ≤ n → ζ ∈ Ehalf n}
  have hBmono : Monotone B := by
    intro N M hNM ζ hζ n hn
    exact hζ n (hNM.trans hn)
  have hEae : E ≤ᵐ[circleLebesgue] ⋃ N, B N := by
    filter_upwards [hconv] with ζ hζ hzE
    have him : Tendsto (fun i => f i ζ) atTop (𝓝 (h ζ)) := by
      exact (Complex.continuous_im.tendsto _).comp hζ
    have habs : Tendsto (fun i => |f i ζ|) atTop (𝓝 |h ζ|) :=
      (continuous_abs.tendsto _).comp him
    have hhalf : A / 2 < |h ζ| := by
      have : A / 2 < A := by linarith
      exact this.trans hzE
    have hev : ∀ᶠ i in atTop, A / 2 < |f i ζ| :=
      habs (Ioi_mem_nhds hhalf)
    obtain ⟨N, hN⟩ := eventually_atTop.1 hev
    exact Set.mem_iUnion.2 ⟨N, fun n hn => hN n hn⟩
  let C : ℝ := 8 / (Real.pi * A)
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  have hEhalfReal (i : ℕ) : circleLebesgue.real (Ehalf i) ≤ C := by
    have hradial := circleMeasureHerglotz_im_radial_weakType μ
      (A := A / 2) (r := hardyDiskAbelRadius (ns i))
      (by linarith) (hardyDiskAbelRadius_nonneg _) (hardyDiskAbelRadius_lt_one _)
    have hconst : 4 / (Real.pi * (A / 2)) = C := by
      dsimp [C]
      field_simp [Real.pi_ne_zero, hA.ne']
      ring
    rw [hconst] at hradial
    simpa [Ehalf, f] using hradial
  have hBmeasure (N : ℕ) : circleLebesgue (B N) ≤ ENNReal.ofReal C := by
    have hsubset : B N ⊆ Ehalf N := fun ζ hζ => hζ N le_rfl
    have hreal : circleLebesgue.real (B N) ≤ C :=
      (ENNReal.toReal_mono (measure_ne_top _ _)
        (measure_mono hsubset)).trans (hEhalfReal N)
    rw [Measure.real_def] at hreal
    exact (ENNReal.toReal_le_toReal (measure_ne_top _ _) (by simp)).mp (by
      simpa [ENNReal.toReal_ofReal hC] using hreal)
  have hunion : circleLebesgue (⋃ N, B N) ≤ ENNReal.ofReal C := by
    apply le_of_tendsto (MeasureTheory.tendsto_measure_iUnion_atTop hBmono)
    exact Filter.Eventually.of_forall hBmeasure
  have hmeasure : circleLebesgue E ≤ ENNReal.ofReal C :=
    (MeasureTheory.measure_mono_ae hEae).trans hunion
  have hreal := ENNReal.toReal_mono (by simp : ENNReal.ofReal C ≠ ⊤) hmeasure
  rw [Measure.real_def]
  simpa [E, h, C, ENNReal.toReal_ofReal hC] using hreal

/-- Real-line Cayley pullback of the boundary conjugate Herglotz transform. -/
def circleMeasureHerglotzBoundaryLineIm
    (μ : ProbabilityMeasure Circle) (x : ℝ) : ℝ :=
  circleMeasureHerglotzBoundaryIm μ (circleCayley x)

theorem poissonWeakL1BigO_circleMeasureHerglotzBoundaryLineIm
    (μ : ProbabilityMeasure Circle) :
    PoissonWeakL1BigO (circleMeasureHerglotzBoundaryLineIm μ) := by
  refine ⟨8 / Real.pi, ?_⟩
  filter_upwards [eventually_gt_atTop 0] with A hA
  let s : Set Circle := {ζ | A < |circleMeasureHerglotzBoundaryIm μ ζ|}
  have hs : MeasurableSet s := by
    exact measurableSet_lt measurable_const
      ((Complex.measurable_im.comp
        (measurable_circleMeasureHerglotzBoundaryValue μ)).abs)
  have hmap := circleCayley_measurePreserving.measure_preimage hs.nullMeasurableSet
  have hmeasure :
      (ProbabilityTheory.cauchyMeasure 0 1
        {x | A < |circleMeasureHerglotzBoundaryLineIm μ x|}).toReal =
      circleLebesgue.real s := by
    rw [Measure.real_def]
    apply congrArg ENNReal.toReal
    simpa [s, circleMeasureHerglotzBoundaryLineIm] using hmap
  rw [hmeasure]
  have hweak := circleMeasureHerglotzBoundaryIm_weakType μ hA
  have hmul := mul_le_mul_of_nonneg_left hweak hA.le
  calc
    A * circleLebesgue.real s ≤ A * (8 / (Real.pi * A)) := hmul
    _ = 8 / Real.pi := by field_simp [Real.pi_ne_zero, hA.ne']

/-- Constant functions have finite weak-`L¹` tails. -/
theorem PoissonWeakL1BigO.const (c : ℝ) :
    PoissonWeakL1BigO (fun _x : ℝ => c) :=
  (poissonWeakL1LittleO_of_abs_le (C := |c|) (fun _ => le_rfl)).bigO

/-- Finite weak-`L¹` tails are preserved by scalar multiplication. -/
theorem PoissonWeakL1BigO.const_mul {f : ℝ → ℝ}
    (hf : PoissonWeakL1BigO f) (c : ℝ) :
    PoissonWeakL1BigO (fun x => c * f x) := by
  rcases eq_or_ne c 0 with rfl | hc
  · simpa using PoissonWeakL1BigO.const 0
  obtain ⟨C, hC⟩ := hf
  refine ⟨|c| * C, ?_⟩
  have hcabs : 0 < |c| := abs_pos.mpr hc
  have hscale : Tendsto (fun A : ℝ => A / |c|) atTop atTop :=
    by
      simpa [div_eq_mul_inv, mul_comm] using
        tendsto_id.const_mul_atTop (inv_pos.mpr hcabs)
  filter_upwards [hscale.eventually hC] with A hA
  have hset : {x : ℝ | A < |c * f x|} = {x | A / |c| < |f x|} := by
    ext x
    simp only [Set.mem_setOf_eq, abs_mul]
    constructor
    · intro h
      rw [div_lt_iff₀ hcabs]
      simpa [mul_comm] using h
    · intro h
      rw [div_lt_iff₀ hcabs] at h
      simpa [mul_comm] using h
  rw [hset]
  calc
    A * (ProbabilityTheory.cauchyMeasure 0 1
        {x | A / |c| < |f x|}).toReal =
        |c| * ((A / |c|) *
          (ProbabilityTheory.cauchyMeasure 0 1
            {x | A / |c| < |f x|}).toReal) := by
          field_simp [hcabs.ne']
    _ ≤ |c| * C := mul_le_mul_of_nonneg_left hA (abs_nonneg c)

/-- Chosen Herglotz measure representing a bounded zero-free logarithm. -/
noncomputable def BoundedZeroFreeLog.herglotzMeasure
    {φ : DiskMultiplier} (L : BoundedZeroFreeLog φ) : ProbabilityMeasure Circle :=
  Classical.choose L.exists_herglotzMeasure_complex

theorem BoundedZeroFreeLog.caratheodoryFn_eq_circleMeasureHerglotz
    {φ : DiskMultiplier} (L : BoundedZeroFreeLog φ)
    {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) :
    L.caratheodoryFn z = circleMeasureHerglotz L.herglotzMeasure z :=
  Classical.choose_spec L.exists_herglotzMeasure_complex z hz

/-- Actual real-line phase of a bounded zero-free multiplier, including singular inner mass. -/
def BoundedZeroFreeLog.boundaryLinePhase
    {φ : DiskMultiplier} (L : BoundedZeroFreeLog φ) (x : ℝ) : ℝ :=
  (φ.fn 0).arg - L.scale *
    circleMeasureHerglotzBoundaryLineIm L.herglotzMeasure x

theorem BoundedZeroFreeLog.boundary_exp_ae
    {φ : DiskMultiplier} (L : BoundedZeroFreeLog φ) :
    diskMultiplierBoundaryFun φ =ᵐ[circleLebesgue] fun ζ =>
      φ.fn 0 * Complex.exp ((L.scale : ℂ) *
        (1 - circleMeasureHerglotzBoundaryValue L.herglotzMeasure ζ)) := by
  let μ := L.herglotzMeasure
  obtain ⟨base, hbase, hH⟩ := exists_circleMeasureHerglotz_radial_subseq_ae μ
  obtain ⟨ns, hns, hφ⟩ :=
    exists_diskMultiplierRadialBoundary_subseq_ae_of_strictMono φ hbase
  filter_upwards [hH, hφ] with ζ hHζ hφζ
  have hHsub : Tendsto (fun i => circleMeasureHerglotz μ
      ((hardyDiskAbelRadius (base (ns i)) : ℂ) * (ζ : ℂ))) atTop
      (𝓝 (circleMeasureHerglotzBoundaryValue μ ζ)) :=
    hHζ.comp hns.tendsto_atTop
  have htarget : Tendsto (fun i =>
      φ.fn 0 * Complex.exp ((L.scale : ℂ) *
        (1 - circleMeasureHerglotz μ
          ((hardyDiskAbelRadius (base (ns i)) : ℂ) * (ζ : ℂ))))) atTop
      (𝓝 (φ.fn 0 * Complex.exp ((L.scale : ℂ) *
        (1 - circleMeasureHerglotzBoundaryValue μ ζ)))) := by
    exact tendsto_const_nhds.mul
      (((tendsto_const_nhds.sub hHsub).const_mul (L.scale : ℂ)).cexp)
  have hradialEq : ∀ i,
      diskMultiplierRadialBoundaryFun (base (ns i)) φ ζ =
        φ.fn 0 * Complex.exp ((L.scale : ℂ) *
          (1 - circleMeasureHerglotz μ
            ((hardyDiskAbelRadius (base (ns i)) : ℂ) * (ζ : ℂ)))) := by
    intro i
    let z : ℂ := (hardyDiskAbelRadius (base (ns i)) : ℂ) * (ζ : ℂ)
    have hzNorm : ‖z‖ < 1 := by
      dsimp [z]
      rw [norm_mul, norm_real, Real.norm_eq_abs,
        abs_of_nonneg (hardyDiskAbelRadius_nonneg _), Circle.norm_coe, mul_one]
      exact hardyDiskAbelRadius_lt_one _
    have hz : z ∈ ball (0 : ℂ) 1 := by
      simpa [Metric.mem_ball, dist_zero_right] using hzNorm
    rw [diskMultiplierRadialBoundaryFun, L.exp_eq z hz,
      L.fn_eq_scale_mul_one_sub_caratheodoryFn,
      L.caratheodoryFn_eq_circleMeasureHerglotz hz]
  have htarget' := htarget.congr' (Filter.Eventually.of_forall fun i => (hradialEq i).symm)
  exact tendsto_nhds_unique hφζ htarget'

theorem BoundedZeroFreeLog.lineBoundary_exp_ae
    {φ : DiskMultiplier} (L : BoundedZeroFreeLog φ) :
    diskMultiplierLineBoundary φ =ᵐ[volume] fun x =>
      φ.fn 0 * Complex.exp ((L.scale : ℂ) *
        (1 - circleMeasureHerglotzBoundaryValue L.herglotzMeasure
          (circleCayley x))) := by
  have hcircle := L.boundary_exp_ae
  have hweighted := hcircle.comp_tendsto
    circleCayley_weighted_measurePreserving.quasiMeasurePreserving.tendsto_ae
  have hvolume := (withDensity_realDensity_ae_eq measurable_standardCauchyWeight
    standardCauchyWeight_pos).mp hweighted
  filter_upwards [diskMultiplierLineBoundary_ae φ, hvolume] with x hline hx
  rw [hline]
  simpa only [Function.comp_apply] using hx

theorem BoundedZeroFreeLog.phaseReflection_eq_exp_ae
    {φ : DiskMultiplier} (L : BoundedZeroFreeLog φ) :
    diskMultiplierPhaseReflectionSymbol φ =ᵐ[volume] fun x =>
      Complex.exp (-2 * I * ((L.boundaryLinePhase x : ℝ) : ℂ)) := by
  filter_upwards [L.lineBoundary_exp_ae] with x hx
  let w : ℂ := (L.scale : ℂ) *
    (1 - circleMeasureHerglotzBoundaryValue L.herglotzMeasure (circleCayley x))
  have hne : diskMultiplierLineBoundary φ x ≠ 0 := by
    rw [hx]
    exact mul_ne_zero L.center_ne_zero (Complex.exp_ne_zero _)
  rw [diskMultiplierPhaseReflectionSymbol, if_neg hne, hx]
  have hphase : (φ.fn 0).arg + w.im = L.boundaryLinePhase x := by
    unfold BoundedZeroFreeLog.boundaryLinePhase
    dsimp [w, circleMeasureHerglotzBoundaryLineIm,
      circleMeasureHerglotzBoundaryIm]
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
      add_zero, Complex.sub_im, Complex.one_im]
    ring
  rw [← hphase]
  exact conj_mul_exp_div_self_eq_exp_phase L.center_ne_zero

/-- Boundary phase of every bounded zero-free multiplier has finite weak-`L¹` Poisson tails. -/
theorem BoundedZeroFreeLog.boundaryLinePhase_weakL1BigO
    {φ : DiskMultiplier} (L : BoundedZeroFreeLog φ) :
    PoissonWeakL1BigO L.boundaryLinePhase := by
  have hH := poissonWeakL1BigO_circleMeasureHerglotzBoundaryLineIm
    L.herglotzMeasure
  have hscaled := hH.const_mul (-L.scale)
  have hconst := PoissonWeakL1BigO.const (φ.fn 0).arg
  apply (hconst.add hscaled).congr
  exact Filter.Eventually.of_forall fun x => by
    simp [BoundedZeroFreeLog.boundaryLinePhase]
    ring

end

end GaloisForLFunctions.HTGeometry
