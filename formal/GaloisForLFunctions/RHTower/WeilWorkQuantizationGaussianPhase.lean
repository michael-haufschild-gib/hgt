import GaloisForLFunctions.RHTower.WeilWorkSettledPhaseCanonicalDisorder
import GaloisForLFunctions.RHTower.WeilWorkQuantizationSubpolynomial
import GaloisForLFunctions.RHTower.ZetaCarrier
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral

/-!
# Actual Gaussian phase energy of a full-positive source

The actual decompleted radial trace has a zero-safe phase identity with the
canonical positive-height phase. Source subpolynomial bounds pay absolute
convergence at every positive Gaussian scale. Negative heights are conjugated
explicitly, yielding the whole complex moment `2M - D`.

The decomposition retains the full physical trace and its phase-defect energy.
It does not supply an asymptotic estimate or spectral quantization.
-/

open Complex Set Filter MeasureTheory
open scoped Topology ComplexConjugate
noncomputable section
namespace RHTower.WeilSpectral
open WeilWorkSettledPhase
variable {lam : ℕ → ℝ}

private theorem linePoint_conj (y : ℝ) :
    conj (tracePoint 0 y) = tracePoint 0 (-y) := by
  simp only [tracePoint, add_zero, map_add, map_mul, Complex.conj_ofReal, Complex.conj_I, Complex.ofReal_neg]
  ring

private theorem linePoint_one_sub (y : ℝ) :
    1 - tracePoint 0 y = conj (tracePoint 0 y) := by
  apply Complex.ext <;> norm_num [tracePoint]

private theorem quantizationTraceF_eq_lineFactor (hW : WeilPositiveFull lam) (y : ℝ) :
    quantizationTraceF hW y = quantizationCompletedTrace hW y / lineFactor (tracePoint 0 y) := by
  simp [quantizationTraceF, lineFactor, tracePoint]

/-- The actual decompleted radial trace respects conjugation, including its zeros. -/
theorem quantizationTraceF_neg (hW : WeilPositiveFull lam) (y : ℝ) :
    quantizationTraceF hW (-y) = conj (quantizationTraceF hW y) := by
  rw [quantizationTraceF_eq_lineFactor, quantizationTraceF_eq_lineFactor]
  rw [quantizationCompletedTrace_neg, ← linePoint_conj, lineFactor_conj, map_div₀]

private theorem linePoint_factor_ne_zero (y : ℝ) :
    lineFactor (tracePoint 0 y) ≠ 0 := by
  apply lineFactor_ne_zero
  · norm_num [tracePoint]
  · intro h; have := congrArg Complex.re h; norm_num [tracePoint] at this
  · intro h; have := congrArg Complex.re h; norm_num [tracePoint] at this

private theorem chi_line_factor (y : ℝ) :
    zetaChi (1 - tracePoint 0 y) =
      lineFactor (tracePoint 0 y) / conj (lineFactor (tracePoint 0 y)) := by
  let s := tracePoint 0 y
  have hG : Gammaℝ s ≠ 0 := Gammaℝ_ne_zero_of_re_pos (by norm_num [s, tracePoint])
  have hcG : conj (Gammaℝ s) ≠ 0 := (map_ne_zero (starRingEnd ℂ)).2 hG
  have hp : s * (s - 1) ≠ 0 := (mul_ne_zero_iff.mp (linePoint_factor_ne_zero y)).1
  have hpoly : conj (s * (s - 1)) = s * (s - 1) := by
    rw [map_mul, map_sub, map_one, ← linePoint_one_sub]
    ring
  change zetaChi (1 - s) = lineFactor s / conj (lineFactor s)
  unfold zetaChi lineFactor
  rw [sub_sub_cancel, linePoint_one_sub, Gammaℝ_conj, map_mul, hpoly]
  field_simp
  change conj (Gammaℝ s) / conj (Gammaℝ s) = (s * (s - 1)) / (s * (s - 1))
  rw [div_self hcG, div_self hp]

/-- The completed radial reflection identifies the actual critical-line phase. -/
theorem quantizationTraceF_phase_ae (hW : WeilPositiveFull lam) :
    ∀ᵐ y : ℝ, 0 < y →
      zetaChi (1 - tracePoint 0 y) * quantizationTraceF hW y =
        canonicalPhase hW y * conj (quantizationTraceF hW y) := by
  have hneg := (Measure.quasiMeasurePreserving_smul volume (by norm_num : (-1 : ℝ) ≠ 0)).ae
    (quantizationCompletedTrace_ae_eq_sourceTrace hW)
  simp only [smul_eq_mul, neg_one_mul] at hneg
  filter_upwards [quantizationCompletedTrace_ae_eq_sourceTrace hW, hneg] with y hp hn
  intro hy
  have hG : quantizationCompletedTrace hW y =
      canonicalPhase hW y * conj (quantizationCompletedTrace hW y) := by
    rw [← quantizationCompletedTrace_neg, hp, hn]
    exact sourceTrace_reflection hW hy
  rw [chi_line_factor, quantizationTraceF_eq_lineFactor]
  change (lineFactor (tracePoint 0 y) / conj (lineFactor (tracePoint 0 y))) *
      (quantizationCompletedTrace hW y / lineFactor (tracePoint 0 y)) =
    canonicalPhase hW y * conj (quantizationCompletedTrace hW y / lineFactor (tracePoint 0 y))
  rw [map_div₀]
  calc
    _ = quantizationCompletedTrace hW y / conj (lineFactor (tracePoint 0 y)) := by
      field_simp [linePoint_factor_ne_zero y]
    _ = _ := by
      conv_lhs => rw [hG]
      ring

/-- No division by the actual trace is needed to obtain its signed phase energy. -/
theorem quantizationTraceF_square_phase_ae (hW : WeilPositiveFull lam) :
    ∀ᵐ y : ℝ, 0 < y →
      zetaChi (1 - tracePoint 0 y) * quantizationTraceF hW y ^ 2 =
        canonicalPhase hW y * (‖quantizationTraceF hW y‖ ^ 2 : ℝ) := by
  filter_upwards [quantizationTraceF_phase_ae hW] with y hy
  intro hpos
  calc
    _ = (zetaChi (1 - tracePoint 0 y) * quantizationTraceF hW y) *
        quantizationTraceF hW y := by ring
    _ = canonicalPhase hW y *
        (quantizationTraceF hW y * conj (quantizationTraceF hW y)) := by rw [hy hpos]; ring
    _ = _ := by rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]


/-- Gaussian at physical height scale `T`; the source boundary is not Gamma damped. -/
def quantizationGaussianWeight (T y : ℝ) : ℝ := Real.exp (-(1 / T ^ 2) * y ^ 2)

private theorem gaussianWeight_pos (T y : ℝ) : 0 < quantizationGaussianWeight T y :=
  Real.exp_pos _

private theorem gaussianWeight_measurable (T : ℝ) : Measurable (quantizationGaussianWeight T) := by
  unfold quantizationGaussianWeight
  fun_prop

/-- Actual critical trace energy is integrable against every positive-scale Gaussian. -/
theorem integrable_quantizationTraceF_gaussian_square (hW : WeilPositiveFull lam)
    {T : ℝ} (hT : 0 < T) :
    Integrable (fun y : ℝ => ‖quantizationTraceF hW y‖ ^ 2 * quantizationGaussianWeight T y) := by
  obtain ⟨C, hC, hF⟩ := exists_quantizationTraceF_subpolynomial hW (p := 1) (by norm_num)
  simp only [Real.rpow_one] at hF
  have hg := integrable_exp_neg_mul_sq (by positivity : 0 < 1 / T ^ 2)
  have hg2 : Integrable (fun y : ℝ => y ^ 2 * quantizationGaussianWeight T y) := by
    simpa only [Real.rpow_two, quantizationGaussianWeight] using
      (integrable_rpow_mul_exp_neg_mul_sq (b := 1 / T ^ 2)
        (by positivity) (s := 2) (by norm_num))
  have hmajor : Integrable (fun y : ℝ =>
      2 * C ^ 2 * (quantizationGaussianWeight T y + y ^ 2 * quantizationGaussianWeight T y)) :=
    (hg.add hg2).const_mul _
  refine hmajor.mono' ?_ (Eventually.of_forall fun y => ?_)
  · exact (((measurable_quantizationTraceF hW).norm.pow_const 2).mul
      (gaussianWeight_measurable T)).aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (gaussianWeight_pos T y).le)]
    have hsq : ‖quantizationTraceF hW y‖ ^ 2 ≤ (C * (1 + |y|)) ^ 2 := by
      nlinarith [hF y, norm_nonneg (quantizationTraceF hW y)]
    have hp : (1 + |y|) ^ 2 ≤ 2 * (1 + y ^ 2) := by nlinarith [sq_abs y, sq_nonneg (|y| - 1)]
    have hbound : ‖quantizationTraceF hW y‖ ^ 2 ≤ 2 * C ^ 2 * (1 + y ^ 2) := by
      nlinarith [mul_le_mul_of_nonneg_left hp (sq_nonneg C)]
    have := mul_le_mul_of_nonneg_right hbound (gaussianWeight_pos T y).le
    nlinarith

/-- Exact unit-circle defect, at the canonical phase rather than an arbitrary lock. -/
theorem quantization_phase_gap_square (hW : WeilPositiveFull lam) (y : ℝ) :
    ‖canonicalPhase hW y - 1‖ ^ 2 = 2 - 2 * (canonicalPhase hW y).re := by
  have h := Complex.normSq_sub (canonicalPhase hW y) 1
  norm_num [Complex.normSq_eq_norm_sq, norm_canonicalPhase] at h
  exact h

/-- Actual phase-defect energy is integrable; no settlement estimate is assumed. -/
theorem integrable_quantizationTraceF_gaussian_defect (hW : WeilPositiveFull lam)
    {T : ℝ} (hT : 0 < T) :
    Integrable (fun y : ℝ => ‖canonicalPhase hW y - 1‖ ^ 2 *
      (‖quantizationTraceF hW y‖ ^ 2 * quantizationGaussianWeight T y)) := by
  refine (integrable_quantizationTraceF_gaussian_square hW hT).bdd_mul (c := 4) ?_
    (Eventually.of_forall fun y => ?_)
  · exact ((measurable_canonicalPhase hW).sub measurable_const).norm.pow_const 2 |>.aestronglyMeasurable
  · have hb : ‖canonicalPhase hW y - 1‖ ≤ 2 := by
      have hb := norm_sub_le (canonicalPhase hW y) 1
      norm_num [norm_canonicalPhase] at hb
      exact hb
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact show ‖canonicalPhase hW y - 1‖ ^ 2 ≤ 4 by
      nlinarith [norm_nonneg (canonicalPhase hW y - 1)]

/-- Positive physical energy on the actual critical trace. -/
def quantizationGaussianEnergy (hW : WeilPositiveFull lam) (T : ℝ) : ℝ :=
  ∫ y in Ioi (0 : ℝ), ‖quantizationTraceF hW y‖ ^ 2 * quantizationGaussianWeight T y

/-- Physical cost of failure of the canonical phase to equal one. -/
def quantizationGaussianDefect (hW : WeilPositiveFull lam) (T : ℝ) : ℝ :=
  ∫ y in Ioi (0 : ℝ), ‖canonicalPhase hW y - 1‖ ^ 2 *
    (‖quantizationTraceF hW y‖ ^ 2 * quantizationGaussianWeight T y)

/-- The actual signed second moment, retaining the universal Gamma-ratio phase. -/
def quantizationGaussianSignedIntegrand (hW : WeilPositiveFull lam) (T y : ℝ) : ℂ :=
  zetaChi (1 - tracePoint 0 y) * quantizationTraceF hW y ^ 2 * quantizationGaussianWeight T y

private theorem continuous_lineFactor_tracePoint :
    Continuous (fun y : ℝ => lineFactor (tracePoint 0 y)) := by
  rw [continuous_iff_continuousAt]
  intro y
  have h0 : tracePoint 0 y ≠ 0 := by
    intro h; have := congrArg Complex.re h; norm_num [tracePoint] at this
  have h1 : tracePoint 0 y ≠ 1 := by
    intro h; have := congrArg Complex.re h; norm_num [tracePoint] at this
  exact (hasDerivAt_lineFactor (by norm_num [tracePoint]) h0 h1).continuousAt.comp
    (by unfold tracePoint; fun_prop)

/-- Absolute convergence of the signed critical moment is supplied by the source bounds. -/
theorem integrable_quantizationGaussianSignedIntegrand (hW : WeilPositiveFull lam)
    {T : ℝ} (hT : 0 < T) : Integrable (quantizationGaussianSignedIntegrand hW T) := by
  refine (integrable_quantizationTraceF_gaussian_square hW hT).mono' ?_
    (Eventually.of_forall fun y => ?_)
  · have hchi : Measurable (fun y : ℝ => zetaChi (1 - tracePoint 0 y)) := by
      simp_rw [chi_line_factor]
      exact continuous_lineFactor_tracePoint.measurable.div
        (Complex.continuous_conj.comp continuous_lineFactor_tracePoint).measurable
    exact ((hchi.mul ((measurable_quantizationTraceF hW).pow_const 2)).mul
      ((gaussianWeight_measurable T).complex_ofReal)).aestronglyMeasurable
  · simp only [quantizationGaussianSignedIntegrand, norm_mul, norm_pow,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos (gaussianWeight_pos T y)]
    rw [zetaChi_norm_on_line (by norm_num [tracePoint])]
    simp

/-- Negative heights are conjugate; the canonical phase is not extended by its definition. -/
theorem quantizationGaussianSignedIntegrand_neg (hW : WeilPositiveFull lam) (T y : ℝ) :
    quantizationGaussianSignedIntegrand hW T (-y) =
      conj (quantizationGaussianSignedIntegrand hW T y) := by
  have he : 1 - tracePoint 0 (-y) = conj (1 - tracePoint 0 y) := by
    rw [← linePoint_conj, map_sub, map_one]
  simp only [quantizationGaussianSignedIntegrand, he, zetaChi_conj,
    quantizationTraceF_neg, map_mul, map_pow, Complex.conj_ofReal,
    quantizationGaussianWeight, neg_sq]

/-- Exact physical decomposition; its asymptotic evaluation is a separate obligation. -/
theorem quantizationGaussian_signed_energy (hW : WeilPositiveFull lam)
    {T : ℝ} (hT : 0 < T) :
    (∫ y : ℝ, quantizationGaussianSignedIntegrand hW T y).re =
      2 * quantizationGaussianEnergy hW T - quantizationGaussianDefect hW T := by
  have hJ := integrable_quantizationGaussianSignedIntegrand hW hT
  have hhalf : (∫ y : ℝ, quantizationGaussianSignedIntegrand hW T y).re =
      2 * ∫ y in Ioi (0 : ℝ), (quantizationGaussianSignedIntegrand hW T y).re := by
    have hir : (∫ y : ℝ, quantizationGaussianSignedIntegrand hW T y).re =
        ∫ y : ℝ, (quantizationGaussianSignedIntegrand hW T y).re := (integral_re hJ).symm
    rw [hir]
    have heven : (fun y : ℝ => (quantizationGaussianSignedIntegrand hW T y).re) =
        fun y => (quantizationGaussianSignedIntegrand hW T |y|).re := by
      funext y
      rcases le_total 0 y with hy | hy
      · rw [abs_of_nonneg hy]
      · rw [abs_of_nonpos hy, quantizationGaussianSignedIntegrand_neg, Complex.conj_re]
    rw [heven, integral_comp_abs (f := fun y => (quantizationGaussianSignedIntegrand hW T y).re)]
    congr 1
    apply setIntegral_congr_fun measurableSet_Ioi
    intro y hy
    change (quantizationGaussianSignedIntegrand hW T y).re =
      (quantizationGaussianSignedIntegrand hW T |y|).re
    rw [abs_of_pos (show 0 < y from hy)]
  rw [hhalf]
  have hpoint : ∀ᵐ y ∂(volume.restrict (Ioi (0 : ℝ))),
      2 * (quantizationGaussianSignedIntegrand hW T y).re =
        2 * (‖quantizationTraceF hW y‖ ^ 2 * quantizationGaussianWeight T y) -
        ‖canonicalPhase hW y - 1‖ ^ 2 *
          (‖quantizationTraceF hW y‖ ^ 2 * quantizationGaussianWeight T y) := by
    filter_upwards [ae_restrict_of_ae (quantizationTraceF_square_phase_ae hW),
      ae_restrict_mem measurableSet_Ioi] with y hp hy
    simp only [quantizationGaussianSignedIntegrand, hp hy, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, quantization_phase_gap_square]
    ring
  rw [← integral_const_mul, integral_congr_ae hpoint,
    integral_sub ((integrable_quantizationTraceF_gaussian_square hW hT).const_mul 2).integrableOn
      (integrable_quantizationTraceF_gaussian_defect hW hT).integrableOn,
    integral_const_mul]
  rfl

/-- The whole complex moment is real and equals the physical energy minus its phase cost. -/
theorem quantizationGaussian_signed_energy_complex (hW : WeilPositiveFull lam)
    {T : ℝ} (hT : 0 < T) :
    (∫ y : ℝ, quantizationGaussianSignedIntegrand hW T y) =
      ((2 * quantizationGaussianEnergy hW T - quantizationGaussianDefect hW T : ℝ) : ℂ) := by
  have hc : conj (∫ y : ℝ, quantizationGaussianSignedIntegrand hW T y) =
      ∫ y : ℝ, quantizationGaussianSignedIntegrand hW T y := by
    calc
      _ = ∫ y : ℝ, conj (quantizationGaussianSignedIntegrand hW T y) := integral_conj.symm
      _ = ∫ y : ℝ, quantizationGaussianSignedIntegrand hW T (-y) := by
        apply integral_congr_ae
        exact Eventually.of_forall fun y => (quantizationGaussianSignedIntegrand_neg hW T y).symm
      _ = _ := integral_neg_eq_self _ _
  apply Complex.ext
  · exact quantizationGaussian_signed_energy hW hT
  · have hi := congrArg Complex.im hc
    simp only [Complex.conj_im] at hi
    simp only [Complex.ofReal_im]
    linarith

end RHTower.WeilSpectral
