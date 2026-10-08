import GaloisForLFunctions.RHTower.WeilWorkQuantizationGaussianEnergy

/-!
# Pole centering preserves the actual phase defect

Zeta has exact critical reflection and the literal pole residue is real.
Subtracting their product leaves the reflection defect unchanged, including
at source zeros. The signed centered square therefore measures the gap
between twice the centered physical energy and the actual canonical phase cost.
-/

open Complex Set Filter MeasureTheory Topology
open scoped ComplexConjugate
noncomputable section
namespace RHTower.WeilWorkSettledPhase
open WeilSpectral
variable {lam : ℕ → ℝ}

private theorem centered_unitary_square {u z : ℂ} (hu : ‖u‖ = 1) :
    ‖u * z - conj z‖ ^ 2 = 2 * ‖z‖ ^ 2 - 2 * (u * z ^ 2).re := by
  have hh := Complex.normSq_sub (u * z) (conj z)
  simp only [Complex.normSq_eq_norm_sq, norm_mul, hu, one_mul,
    Complex.norm_conj, starRingEnd_self_apply] at hh
  rw [show u * z * z = u * z ^ 2 by ring] at hh
  linarith

private theorem critical_zeta_reflection (t : ℝ) :
    zetaChi (1 - tracePoint 0 t) * riemannZeta (tracePoint 0 t) =
      conj (riemannZeta (tracePoint 0 t)) := by
  have hs : 1 - tracePoint 0 t = conj (tracePoint 0 t) := by
    apply Complex.ext <;> norm_num [tracePoint]
  have hzero : 1 - tracePoint 0 t ≠ (0 : ℂ) := by
    intro h; have := congrArg Complex.re h; norm_num [tracePoint] at this
  have hone : 1 - tracePoint 0 t ≠ (1 : ℂ) := by
    intro h; have := congrArg Complex.re h; norm_num [tracePoint] at this
  have h := zeta_eq_zetaChi_mul hzero hone
    (show Gammaℝ (1 - (1 - tracePoint 0 t)) ≠ 0 by
      rw [sub_sub_cancel]
      exact Gammaℝ_ne_zero_of_re_pos (by norm_num [tracePoint]))
  rw [sub_sub_cancel] at h
  calc
    _ = riemannZeta (1 - tracePoint 0 t) := h.symm
    _ = _ := by rw [hs, riemannZeta_conj]

/-- Removing the actual real polar zeta term does not change the skew reflection. -/
theorem centeredTrace_reflection_defect (hW : WeilPositiveFull lam) (t : ℝ) :
    zetaChi (1 - tracePoint 0 t) * quantizationCenteredTrace hW t -
        conj (quantizationCenteredTrace hW t) =
      zetaChi (1 - tracePoint 0 t) * quantizationTraceF hW t -
        conj (quantizationTraceF hW t) := by
  have hb := sourceCompletion_conj hW (s := 1) (by norm_num)
  simp only [map_one] at hb
  simp only [quantizationCenteredTrace, map_sub, map_mul, ← hb]
  have hz := critical_zeta_reflection t
  linear_combination -sourceCompletion hW 1 * hz

/-- Zero-safe pointwise physical law, with no functional equation assumed for the source. -/
theorem centeredTrace_phase_energy_ae (hW : WeilPositiveFull lam) :
    ∀ᵐ t : ℝ, 0 < t →
      ‖canonicalPhase hW t - 1‖ ^ 2 * ‖quantizationTraceF hW t‖ ^ 2 =
        2 * ‖quantizationCenteredTrace hW t‖ ^ 2 -
          2 * (zetaChi (1 - tracePoint 0 t) * quantizationCenteredTrace hW t ^ 2).re := by
  filter_upwards [quantizationTraceF_phase_ae hW] with t ht
  intro hpos
  have he : zetaChi (1 - tracePoint 0 t) * quantizationCenteredTrace hW t -
      conj (quantizationCenteredTrace hW t) =
      (canonicalPhase hW t - 1) * conj (quantizationTraceF hW t) := by
    rw [centeredTrace_reflection_defect, ht hpos]
    ring
  have hh := centered_unitary_square (z := quantizationCenteredTrace hW t)
    (zetaChi_norm_on_line (s := 1 - tracePoint 0 t) (by norm_num [tracePoint]))
  rw [he, norm_mul, Complex.norm_conj, mul_pow] at hh
  exact hh

def centeredGaussianSignedTrace (hW : WeilPositiveFull lam) (T t : ℝ) : ℂ :=
  zetaChi (1 - tracePoint 0 t) * quantizationCenteredTrace hW t ^ 2 *
    (quantizationGaussianWeight T t : ℂ)

theorem integrable_centeredGaussianSignedTrace (hW : WeilPositiveFull lam)
    {T : ℝ} (hT : 0 < T) : Integrable (centeredGaussianSignedTrace hW T) := by
  have hchi : Continuous (fun t : ℝ => zetaChi (1 - tracePoint 0 t)) := by
    rw [continuous_iff_continuousAt]
    intro t
    have hG : Gammaℝ (1 - (1 - tracePoint 0 t)) ≠ 0 := by
      rw [sub_sub_cancel]
      exact Gammaℝ_ne_zero_of_re_pos (by norm_num [tracePoint])
    have ht : ContinuousAt (fun t : ℝ => 1 - tracePoint 0 t) t := by
      unfold tracePoint
      fun_prop
    exact (zetaChi_analyticAt hG).continuousAt.comp (f := fun t : ℝ => 1 - tracePoint 0 t) ht
  have hg : Measurable (quantizationGaussianWeight T) := by
    unfold quantizationGaussianWeight
    fun_prop
  refine (integrable_quantizationCenteredTrace_gaussian_square hW hT).mono' ?_
    (Eventually.of_forall fun t => ?_)
  · exact ((hchi.measurable.mul ((measurable_quantizationCenteredTrace hW).pow_const 2)).mul
      hg.complex_ofReal).aestronglyMeasurable
  · simp only [centeredGaussianSignedTrace, norm_mul, norm_pow, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (show 0 < quantizationGaussianWeight T t from Real.exp_pos _),
      zetaChi_norm_on_line (s := 1 - tracePoint 0 t) (by norm_num [tracePoint]), one_mul, le_refl]

theorem centeredGaussianSignedTrace_neg (hW : WeilPositiveFull lam) (T t : ℝ) :
    centeredGaussianSignedTrace hW T (-t) = conj (centeredGaussianSignedTrace hW T t) := by
  have he : 1 - tracePoint 0 (-t) = conj (1 - tracePoint 0 t) := by
    rw [map_sub, map_one, tracePoint_conj]
  simp only [centeredGaussianSignedTrace, he, zetaChi_conj,
    quantizationCenteredTrace_neg, map_mul, map_pow, Complex.conj_ofReal,
    quantizationGaussianWeight, neg_sq]

/-- Exact equality; estimating the signed integral remains a separate analytic step. -/
theorem centeredGaussian_signed_energy (hW : WeilPositiveFull lam)
    {T : ℝ} (hT : 0 < T) :
    (∫ t : ℝ, centeredGaussianSignedTrace hW T t).re =
      2 * quantizationCenteredGaussianEnergy hW T - quantizationGaussianDefect hW T := by
  have hJ := integrable_centeredGaussianSignedTrace hW hT
  have hhalf : (∫ t : ℝ, centeredGaussianSignedTrace hW T t).re =
      2 * ∫ t in Ioi (0 : ℝ), (centeredGaussianSignedTrace hW T t).re := by
    have hir : (∫ t : ℝ, centeredGaussianSignedTrace hW T t).re =
        ∫ t : ℝ, (centeredGaussianSignedTrace hW T t).re := (integral_re hJ).symm
    rw [hir]
    have heven : (fun t : ℝ => (centeredGaussianSignedTrace hW T t).re) =
        fun t => (centeredGaussianSignedTrace hW T |t|).re := by
      funext t
      rcases le_total 0 t with ht | ht
      · rw [abs_of_nonneg ht]
      · rw [abs_of_nonpos ht, centeredGaussianSignedTrace_neg, Complex.conj_re]
    rw [heven, integral_comp_abs (f := fun t => (centeredGaussianSignedTrace hW T t).re)]
    congr 1
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    change (centeredGaussianSignedTrace hW T t).re = (centeredGaussianSignedTrace hW T |t|).re
    rw [abs_of_pos (show 0 < t from ht)]
  rw [hhalf]
  have hpoint : ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))),
      2 * (centeredGaussianSignedTrace hW T t).re =
        2 * (‖quantizationCenteredTrace hW t‖ ^ 2 * quantizationGaussianWeight T t) -
        ‖canonicalPhase hW t - 1‖ ^ 2 *
          (‖quantizationTraceF hW t‖ ^ 2 * quantizationGaussianWeight T t) := by
    filter_upwards [ae_restrict_of_ae (centeredTrace_phase_energy_ae hW),
      ae_restrict_mem measurableSet_Ioi] with t hp ht
    have hh := hp ht
    simp only [Complex.mul_re] at hh
    simp only [centeredGaussianSignedTrace, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    linear_combination quantizationGaussianWeight T t * hh
  rw [← integral_const_mul, integral_congr_ae hpoint,
    integral_sub ((integrable_quantizationCenteredTrace_gaussian_square hW hT).const_mul 2).integrableOn
      (integrable_quantizationTraceF_gaussian_defect hW hT).integrableOn,
    integral_const_mul]
  rfl

end RHTower.WeilWorkSettledPhase
