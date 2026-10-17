import GaloisForLFunctions.HTGeometry.BurnolDepthCompletion
import GaloisForLFunctions.HTGeometry.BochnerLaplaceHolomorphy
import GaloisForLFunctions.HTGeometry.MonomialLaplaceComplex

/-! Literal complex Burnol features, their cubic Gram, and holomorphic Laplace coordinates. -/

noncomputable section
open MeasureTheory Set Filter Complex
open scoped ENNReal InnerProductSpace ComplexConjugate

namespace GaloisForLFunctions.HTGeometry
open _root_.HTGeometry

/-- Complex-rate Burnol feature on the literal time half-line. -/
def burnolComplexFeatureFun (z : ℂ) (t : ℝ) : ℂ := (t : ℂ) * expRay z t

theorem norm_burnolComplexFeatureFun (z : ℂ) (t : ℝ) :
    ‖burnolComplexFeatureFun z t‖ = ‖burnolDepthFeature z.re 0 t‖ := by
  simp only [burnolComplexFeatureFun, norm_mul, norm_expRay, burnolDepthFeature,
    Nat.cast_zero, zero_add, one_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _)]

theorem memLp_burnolComplexFeatureFun {z : ℂ} (hz : 0 < z.re) :
    MemLp (burnolComplexFeatureFun z) 2 (volume.restrict (Ioi 0)) := by
  refine (memLp_burnolDepthFeature hz 0).of_le
    ((show Continuous (burnolComplexFeatureFun z) by
      unfold burnolComplexFeatureFun expRay; fun_prop).aestronglyMeasurable.restrict) ?_
  filter_upwards with t
  exact (norm_burnolComplexFeatureFun z t).le

def burnolComplexFeature (z : ℂ) (hz : 0 < z.re) : BurnolHalfLineL2 :=
  (memLp_burnolComplexFeatureFun hz).toLp (burnolComplexFeatureFun z)

theorem burnolComplexFeature_ae (z : ℂ) (hz : 0 < z.re) :
    (burnolComplexFeature z hz : ℝ → ℂ) =ᵐ[volume.restrict (Ioi 0)]
      burnolComplexFeatureFun z := (memLp_burnolComplexFeatureFun hz).coeFn_toLp

theorem inner_burnolComplexFeature {w z : ℂ} (hw : 0 < w.re) (hz : 0 < z.re) :
    inner ℂ (burnolComplexFeature w hw) (burnolComplexFeature z hz) =
      2 / (z + conj w) ^ 3 := by
  rw [L2.inner_def]
  have heq : (fun t : ℝ => inner ℂ (burnolComplexFeature w hw t)
      (burnolComplexFeature z hz t)) =ᵐ[volume.restrict (Ioi 0)]
        fun t => (t : ℂ) ^ 2 * Complex.exp (-((z + conj w) * t)) := by
    filter_upwards [burnolComplexFeature_ae w hw, burnolComplexFeature_ae z hz] with t hw' hz'
    rw [hw', hz', RCLike.inner_apply]
    simp only [burnolComplexFeatureFun, expRay, map_mul, Complex.conj_ofReal]
    rw [← Complex.exp_conj]
    simp only [map_neg, map_mul, Complex.conj_ofReal]
    rw [show (t : ℂ) * Complex.exp (-(z * t)) *
        ((t : ℂ) * Complex.exp (-(conj w * t))) =
        (t : ℂ)^2 * (Complex.exp (-(z*t)) * Complex.exp (-(conj w*t))) by ring,
      ← Complex.exp_add]
    congr 2
    ring
  rw [integral_congr_ae heq]
  have hrate : 0 < (z + conj w).re := by simp only [Complex.add_re, Complex.conj_re]; linarith
  simpa using integral_Ioi_pow_mul_cexp hrate 2

theorem burnolComplexFeature_ne_zero {z : ℂ} (hz : 0 < z.re) :
    burnolComplexFeature z hz ≠ 0 := by
  intro h
  have hi := inner_burnolComplexFeature hz hz
  rw [h, inner_zero_left] at hi
  have hden : z + conj z ≠ 0 := by
    intro he
    have := congrArg Complex.re he
    simp only [Complex.add_re, Complex.conj_re, Complex.zero_re] at this
    linarith
  exact (div_ne_zero (by norm_num) (pow_ne_zero _ hden)) hi.symm

theorem burnolComplexFeature_ofReal {x : ℝ} (hx : 0 < x) :
    burnolComplexFeature (x : ℂ) hx = burnolDepthFeatureL2 ⟨x, hx⟩ 0 := by
  refine Lp.ext ?_
  filter_upwards [burnolComplexFeature_ae (x : ℂ) hx, burnolDepthFeatureL2_ae ⟨x,hx⟩ 0]
    with t h1 h2
  rw [h1, h2]
  simp [burnolComplexFeatureFun, expRay, burnolDepthFeature, ← Complex.ofReal_mul,
    ← Complex.ofReal_exp, ← Complex.ofReal_neg]

theorem burnolComplexFeature_depth (ell : Ioi (0 : ℝ)) (n : ℕ) :
    burnolComplexFeature (((n + 1 : ℝ) * ell : ℝ) : ℂ)
      (by change 0 < (n + 1 : ℝ) * ell; exact mul_pos (by positivity) ell.property) = burnolDepthFeatureL2 ell n := by
  rw [burnolComplexFeature_ofReal]
  refine Lp.ext ?_
  filter_upwards [burnolDepthFeatureL2_ae
      (⟨(n + 1 : ℝ) * ell, mul_pos (by positivity : (0 : ℝ) < n + 1) ell.property⟩ : Ioi (0 : ℝ)) 0,
    burnolDepthFeatureL2_ae ell n] with t h1 h2
  rw [h1, h2]
  simp [burnolDepthFeature]

/-- Scalar Laplace coordinate, defined independently of the frequency domain. -/
def burnolComplexCoordinate (f : BurnolHalfLineL2) (z : ℂ) : ℂ :=
  bochnerLaplaceRay (Ioi (0 : ℝ) |>.indicator fun t => (t : ℂ) * conj (f t)) z

private theorem burnolCoordinate_source_measurable (f : BurnolHalfLineL2) :
    AEStronglyMeasurable (Ioi (0 : ℝ) |>.indicator fun t => (t : ℂ) * conj (f t)) volume := by
  apply (aestronglyMeasurable_indicator_iff measurableSet_Ioi).2
  exact (Complex.continuous_ofReal.aestronglyMeasurable.restrict).mul
    ((Complex.continuous_conj.comp_aestronglyMeasurable (Lp.memLp f).1))

private theorem burnolCoordinate_source_integrable (f : BurnolHalfLineL2) {c : ℝ} (hc : 0 < c) :
    IntegrableOn (fun t => expRay (c : ℂ) t •
      (Ioi (0 : ℝ) |>.indicator fun t => (t : ℂ) * conj (f t)) t) (Ioi 0) := by
  have hconj : MemLp (fun t : ℝ => conj (f t)) 2 (volume.restrict (Ioi 0)) :=
    (Lp.memLp f).star
  refine ((memLp_burnolComplexFeatureFun (z := (c : ℂ)) hc).integrable_mul hconj).congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  simp only [Pi.mul_apply, burnolComplexFeatureFun, Set.indicator_of_mem ht, smul_eq_mul]
  ring

theorem burnolComplexCoordinate_eq_inner (f : BurnolHalfLineL2) {z : ℂ} (hz : 0 < z.re) :
    burnolComplexCoordinate f z = inner ℂ f (burnolComplexFeature z hz) := by
  rw [burnolComplexCoordinate, bochnerLaplaceRay, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi, burnolComplexFeature_ae z hz] with t ht he
  rw [he, RCLike.inner_apply]
  simp only [Set.indicator_of_mem ht, burnolComplexFeatureFun, smul_eq_mul]
  ring

theorem burnolComplexCoordinate_differentiableAt (f : BurnolHalfLineL2) {z : ℂ}
    (hz : 0 < z.re) : DifferentiableAt ℂ (burnolComplexCoordinate f) z :=
  bochnerLaplaceRay_differentiableAt (burnolCoordinate_source_measurable f)
    (burnolCoordinate_source_integrable f (by linarith : 0 < z.re / 2)) z (by linarith)

theorem burnolComplexCoordinate_bounded (f : BurnolHalfLineL2) {δ : ℝ} (hδ : 0 < δ) :
    ∃ M : ℝ, ∀ z : ℂ, δ ≤ z.re → ‖burnolComplexCoordinate f z‖ ≤ M := by
  refine ⟨∫ t in Ioi (0 : ℝ), ‖expRay (δ : ℂ) t •
    ((Ioi (0 : ℝ)).indicator (fun u => (u : ℂ) * conj (f u))) t‖, ?_⟩
  intro z hz
  exact bochnerLaplaceRay_norm_le (burnolCoordinate_source_integrable f hδ) z hz

end GaloisForLFunctions.HTGeometry
