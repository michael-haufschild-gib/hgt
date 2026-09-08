import GaloisForLFunctions.RHTower.SelbergMaassCurvatureCovariance
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-!
# Planar test scaling and constant-mode cancellation

Literal affine rescaling has inverse-square Laplacian scaling and square area
scaling. In dimension two these cancel in the Laplacian L¹ norm. A fixed smooth
cutoff localizes to shrinking positive-height neighborhoods; local Green gives
zero total Laplacian. These identities retain every source support condition.
-/

open Set Filter Topology MeasureTheory UpperHalfPlane
open scoped ContDiff
namespace GaloisForLFunctions.RHTower.SelbergPlanarTestScaling
open SelbergMaassTraceEnergy SelbergLocalTestGreen SelbergMaassCurvatureCovariance
noncomputable section

/-- A translated inverse-scale test in the literal complex chart. -/
def rescale (phi : ℂ → ℝ) (c : ℂ) (r : ℝ) (z : ℂ) : ℝ := phi (r⁻¹ • (z - c))

/-- Rescaling preserves the original C² regularity. -/
theorem rescale_contDiff {phi : ℂ → ℝ} (hp : ContDiff ℝ 2 phi) (c : ℂ) (r : ℝ) :
    ContDiff ℝ 2 (rescale phi c r) :=
  hp.comp ((contDiff_id.sub contDiff_const).const_smul _)

/-- Nonzero rescaling preserves compact support. -/
theorem rescale_compact {phi : ℂ → ℝ} (hc : HasCompactSupport phi) (c : ℂ) {r : ℝ} (hr : r ≠ 0) :
    HasCompactSupport (rescale phi c r) :=
  hc.comp_homeomorph ((Homeomorph.subRight c).trans (Homeomorph.smulOfNeZero r⁻¹ (inv_ne_zero hr)))

/-- The actual real planar Laplacian scales by the inverse squared radius. -/
theorem rescale_laplacian {phi : ℂ → ℝ} (hp : ContDiff ℝ 2 phi) (c : ℂ) (r : ℝ) (z : ℂ) :
    realLaplacian (rescale phi c r) z = r⁻¹ ^ 2 * realLaplacian phi (r⁻¹ • (z - c)) := by
  let T : ℂ → ℂ := fun w => r⁻¹ • (w - c)
  have hT : ContDiff ℂ 2 T := by
    simpa only [T, Complex.real_smul] using
      (contDiff_const.mul (contDiff_id.sub contDiff_const) : ContDiff ℂ 2 (fun w : ℂ => ((r⁻¹ : ℝ) : ℂ) * (w - c)))
  have hd : deriv T z = ((r⁻¹ : ℝ) : ℂ) := by
    have h := ((hasDerivAt_id z).sub_const c).const_mul ((r⁻¹ : ℝ) : ℂ)
    simpa only [T, Complex.real_smul, mul_one, id_eq] using h.deriv
  have h := HTGeometry.ComplexC2Laplacian.laplacian_holomorphic_comp
    (Complex.ofRealCLM.contDiff.contDiffAt.comp (T z) hp.contDiffAt) hT.contDiffAt
  change HTGeometry.ComplexC2Laplacian.laplacian
    (fun w => (rescale phi c r w : ℂ)) z = _ at h
  simp only [Function.comp_def, Complex.ofRealCLM_apply] at h
  rw [laplacian_ofReal (rescale_contDiff hp c r).contDiffAt,
    laplacian_ofReal hp.contDiffAt, hd, Complex.normSq_ofReal] at h
  apply Complex.ofReal_injective
  simpa only [Complex.ofReal_mul, Complex.ofReal_pow, T, pow_two] using h

/-- In real dimension two, chart rescaling multiplies every test integral by r². -/
theorem integral_rescale (phi : ℂ → ℝ) (c : ℂ) (r : ℝ) :
    (∫ z, rescale phi c r z) = r ^ 2 * ∫ z, phi z := by
  unfold rescale
  rw [integral_sub_right_eq_self (fun z : ℂ => phi (r⁻¹ • z)) c,
    Measure.integral_comp_inv_smul volume phi r, Complex.finrank_real_complex]
  simp only [abs_of_nonneg (sq_nonneg r), smul_eq_mul]

/-- The L¹ norm of the rescaled Laplacian is independent of nonzero scale. -/
theorem integral_norm_rescale_laplacian {phi : ℂ → ℝ} (hp : ContDiff ℝ 2 phi)
    (c : ℂ) {r : ℝ} (hr : r ≠ 0) :
    (∫ z, ‖realLaplacian (rescale phi c r) z‖) = ∫ z, ‖realLaplacian phi z‖ := by
  simp_rw [rescale_laplacian hp, norm_mul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg r⁻¹)]
  rw [integral_const_mul]
  change r⁻¹ ^ 2 * (∫ z, rescale (fun w => |realLaplacian phi w|) c r z) = _
  rw [integral_rescale]
  field_simp

/-- A fixed planar smooth cutoff, one on the unit disk and zero outside radius two. -/
def unitCutoff : ContDiffBump (0 : ℂ) := ⟨1, 2, one_pos, one_lt_two⟩

/-- The actual localized planar cutoff. -/
def cutoff (c : ℂ) (r : ℝ) : ℂ → ℝ := rescale unitCutoff c r

/-- The localized cutoff is C² at every scale. -/
theorem cutoff_contDiff (c : ℂ) (r : ℝ) : ContDiff ℝ 2 (cutoff c r) :=
  rescale_contDiff unitCutoff.contDiff c r

/-- Every nonzero-scale cutoff has compact support. -/
theorem cutoff_compact (c : ℂ) {r : ℝ} (hr : r ≠ 0) : HasCompactSupport (cutoff c r) :=
  rescale_compact unitCutoff.hasCompactSupport c hr

/-- The cutoff is nonnegative everywhere. -/
theorem cutoff_nonneg (c : ℂ) (r : ℝ) (z : ℂ) : 0 ≤ cutoff c r z := unitCutoff.nonneg

/-- Every scale retains the value one at its center. -/
theorem cutoff_center (c : ℂ) (r : ℝ) : cutoff c r c = 1 := by
  apply unitCutoff.one_of_mem_closedBall
  simp [unitCutoff]

/-- All cutoff support lies within twice the positive scale of its center. -/
theorem cutoff_support (c : ℂ) {r : ℝ} (hr : 0 < r) :
    tsupport (cutoff c r) ⊆ Metric.closedBall c (2 * r) := by
  intro z hz
  have h := tsupport_comp_subset_preimage (unitCutoff : ℂ → ℝ)
    ((continuous_id.sub continuous_const).const_smul r⁻¹) hz
  change r⁻¹ • (z - c) ∈ tsupport (unitCutoff : ℂ → ℝ) at h
  rw [unitCutoff.tsupport_eq] at h
  have hb : r⁻¹ * ‖z - c‖ ≤ 2 := by
    simpa only [Metric.mem_closedBall, dist_zero_right, norm_smul,
      Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr), unitCutoff] using h
  have hh := mul_le_mul_of_nonneg_left hb hr.le
  rw [← mul_assoc, mul_inv_cancel₀ hr.ne', one_mul] at hh
  simpa only [Metric.mem_closedBall, dist_eq_norm, mul_comm r] using hh

/-- Small centered cutoffs lie entirely at positive height. -/
theorem cutoff_support_upper (c : ℂ) {r : ℝ} (hr : 0 < r) (hcr : 2 * r < c.im) :
    tsupport (cutoff c r) ⊆ {z : ℂ | 0 < z.im} := by
  intro z hz
  have hb := cutoff_support c hr hz
  rw [Metric.mem_closedBall, dist_eq_norm] at hb
  have hi := Complex.abs_im_le_norm (z - c)
  rw [Complex.sub_im] at hi
  have hn := neg_abs_le (z.im - c.im)
  change 0 < z.im
  linarith

/-- Shrinking planar cutoffs have exactly quadratic L¹ mass. -/
theorem integral_norm_cutoff (c : ℂ) (r : ℝ) :
    (∫ z, ‖cutoff c r z‖) = r ^ 2 * ∫ z, ‖unitCutoff z‖ :=
  integral_rescale (fun z => ‖unitCutoff z‖) c r

/-- Shrinking planar cutoff Laplacians have fixed L¹ mass. -/
theorem integral_norm_cutoff_laplacian (c : ℂ) {r : ℝ} (hr : r ≠ 0) :
    (∫ z, ‖realLaplacian (cutoff c r) z‖) = ∫ z, ‖realLaplacian unitCutoff z‖ :=
  integral_norm_rescale_laplacian unitCutoff.contDiff c hr

/-- Every admissible compact test has zero total planar Laplacian. -/
theorem integral_laplacian_zero {phi : ℂ → ℝ} (hp : ContDiff ℝ 2 phi)
    (hc : HasCompactSupport phi) (hs : tsupport phi ⊆ {z : ℂ | 0 < z.im}) :
    (∫ z, realLaplacian phi z) = 0 := by
  have h := integral_test_laplacian hp hc hs (F := fun _ => (1 : ℝ)) contDiffOn_const
  have hzero : realLaplacian (fun _ : ℂ => (1 : ℝ)) = fun _ => 0 := by
    funext z
    change fderiv ℝ (fun w : ℂ => fderiv ℝ (fun _ : ℂ => (1 : ℝ)) w 1) z 1 +
      fderiv ℝ (fun w : ℂ => fderiv ℝ (fun _ : ℂ => (1 : ℝ)) w Complex.I) z Complex.I = 0
    simp
  simpa only [hzero, mul_zero, integral_zero, mul_one] using h.symm

end
end GaloisForLFunctions.RHTower.SelbergPlanarTestScaling
