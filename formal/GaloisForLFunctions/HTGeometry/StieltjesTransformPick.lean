import Mathlib

/-!
# The Stieltjes transform of a positive measure is a Pick function

The analytic bridge between the moment problem and Nevanlinna–Pick theory, absent from mathlib as a
packaged statement.  For a positive measure `μ` on `ℝ`, its **Stieltjes/Cauchy transform**

`S_μ(z) = ∫ (x − z)⁻¹ dμ(x)`

maps the open upper half-plane into the closed upper half-plane, and into the open upper half-plane
when `μ ≠ 0` — it is a **Pick (Herglotz/Nevanlinna) function**.  The mechanism is the pointwise
positivity of the imaginary part of the Cauchy kernel,

`Im (x − z)⁻¹ = Im z / |x − z|²  ≥ 0   (> 0 when Im z > 0)`,

combined with commuting `Im` through the Bochner integral.  This Herglotz positivity is the load-bearing
analytic input of the Nevanlinna-parametrization and Pick-defect cards
(`nevanlinna-boundary-bauer-retract-maximal-ht`, `pick-defect-finite-selector-maximal-ht-phase-law`):
every representing measure of an indeterminate moment sequence produces, through `S_μ`, a Pick function
whose boundary behaviour carries the moment data.
-/

open scoped BigOperators
open MeasureTheory Complex

namespace HTGeometry

/-- The imaginary part of the Cauchy kernel at a real point: `Im (x − z)⁻¹ = Im z / |x − z|²`. -/
theorem cauchyKernel_im (x : ℝ) (z : ℂ) :
    (((x : ℂ) - z)⁻¹).im = z.im / Complex.normSq ((x : ℂ) - z) := by
  rw [Complex.inv_im]
  simp [Complex.sub_im, Complex.ofReal_im]

/-- Commuting the imaginary part through the Bochner integral of an integrable complex function. -/
theorem im_integral {μ : Measure ℝ} {f : ℝ → ℂ} (hf : Integrable f μ) :
    (∫ x, f x ∂μ).im = ∫ x, (f x).im ∂μ := by
  rw [← Complex.imCLM_apply, ← ContinuousLinearMap.integral_comp_comm Complex.imCLM hf]
  rfl

/-- **Herglotz positivity (closed half-plane).**  The Stieltjes transform of a positive measure has
nonnegative imaginary part throughout the closed upper half-plane. -/
theorem stieltjesTransform_im_nonneg {μ : Measure ℝ} (z : ℂ) (hz : 0 ≤ z.im)
    (hInt : Integrable (fun x : ℝ => ((x : ℂ) - z)⁻¹) μ) :
    0 ≤ (∫ x, ((x : ℂ) - z)⁻¹ ∂μ).im := by
  rw [im_integral hInt]
  refine integral_nonneg (fun x => ?_)
  rw [cauchyKernel_im x z]
  exact div_nonneg hz (Complex.normSq_nonneg _)

/-- The imaginary part of the Cauchy kernel is strictly positive in the open upper half-plane. -/
theorem cauchyKernel_im_pos (x : ℝ) (z : ℂ) (hz : 0 < z.im) :
    0 < (((x : ℂ) - z)⁻¹).im := by
  rw [cauchyKernel_im x z]
  refine div_pos hz ?_
  rw [Complex.normSq_pos]
  intro hzero
  have hzx : z = (x : ℂ) := by
    have := sub_eq_zero.mp hzero
    exact this.symm
  rw [hzx] at hz
  simp [Complex.ofReal_im] at hz

/-- **Pick property (open half-plane).**  The Stieltjes transform of a nonzero positive measure has
strictly positive imaginary part everywhere in the open upper half-plane: `S_μ` is a Pick function. -/
theorem stieltjesTransform_im_pos {μ : Measure ℝ} (z : ℂ) (hz : 0 < z.im)
    (hμ : 0 < μ Set.univ) (hInt : Integrable (fun x : ℝ => ((x : ℂ) - z)⁻¹) μ) :
    0 < (∫ x, ((x : ℂ) - z)⁻¹ ∂μ).im := by
  rw [im_integral hInt]
  have hIntIm : Integrable (fun x : ℝ => (((x : ℂ) - z)⁻¹).im) μ := hInt.im
  rw [integral_pos_iff_support_of_nonneg (fun x => (cauchyKernel_im_pos x z hz).le) hIntIm]
  have hsupp : Function.support (fun x : ℝ => (((x : ℂ) - z)⁻¹).im) = Set.univ := by
    ext x
    simp only [Function.mem_support, Set.mem_univ, iff_true]
    exact ne_of_gt (cauchyKernel_im_pos x z hz)
  rw [hsupp]
  exact hμ

/-- **Holomorphy of the Stieltjes transform.**  For a finite measure `μ`, the Cauchy–Stieltjes
transform `z ↦ ∫ (x − z)⁻¹ dμ` is complex-differentiable at every point of the open upper half-plane,
with derivative `∫ (x − z₀)⁻² dμ`.  Differentiation under the integral sign is licensed by the local
Lipschitz domination `‖(x − z)⁻²‖ ≤ (Im z₀/2)⁻²` on a ball around `z₀` that stays in the half-plane. -/
theorem stieltjes_hasDerivAt {μ : Measure ℝ} [IsFiniteMeasure μ] (z₀ : ℂ) (hz₀ : 0 < z₀.im) :
    HasDerivAt (fun z => ∫ x, ((x : ℂ) - z)⁻¹ ∂μ)
      (∫ x, (((x : ℂ) - z₀) ^ 2)⁻¹ ∂μ) z₀ := by
  set r : ℝ := z₀.im / 2 with hr
  have hrpos : 0 < r := by rw [hr]; linarith
  set s : Set ℂ := Metric.ball z₀ r with hs
  have him : ∀ z ∈ s, r ≤ z.im := by
    intro z hz
    rw [hs, Metric.mem_ball] at hz
    have h1 : |z.im - z₀.im| ≤ dist z z₀ := by
      have := Complex.abs_im_le_norm (z - z₀)
      simpa [Complex.dist_eq, Complex.sub_im] using this
    have h2 : |z.im - z₀.im| < r := lt_of_le_of_lt h1 hz
    rw [abs_lt] at h2; rw [hr]; linarith [h2.1]
  have hbnd : ∀ (x : ℝ), ∀ z ∈ s, r ≤ ‖(x : ℂ) - z‖ := by
    intro x z hz
    have hi : |((x : ℂ) - z).im| ≤ ‖(x : ℂ) - z‖ := Complex.abs_im_le_norm _
    have he : ((x : ℂ) - z).im = -z.im := by simp [Complex.sub_im]
    rw [he] at hi
    have hz' : r ≤ z.im := him z hz
    have habs : |(-z.im)| = z.im := by rw [abs_neg, abs_of_nonneg (by linarith)]
    rw [habs] at hi; linarith
  have hne : ∀ (x : ℝ), ∀ z ∈ s, (x : ℂ) - z ≠ 0 := by
    intro x z hz h0
    have := hbnd x z hz; rw [h0, norm_zero] at this; linarith
  have hz₀s : z₀ ∈ s := Metric.mem_ball_self hrpos
  have hderiv : ∀ (x : ℝ), ∀ z ∈ s,
      HasDerivAt (fun w => ((x : ℂ) - w)⁻¹) ((((x : ℂ) - z) ^ 2)⁻¹) z := by
    intro x z hz
    have hf : HasDerivAt (fun w => (x : ℂ) - w) (-1) z := by
      simpa using (hasDerivAt_id z).const_sub (x : ℂ)
    have := hf.inv (hne x z hz)
    convert! this using 1
    field_simp
  have hcont : ∀ z ∈ s, Continuous (fun x : ℝ => ((x : ℂ) - z)⁻¹) := by
    intro z hz
    exact (continuous_ofReal.sub continuous_const).inv₀ (fun x => hne x z hz)
  have hnormbnd : ∀ (x : ℝ), ∀ z ∈ s, ‖(((x : ℂ) - z) ^ 2)⁻¹‖ ≤ (r ^ 2)⁻¹ := by
    intro x z hz
    rw [norm_inv, norm_pow]
    have hb := hbnd x z hz
    have hnp : 0 < ‖(x : ℂ) - z‖ := lt_of_lt_of_le hrpos hb
    rw [inv_le_inv₀ (pow_pos hnp 2) (pow_pos hrpos 2)]
    nlinarith [hb, hrpos.le]
  refine (hasDerivAt_integral_of_dominated_loc_of_lip (bound := fun _ => (r ^ 2)⁻¹)
      (Metric.ball_mem_nhds z₀ hrpos) ?_ ?_ ?_ ?_ ?_ ?_).2
  · exact Filter.eventually_of_mem (Metric.ball_mem_nhds z₀ hrpos)
      (fun z hz => (hcont z hz).aestronglyMeasurable)
  · exact ⟨(hcont z₀ hz₀s).aestronglyMeasurable, HasFiniteIntegral.of_bounded (C := r⁻¹)
      (ae_of_all μ (fun x => by
        rw [norm_inv, inv_le_inv₀ (lt_of_lt_of_le hrpos (hbnd x z₀ hz₀s)) hrpos]
        exact hbnd x z₀ hz₀s))⟩
  · exact Continuous.aestronglyMeasurable
      (((continuous_ofReal.sub continuous_const).pow 2).inv₀
        (fun x => pow_ne_zero 2 (hne x z₀ hz₀s)))
  · refine ae_of_all μ (fun x => ?_)
    refine Convex.lipschitzOnWith_of_nnnorm_hasDerivWithin_le (convex_ball z₀ r)
      (fun z hz => (hderiv x z hz).hasDerivWithinAt) (fun z hz => ?_)
    rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_nnabs, abs_of_nonneg (by positivity)]
    exact hnormbnd x z hz
  · exact integrable_const _
  · exact ae_of_all μ (fun x => hderiv x z₀ hz₀s)

/-- The Stieltjes transform of a finite measure is holomorphic on the open upper half-plane — a Pick
function is analytic there. -/
theorem stieltjesTransform_differentiableOn {μ : Measure ℝ} [IsFiniteMeasure μ] :
    DifferentiableOn ℂ (fun z => ∫ x, ((x : ℂ) - z)⁻¹ ∂μ) {z : ℂ | 0 < z.im} :=
  fun z hz => ((stieltjes_hasDerivAt z hz).differentiableAt).differentiableWithinAt

/-- **Herglotz growth bound.**  The Stieltjes transform of a finite measure satisfies
`‖S_μ(z)‖ ≤ μ(ℝ) / Im z` throughout the open upper half-plane — the standard growth estimate of a
Pick function, forcing `S_μ(z) → 0` as `Im z → ∞`. -/
theorem stieltjesTransform_norm_le {μ : Measure ℝ} [IsFiniteMeasure μ] (z : ℂ) (hz : 0 < z.im) :
    ‖∫ x, ((x : ℂ) - z)⁻¹ ∂μ‖ ≤ (μ Set.univ).toReal / z.im := by
  have hcont : Continuous (fun x : ℝ => ((x : ℂ) - z)⁻¹) := by
    refine (continuous_ofReal.sub continuous_const).inv₀ (fun x h0 => ?_)
    have : (x : ℂ).im = z.im := by
      change (x : ℂ) - z = 0 at h0
      exact congrArg Complex.im (sub_eq_zero.mp h0)
    rw [Complex.ofReal_im] at this; linarith
  have hbound : ∀ x : ℝ, ‖((x : ℂ) - z)⁻¹‖ ≤ (z.im)⁻¹ := by
    intro x
    rw [norm_inv]
    have hi : z.im ≤ ‖(x : ℂ) - z‖ := by
      have hle := Complex.abs_im_le_norm ((x : ℂ) - z)
      have he : ((x : ℂ) - z).im = -z.im := by simp [Complex.sub_im]
      rw [he, abs_neg, abs_of_nonneg hz.le] at hle
      exact hle
    have hnp : 0 < ‖(x : ℂ) - z‖ := lt_of_lt_of_le hz hi
    rw [inv_le_inv₀ hnp hz]; exact hi
  have hInt : Integrable (fun x : ℝ => ((x : ℂ) - z)⁻¹) μ :=
    ⟨hcont.aestronglyMeasurable, HasFiniteIntegral.of_bounded (C := (z.im)⁻¹)
      (ae_of_all μ hbound)⟩
  calc ‖∫ x, ((x : ℂ) - z)⁻¹ ∂μ‖
      ≤ ∫ x, ‖((x : ℂ) - z)⁻¹‖ ∂μ := norm_integral_le_integral_norm _
    _ ≤ ∫ _x : ℝ, (z.im)⁻¹ ∂μ := integral_mono hInt.norm (integrable_const _) hbound
    _ = (μ Set.univ).toReal / z.im := by
        rw [integral_const, smul_eq_mul, ← div_eq_mul_inv, Measure.real]

/-- **Poisson representation of the imaginary part.**  The imaginary part of the Stieltjes transform
is the Poisson integral of `μ`: for `z = a + i b`,
`Im S_μ(z) = ∫ b / ((x − a)² + b²) dμ(x)`.  This is the harmonic-measure kernel whose boundary limit
`b → 0⁺` recovers `μ` (Stieltjes–Perron inversion); it exhibits `Im S_μ` as a nonnegative harmonic
function on the upper half-plane, the analytic heart of the Herglotz representation. -/
theorem stieltjesTransform_im_eq_poisson {μ : Measure ℝ} (z : ℂ)
    (hInt : Integrable (fun x : ℝ => ((x : ℂ) - z)⁻¹) μ) :
    (∫ x, ((x : ℂ) - z)⁻¹ ∂μ).im
      = ∫ x, z.im / ((x - z.re) ^ 2 + z.im ^ 2) ∂μ := by
  rw [im_integral hInt]
  refine integral_congr_ae (ae_of_all μ (fun x => ?_))
  show (((x : ℂ) - z)⁻¹).im = z.im / ((x - z.re) ^ 2 + z.im ^ 2)
  rw [cauchyKernel_im, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im]
  congr 1
  ring

/-- Commuting the real part through the Bochner integral of an integrable complex function. -/
theorem re_integral {μ : Measure ℝ} {f : ℝ → ℂ} (hf : Integrable f μ) :
    (∫ x, f x ∂μ).re = ∫ x, (f x).re ∂μ := by
  rw [← Complex.reCLM_apply, ← ContinuousLinearMap.integral_comp_comm Complex.reCLM hf]
  rfl

/-- The real part of the Cauchy kernel: `Re (x − z)⁻¹ = (x − Re z) / |x − z|²`. -/
theorem cauchyKernel_re (x : ℝ) (z : ℂ) :
    (((x : ℂ) - z)⁻¹).re = (x - z.re) / Complex.normSq ((x : ℂ) - z) := by
  rw [Complex.inv_re]
  simp [Complex.sub_re, Complex.ofReal_re]

/-- **Schwarz reflection (real symmetry).**  The Stieltjes transform of a (real) measure is
real-symmetric: `S_μ(z̄) = conj(S_μ(z))`.  This is the defining symmetry of a **real-symmetric** Pick
function, which is what represents a Hamburger moment sequence. -/
theorem stieltjesTransform_conj {μ : Measure ℝ} (z : ℂ) :
    ∫ x, ((x : ℂ) - (starRingEnd ℂ) z)⁻¹ ∂μ
      = (starRingEnd ℂ) (∫ x, ((x : ℂ) - z)⁻¹ ∂μ) := by
  rw [← integral_conj]
  refine integral_congr_ae (ae_of_all μ (fun x => ?_))
  show ((x : ℂ) - (starRingEnd ℂ) z)⁻¹ = (starRingEnd ℂ) (((x : ℂ) - z)⁻¹)
  rw [map_inv₀, map_sub, Complex.conj_ofReal]

/-- **Conjugate-Poisson representation of the real part.**  For `z = a + i b`,
`Re S_μ(z) = ∫ (x − a) / ((x − a)² + b²) dμ(x)` — the conjugate harmonic of the Poisson integral. -/
theorem stieltjesTransform_re_eq_conjPoisson {μ : Measure ℝ} (z : ℂ)
    (hInt : Integrable (fun x : ℝ => ((x : ℂ) - z)⁻¹) μ) :
    (∫ x, ((x : ℂ) - z)⁻¹ ∂μ).re
      = ∫ x, (x - z.re) / ((x - z.re) ^ 2 + z.im ^ 2) ∂μ := by
  rw [re_integral hInt]
  refine integral_congr_ae (ae_of_all μ (fun x => ?_))
  show (((x : ℂ) - z)⁻¹).re = (x - z.re) / ((x - z.re) ^ 2 + z.im ^ 2)
  rw [cauchyKernel_re, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im]
  congr 1
  ring

/-- **Lower-half-plane image.**  By real symmetry, a nonzero measure's Stieltjes transform sends the
open lower half-plane into itself: `Im S_μ(z) < 0` when `Im z < 0`.  With `stieltjesTransform_im_pos`
this shows `S_μ` maps each open half-plane into itself — the full Pick mapping property. -/
theorem stieltjesTransform_im_neg {μ : Measure ℝ} (z : ℂ) (hz : z.im < 0)
    (hμ : 0 < μ Set.univ)
    (hInt : Integrable (fun x : ℝ => ((x : ℂ) - (starRingEnd ℂ) z)⁻¹) μ) :
    (∫ x, ((x : ℂ) - z)⁻¹ ∂μ).im < 0 := by
  have hcz : 0 < ((starRingEnd ℂ) z).im := by rw [Complex.conj_im]; linarith
  have hp := stieltjesTransform_im_pos ((starRingEnd ℂ) z) hcz hμ hInt
  rw [stieltjesTransform_conj, Complex.conj_im] at hp
  linarith

end HTGeometry
