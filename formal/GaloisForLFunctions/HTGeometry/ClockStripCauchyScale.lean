import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Analytic.Within

/-!
# The analytic scale in sup-norm form: Cauchy's estimate on a strip

The coefficient form of the scale of analytic spaces carries the algebra estimate, but its elements
are sequences. For the passage back to the clock equation the elements should be functions, and the
transverse Laplacian should be the actual second derivative. That is the sup-norm form of the same
scale: the space of radius `ρ` is the bounded holomorphic functions on the strip `|Im z| < ρ`, and
the derivative loss is Cauchy's estimate.

Applied once, Cauchy's estimate on a disc of radius `(ρ - ρ')/2` gives `‖f'‖ ≤ 2M/(ρ - ρ')` on the
strip of half-width `ρ'`. Applied twice, through the intermediate half-width `(ρ + ρ')/2`, it gives
`‖f''‖ ≤ 16M/(ρ - ρ')²` — the sup-norm counterpart of the coefficient bound `4/(ρ - ρ')²`.
-/

namespace GaloisForLFunctions.HTGeometry

open Complex Metric

/-! ## The strip -/

/-- The open horizontal strip of half-width `ρ`. -/
def imStrip (ρ : ℝ) : Set ℂ := {z : ℂ | |z.im| < ρ}

theorem mem_imStrip {ρ : ℝ} {z : ℂ} : z ∈ imStrip ρ ↔ |z.im| < ρ := Iff.rfl

theorem isOpen_imStrip (ρ : ℝ) : IsOpen (imStrip ρ) :=
  isOpen_lt (continuous_abs.comp Complex.continuous_im) continuous_const

theorem imStrip_mono {ρ' ρ : ℝ} (h : ρ' ≤ ρ) : imStrip ρ' ⊆ imStrip ρ :=
  fun _ hz => lt_of_lt_of_le hz h

/-- A disc centred inside the strip of half-width `ρ'` and of radius at most half the gap stays
inside the strip of half-width `ρ`. -/
theorem closedBall_subset_imStrip {ρ ρ' : ℝ} (hρ : ρ' < ρ) {z : ℂ} (hz : |z.im| ≤ ρ') :
    closedBall z ((ρ - ρ') / 2) ⊆ imStrip ρ := by
  intro w hw
  have hnorm : ‖w - z‖ ≤ (ρ - ρ') / 2 := by
    rw [← dist_eq_norm]
    exact mem_closedBall.mp hw
  have him : |w.im - z.im| ≤ (ρ - ρ') / 2 := by
    have h := Complex.abs_im_le_norm (w - z)
    rw [Complex.sub_im] at h
    linarith
  have hsplit : |w.im| ≤ |z.im| + |w.im - z.im| := by
    have := abs_sub_abs_le_abs_sub w.im z.im
    linarith
  show |w.im| < ρ
  linarith

/-! ## Cauchy's estimate on the strip -/

/-- **One derivative costs one power of the gap.** -/
theorem norm_deriv_le_on_imStrip {ρ ρ' M : ℝ} (hρ : ρ' < ρ) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (imStrip ρ)) (hM : ∀ z ∈ imStrip ρ, ‖f z‖ ≤ M)
    {z : ℂ} (hz : |z.im| ≤ ρ') : ‖deriv f z‖ ≤ 2 * M / (ρ - ρ') := by
  have hRpos : (0 : ℝ) < (ρ - ρ') / 2 := by linarith
  have hsub := closedBall_subset_imStrip hρ hz
  have hdc : DiffContOnCl ℂ f (ball z ((ρ - ρ') / 2)) := by
    refine ⟨hf.mono (ball_subset_closedBall.trans hsub), ?_⟩
    rw [closure_ball z hRpos.ne']
    exact hf.continuousOn.mono hsub
  have hC : ∀ w ∈ sphere z ((ρ - ρ') / 2), ‖f w‖ ≤ M := fun w hw =>
    hM w (hsub (sphere_subset_closedBall hw))
  have hbase := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hRpos hdc hC
  have hgap : (0 : ℝ) < ρ - ρ' := by linarith
  calc ‖deriv f z‖ ≤ M / ((ρ - ρ') / 2) := hbase
    _ = 2 * M / (ρ - ρ') := by field_simp

/-- **Two derivatives cost two powers of the gap.** -/
theorem norm_deriv_deriv_le_on_imStrip {ρ ρ' M : ℝ} (hρ : ρ' < ρ) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f (imStrip ρ)) (hM : ∀ z ∈ imStrip ρ, ‖f z‖ ≤ M)
    {z : ℂ} (hz : |z.im| ≤ ρ') : ‖deriv (deriv f) z‖ ≤ 16 * M / (ρ - ρ') ^ 2 := by
  have hgap : (0 : ℝ) < ρ - ρ' := by linarith
  have hmid : ρ' < (ρ + ρ') / 2 := by linarith
  have hmid' : (ρ + ρ') / 2 < ρ := by linarith
  -- the derivative is holomorphic on the strip
  have hana : AnalyticOnNhd ℂ f (imStrip ρ) := hf.analyticOnNhd (isOpen_imStrip ρ)
  have hderiv : DifferentiableOn ℂ (deriv f) (imStrip ((ρ + ρ') / 2)) :=
    ((hana.deriv (isOpen_imStrip ρ)).mono (imStrip_mono hmid'.le)).differentiableOn
  -- and bounded there by the first estimate
  have hMd : ∀ w ∈ imStrip ((ρ + ρ') / 2), ‖deriv f w‖ ≤ 4 * M / (ρ - ρ') := by
    intro w hw
    have hb := norm_deriv_le_on_imStrip hmid' hf hM (le_of_lt (mem_imStrip.mp hw))
    have hrw : 2 * M / (ρ - (ρ + ρ') / 2) = 4 * M / (ρ - ρ') := by
      field_simp
      ring
    rwa [hrw] at hb
  have hsecond := norm_deriv_le_on_imStrip hmid hderiv hMd hz
  have hrw : 2 * (4 * M / (ρ - ρ')) / ((ρ + ρ') / 2 - ρ') = 16 * M / (ρ - ρ') ^ 2 := by
    field_simp
    ring
  rwa [hrw] at hsecond

end GaloisForLFunctions.HTGeometry
