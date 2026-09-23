import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# The Cauchy coordinate maps a half-plane into a disc

For `a > 0` the map `z ↦ (z + a)⁻¹` carries the right half-plane `Re z > 0` into the open disc of
centre and radius `1/(2a)`.  The computation is the elementary identity

`(z + a)⁻¹ − 1/(2a) = (a − z)/(2a(z + a))`,

whose norm is below `1/(2a)` exactly when `‖z − a‖ < ‖z + a‖`, i.e. exactly when `Re z > 0`.

This is the change of coordinate under which polynomial approximation on a disc becomes
approximation by polynomials in a single Cauchy coordinate on a half-plane.

* `HTGeometry.norm_sub_lt_norm_add_of_re_pos`;
* `HTGeometry.cauchyCoordinate_mem_ball_of_re_pos`;
* `HTGeometry.exists_radius_lt_of_isCompact_re_pos`;
* `HTGeometry.re_inv_sub_pos_of_mem_ball`;
* `HTGeometry.differentiableOn_transport_of_re_pos`.
-/

open Complex Metric

namespace HTGeometry

/-- On the right half-plane the pole at `-a` is farther than the pole at `a`. -/
theorem norm_sub_lt_norm_add_of_re_pos {a : ℝ} (ha : 0 < a) {z : ℂ} (hz : 0 < z.re) :
    ‖z - (a : ℂ)‖ < ‖z + (a : ℂ)‖ := by
  have hsq : ‖z - (a : ℂ)‖ ^ (2 : ℕ) < ‖z + (a : ℂ)‖ ^ (2 : ℕ) := by
    rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.add_re,
      Complex.add_im, Complex.ofReal_re, Complex.ofReal_im]
    nlinarith
  have h0 : (0 : ℝ) ≤ ‖z - (a : ℂ)‖ := norm_nonneg _
  nlinarith [norm_nonneg (z + (a : ℂ))]

/-- **The Cauchy coordinate maps the right half-plane into a disc.** -/
theorem cauchyCoordinate_mem_ball_of_re_pos {a : ℝ} (ha : 0 < a) {z : ℂ} (hz : 0 < z.re) :
    (z + (a : ℂ))⁻¹ ∈ ball ((1 / (2 * a) : ℝ) : ℂ) (1 / (2 * a)) := by
  have hne : z + (a : ℂ) ≠ 0 := by
    intro hcon
    have hre : z.re + a = 0 := by
      have := congrArg Complex.re hcon
      simpa using this
    linarith
  have hnormpos : (0 : ℝ) < ‖z + (a : ℂ)‖ := norm_pos_iff.2 hne
  have hane : (a : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 (ne_of_gt ha)
  have hcast : ((1 / (2 * a) : ℝ) : ℂ) = 1 / ((2 : ℂ) * (a : ℂ)) := by
    push_cast
    ring
  have hkey : (z + (a : ℂ))⁻¹ - ((1 / (2 * a) : ℝ) : ℂ)
      = ((a : ℂ) - z) / ((2 : ℂ) * (a : ℂ) * (z + (a : ℂ))) := by
    rw [hcast]
    field_simp
    ring
  rw [mem_ball, Complex.dist_eq, hkey, norm_div, norm_mul, norm_mul,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha]
  norm_num
  rw [div_lt_iff₀ (by positivity)]
  have hrev : ‖(a : ℂ) - z‖ = ‖z - (a : ℂ)‖ := norm_sub_rev _ _
  have hlt := norm_sub_lt_norm_add_of_re_pos ha hz
  rw [hrev]
  have hfac : a⁻¹ * (1 / 2) * (2 * a * ‖z + (a : ℂ)‖) = ‖z + (a : ℂ)‖ := by
    field_simp
  rw [hfac]
  exact hlt

/-- **A compact subset of the half-plane lands in a strictly smaller disc.**  Continuity of the
Cauchy coordinate on a compact set turns the pointwise strict bound into a uniform one with room to
spare — which is what a transported approximation needs. -/
theorem exists_radius_lt_of_isCompact_re_pos {a : ℝ} (ha : 0 < a) {K : Set ℂ}
    (hK : IsCompact K) (hKsub : ∀ z ∈ K, 0 < z.re) :
    ∃ ρ : ℝ, 0 ≤ ρ ∧ ρ < 1 / (2 * a) ∧
      ∀ z ∈ K, ‖(z + (a : ℂ))⁻¹ - ((1 / (2 * a) : ℝ) : ℂ)‖ ≤ ρ := by
  have hpos : (0 : ℝ) < 1 / (2 * a) := by positivity
  rcases Set.eq_empty_or_nonempty K with hempty | hne
  · exact ⟨0, le_rfl, hpos, fun z hz => absurd (hempty ▸ hz) (Set.notMem_empty z)⟩
  · have hnezero : ∀ z ∈ K, z + (a : ℂ) ≠ 0 := by
      intro z hz hcon
      have hre : z.re + a = 0 := by
        have := congrArg Complex.re hcon
        simpa using this
      have := hKsub z hz
      linarith
    have hcont : ContinuousOn
        (fun z : ℂ => ‖(z + (a : ℂ))⁻¹ - ((1 / (2 * a) : ℝ) : ℂ)‖) K := by
      refine ContinuousOn.norm ?_
      refine ContinuousOn.sub ?_ continuousOn_const
      exact ContinuousOn.inv₀ (by fun_prop) hnezero
    obtain ⟨z₀, hz₀K, hz₀max⟩ := hK.exists_isMaxOn hne hcont
    refine ⟨‖(z₀ + (a : ℂ))⁻¹ - ((1 / (2 * a) : ℝ) : ℂ)‖, norm_nonneg _, ?_, ?_⟩
    · have := cauchyCoordinate_mem_ball_of_re_pos ha (hKsub z₀ hz₀K)
      rw [mem_ball, Complex.dist_eq] at this
      exact this
    · intro z hz
      exact hz₀max hz

/-- **The inverse coordinate maps the disc back to the half-plane.**  The condition `‖w − c‖ < c`
with `c = 1/(2a)` is `normSq w < 2c·Re w`, which is exactly `Re(w⁻¹) > a`. -/
theorem re_inv_sub_pos_of_mem_ball {a : ℝ} (ha : 0 < a) {w : ℂ}
    (hw : w ∈ ball ((1 / (2 * a) : ℝ) : ℂ) (1 / (2 * a))) : 0 < (w⁻¹ - (a : ℂ)).re := by
  have hc : (0 : ℝ) < 1 / (2 * a) := by positivity
  have hdist : ‖w - ((1 / (2 * a) : ℝ) : ℂ)‖ < 1 / (2 * a) := by
    rw [mem_ball, Complex.dist_eq] at hw
    exact hw
  have hsq : Complex.normSq (w - ((1 / (2 * a) : ℝ) : ℂ)) < (1 / (2 * a)) ^ (2 : ℕ) := by
    have h1 : ‖w - ((1 / (2 * a) : ℝ) : ℂ)‖ ^ (2 : ℕ) < (1 / (2 * a)) ^ (2 : ℕ) := by
      have h0 : (0 : ℝ) ≤ ‖w - ((1 / (2 * a) : ℝ) : ℂ)‖ := norm_nonneg _
      nlinarith
    rwa [Complex.normSq_eq_norm_sq]
  have hc2 : (1 : ℝ) / (2 * a) * 2 = 1 / a := by
    field_simp
  have hexp : Complex.normSq (w - ((1 / (2 * a) : ℝ) : ℂ))
      = Complex.normSq w - (1 / a) * w.re + (1 / (2 * a)) ^ (2 : ℕ) := by
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
      Complex.ofReal_im]
    have ha' : a ≠ 0 := ne_of_gt ha
    field_simp
    ring
  have hkey : Complex.normSq w < (1 / a) * w.re := by
    rw [hexp] at hsq
    linarith
  have hwne : w ≠ 0 := by
    intro hcon
    rw [hcon] at hkey
    simp at hkey
  have hnpos : (0 : ℝ) < Complex.normSq w := Complex.normSq_pos.2 hwne
  have hre : (w⁻¹ - (a : ℂ)).re = w.re / Complex.normSq w - a := by
    simp [Complex.inv_re, Complex.sub_re]
  rw [hre, sub_pos, lt_div_iff₀ hnpos]
  have hmul : a * Complex.normSq w < a * ((1 / a) * w.re) :=
    mul_lt_mul_of_pos_left hkey ha
  have hsimp : a * ((1 / a) * w.re) = w.re := by
    field_simp
  rw [hsimp] at hmul
  exact hmul

/-- **Holomorphy transports to the disc.**  A function holomorphic on the right half-plane pulls
back through the inverse coordinate to a function holomorphic on the disc. -/
theorem differentiableOn_transport_of_re_pos {a : ℝ} (ha : 0 < a) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f {z : ℂ | 0 < z.re}) :
    DifferentiableOn ℂ (fun w : ℂ => f (w⁻¹ - (a : ℂ)))
      (ball ((1 / (2 * a) : ℝ) : ℂ) (1 / (2 * a))) := by
  intro w hw
  have hpos := re_inv_sub_pos_of_mem_ball ha hw
  have hwne : w ≠ 0 := by
    intro hcon
    rw [hcon] at hpos
    simp at hpos
    linarith
  have hinner : DifferentiableAt ℂ (fun v : ℂ => v⁻¹ - (a : ℂ)) w :=
    (differentiableAt_inv hwne).sub_const _
  have houter : DifferentiableAt ℂ f (w⁻¹ - (a : ℂ)) :=
    hf.differentiableAt ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hpos)
  exact (houter.comp w hinner).differentiableWithinAt

end HTGeometry
