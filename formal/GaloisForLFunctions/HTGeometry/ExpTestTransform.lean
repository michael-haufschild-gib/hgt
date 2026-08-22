import GaloisForLFunctions.HTGeometry.CompactTestTransform
import GaloisForLFunctions.HTGeometry.LineScalingL2
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# The exponential transform of a test function in the half-plane variable

Rotating the entire Fourier extension `testTransform ψ z = ∫ ψ(L)e^{izL}dL` by `z = -iw` gives
`∫ ψ(L)e^{wL}dL`, the multiplier used to make a boundary datum that is only square-integrable
integrable along vertical lines.  Its quadratic decay in `Im w`, uniform on vertical strips, is the
rotated form of the two-integration-by-parts estimate.

## Main results

* `expTestTransform`
* `exists_expTestTransform_decay`
* `memLp_two_expTestTransform_line`
-/

open Complex MeasureTheory Set Filter

open scoped ContDiff

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The exponential transform `∫ ψ(L) e^{wL} dL` of a test function. -/
def expTestTransform (ψ : ℝ → ℂ) (w : ℂ) : ℂ := testTransform ψ (-(Complex.I * w))

theorem expTestTransform_eq (ψ : ℝ → ℂ) (w : ℂ) :
    expTestTransform ψ w = ∫ L : ℝ, ψ L * Complex.exp (w * (L : ℂ)) := by
  rw [expTestTransform, testTransform]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun L => ?_)
  have hI : Complex.I * (-(Complex.I * w)) = w := by
    linear_combination (-w) * Complex.I_sq
  rw [hI]

theorem differentiable_expTestTransform {ψ : ℝ → ℂ} (hc : Continuous ψ)
    (hs : HasCompactSupport ψ) : Differentiable ℂ (expTestTransform ψ) := by
  intro w
  have hlin : DifferentiableAt ℂ (fun v : ℂ => -(Complex.I * v)) w := by
    simpa using (differentiableAt_id.const_mul Complex.I).neg
  exact ((differentiable_testTransform hc hs) _).comp w hlin

theorem rot_re (w : ℂ) : (-(Complex.I * w)).re = w.im := by simp

theorem rot_im (w : ℂ) : (-(Complex.I * w)).im = -w.re := by simp

theorem norm_rot (w : ℂ) : ‖-(Complex.I * w)‖ = ‖w‖ := by
  rw [norm_neg, norm_mul, Complex.norm_I, one_mul]

/-- **Quadratic decay in the height, uniformly on a vertical strip.** -/
theorem exists_expTestTransform_decay {ψ : ℝ → ℂ} (hψ : ContDiff ℝ ∞ ψ)
    (hs : HasCompactSupport ψ) (c d : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w : ℂ, w.re ∈ uIcc c d →
      ‖expTestTransform ψ w‖ ≤ C / (1 + w.im ^ 2) := by
  obtain ⟨C, hC0, hC⟩ := exists_testTransform_decay hψ hs (-c) (-d)
  refine ⟨C, hC0, fun w hw => ?_⟩
  have hmem : (-(Complex.I * w)).im ∈ uIcc (-c) (-d) := by
    rw [rot_im]
    rcases Set.mem_uIcc.mp hw with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Set.mem_uIcc.mpr (Or.inr ⟨by linarith, by linarith⟩)
    · exact Set.mem_uIcc.mpr (Or.inl ⟨by linarith, by linarith⟩)
  have hb := hC _ hmem
  rw [norm_rot] at hb
  refine le_trans hb ?_
  refine div_le_div_of_nonneg_left hC0 (by positivity) ?_
  have hsq : ‖w‖ ^ 2 = w.re ^ 2 + w.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  nlinarith [sq_nonneg w.re]

theorem integrable_one_div_one_add_sq (C : ℝ) :
    Integrable (fun y : ℝ => C / (1 + y ^ 2)) := by
  simpa [div_eq_mul_inv] using (integrable_inv_one_add_sq).const_mul C

/-- The exponential transform is integrable along every vertical line. -/
theorem integrable_expTestTransform_line {ψ : ℝ → ℂ} (hψ : ContDiff ℝ ∞ ψ)
    (hs : HasCompactSupport ψ) (σ : ℝ) :
    Integrable (fun y : ℝ => expTestTransform ψ ((σ : ℂ) + (y : ℝ) * Complex.I)) := by
  obtain ⟨C, hC0, hC⟩ := exists_expTestTransform_decay hψ hs σ σ
  have hcont : Continuous (fun y : ℝ => expTestTransform ψ ((σ : ℂ) + (y : ℝ) * Complex.I)) := by
    refine ((differentiable_expTestTransform hψ.continuous hs).continuous).comp ?_
    fun_prop
  refine Integrable.mono' (integrable_one_div_one_add_sq C) hcont.aestronglyMeasurable ?_
  filter_upwards with y
  have hre : ((σ : ℂ) + (y : ℝ) * Complex.I).re = σ := by simp
  have him : ((σ : ℂ) + (y : ℝ) * Complex.I).im = y := by simp
  have hmem : ((σ : ℂ) + (y : ℝ) * Complex.I).re ∈ uIcc σ σ := by
    rw [hre]
    simp
  have h := hC _ hmem
  rw [him] at h
  exact h

/-- The exponential transform is square-integrable along every vertical line. -/
theorem memLp_two_expTestTransform_line {ψ : ℝ → ℂ} (hψ : ContDiff ℝ ∞ ψ)
    (hs : HasCompactSupport ψ) (σ : ℝ) :
    MemLp (fun y : ℝ => expTestTransform ψ ((σ : ℂ) + (y : ℝ) * Complex.I)) 2 volume := by
  obtain ⟨C, hC0, hC⟩ := exists_expTestTransform_decay hψ hs σ σ
  have hcont : Continuous (fun y : ℝ => expTestTransform ψ ((σ : ℂ) + (y : ℝ) * Complex.I)) := by
    refine ((differentiable_expTestTransform hψ.continuous hs).continuous).comp ?_
    fun_prop
  refine (memLp_two_iff_integrable_sq_norm hcont.aestronglyMeasurable).2 ?_
  refine Integrable.mono' (integrable_one_div_one_add_sq (C ^ 2)) ?_ ?_
  · exact (hcont.norm.pow 2).aestronglyMeasurable
  · filter_upwards with y
    have hre : ((σ : ℂ) + (y : ℝ) * Complex.I).re = σ := by simp
    have him : ((σ : ℂ) + (y : ℝ) * Complex.I).im = y := by simp
    have hmem : ((σ : ℂ) + (y : ℝ) * Complex.I).re ∈ uIcc σ σ := by
      rw [hre]
      simp
    have h := hC _ hmem
    rw [him] at h
    have hpos : (0 : ℝ) < 1 + y ^ 2 := by positivity
    have hnn : (0 : ℝ) ≤ ‖expTestTransform ψ ((σ : ℂ) + (y : ℝ) * Complex.I)‖ := norm_nonneg _
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have hsq : ‖expTestTransform ψ ((σ : ℂ) + (y : ℝ) * Complex.I)‖ ^ 2
        ≤ (C / (1 + y ^ 2)) ^ 2 := by
      exact pow_le_pow_left₀ hnn h 2
    refine le_trans hsq ?_
    rw [div_pow]
    refine div_le_div_of_nonneg_left (by positivity) hpos ?_
    nlinarith [sq_nonneg y]

end

end GaloisForLFunctions.HTGeometry
