import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic.Ring

/-!
# Exact central circle sine transform

For a function holomorphic on a positive-radius open disk and continuous on
its closure, the central circle integral against `sin(t / z)` selects every
even Taylor derivative, with both factorials retained. The identity holds at
every complex clock and requires no parity assumption on the function.

A uniform odd-factorial envelope justifies the complete sine-series
interchange on the circle. The higher Cauchy derivative formula evaluates
each term; it applies to the regular function rather than to the sine kernel,
whose essential singularity at the center is intentional.
-/

open Complex Set Metric Filter Topology MeasureTheory

namespace RHTower
noncomputable section

/-- The even-derivative coefficient selected by the central sine contour. -/
def liClockCentralSineContourTerm (G : ℂ → ℂ) (t : ℂ) (j : ℕ) : ℂ :=
  (-1 : ℂ) ^ j * iteratedDeriv (2 * j) G 0 * t ^ (2 * j + 1) /
    (((2 * j).factorial : ℂ) * ((2 * j + 1).factorial : ℂ))

private def sineContourTerm (G : ℂ → ℂ) (t : ℂ) (j : ℕ) (z : ℂ) : ℂ :=
  G z * ((-1 : ℂ) ^ j * (t / z) ^ (2 * j + 1) / ((2 * j + 1).factorial : ℂ))

private theorem circleIntegral_sineContourTerm {r : ℝ} (hr : 0 < r) {G : ℂ → ℂ}
    (hG : DiffContOnCl ℂ G (ball 0 r)) (t : ℂ) (j : ℕ) :
    (∮ z in C(0, r), sineContourTerm G t j z) =
      (2 * Real.pi * I) * liClockCentralSineContourTerm G t j := by
  let d : ℂ := (-1 : ℂ) ^ j * t ^ (2 * j + 1) / ((2 * j + 1).factorial : ℂ)
  have heq : sineContourTerm G t j = fun z => d * ((1 / z ^ (2 * j + 1)) * G z) := by
    funext z
    dsimp only [sineContourTerm, d]
    simp only [div_eq_mul_inv, one_mul]
    ring
  have hC : (∮ z in C(0, r), (1 / z ^ (2 * j + 1)) * G z) =
      (2 * Real.pi * I / ((2 * j).factorial : ℂ)) * iteratedDeriv (2 * j) G 0 := by
    simpa only [sub_zero, smul_eq_mul] using
      DiffContOnCl.circleIntegral_one_div_sub_center_pow_smul hr (2 * j) hG
  rw [heq, circleIntegral.integral_const_mul, hC]
  dsimp only [d, liClockCentralSineContourTerm]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

private theorem hasSum_circleIntegral_sineContourTerm {r : ℝ} (hr : 0 < r) {G : ℂ → ℂ}
    (hG : DiffContOnCl ℂ G (ball 0 r)) (t : ℂ) :
    HasSum (fun j : ℕ => ∮ z in C(0, r), sineContourTerm G t j z)
      (∮ z in C(0, r), G z * Complex.sin (t / z)) := by
  have hGc : ContinuousOn G (sphere 0 r) :=
    hG.continuousOn_ball.mono sphere_subset_closedBall
  obtain ⟨C, hC⟩ := (isCompact_sphere (0 : ℂ) r).bddAbove_image hGc.norm
  let M : ℝ := max C 0
  have hM : 0 ≤ M := le_max_right _ _
  have hGM (z : ℂ) (hz : z ∈ sphere 0 r) : ‖G z‖ ≤ M :=
    (hC ⟨z, hz, rfl⟩).trans (le_max_left _ _)
  let x : ℝ := ‖t‖ / r
  let b : ℕ → ℝ := fun j => (r * M) * (x ^ (2 * j + 1) / ((2 * j + 1).factorial : ℝ))
  have hb : Summable b := (Real.hasSum_sinh x).summable.mul_left (r * M)
  have hterm (j : ℕ) (z : ℂ) (hz : z ∈ sphere 0 r) :
      ‖sineContourTerm G t j z‖ ≤ M * (x ^ (2 * j + 1) / ((2 * j + 1).factorial : ℝ)) := by
    have hzNorm : ‖z‖ = r := by simpa only [mem_sphere_iff_norm, sub_zero] using hz
    simp only [sineContourTerm, norm_mul, norm_div, norm_pow, norm_neg, norm_one,
      one_pow, one_mul, Complex.norm_natCast, hzNorm]
    exact mul_le_mul_of_nonneg_right (hGM z hz)
      (div_nonneg (pow_nonneg (div_nonneg (norm_nonneg _) hr.le) _) (Nat.cast_nonneg _))
  have hGG : Continuous (fun θ : ℝ => G (circleMap 0 r θ)) :=
    hGc.comp_continuous (continuous_circleMap 0 r) (circleMap_mem_sphere 0 hr.le)
  have hd : Continuous (fun θ : ℝ => deriv (circleMap 0 r) θ) := by
    simpa only [deriv_circleMap, Pi.mul_apply] using!
      (continuous_circleMap 0 r).mul continuous_const
  have hdiv : Continuous (fun θ : ℝ => t / circleMap 0 r θ) :=
    continuous_const.div (continuous_circleMap 0 r) (fun _ => circleMap_ne_center hr.ne')
  have hcont (j : ℕ) : Continuous (fun θ : ℝ =>
      deriv (circleMap 0 r) θ • sineContourTerm G t j (circleMap 0 r θ)) := by
    simpa only [sineContourTerm, smul_eq_mul, Pi.mul_apply, Pi.pow_apply] using!
      hd.mul (hGG.mul ((continuous_const.mul (hdiv.pow (2 * j + 1))).div_const _))
  have hbound (j : ℕ) (θ : ℝ) :
      ‖deriv (circleMap 0 r) θ • sineContourTerm G t j (circleMap 0 r θ)‖ ≤ b j := by
    rw [norm_smul, deriv_circleMap, norm_mul, norm_I, norm_circleMap_zero,
      abs_of_pos hr, mul_one]
    exact (mul_le_mul_of_nonneg_left
      (hterm j _ (circleMap_mem_sphere 0 hr.le θ)) hr.le).trans_eq (by dsimp only [b]; ring)
  have hlim (θ : ℝ) : HasSum (fun j : ℕ =>
      deriv (circleMap 0 r) θ • sineContourTerm G t j (circleMap 0 r θ))
      (deriv (circleMap 0 r) θ • (G (circleMap 0 r θ) * Complex.sin (t / circleMap 0 r θ))) := by
    simpa only [sineContourTerm, smul_eq_mul, mul_assoc] using
      (Complex.hasSum_sin (t / circleMap 0 r θ)).mul_left
        (deriv (circleMap 0 r) θ * G (circleMap 0 r θ))
  exact intervalIntegral.hasSum_integral_of_dominated_convergence
    (μ := volume) (a := 0) (b := 2 * Real.pi) (fun j _ => b j)
    (fun j => (hcont j).aestronglyMeasurable)
    (fun j => Filter.Eventually.of_forall (fun θ _ => hbound j θ))
    (Filter.Eventually.of_forall (fun _ _ => hb)) intervalIntegrable_const
    (Filter.Eventually.of_forall (fun θ _ => hlim θ))

private theorem hasSum_liClockCentralSineContourTerm {r : ℝ} (hr : 0 < r) {G : ℂ → ℂ}
    (hG : DiffContOnCl ℂ G (ball 0 r)) (t : ℂ) :
    HasSum (liClockCentralSineContourTerm G t)
      ((2 * Real.pi * I)⁻¹ * ∮ z in C(0, r), G z * Complex.sin (t / z)) := by
  have h := (hasSum_circleIntegral_sineContourTerm hr hG t).congr_fun
    (fun j => (circleIntegral_sineContourTerm hr hG t j).symm)
  simpa only [← mul_assoc, inv_mul_cancel₀ two_pi_I_ne_zero, one_mul] using
    h.mul_left (2 * Real.pi * I)⁻¹

/-- The complete central sine-transform series is absolutely summable at every complex clock. -/
theorem summable_norm_liClockCentralSineContourTerm {r : ℝ} (hr : 0 < r) {G : ℂ → ℂ}
    (hG : DiffContOnCl ℂ G (ball 0 r)) (t : ℂ) :
    Summable (fun j : ℕ => ‖liClockCentralSineContourTerm G t j‖) :=
  (hasSum_liClockCentralSineContourTerm hr hG t).summable.norm

/-- The complete central sine-transform series is summable at every complex clock. -/
theorem summable_liClockCentralSineContourTerm {r : ℝ} (hr : 0 < r) {G : ℂ → ℂ}
    (hG : DiffContOnCl ℂ G (ball 0 r)) (t : ℂ) :
    Summable (liClockCentralSineContourTerm G t) :=
  (summable_norm_liClockCentralSineContourTerm hr hG t).of_norm

/-- The positively oriented central circle sine transform selects all even derivatives exactly. -/
theorem liClockCentralSineContour_eq_tsum {r : ℝ} (hr : 0 < r) {G : ℂ → ℂ}
    (hG : DiffContOnCl ℂ G (ball 0 r)) (t : ℂ) :
    (∮ z in C(0, r), G z * Complex.sin (t / z)) =
      (2 * Real.pi * I) * ∑' j : ℕ, liClockCentralSineContourTerm G t j := by
  rw [(hasSum_liClockCentralSineContourTerm hr hG t).tsum_eq]
  simp only [← mul_assoc, mul_inv_cancel₀ two_pi_I_ne_zero, one_mul]

end
end RHTower
