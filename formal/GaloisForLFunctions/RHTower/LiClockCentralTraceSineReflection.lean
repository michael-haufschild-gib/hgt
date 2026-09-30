import GaloisForLFunctions.RHTower.LiClockCentralSineContourStability
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# The central odd-trace sine series and anti-Schwarz reality

The normalized negative trace contour selects the odd derivatives of a
regular trace, with the square of the raw odd factorial in every coefficient.
The complete series is absolutely summable at every complex clock. The trace
may have an arbitrary center value and arbitrary even Taylor coefficients.

The sine-series interchange is dominated uniformly on the circle, where
division by the coordinate is harmless. The higher Cauchy formula applies to
the regular trace itself. Global anti-Schwarz symmetry makes every selected
odd derivative real and therefore makes the contour real at every real clock.
-/

open Complex Set Metric Filter Topology MeasureTheory
open scoped ComplexConjugate

namespace RHTower
noncomputable section

/-- The raw odd derivative selected by the trace sine contour, with both factorials. -/
def liClockCentralTraceSineContourTerm (T : ℂ → ℂ) (t : ℂ) (j : ℕ) : ℂ :=
  (-1 : ℂ) ^ j * iteratedDeriv (2 * j + 1) T 0 * t ^ (2 * j + 1) /
    (((2 * j + 1).factorial : ℂ) ^ 2)

private def traceSineContourTerm (T : ℂ → ℂ) (t : ℂ) (j : ℕ) (z : ℂ) : ℂ :=
  (T z / z) * ((-1 : ℂ) ^ j * (t / z) ^ (2 * j + 1) / ((2 * j + 1).factorial : ℂ))

private theorem circleIntegral_traceSineContourTerm {r : ℝ} (hr : 0 < r) {T : ℂ → ℂ}
    (hT : DiffContOnCl ℂ T (ball 0 r)) (t : ℂ) (j : ℕ) :
    (∮ z in C(0, r), traceSineContourTerm T t j z) =
      (2 * Real.pi * I) * liClockCentralTraceSineContourTerm T t j := by
  let d : ℂ := (-1 : ℂ) ^ j * t ^ (2 * j + 1) / ((2 * j + 1).factorial : ℂ)
  have heq : traceSineContourTerm T t j =
      fun z => d * ((1 / z ^ (2 * j + 2)) * T z) := by
    funext z
    dsimp only [traceSineContourTerm, d]
    simp only [div_eq_mul_inv, one_mul, pow_succ, mul_inv_rev]
    ring
  have hC : (∮ z in C(0, r), (1 / z ^ (2 * j + 2)) * T z) =
      (2 * Real.pi * I / ((2 * j + 1).factorial : ℂ)) * iteratedDeriv (2 * j + 1) T 0 := by
    simpa only [sub_zero, smul_eq_mul, Nat.add_assoc] using
      DiffContOnCl.circleIntegral_one_div_sub_center_pow_smul hr (2 * j + 1) hT
  rw [heq, circleIntegral.integral_const_mul, hC]
  dsimp only [d, liClockCentralTraceSineContourTerm]
  simp only [div_eq_mul_inv, mul_inv_rev, pow_two]
  ring

private theorem hasSum_circleIntegral_traceSineContourTerm {r : ℝ} (hr : 0 < r)
    {T : ℂ → ℂ} (hT : DiffContOnCl ℂ T (ball 0 r)) (t : ℂ) :
    HasSum (fun j : ℕ => ∮ z in C(0, r), traceSineContourTerm T t j z)
      (∮ z in C(0, r), (T z / z) * Complex.sin (t / z)) := by
  have hTc : ContinuousOn T (sphere 0 r) :=
    hT.continuousOn_ball.mono sphere_subset_closedBall
  obtain ⟨C, hC⟩ := (isCompact_sphere (0 : ℂ) r).bddAbove_image hTc.norm
  let M : ℝ := max C 0
  have hM : 0 ≤ M := le_max_right _ _
  have hTM (z : ℂ) (hz : z ∈ sphere 0 r) : ‖T z‖ ≤ M :=
    (hC ⟨z, hz, rfl⟩).trans (le_max_left _ _)
  let x : ℝ := ‖t‖ / r
  let b : ℕ → ℝ := fun j => M * (x ^ (2 * j + 1) / ((2 * j + 1).factorial : ℝ))
  have hb : Summable b := (Real.hasSum_sinh x).summable.mul_left M
  have hterm (j : ℕ) (z : ℂ) (hz : z ∈ sphere 0 r) :
      ‖traceSineContourTerm T t j z‖ ≤
        (M / r) * (x ^ (2 * j + 1) / ((2 * j + 1).factorial : ℝ)) := by
    have hzNorm : ‖z‖ = r := by simpa only [mem_sphere_iff_norm, sub_zero] using hz
    simp only [traceSineContourTerm, norm_mul, norm_div, norm_pow, norm_neg, norm_one,
      one_pow, one_mul, Complex.norm_natCast, hzNorm]
    exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right (hTM z hz) hr.le)
      (div_nonneg (pow_nonneg (div_nonneg (norm_nonneg _) hr.le) _) (Nat.cast_nonneg _))
  have hTT : Continuous (fun θ : ℝ => T (circleMap 0 r θ) / circleMap 0 r θ) :=
    (hTc.comp_continuous (continuous_circleMap 0 r) (circleMap_mem_sphere 0 hr.le)).div
      (continuous_circleMap 0 r) (fun _ => circleMap_ne_center hr.ne')
  have hd : Continuous (fun θ : ℝ => deriv (circleMap 0 r) θ) := by
    simpa only [deriv_circleMap, Pi.mul_apply] using!
      (continuous_circleMap 0 r).mul continuous_const
  have hdiv : Continuous (fun θ : ℝ => t / circleMap 0 r θ) :=
    continuous_const.div (continuous_circleMap 0 r) (fun _ => circleMap_ne_center hr.ne')
  have hcont (j : ℕ) : Continuous (fun θ : ℝ =>
      deriv (circleMap 0 r) θ • traceSineContourTerm T t j (circleMap 0 r θ)) := by
    simpa only [traceSineContourTerm, smul_eq_mul, Pi.mul_apply, Pi.pow_apply] using!
      hd.mul (hTT.mul ((continuous_const.mul (hdiv.pow (2 * j + 1))).div_const _))
  have hbound (j : ℕ) (θ : ℝ) :
      ‖deriv (circleMap 0 r) θ • traceSineContourTerm T t j (circleMap 0 r θ)‖ ≤ b j := by
    rw [norm_smul, deriv_circleMap, norm_mul, norm_I, norm_circleMap_zero,
      abs_of_pos hr, mul_one]
    refine (mul_le_mul_of_nonneg_left
      (hterm j _ (circleMap_mem_sphere 0 hr.le θ)) hr.le).trans_eq ?_
    dsimp only [b]
    field_simp
  have hlim (θ : ℝ) : HasSum (fun j : ℕ =>
      deriv (circleMap 0 r) θ • traceSineContourTerm T t j (circleMap 0 r θ))
      (deriv (circleMap 0 r) θ •
        ((T (circleMap 0 r θ) / circleMap 0 r θ) * Complex.sin (t / circleMap 0 r θ))) := by
    simpa only [traceSineContourTerm, smul_eq_mul, mul_assoc] using
      (Complex.hasSum_sin (t / circleMap 0 r θ)).mul_left
        (deriv (circleMap 0 r) θ * (T (circleMap 0 r θ) / circleMap 0 r θ))
  exact intervalIntegral.hasSum_integral_of_dominated_convergence
    (μ := volume) (a := 0) (b := 2 * Real.pi) (fun j _ => b j)
    (fun j => (hcont j).aestronglyMeasurable)
    (fun j => Filter.Eventually.of_forall (fun θ _ => hbound j θ))
    (Filter.Eventually.of_forall (fun _ _ => hb)) intervalIntegrable_const
    (Filter.Eventually.of_forall (fun θ _ => hlim θ))

private theorem hasSum_liClockCentralTraceSineContourTerm {r : ℝ} (hr : 0 < r)
    {T : ℂ → ℂ} (hT : DiffContOnCl ℂ T (ball 0 r)) (t : ℂ) :
    HasSum (liClockCentralTraceSineContourTerm T t)
      ((2 * Real.pi * I)⁻¹ * ∮ z in C(0, r), (T z / z) * Complex.sin (t / z)) := by
  have h := (hasSum_circleIntegral_traceSineContourTerm hr hT t).congr_fun
    (fun j => (circleIntegral_traceSineContourTerm hr hT t j).symm)
  simpa only [← mul_assoc, inv_mul_cancel₀ two_pi_I_ne_zero, one_mul] using
    h.mul_left (2 * Real.pi * I)⁻¹

/-- The complete raw odd-derivative sine series is absolutely summable at every complex clock. -/
theorem summable_norm_liClockCentralTraceSineContourTerm {r : ℝ} (hr : 0 < r)
    {T : ℂ → ℂ} (hT : DiffContOnCl ℂ T (ball 0 r)) (t : ℂ) :
    Summable (fun j : ℕ => ‖liClockCentralTraceSineContourTerm T t j‖) :=
  (hasSum_liClockCentralTraceSineContourTerm hr hT t).summable.norm

/-- The complete raw odd-derivative sine series is summable at every complex clock. -/
theorem summable_liClockCentralTraceSineContourTerm {r : ℝ} (hr : 0 < r)
    {T : ℂ → ℂ} (hT : DiffContOnCl ℂ T (ball 0 r)) (t : ℂ) :
    Summable (liClockCentralTraceSineContourTerm T t) :=
  (summable_norm_liClockCentralTraceSineContourTerm hr hT t).of_norm

/-- Exact odd-derivative series for the literal normalized negative trace contour. -/
theorem liClockCentralTraceSineContour_eq_neg_tsum {r : ℝ} (hr : 0 < r)
    {T : ℂ → ℂ} (hT : DiffContOnCl ℂ T (ball 0 r)) (t : ℂ) :
    liClockCentralTraceSineContour T r t = -∑' j : ℕ, liClockCentralTraceSineContourTerm T t j := by
  rw [(hasSum_liClockCentralTraceSineContourTerm hr hT t).tsum_eq]
  have heq : (fun z : ℂ => T z * Complex.sin (t / z) / z) =
      (fun z => (T z / z) * Complex.sin (t / z)) := by
    funext z
    ring
  unfold liClockCentralTraceSineContour
  rw [heq]
  ring

private theorem iteratedDeriv_conj_conj (n : ℕ) (T : ℂ → ℂ) :
    iteratedDeriv n (conj ∘ T ∘ conj) = conj ∘ iteratedDeriv n T ∘ conj := by
  induction n with
  | zero => rfl
  | succ n ih => rw [iteratedDeriv_succ, iteratedDeriv_succ, ih, deriv_conj_conj]

private theorem odd_iteratedDeriv_conj (T : ℂ → ℂ)
    (hreflection : ∀ z : ℂ, T (-conj z) = -conj (T z)) (j : ℕ) :
    conj (iteratedDeriv (2 * j + 1) T 0) = iteratedDeriv (2 * j + 1) T 0 := by
  have href : (conj ∘ T ∘ conj) = (fun z => -T (-z)) := by
    funext z
    simpa [Function.comp_apply] using congrArg conj (hreflection (-z))
  have h := congrFun (iteratedDeriv_conj_conj (2 * j + 1) T) 0
  rw [href, iteratedDeriv_fun_neg, iteratedDeriv_comp_neg] at h
  simpa [Function.comp_apply, smul_eq_mul, pow_add, pow_mul] using h.symm

/-- Anti-Schwarz traces give a conjugation-fixed contour at every real clock. -/
theorem liClockCentralTraceSineContour_conj_ofReal {r : ℝ} (hr : 0 < r)
    {T : ℂ → ℂ} (hT : DiffContOnCl ℂ T (ball 0 r))
    (hreflection : ∀ z : ℂ, T (-conj z) = -conj (T z)) (t : ℝ) :
    conj (liClockCentralTraceSineContour T r (t : ℂ)) =
      liClockCentralTraceSineContour T r (t : ℂ) := by
  rw [liClockCentralTraceSineContour_eq_neg_tsum hr hT, map_neg, Complex.conj_tsum]
  apply congrArg Neg.neg
  apply tsum_congr
  intro j
  simp [liClockCentralTraceSineContourTerm, map_div₀, map_mul, map_pow,
    odd_iteratedDeriv_conj T hreflection]

/-- The literal trace sine contour has zero imaginary part at real clocks under anti-Schwarz symmetry. -/
theorem liClockCentralTraceSineContour_im_ofReal_eq_zero {r : ℝ} (hr : 0 < r)
    {T : ℂ → ℂ} (hT : DiffContOnCl ℂ T (ball 0 r))
    (hreflection : ∀ z : ℂ, T (-conj z) = -conj (T z)) (t : ℝ) :
    (liClockCentralTraceSineContour T r (t : ℂ)).im = 0 :=
  Complex.conj_eq_iff_im.mp (liClockCentralTraceSineContour_conj_ofReal hr hT hreflection t)

end
end RHTower
