import Mathlib

/-!
# A one-sided ceiling bounds the variance of a skew-free distribution

If `f ≤ M` almost surely under a probability measure, then pointwise `(M - f)(M + f)² ≥ 0`.
Integrating gives `M ∫f² + ∫f³ ≤ M³ + M² ∫f` (`mul_integral_sq_add_integral_cube_le`).  For a
centred, skew-free `f` (`∫f = 0`, `∫f³ = 0`) this is `∫f² ≤ M²` (`integral_sq_le_sq_of_skew_free`).
Equality holds only for the two-point law `±M`.

So a centred symmetric fluctuation whose standard deviation reaches the ceiling `M` must cross it
unless it is exactly two-valued.  A one-sided ceiling on a skew-free fluctuation caps its variance
at the square of the ceiling.
-/

open MeasureTheory

namespace GaloisForLFunctions.HTGeometry

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- **One-sided ceiling inequality.**  If `f ≤ M` almost everywhere for a probability measure `μ`,
then `M ∫f² + ∫f³ ≤ M³ + M² ∫f`.  Integrate `(M - f)(M + f)² ≥ 0`. -/
theorem mul_integral_sq_add_integral_cube_le [IsProbabilityMeasure μ] {f : Ω → ℝ} {M : ℝ}
    (hle : ∀ᵐ ω ∂μ, f ω ≤ M) (hf1 : Integrable f μ)
    (hf2 : Integrable (fun ω => f ω ^ 2) μ) (hf3 : Integrable (fun ω => f ω ^ 3) μ) :
    M * ∫ ω, f ω ^ 2 ∂μ + ∫ ω, f ω ^ 3 ∂μ ≤ M ^ 3 + M ^ 2 * ∫ ω, f ω ∂μ := by
  have hpt : ∀ ω, (M - f ω) * (M + f ω) ^ 2 =
      M ^ 3 + M ^ 2 * f ω - M * f ω ^ 2 - f ω ^ 3 := fun ω => by ring
  have hnonneg : 0 ≤ ∫ ω, (M - f ω) * (M + f ω) ^ 2 ∂μ := by
    refine integral_nonneg_of_ae ?_
    filter_upwards [hle] with ω hω
    exact mul_nonneg (by linarith) (sq_nonneg _)
  have hA : Integrable (fun ω => M ^ 3 + M ^ 2 * f ω) μ :=
    (integrable_const _).add (hf1.const_mul _)
  have hB : Integrable (fun ω => M ^ 3 + M ^ 2 * f ω - M * f ω ^ 2) μ :=
    hA.sub (hf2.const_mul _)
  have hexp : ∫ ω, (M - f ω) * (M + f ω) ^ 2 ∂μ =
      M ^ 3 + M ^ 2 * (∫ ω, f ω ∂μ) - M * (∫ ω, f ω ^ 2 ∂μ) - ∫ ω, f ω ^ 3 ∂μ := by
    simp_rw [hpt]
    rw [integral_sub hB hf3, integral_sub hA (hf2.const_mul _),
      integral_add (integrable_const _) (hf1.const_mul _), integral_const, integral_const_mul,
      integral_const_mul]
    simp
  rw [hexp] at hnonneg
  linarith

/-- **Skew-free variance ceiling.**  If `f ≤ M` almost everywhere, `∫f = 0` and `∫f³ = 0` under a
probability measure, then `∫f² ≤ M²`. -/
theorem integral_sq_le_sq_of_skew_free [IsProbabilityMeasure μ] {f : Ω → ℝ} {M : ℝ}
    (hle : ∀ᵐ ω ∂μ, f ω ≤ M) (hf1 : Integrable f μ)
    (hf2 : Integrable (fun ω => f ω ^ 2) μ) (hf3 : Integrable (fun ω => f ω ^ 3) μ)
    (hmean : ∫ ω, f ω ∂μ = 0) (hskew : ∫ ω, f ω ^ 3 ∂μ = 0) :
    ∫ ω, f ω ^ 2 ∂μ ≤ M ^ 2 := by
  have h := mul_integral_sq_add_integral_cube_le hle hf1 hf2 hf3
  rw [hmean, hskew] at h
  have hV : 0 ≤ ∫ ω, f ω ^ 2 ∂μ := integral_nonneg fun ω => sq_nonneg _
  have hM : 0 ≤ M := by
    have := integral_mono_ae hf1 (integrable_const M) hle
    rw [hmean, integral_const] at this
    simpa using this
  rcases hM.eq_or_lt with h0 | hpos
  · -- `M = 0`: then `f ≤ 0` with mean zero, so `f = 0` almost everywhere
    subst h0
    have hfz : f =ᵐ[μ] 0 := by
      have hnn : 0 ≤ᵐ[μ] fun ω => -f ω := by
        filter_upwards [hle] with ω hω
        simp only [Pi.zero_apply]
        linarith
      have hint : ∫ ω, -f ω ∂μ = 0 := by rw [integral_neg, hmean, neg_zero]
      have := (integral_eq_zero_iff_of_nonneg_ae hnn hf1.neg).mp hint
      filter_upwards [this] with ω hω
      simp only [Pi.zero_apply] at hω ⊢
      linarith
    have hsq : (fun ω => f ω ^ 2) =ᵐ[μ] fun _ => (0 : ℝ) :=
      hfz.mono fun ω hω => by
        simp only [Pi.zero_apply] at hω
        show f ω ^ 2 = 0
        rw [hω]
        norm_num
    have : ∫ ω, f ω ^ 2 ∂μ = 0 := by
      rw [integral_congr_ae hsq, integral_zero]
    rw [this]
    norm_num
  · nlinarith

end GaloisForLFunctions.HTGeometry
