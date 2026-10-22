import GaloisForLFunctions.RHTower.Suzuki.SuzukiGammaWallTailEstimate
import GaloisForLFunctions.RHTower.StripPropagatorLineDecay

/-!
# The transported remaining amplitude is a Hardy density

The integral surviving two integrations by parts carries the quadratically decaying amplitude
`(1+t)^{-2}` against the inverse Gamma propagator, whose growth is `(1+t)^{p}` with `p = 1/2 + σ`.
Written in the normalization of the weighted Hardy inequality — that is, after removing the factor
`t^{p-1}` under the integral — the resulting density is

`t^{1-p}(1+t)^{p}(1+t)^{-2} ≤ (1+t)^{p}t^{-1-p}`,

because `t^(2 : ℕ) ≤ (1+t)^(2 : ℕ)`.  The right side is exactly the Hardy density of the terminal ray, whose
square is integrable for every `p > 1/2`.  So the growth of the inverse propagator is entirely
absorbed, and the three separate regimes `p < 1`, `p = 1`, `p > 1` of the classical computation never
appear.
-/

open MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace GaloisForLFunctions.RHTower

/-- The scalar bridge: a quadratically decaying amplitude, transported by the inverse propagator and
rescaled to the Hardy normalization, is dominated by the Hardy density. -/
theorem hardyRescale_le_wallTailDensity {p t : ℝ} (ht : 1 < t) :
    t ^ (1 - p) * ((1 + t)⁻¹) ^ 2 * (1 + t) ^ p ≤ wallTailDensity p t := by
  have ht0 : (0 : ℝ) < t := lt_trans zero_lt_one ht
  have h1t : (0 : ℝ) < 1 + t := by linarith
  have hsplit : t ^ (1 - p) = t ^ (-1 - p) * t ^ (2 : ℝ) := by
    rw [← Real.rpow_add ht0]
    congr 1
    ring
  have hsq : ((1 + t)⁻¹) ^ 2 = ((1 + t) ^ (2 : ℝ))⁻¹ := by
    rw [Real.rpow_two, ← inv_pow]
  have hratio : t ^ (2 : ℝ) * ((1 + t) ^ (2 : ℝ))⁻¹ ≤ 1 := by
    rw [Real.rpow_two, Real.rpow_two]
    rw [mul_inv_le_iff₀ (by positivity), one_mul]
    nlinarith [ht0]
  have hpnn : (0 : ℝ) ≤ (1 + t) ^ p := Real.rpow_nonneg h1t.le _
  have hnn : (0 : ℝ) ≤ t ^ (-1 - p) := Real.rpow_nonneg ht0.le _
  calc t ^ (1 - p) * ((1 + t)⁻¹) ^ 2 * (1 + t) ^ p
      = (1 + t) ^ p * (t ^ (-1 - p) * (t ^ (2 : ℝ) * ((1 + t) ^ (2 : ℝ))⁻¹)) := by
        rw [hsplit, hsq]; ring
    _ ≤ (1 + t) ^ p * (t ^ (-1 - p) * 1) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hratio hnn) hpnn
    _ = wallTailDensity p t := by rw [wallTailDensity]; ring

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]
  [Nontrivial X]

variable {E : ℂ → ℂ} {T : X →L[ℂ] X}

omit [Nontrivial X] in
/-- **The transported amplitude obeys the Hardy density bound.**  A remaining amplitude decaying
like `(1+t)^{-2}` — the size supplied by the two-fold integration by parts — becomes, after transport
by the inverse Gamma propagator and rescaling by `t^{1-p}`, a density dominated by `wallTailDensity`,
whose square is integrable on the terminal ray for every `p > 1/2`. -/
theorem norm_hardyRescaled_transport_le {σ : ℝ} {K₂ a : ℝ} (hK₂ : 0 ≤ K₂)
    (hb₂ : ∀ x : ℝ, ‖stripPropagatorInv E T ((x : ℂ) + (σ : ℂ) * Complex.I)‖
      ≤ K₂ * (1 + |x|) ^ (1 / 2 + σ))
    {A : ℝ → X} (hA : ∀ t : ℝ, 1 < t → ‖A t‖ ≤ a * ((1 + t)⁻¹) ^ 2)
    {t : ℝ} (ht : 1 < t) :
    ‖(t ^ (1 - (1 / 2 + σ)) : ℝ) •
        stripPropagatorInv E T ((t : ℂ) + (σ : ℂ) * Complex.I) (A t)‖
      ≤ (K₂ * a) * wallTailDensity (1 / 2 + σ) t := by
  set p : ℝ := 1 / 2 + σ with hpdef
  have ht0 : (0 : ℝ) < t := lt_trans zero_lt_one ht
  have habs : |t| = t := abs_of_pos ht0
  have hanb : 0 ≤ a := by
    have h0 := le_trans (norm_nonneg _) (hA t ht)
    have hw : (0 : ℝ) < ((1 + t)⁻¹) ^ 2 := by positivity
    nlinarith [hw]
  have hrpow : (0 : ℝ) ≤ t ^ (1 - p) := Real.rpow_nonneg ht0.le _
  have hop : ‖stripPropagatorInv E T ((t : ℂ) + (σ : ℂ) * Complex.I) (A t)‖
      ≤ (K₂ * (1 + t) ^ p) * (a * ((1 + t)⁻¹) ^ 2) := by
    have h1 : ‖stripPropagatorInv E T ((t : ℂ) + (σ : ℂ) * Complex.I) (A t)‖
        ≤ ‖stripPropagatorInv E T ((t : ℂ) + (σ : ℂ) * Complex.I)‖ * ‖A t‖ :=
      ContinuousLinearMap.le_opNorm _ _
    have h2 : ‖stripPropagatorInv E T ((t : ℂ) + (σ : ℂ) * Complex.I)‖ ≤ K₂ * (1 + t) ^ p := by
      have := hb₂ t
      rwa [habs] at this
    exact h1.trans (mul_le_mul h2 (hA t ht) (norm_nonneg _) (by positivity))
  calc ‖(t ^ (1 - p) : ℝ) • stripPropagatorInv E T ((t : ℂ) + (σ : ℂ) * Complex.I) (A t)‖
      = t ^ (1 - p) * ‖stripPropagatorInv E T ((t : ℂ) + (σ : ℂ) * Complex.I) (A t)‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hrpow]
    _ ≤ t ^ (1 - p) * ((K₂ * (1 + t) ^ p) * (a * ((1 + t)⁻¹) ^ 2)) :=
        mul_le_mul_of_nonneg_left hop hrpow
    _ = (K₂ * a) * (t ^ (1 - p) * ((1 + t)⁻¹) ^ 2 * (1 + t) ^ p) := by ring
    _ ≤ (K₂ * a) * wallTailDensity p t :=
        mul_le_mul_of_nonneg_left (hardyRescale_le_wallTailDensity ht) (by positivity)

end GaloisForLFunctions.RHTower
