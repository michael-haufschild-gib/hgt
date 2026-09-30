import GaloisForLFunctions.RHTower.SmoothAFEReflectedCarrierFirstMean
import GaloisForLFunctions.RHTower.SteinhausSmoothCarrierProjection

open MeasureTheory Filter
open scoped Topology

noncomputable section
namespace RHTower
open SteinhausModel

/-- Every actual smooth background vanishes in first mean, uniformly over all conditioning cutoffs. -/
theorem eventually_integral_norm_reflectedPrimalSmoothCarrier_le
    {d : ℝ} (hd : 0 < d) (hdhalf : d < 1 / 2) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ tau : ℝ, (N : ℝ) ≤ tau → ∀ r : ℝ, 0 < r → ∀ Y : ℕ,
      (∫ ω, ‖steinhausSmoothCarrier
        (smoothAFEZetaRightReflectedPrimalPositiveCoefficient d tau r N) N Y ω‖
          ∂steinhausMeasure) ≤ ε := by
  filter_upwards [eventually_integral_norm_reflectedPrimalCarrier_le hd hdhalf hε] with N hN
  intro tau htau r hr Y
  exact (integral_norm_steinhausSmoothCarrier_le _ N Y).trans (hN tau htau r hr)

/-- Finite-node background first means vanish simultaneously, with one bound for every admissible height and cutoff. -/
theorem eventually_integral_sum_norm_reflectedPrimalSmoothCarrier_le
    {J : ℕ} (d b : Fin J → ℝ) (hd : ∀ j, 0 < d j) (hdhalf : ∀ j, d j < 1 / 2)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ∀ tau : ℝ, (∀ j, (N : ℝ) ≤ tau + b j) →
      ∀ r : ℝ, 0 < r → ∀ Y : ℕ,
        (∫ ω, ∑ j, ‖steinhausSmoothCarrier
          (smoothAFEZetaRightReflectedPrimalPositiveCoefficient (d j) (tau + b j) r N)
            N Y ω‖ ∂steinhausMeasure) ≤ ε := by
  have hJ : (0 : ℝ) < J + 1 := by positivity
  have hsmall := fun j => eventually_integral_norm_reflectedPrimalSmoothCarrier_le
    (hd j) (hdhalf j) (div_pos hε hJ)
  filter_upwards [Filter.eventually_all.mpr hsmall] with N hN
  intro tau htau r hr Y
  have hi (j : Fin J) : Integrable (fun ω => ‖steinhausSmoothCarrier
      (smoothAFEZetaRightReflectedPrimalPositiveCoefficient (d j) (tau + b j) r N)
        N Y ω‖) steinhausMeasure :=
    integrable_norm_steinhausFiniteSum _ _
  rw [integral_finsetSum _ (fun j _ => hi j)]
  calc
    _ ≤ ∑ _j : Fin J, ε / ((J : ℝ) + 1) :=
      Finset.sum_le_sum (fun j _ => hN j (tau + b j) (htau j) r hr Y)
    _ = (J : ℝ) * (ε / ((J : ℝ) + 1)) := by simp
    _ ≤ ε := by
      rw [← mul_div_assoc, div_le_iff₀ hJ]
      have hJR : (0 : ℝ) ≤ J := Nat.cast_nonneg _
      nlinarith

end RHTower
