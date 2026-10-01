import GaloisForLFunctions.RHTower.BohrMoments
import GaloisForLFunctions.RHTower.SteinhausComplexSecondMoment

open Complex MeasureTheory Finset
noncomputable section
namespace RHTower
open SteinhausModel

/-- Literal multiplicative convolution of two finite complex coefficient families. -/
def dpolyComplexConv (a b : ℕ → ℂ) (S T : Finset ℕ) (k : ℕ) : ℂ :=
  ∑ q ∈ (S ×ˢ T).filter (fun q => q.1 * q.2 = k), a q.1 * b q.2

/-- Products of complex Steinhaus polynomials group by their actual integer
frequencies, with all multiplicative collisions retained. -/
theorem model_mul_complex (a b : ℕ → ℂ) (S T : Finset ℕ)
    (hS : ∀ n ∈ S, n ≠ 0) (hT : ∀ n ∈ T, n ≠ 0) (ω : Omega) :
    (∑ n ∈ S, a n * X n ω) * (∑ n ∈ T, b n * X n ω) =
      ∑ k ∈ prodSupport S T, dpolyComplexConv a b S T k * X k ω := by
  classical
  rw [sum_mul_sum, ← sum_product']
  have hmap : ∀ q ∈ S ×ˢ T, q.1 * q.2 ∈ prodSupport S T := fun q hq =>
    mem_image.mpr ⟨q, hq, rfl⟩
  rw [← sum_fiberwise_of_maps_to hmap
    (fun q => (a q.1 * X q.1 ω) * (b q.2 * X q.2 ω))]
  apply sum_congr rfl
  intro k _
  rw [dpolyComplexConv, sum_mul]
  apply sum_congr rfl
  intro q hq
  obtain ⟨⟨hqS, hqT⟩, hprod⟩ := (show (q.1 ∈ S ∧ q.2 ∈ T) ∧ q.1 * q.2 = k by
    simpa only [mem_filter, mem_product] using hq)
  rw [← hprod, X_mul (hS q.1 hqS) (hT q.2 hqT)]
  ring

/-- The actual product-weighted second moment is exactly the convolution
coefficient energy, for arbitrary complex finite coefficient families. -/
theorem integral_normSq_product_steinhaus_eq_convolution
    (a b : ℕ → ℂ) (S T : Finset ℕ)
    (hS : ∀ n ∈ S, n ≠ 0) (hT : ∀ n ∈ T, n ≠ 0) :
    (∫ ω, ‖∑ n ∈ S, a n * X n ω‖ ^ 2 *
      ‖∑ n ∈ T, b n * X n ω‖ ^ 2 ∂steinhausMeasure) =
        ∑ k ∈ prodSupport S T, ‖dpolyComplexConv a b S T k‖ ^ 2 := by
  have hprod (ω : Omega) : ‖∑ n ∈ S, a n * X n ω‖ ^ 2 *
      ‖∑ n ∈ T, b n * X n ω‖ ^ 2 =
      ‖∑ k ∈ prodSupport S T, dpolyComplexConv a b S T k * X k ω‖ ^ 2 := by
    rw [← model_mul_complex a b S T hS hT ω, norm_mul, mul_pow]
  rw [integral_congr_ae (Filter.Eventually.of_forall hprod)]
  apply integral_normSq_dpoly_complex
  intro k hk
  obtain ⟨q, hq, rfl⟩ := mem_image.mp hk
  exact Nat.mul_ne_zero (hS q.1 (mem_product.mp hq).1) (hT q.2 (mem_product.mp hq).2)

end RHTower
