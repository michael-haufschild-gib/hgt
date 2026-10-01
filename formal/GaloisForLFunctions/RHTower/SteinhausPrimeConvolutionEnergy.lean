import GaloisForLFunctions.RHTower.SteinhausComplexConvolution
import GaloisForLFunctions.RHTower.Sieve.RamareLadderErrorSharp

open Complex MeasureTheory Finset
noncomputable section
namespace RHTower
open SteinhausModel Sieve

private theorem norm_sum_sq_le_card_sum_sq {ι : Type*} (F : Finset ι) (b : ι → ℂ) :
    ‖∑ i ∈ F, b i‖ ^ 2 ≤ (F.card : ℝ) * ∑ i ∈ F, ‖b i‖ ^ 2 := by
  have htri := norm_sum_le F b
  have hcs := sum_mul_sq_le_sq_mul_sq F (fun _ => (1 : ℝ)) (fun i => ‖b i‖)
  have hs : (∑ i ∈ F, ‖b i‖) ^ 2 ≤ (F.card : ℝ) * ∑ i ∈ F, ‖b i‖ ^ 2 := by
    simpa only [one_mul, one_pow, sum_const, nsmul_eq_mul, mul_one] using hcs
  exact (pow_le_pow_left₀ (norm_nonneg _) htri 2).trans hs

/-- Each convolution coefficient has at most one representation per selected
prime divisor, regardless of the cofactor support. -/
theorem card_primeConvolution_fibre_le (P S : Finset ℕ)
    (hP : ∀ p ∈ P, Nat.Prime p) (k : ℕ) :
    ((P ×ˢ S).filter (fun q => q.1 * q.2 = k)).card ≤ (primeFactorsIn P k).card := by
  classical
  apply card_le_card_of_injOn (fun q : ℕ × ℕ => q.1)
  · intro q hq
    obtain ⟨hqPS, hprod⟩ := mem_filter.mp hq
    exact mem_primeFactorsIn.mpr ⟨(mem_product.mp hqPS).1, ⟨q.2, hprod.symm⟩⟩
  · intro q hq z hz hqz
    change q.1 = z.1 at hqz
    have hprod := (mem_filter.mp hq).2.trans (mem_filter.mp hz).2.symm
    rw [← hqz] at hprod
    exact Prod.ext hqz (Nat.eq_of_mul_eq_mul_left
      (hP q.1 (mem_product.mp (mem_filter.mp hq).1).1).pos hprod)

/-- Multiplication by a prime polynomial costs at most one extra selected
prime divisor in the exact complex convolution energy. -/
theorem sum_normSq_primeConvolution_le_occupation
    (P S : Finset ℕ) (v a : ℕ → ℂ) (hP : ∀ p ∈ P, Nat.Prime p) :
    (∑ k ∈ prodSupport P S, ‖dpolyComplexConv v a P S k‖ ^ 2) ≤
      (∑ p ∈ P, ‖v p‖ ^ 2) *
        ∑ n ∈ S, (1 + ((primeFactorsIn P n).card : ℝ)) * ‖a n‖ ^ 2 := by
  classical
  have hpoint (k : ℕ) : ‖dpolyComplexConv v a P S k‖ ^ 2 ≤
      ((primeFactorsIn P k).card : ℝ) *
        ∑ q ∈ (P ×ˢ S).filter (fun q => q.1 * q.2 = k), ‖v q.1 * a q.2‖ ^ 2 := by
    have h := norm_sum_sq_le_card_sum_sq ((P ×ˢ S).filter (fun q => q.1 * q.2 = k))
      (fun q => v q.1 * a q.2)
    have hc : (((P ×ˢ S).filter (fun q => q.1 * q.2 = k)).card : ℝ) ≤
        (primeFactorsIn P k).card := by exact_mod_cast card_primeConvolution_fibre_le P S hP k
    exact h.trans (mul_le_mul_of_nonneg_right hc (sum_nonneg (fun _ _ => sq_nonneg _)))
  have hmap : ∀ q ∈ P ×ˢ S, q.1 * q.2 ∈ prodSupport P S := fun q hq =>
    mem_image.mpr ⟨q, hq, rfl⟩
  calc
    _ ≤ ∑ k ∈ prodSupport P S, ((primeFactorsIn P k).card : ℝ) *
        ∑ q ∈ (P ×ˢ S).filter (fun q => q.1 * q.2 = k), ‖v q.1 * a q.2‖ ^ 2 :=
      sum_le_sum (fun k _ => hpoint k)
    _ = ∑ q ∈ P ×ˢ S, ((primeFactorsIn P (q.1 * q.2)).card : ℝ) * ‖v q.1 * a q.2‖ ^ 2 := by
      rw [← sum_fiberwise_of_maps_to hmap
        (fun q => ((primeFactorsIn P (q.1 * q.2)).card : ℝ) * ‖v q.1 * a q.2‖ ^ 2)]
      apply sum_congr rfl
      intro k _
      rw [mul_sum]
      apply sum_congr rfl
      intro q hq
      rw [(mem_filter.mp hq).2]
    _ ≤ ∑ q ∈ P ×ˢ S, (1 + ((primeFactorsIn P q.2).card : ℝ)) * ‖v q.1 * a q.2‖ ^ 2 := by
      apply sum_le_sum
      intro q hq
      have h := card_primeFactorsIn_mul_le hP (hP q.1 (mem_product.mp hq).1) q.2
      have hr : ((primeFactorsIn P (q.1 * q.2)).card : ℝ) ≤
          1 + (primeFactorsIn P q.2).card := by exact_mod_cast (by omega :
            (primeFactorsIn P (q.1 * q.2)).card ≤ 1 + (primeFactorsIn P q.2).card)
      exact mul_le_mul_of_nonneg_right hr (sq_nonneg _)
    _ = _ := by
      rw [sum_product]
      simp_rw [norm_mul, mul_pow, mul_sum, sum_mul]
      rw [sum_comm]
      apply sum_congr rfl
      intro p _
      apply sum_congr rfl
      intro n _
      ring

/-- Actual original-law density-weighted second moment, with the precise
selected prime occupation cost and no independence assumption on the density. -/
theorem integral_normSq_primePoly_mul_density_le_occupation
    (P S : Finset ℕ) (v a : ℕ → ℂ) (hP : ∀ p ∈ P, Nat.Prime p)
    (hS : ∀ n ∈ S, n ≠ 0) :
    (∫ ω, ‖∑ p ∈ P, v p * X p ω‖ ^ 2 *
      ‖∑ n ∈ S, a n * X n ω‖ ^ 2 ∂steinhausMeasure) ≤
      (∑ p ∈ P, ‖v p‖ ^ 2) *
        ∑ n ∈ S, (1 + ((primeFactorsIn P n).card : ℝ)) * ‖a n‖ ^ 2 := by
  rw [integral_normSq_product_steinhaus_eq_convolution v a P S
    (fun p hp => (hP p hp).ne_zero) hS]
  exact sum_normSq_primeConvolution_le_occupation P S v a hP

end RHTower
