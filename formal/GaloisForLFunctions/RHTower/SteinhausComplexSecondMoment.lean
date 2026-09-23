import GaloisForLFunctions.RHTower.SteinhausModel

/-!
# Complex-coefficient Steinhaus second moment

The foundational Steinhaus model proves its finite Parseval identity for real
coefficients.  Terminal approximate-functional-equation carriers have complex
coefficients, so this file records the same exact identity without a reality
restriction.
-/

namespace RHTower
namespace SteinhausModel

open MeasureTheory Complex

/-- **Complex-coefficient Steinhaus Parseval identity.** -/
theorem integral_dpoly_mul_conj_complex (a : ℕ → ℂ) (s : Finset ℕ)
    (hs : ∀ n ∈ s, n ≠ 0) :
    ∫ omega, (∑ n ∈ s, a n * X n omega) *
        (starRingEnd ℂ) (∑ n ∈ s, a n * X n omega) ∂steinhausMeasure =
      ((∑ n ∈ s, ‖a n‖ ^ (2 : ℕ) : ℝ) : ℂ) := by
  classical
  have hexp : ∀ omega : Omega, (∑ n ∈ s, a n * X n omega) *
      (starRingEnd ℂ) (∑ n ∈ s, a n * X n omega) =
        ∑ n ∈ s, ∑ m ∈ s,
          (a n * (starRingEnd ℂ) (a m)) *
            (X n omega * (starRingEnd ℂ) (X m omega)) := by
    intro omega
    rw [map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl (fun n hn => ?_)
    refine Finset.sum_congr rfl (fun m hm => ?_)
    rw [map_mul]
    ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hexp)]
  rw [integral_finsetSum _ (fun n _ => integrable_finsetSum _
    (fun m _ => (integrable_X_mul_conj n m).const_mul _))]
  have hinner : ∀ n ∈ s,
      ∫ omega, ∑ m ∈ s,
          (a n * (starRingEnd ℂ) (a m)) *
            (X n omega * (starRingEnd ℂ) (X m omega)) ∂steinhausMeasure =
        a n * (starRingEnd ℂ) (a n) := by
    intro n hn
    rw [integral_finsetSum _ (fun m _ => (integrable_X_mul_conj n m).const_mul _)]
    have hterm : ∀ m ∈ s,
        ∫ omega, (a n * (starRingEnd ℂ) (a m)) *
            (X n omega * (starRingEnd ℂ) (X m omega)) ∂steinhausMeasure =
          if n = m then a n * (starRingEnd ℂ) (a m) else 0 := by
      intro m hm
      rw [integral_const_mul, integral_X_mul_conj (hs n hn) (hs m hm)]
      rcases eq_or_ne n m with rfl | hne
      · rw [if_pos rfl, if_pos rfl, mul_one]
      · rw [if_neg hne, if_neg hne, mul_zero]
    rw [Finset.sum_congr rfl hterm]
    have hswap : ∀ m ∈ s,
        (if n = m then a n * (starRingEnd ℂ) (a m) else 0) =
          if m = n then a n * (starRingEnd ℂ) (a m) else 0 := by
      intro m hm
      simp only [eq_comm]
    rw [Finset.sum_congr rfl hswap, Finset.sum_ite_eq' s n
      (fun m => a n * (starRingEnd ℂ) (a m)), if_pos hn]
  rw [Finset.sum_congr rfl hinner]
  push_cast
  refine Finset.sum_congr rfl (fun n hn => ?_)
  rw [Complex.mul_conj']

/-- Norm-squared form of complex-coefficient Steinhaus Parseval. -/
theorem integral_normSq_dpoly_complex (a : ℕ → ℂ) (s : Finset ℕ)
    (hs : ∀ n ∈ s, n ≠ 0) :
    ∫ omega, ‖∑ n ∈ s, a n * X n omega‖ ^ (2 : ℕ) ∂steinhausMeasure =
      ∑ n ∈ s, ‖a n‖ ^ (2 : ℕ) := by
  have h := integral_dpoly_mul_conj_complex a s hs
  have hpoint : ∀ omega : Omega, (∑ n ∈ s, a n * X n omega) *
      (starRingEnd ℂ) (∑ n ∈ s, a n * X n omega) =
        ((‖∑ n ∈ s, a n * X n omega‖ ^ (2 : ℕ) : ℝ) : ℂ) := by
    intro omega
    rw [Complex.mul_conj']
    push_cast
    ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hpoint),
    integral_complex_ofReal] at h
  exact_mod_cast h

end SteinhausModel
end RHTower
