import GaloisForLFunctions.RHTower.Sieve.TypeIIFibreCorrelation
import GaloisForLFunctions.RHTower.Sieve.ZetaConvolutionTypeI

/-!
# The type-II form of a convolution over a block

Masking the summand by the fibre indicator turns the coupled double sum produced by the
convolution rearrangement into an honest product-shaped bilinear form, to which Cauchy--Schwarz
and the correlation expansion apply unchanged.
-/

namespace RHTower.Sieve

open Finset RHTower

noncomputable section

theorem ndPhaseExp_eq_ndExp_comm (T r : ℝ) (d m : ℕ) :
    ndPhaseExp T r (d * m) = ndExp T r m d := by
  rw [ndPhaseExp, ndExp]
  congr 2
  push_cast
  ring

/-- **The coupled double sum is a masked bilinear form.** -/
theorem sum_typeII_masked_eq {A B L : ℕ} (hA : 1 ≤ A) (hB : 1 ≤ B) (T r : ℝ) (f g : ℕ → ℂ) :
    (∑ p ∈ (Finset.Icc 1 L ×ˢ Finset.Icc 1 L).filter (fun p => p.1 * p.2 ∈ Finset.Ico A B),
        f p.1 * g p.2 * ndPhaseExp T r (p.1 * p.2))
      = ∑ d ∈ Finset.Icc 1 L, f d * ∑ m ∈ Finset.Icc 1 L, g m * maskedNdExp T r A B d m := by
  classical
  rw [Finset.sum_filter, Finset.sum_product]
  refine Finset.sum_congr rfl fun d hd => ?_
  rw [Finset.mem_Icc] at hd
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [maskedNdExp]
  by_cases hmem : m ∈ fibreIco A B d
  · have hprod : d * m ∈ Finset.Ico A B := by
      rw [fibreIco] at hmem
      have := (mem_fibre_iff hd.1 hA hB m).2 hmem
      rwa [Nat.mul_comm] at this
    rw [if_pos hmem, if_pos hprod, ndPhaseExp_eq_ndExp_comm]
    ring
  · have hprod : d * m ∉ Finset.Ico A B := by
      intro hcon
      refine hmem ?_
      rw [fibreIco]
      refine (mem_fibre_iff hd.1 hA hB m).1 ?_
      rwa [Nat.mul_comm]
    rw [if_neg hmem, if_neg hprod]
    ring

/-- **The masked type-II energy bound.** -/
theorem norm_typeII_masked_sq_le (T r : ℝ) (A B P Q : ℕ) (Ms : Finset ℕ) (a b : ℕ → ℂ) :
    ‖∑ d ∈ Finset.Ico P Q, a d * ∑ m ∈ Ms, b m * maskedNdExp T r A B d m‖ ^ 2
      ≤ (∑ d ∈ Finset.Ico P Q, ‖a d‖ ^ 2)
        * ∑ m₁ ∈ Ms, ∑ m₂ ∈ Ms, ‖b m₁‖ * ‖b m₂‖
            * ‖∑ d ∈ Finset.Ico P Q,
                maskedNdExp T r A B d m₁ * (starRingEnd ℂ) (maskedNdExp T r A B d m₂)‖ := by
  refine le_trans (norm_bilinear_sq_le (Finset.Ico P Q) a
    (fun d => ∑ m ∈ Ms, b m * maskedNdExp T r A B d m)) ?_
  refine mul_le_mul_of_nonneg_left ?_ (Finset.sum_nonneg fun d _ => sq_nonneg _)
  exact sum_normSq_inner_le (Finset.Ico P Q) Ms b (fun d m => maskedNdExp T r A B d m)

end

end RHTower.Sieve
