import GaloisForLFunctions.RHTower.Sieve.TypeIIDyadicBlocks

/-!
# Splitting a pair sum into its diagonal and off-diagonal parts

The type-II energy is a sum over ordered pairs.  The diagonal is trivial (the correlation is the
length of the block); every other pair carries a genuine exponential-sum bound.
-/

namespace RHTower.Sieve

open Finset ArithmeticFunction RHTower

noncomputable section

/-- **The diagonal / off-diagonal split of a pair sum.**  The corpus's
`HTGeometry.sum_pair_eq_diag_add_offDiagonal` is the `Fintype`/sigma-type form; the type-II energy
needs the `Finset`/`erase` form, since its index set is `Icc 1 L`. -/
theorem sum_pair_split (S : Finset ℕ) (F : ℕ → ℕ → ℝ) :
    (∑ m₁ ∈ S, ∑ m₂ ∈ S, F m₁ m₂)
      = (∑ m ∈ S, F m m) + ∑ m₁ ∈ S, ∑ m₂ ∈ S.erase m₁, F m₁ m₂ := by
  classical
  have hstep : ∀ m₁ ∈ S, (∑ m₂ ∈ S, F m₁ m₂)
      = F m₁ m₁ + ∑ m₂ ∈ S.erase m₁, F m₁ m₂ :=
    fun m₁ hm₁ => (Finset.add_sum_erase S (F m₁) hm₁).symm
  rw [Finset.sum_congr rfl hstep, Finset.sum_add_distrib]

/-- **The diagonal contribution of the type-II energy.** -/
theorem diag_pair_sum_le (T r : ℝ) (A B L V P Q : ℕ) :
    (∑ m ∈ Finset.Icc 1 L,
        ‖((typeIIShort V m : ℝ) : ℂ)‖ * ‖((typeIIShort V m : ℝ) : ℂ)‖
          * ‖∑ d ∈ Finset.Ico P Q,
              maskedNdExp T r A B d m * (starRingEnd ℂ) (maskedNdExp T r A B d m)‖)
      ≤ ((Q - P : ℕ) : ℝ) * ∑ m ∈ Finset.Icc 1 L, ‖((typeIIShort V m : ℝ) : ℂ)‖ ^ 2 := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun m _ => ?_
  have hcorr := norm_masked_correlation_diag_le T r A B P Q m
  have hnn : (0 : ℝ) ≤ ‖((typeIIShort V m : ℝ) : ℂ)‖ * ‖((typeIIShort V m : ℝ) : ℂ)‖ := by
    positivity
  have hid : ((Q - P : ℕ) : ℝ) * ‖((typeIIShort V m : ℝ) : ℂ)‖ ^ 2
      = (‖((typeIIShort V m : ℝ) : ℂ)‖ * ‖((typeIIShort V m : ℝ) : ℂ)‖) * ((Q - P : ℕ) : ℝ) := by
    ring
  rw [hid]
  exact mul_le_mul_of_nonneg_left hcorr hnn

end

end RHTower.Sieve
