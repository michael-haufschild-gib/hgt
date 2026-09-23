import GaloisForLFunctions.RHTower.Sieve.VaughanTypeIIEstimate

/-!
# The von Mangoldt block sum against the near-diagonal phase

Vaughan's identity plus the three estimates of the previous files give a single bound for
`Σ_{n ∈ [A,B)} Λ(n)·e(F_{T,r}(n))` on a block above the truncation: two explicit type-I totals and
the square root of a type-II energy.  Everything after this point is optimisation.
-/

namespace RHTower.Sieve

open Finset ArithmeticFunction RHTower

noncomputable section

/-- The type-II energy of the block. -/
def typeIIEnergy (T r : ℝ) (A B L U V : ℕ) : ℝ :=
  (∑ d ∈ Finset.Ico 1 (L + 1), ‖((typeIILong U d : ℝ) : ℂ)‖ ^ (2 : ℕ))
    * ∑ m₁ ∈ Finset.Icc 1 L, ∑ m₂ ∈ Finset.Icc 1 L,
        ‖((typeIIShort V m₁ : ℝ) : ℂ)‖ * ‖((typeIIShort V m₂ : ℝ) : ℂ)‖
          * ‖∑ d ∈ Finset.Ico 1 (L + 1),
              maskedNdExp T r A B d m₁ * (starRingEnd ℂ) (maskedNdExp T r A B d m₂)‖

theorem typeIIEnergy_nonneg (T r : ℝ) (A B L U V : ℕ) : 0 ≤ typeIIEnergy T r A B L U V := by
  rw [typeIIEnergy]
  refine mul_nonneg (Finset.sum_nonneg fun d _ => sq_nonneg _) ?_
  refine Finset.sum_nonneg fun m₁ _ => Finset.sum_nonneg fun m₂ _ => ?_
  positivity

/-- **The von Mangoldt block estimate.** -/
theorem norm_sum_vonMangoldt_ndPhaseExp_le {T r : ℝ} (hT : 0 < T) (hr : 0 < r)
    {U V A B L : ℕ} (hUA : U < A) (hA : 1 ≤ A) (hB : 1 ≤ B) (hBL : B - 1 ≤ L)
    (hcond : ∀ b ∈ Finset.Icc 1 L,
      r / b ≤ (((A - 1) / b + 1 : ℕ) : ℝ)
        ∧ nearDiagonalLambda T (r / b) ((((A - 1) / b + 1 : ℕ)) : ℝ) ≤ 1) :
    ‖∑ n ∈ Finset.Ico A B, ((vonMangoldt n : ℝ) : ℂ) * ndPhaseExp T r n‖
      ≤ (∑ b ∈ Finset.Icc 1 L, Real.log b * fibreBound T r A B b)
        + (∑ b ∈ Finset.Icc 1 L,
            2 * fibreBound T r A B b * Real.log ((((B - 1) / b + 1 - 1 : ℕ)) : ℝ))
        + Real.sqrt (typeIIEnergy T r A B L U V) := by
  rw [sum_vonMangoldt_block_decomp (V := V) hUA (ndPhaseExp T r)]
  refine le_trans (norm_add_le _ _) ?_
  refine add_le_add (le_trans (norm_add_le _ _) (add_le_add ?_ ?_)) ?_
  · rw [norm_neg]
    exact norm_zeta_piece_le hT hr hA hB hBL hcond
  · exact norm_log_piece_le hT hr hA hB hBL hcond
  · have hsq := norm_typeII_piece_sq_le hA hB hBL T r U V
    have hnn : (0 : ℝ) ≤ ‖∑ n ∈ Finset.Ico A B,
        (((typeIILong U * typeIIShort V) n : ℝ) : ℂ) * ndPhaseExp T r n‖ := norm_nonneg _
    have hmono := Real.sqrt_le_sqrt hsq
    rw [Real.sqrt_sq hnn] at hmono
    exact hmono

end

end RHTower.Sieve
