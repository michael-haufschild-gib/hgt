import GaloisForLFunctions.RHTower.Sieve.TypeIIBlockSwapBound

/-!
# The two per-block energy bounds, with the coefficient energies inserted

Both orientations of the block form reduce to the same three factors: the coefficient energy of
the variable Cauchy--Schwarz was applied to, the coefficient energy of the other variable over the
range that actually contributes, and the gap sum of the correlation bound.
-/

namespace RHTower.Sieve

open Finset ArithmeticFunction RHTower

noncomputable section

/-- **The block form, estimated through the long variable.** -/
theorem norm_maskedBlockSum_sq_le_bound {T r : ℝ} (hT : 0 < T) (hr : 0 < r)
    {A B L P Q : ℕ} (hA : 1 ≤ A) (hB : 1 ≤ B) (hP : 1 ≤ P) (hQ : 2 ≤ Q) (a b : ℕ → ℝ)
    (hfour : ∀ m ∈ effSet A B P Q L, 4 * (r / m) ≤ (P : ℝ))
    (hlam : ∀ m₁ ∈ effSet A B P Q L, ∀ m₂ ∈ effSet A B P Q L,
      curvedLambda (T * |r / m₁ - r / m₂|) (P : ℝ) ≤ 1) :
    ‖maskedBlockSum T r A B L P Q a b‖ ^ 2
      ≤ (∑ d ∈ Finset.Ico P Q, |a d| ^ 2)
        * (((Q - P : ℕ) : ℝ) * (∑ m ∈ effSet A B P Q L, |b m| ^ 2)
          + (∑ m ∈ effSet A B P Q L, |b m| ^ 2)
            * (2 * ∑ h ∈ Finset.Icc 1 (effGap A B P Q),
                gapCorrBound T r (effLow A Q) (effHigh B P) P Q h)) := by
  refine le_trans (norm_maskedBlockSum_sq_le T r A B L P Q a b) ?_
  refine mul_le_mul_of_nonneg_left (pairSum_block_le hT hr hA hB hP hQ b hfour hlam) ?_
  exact Finset.sum_nonneg fun d _ => sq_nonneg _

/-- The effective set lies in the initial segment cut out by the block. -/
theorem effSet_subset_Icc_effHigh {A B P Q L : ℕ} (hP : 1 ≤ P) (hQ : 2 ≤ Q) :
    effSet A B P Q L ⊆ Finset.Icc 1 (effHigh B P) := by
  intro m hm
  obtain ⟨h1, -, h3⟩ := effSet_confined hP hQ m hm
  exact Finset.mem_Icc.2 ⟨h1, h3⟩

/-- The effective interval lies in the same initial segment. -/
theorem Ico_eff_subset_Icc_effHigh (A B P Q : ℕ) :
    Finset.Ico (effLow A Q) (effHigh B P + 1) ⊆ Finset.Icc 1 (effHigh B P) := by
  intro m hm
  rw [Finset.mem_Ico] at hm
  rw [Finset.mem_Icc]
  exact ⟨le_trans (one_le_effLow A Q) hm.1, by omega⟩

/-- The short-side energy over any subset of an initial segment. -/
theorem sum_typeIIShort_sq_subset_le {S : Finset ℕ} {N : ℕ} (hS : S ⊆ Finset.Icc 1 N) (V : ℕ) :
    (∑ m ∈ S, |typeIIShort V m| ^ 2) ≤ 2 * (N : ℝ) + 2 * ((N : ℝ) * invSum N ^ 3) := by
  have hsub : (∑ m ∈ S, |typeIIShort V m| ^ 2)
      ≤ ∑ m ∈ Finset.Icc 1 N, |typeIIShort V m| ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg hS fun m _ _ => sq_nonneg _
  have hfull := sum_typeIIShort_sq_le V N
  have hnorm : ∀ m : ℕ, ‖((typeIIShort V m : ℝ) : ℂ)‖ = |typeIIShort V m| := fun m => by
    rw [Complex.norm_real, Real.norm_eq_abs]
  simp only [hnorm] at hfull
  linarith [hsub, hfull]

/-- The long-side energy of a block, in absolute-value form. -/
theorem sum_typeIILong_sq_block_abs_le {C : ℝ}
    (hC : ∀ (U P Q L : ℕ), 1 ≤ L → Q ≤ L + 1 →
      (∑ d ∈ Finset.Ico P Q, ‖((typeIILong U d : ℝ) : ℂ)‖ ^ 2)
        ≤ C * (Q : ℝ) * Real.log (L : ℝ))
    (U P Q L : ℕ) (hL : 1 ≤ L) (hQL : Q ≤ L + 1) :
    (∑ d ∈ Finset.Ico P Q, |typeIILong U d| ^ 2) ≤ C * (Q : ℝ) * Real.log (L : ℝ) := by
  have h := hC U P Q L hL hQL
  have hnorm : ∀ d : ℕ, ‖((typeIILong U d : ℝ) : ℂ)‖ = |typeIILong U d| := fun d => by
    rw [Complex.norm_real, Real.norm_eq_abs]
  simpa only [hnorm] using h

end

end RHTower.Sieve
