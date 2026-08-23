import GaloisForLFunctions.RHTower.Sieve.SubCriticalPowerSum
import GaloisForLFunctions.RHTower.Sieve.VonMangoldtParityCorrection

/-!
# The parity reduction

The congruence `r ≡ m (mod 2)` restricts the von Mangoldt sum to one parity class.  Removing the
restriction changes the sum only at even prime powers, whose total mass on `[1, N]` is at most
`log N` — so the parity condition costs a single logarithm, exactly as the card says.
-/

namespace RHTower.Sieve

open Finset ArithmeticFunction

noncomputable section

theorem norm_sum_even_le {T r : ℝ} {A B : ℕ} (hB : 1 ≤ B) :
    ‖∑ m ∈ (Finset.Ico A B).filter (fun m => 2 ∣ m),
        ((vonMangoldt m : ℝ) : ℂ) * ndPhaseExp T r m‖ ≤ Real.log (B : ℝ) := by
  classical
  refine le_trans (norm_sum_le _ _) ?_
  have hterm : ∀ m ∈ (Finset.Ico A B).filter (fun m => 2 ∣ m),
      ‖((vonMangoldt m : ℝ) : ℂ) * ndPhaseExp T r m‖ ≤ vonMangoldt m := by
    intro m _
    rw [norm_mul, ndPhaseExp, phaseExp, Complex.norm_exp]
    have hnorm : ‖((vonMangoldt m : ℝ) : ℂ)‖ = vonMangoldt m := by
      rw [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
    rw [hnorm]
    simp
  refine le_trans (Finset.sum_le_sum hterm) ?_
  have hzero : (vonMangoldt 0 : ℝ) = 0 := by simp
  rw [← Finset.sum_erase ((Finset.Ico A B).filter (fun m => 2 ∣ m)) hzero]
  have hsub : ((Finset.Ico A B).filter (fun m => 2 ∣ m)).erase 0
      ⊆ (Finset.Icc 1 B).filter (fun m => 2 ∣ m) := by
    intro m hm
    have hm0 : m ≠ 0 := Finset.ne_of_mem_erase hm
    have hmm := Finset.mem_of_mem_erase hm
    rw [Finset.mem_filter, Finset.mem_Ico] at hmm
    rw [Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨by omega, by omega⟩, hmm.2⟩
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun m _ _ => ArithmeticFunction.vonMangoldt_nonneg)) ?_
  exact sum_vonMangoldt_even_le hB

/-- **The parity reduction.**  Restricting to the odd class costs one logarithm. -/
theorem norm_sum_odd_le {T r : ℝ} {A B : ℕ} (hB : 1 ≤ B) :
    ‖∑ m ∈ (Finset.Ico A B).filter (fun m => ¬ 2 ∣ m),
        ((vonMangoldt m : ℝ) : ℂ) * ndPhaseExp T r m‖
      ≤ ‖∑ m ∈ Finset.Ico A B, ((vonMangoldt m : ℝ) : ℂ) * ndPhaseExp T r m‖
        + Real.log (B : ℝ) := by
  classical
  have hsplit : (∑ m ∈ Finset.Ico A B, ((vonMangoldt m : ℝ) : ℂ) * ndPhaseExp T r m)
      = (∑ m ∈ (Finset.Ico A B).filter (fun m => 2 ∣ m),
          ((vonMangoldt m : ℝ) : ℂ) * ndPhaseExp T r m)
        + ∑ m ∈ (Finset.Ico A B).filter (fun m => ¬ 2 ∣ m),
            ((vonMangoldt m : ℝ) : ℂ) * ndPhaseExp T r m :=
    (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  have heq : (∑ m ∈ (Finset.Ico A B).filter (fun m => ¬ 2 ∣ m),
      ((vonMangoldt m : ℝ) : ℂ) * ndPhaseExp T r m)
      = (∑ m ∈ Finset.Ico A B, ((vonMangoldt m : ℝ) : ℂ) * ndPhaseExp T r m)
        - ∑ m ∈ (Finset.Ico A B).filter (fun m => 2 ∣ m),
            ((vonMangoldt m : ℝ) : ℂ) * ndPhaseExp T r m := by
    rw [hsplit]
    ring
  rw [heq]
  refine le_trans (norm_sub_le _ _) ?_
  linarith [norm_sum_even_le (T := T) (r := r) (A := A) hB]

end

end RHTower.Sieve
