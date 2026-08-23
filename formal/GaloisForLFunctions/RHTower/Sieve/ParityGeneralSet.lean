import GaloisForLFunctions.RHTower.Sieve.WeightedTailNorm

/-!
# The parity correction over an arbitrary index set

The shift filter that the tail's `r`-sum produces is not literally an interval, so the parity
correction is restated for an arbitrary `S ⊆ [1, B]`.
-/

namespace RHTower.Sieve

open Finset ArithmeticFunction

noncomputable section

theorem norm_sum_even_set_le {T rr : ℝ} {S : Finset ℕ} {B : ℕ} (hB : 1 ≤ B)
    (hS : S ⊆ Finset.Icc 1 B) :
    ‖∑ m ∈ S.filter (fun m : ℕ => 2 ∣ m),
        ((vonMangoldt m : ℝ) : ℂ) * ndPhaseExp T rr m‖ ≤ Real.log (B : ℝ) := by
  classical
  refine le_trans (norm_sum_le _ _) ?_
  have hterm : ∀ m ∈ S.filter (fun m : ℕ => 2 ∣ m),
      ‖((vonMangoldt m : ℝ) : ℂ) * ndPhaseExp T rr m‖ ≤ vonMangoldt m := by
    intro m _
    rw [norm_mul, ndPhaseExp, phaseExp, Complex.norm_exp]
    have hnorm : ‖((vonMangoldt m : ℝ) : ℂ)‖ = vonMangoldt m := by
      rw [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
    rw [hnorm]
    simp
  refine le_trans (Finset.sum_le_sum hterm) ?_
  have hsub : S.filter (fun m : ℕ => 2 ∣ m) ⊆ (Finset.Icc 1 B).filter (fun m : ℕ => 2 ∣ m) := by
    intro m hm
    rw [Finset.mem_filter] at hm ⊢
    exact ⟨hS hm.1, hm.2⟩
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun m _ _ => ArithmeticFunction.vonMangoldt_nonneg)) ?_
  exact sum_vonMangoldt_even_le hB

/-- **The parity correction over an arbitrary index set.** -/
theorem norm_sum_parity_set_le {T rr : ℝ} {S : Finset ℕ} {B r : ℕ} (hB : 1 ≤ B)
    (hS : S ⊆ Finset.Icc 1 B) :
    ‖∑ m ∈ S.filter (fun m : ℕ => r % 2 = m % 2),
        ((vonMangoldt m : ℝ) : ℂ) * ndPhaseExp T rr m‖
      ≤ ‖∑ m ∈ S, ((vonMangoldt m : ℝ) : ℂ) * ndPhaseExp T rr m‖ + Real.log (B : ℝ) := by
  classical
  have hnn : (0 : ℝ) ≤ ‖∑ m ∈ S, ((vonMangoldt m : ℝ) : ℂ) * ndPhaseExp T rr m‖ :=
    norm_nonneg _
  rcases Nat.even_or_odd r with he | ho
  · have hr : r % 2 = 0 := Nat.even_iff.1 he
    have hfilter : S.filter (fun m : ℕ => r % 2 = m % 2) = S.filter (fun m : ℕ => 2 ∣ m) := by
      refine Finset.filter_congr fun m _ => ?_
      rw [hr]
      constructor
      · intro h; omega
      · intro h; omega
    rw [hfilter]
    linarith [norm_sum_even_set_le (T := T) (rr := rr) hB hS]
  · have hr : r % 2 = 1 := Nat.odd_iff.1 ho
    have hfilter : S.filter (fun m : ℕ => r % 2 = m % 2)
        = S.filter (fun m : ℕ => ¬ 2 ∣ m) := by
      refine Finset.filter_congr fun m _ => ?_
      rw [hr]
      constructor
      · intro h; omega
      · intro h; omega
    rw [hfilter]
    have hsplit : (∑ m ∈ S, ((vonMangoldt m : ℝ) : ℂ) * ndPhaseExp T rr m)
        = (∑ m ∈ S.filter (fun m : ℕ => 2 ∣ m),
            ((vonMangoldt m : ℝ) : ℂ) * ndPhaseExp T rr m)
          + ∑ m ∈ S.filter (fun m : ℕ => ¬ 2 ∣ m),
              ((vonMangoldt m : ℝ) : ℂ) * ndPhaseExp T rr m :=
      (Finset.sum_filter_add_sum_filter_not _ _ _).symm
    have heq : (∑ m ∈ S.filter (fun m : ℕ => ¬ 2 ∣ m),
        ((vonMangoldt m : ℝ) : ℂ) * ndPhaseExp T rr m)
        = (∑ m ∈ S, ((vonMangoldt m : ℝ) : ℂ) * ndPhaseExp T rr m)
          - ∑ m ∈ S.filter (fun m : ℕ => 2 ∣ m),
              ((vonMangoldt m : ℝ) : ℂ) * ndPhaseExp T rr m := by
      rw [hsplit]; ring
    rw [heq]
    refine le_trans (norm_sub_le _ _) ?_
    linarith [norm_sum_even_set_le (T := T) (rr := rr) hB hS]

/-- **The weighted tail from a block bound.**  Substituting an estimate for the unrestricted inner
sum leaves only the harmonic total and one logarithm per shift. -/
theorem norm_weightedTail_le_of_blockBound {T ε : ℝ} (hε : 0 ≤ ε) {mLo mHi rLo : ℕ}
    (hmLo : 1 ≤ mLo) (hmHi : 1 ≤ mHi) (G : ℕ → ℝ)
    (hG : ∀ r ∈ Finset.Icc rLo ⌊(mHi : ℝ) * ε⌋₊,
      ‖∑ m ∈ (Finset.Icc mLo mHi).filter (fun m : ℕ => r ≤ ⌊(m : ℝ) * ε⌋₊),
          ((vonMangoldt m : ℝ) : ℂ) * ndPhaseExp T r m‖ ≤ G r) :
    ‖weightedNearDiagonalTail T ε mLo mHi rLo‖
      ≤ ∑ r ∈ Finset.Icc rLo ⌊(mHi : ℝ) * ε⌋₊, (G r + Real.log (mHi : ℝ)) / (r : ℝ) := by
  classical
  refine le_trans (norm_weightedNearDiagonalTail_le T ε hε mLo mHi rLo) ?_
  refine Finset.sum_le_sum fun r hr => ?_
  have hsplit : (Finset.Icc mLo mHi).filter
      (fun m : ℕ => r ≤ ⌊(m : ℝ) * ε⌋₊ ∧ r % 2 = m % 2)
      = ((Finset.Icc mLo mHi).filter (fun m : ℕ => r ≤ ⌊(m : ℝ) * ε⌋₊)).filter
          (fun m : ℕ => r % 2 = m % 2) := by
    rw [Finset.filter_filter]
  have hsub : (Finset.Icc mLo mHi).filter (fun m : ℕ => r ≤ ⌊(m : ℝ) * ε⌋₊)
      ⊆ Finset.Icc 1 mHi := by
    intro m hm
    rw [Finset.mem_filter, Finset.mem_Icc] at hm
    rw [Finset.mem_Icc]
    exact ⟨le_trans hmLo hm.1.1, hm.1.2⟩
  rw [hsplit]
  have hpar := norm_sum_parity_set_le (T := T) (rr := (r : ℝ)) (r := r) hmHi hsub
  have hblock := hG r hr
  have hrnn : (0 : ℝ) ≤ (r : ℝ) := Nat.cast_nonneg r
  refine div_le_div_of_nonneg_right ?_ ?_ |>.trans (le_of_eq rfl)
  · linarith [hpar, hblock]
  · exact hrnn

end

end RHTower.Sieve
