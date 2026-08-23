import GaloisForLFunctions.RHTower.Sieve.FilteredSumSwap
import GaloisForLFunctions.RHTower.NearDiagonalTailBound

/-!
# The parity-weighted near-diagonal tail

The card's `E_Λ(T)`.  The corpus already owns the UNWEIGHTED tail
(`RHTower.nearDiagonalTail`, `kubalalikaEps`, `kubalalikaTailSum`, and the `O(T^{7/8})` bound); the
card's content is the same double sum with the arithmetic weight `Λ(m)` and the parity condition
`r ≡ m (mod 2)` retained.  All the parameter definitions and the shift-ceiling monotonicity are
reused from there.
-/

namespace RHTower.Sieve

open Finset ArithmeticFunction RHTower

noncomputable section

/-- **The parity-weighted near-diagonal tail.**  The card's `E_Λ`, in abstract parameters. -/
def weightedNearDiagonalTail (T ε : ℝ) (mLo mHi rLo : ℕ) : ℂ :=
  ∑ m ∈ Finset.Icc mLo mHi,
    ((vonMangoldt m : ℝ) : ℂ)
      * ∑ r ∈ (Finset.Icc rLo ⌊(m : ℝ) * ε⌋₊).filter (fun r => r % 2 = m % 2),
          ndPhaseExp T r m / (r : ℂ)

/-- **The card's `E_Λ(T)`** at the Kubalalika localization `ε = T^{-1/4}`,
`V = T/((1+ε)log²T)`, `R = T^{1/4}`. -/
def kubalalikaWeightedTail (T : ℝ) : ℂ :=
  weightedNearDiagonalTail T (kubalalikaEps T)
    ⌈T / ((1 + kubalalikaEps T) * (Real.log T) ^ 2)⌉₊
    ⌊T * (1 + kubalalikaEps T)⌋₊
    ⌈Real.sqrt (Real.sqrt T)⌉₊

/-- **The tail as an `r`-sum.** -/
theorem weightedNearDiagonalTail_swap (T ε : ℝ) (hε : 0 ≤ ε) (mLo mHi rLo : ℕ) :
    weightedNearDiagonalTail T ε mLo mHi rLo
      = ∑ r ∈ Finset.Icc rLo ⌊(mHi : ℝ) * ε⌋₊,
          ∑ m ∈ (Finset.Icc mLo mHi).filter
              (fun m : ℕ => r ≤ ⌊(m : ℝ) * ε⌋₊ ∧ r % 2 = m % 2),
            ((vonMangoldt m : ℝ) : ℂ) * (ndPhaseExp T r m / (r : ℂ)) := by
  classical
  have hinner : ∀ m ∈ Finset.Icc mLo mHi,
      (((vonMangoldt m : ℝ) : ℂ)
        * ∑ r ∈ (Finset.Icc rLo ⌊(m : ℝ) * ε⌋₊).filter (fun r => r % 2 = m % 2),
            ndPhaseExp T r m / (r : ℂ))
      = ∑ r ∈ (Finset.Icc rLo ⌊(mHi : ℝ) * ε⌋₊).filter
            (fun r : ℕ => r ≤ ⌊(m : ℝ) * ε⌋₊ ∧ r % 2 = m % 2),
          ((vonMangoldt m : ℝ) : ℂ) * (ndPhaseExp T r m / (r : ℂ)) := by
    intro m hm
    rw [Finset.mem_Icc] at hm
    have hset : (Finset.Icc rLo ⌊(m : ℝ) * ε⌋₊).filter (fun r : ℕ => r % 2 = m % 2)
        = (Finset.Icc rLo ⌊(mHi : ℝ) * ε⌋₊).filter
            (fun r : ℕ => r ≤ ⌊(m : ℝ) * ε⌋₊ ∧ r % 2 = m % 2) := by
      ext r
      simp only [Finset.mem_filter, Finset.mem_Icc]
      constructor
      · rintro ⟨⟨h1, h2⟩, h3⟩
        exact ⟨⟨h1, le_trans h2 (shiftCeil_mono hε hm.2)⟩, h2, h3⟩
      · rintro ⟨⟨h1, -⟩, h2, h3⟩
        exact ⟨⟨h1, h2⟩, h3⟩
    rw [hset, Finset.mul_sum]
  rw [weightedNearDiagonalTail, Finset.sum_congr rfl hinner]
  exact sum_filter_swap _ _ (fun m r : ℕ => r ≤ ⌊(m : ℝ) * ε⌋₊ ∧ r % 2 = m % 2)
    (fun m r : ℕ => ((vonMangoldt m : ℝ) : ℂ) * (ndPhaseExp T r m / (r : ℂ)))

end

end RHTower.Sieve
