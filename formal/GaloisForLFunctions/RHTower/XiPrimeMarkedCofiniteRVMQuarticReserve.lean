import GaloisForLFunctions.RHTower.XiPrimeMarkedFiniteTwoLevelDiagonalCarrier

/-!
# Cofinite RVM reserve for quartic source incidence

The first `N` marked primes form a canonical finite prefix.  Outside that prefix the diagonal
operator is the exact reciprocal smooth-RVM skeleton, and its Hilbert--Schmidt energy tends to
zero.  The theorem is cofinal in `N`: an arbitrarily large prescribed prefix may be discarded.
This gives enough room for a disjoint finite moment carrier and a late trace-class cycle carrier.
-/

open scoped BigOperators InnerProductSpace Nat.Prime

namespace RHTower

noncomputable section

open ContinuousLinearMap

/-- Canonical finite prefix of the marked-prime basis. -/
def routeKInitialPrimeFinset (N : ℕ) : Finset Nat.Primes :=
  (Finset.range N).image nthPrimeSubtype

theorem mem_routeKInitialPrimeFinset_iff
    (N : ℕ) (p : Nat.Primes) :
    p ∈ routeKInitialPrimeFinset N ↔ nthPrimeEquiv.symm p < N := by
  constructor
  · intro hp
    rw [routeKInitialPrimeFinset, Finset.mem_image] at hp
    obtain ⟨n, hn, rfl⟩ := hp
    simp only [Finset.mem_range] at hn
    change nthPrimeEquiv.symm (nthPrimeEquiv n) < N
    simpa using hn
  · intro hp
    rw [routeKInitialPrimeFinset, Finset.mem_image]
    refine ⟨nthPrimeEquiv.symm p, ?_, ?_⟩
    · simpa only [Finset.mem_range] using hp
    · change nthPrimeEquiv (nthPrimeEquiv.symm p) = p
      exact nthPrimeEquiv.apply_symm_apply p

/-- Exact diagonal weight of the RVM reserve after the canonical cut. -/
theorem routeKRVMTailWeight_initial
    (N : ℕ) (p : Nat.Primes) :
    routeKRVMTailWeight (routeKInitialPrimeFinset N) p =
      if nthPrimeEquiv.symm p < N then 0
      else routeKPrimeRVMReciprocal p := by
  rw [routeKRVMTailWeight]
  simp only [mem_routeKInitialPrimeFinset_iff]

/-- Cofinal small-tail theorem: beyond an arbitrarily large prime prefix, reciprocal-RVM energy
is arbitrarily small. -/
theorem exists_routeKRVM_initial_tail_energy_lt
    {ε : ℝ} (hε : 0 < ε) (N₀ : ℕ) :
    ∃ N : ℕ, N₀ ≤ N ∧
      hsNormSq (routeKRVMTailOperator (routeKInitialPrimeFinset N)) < ε := by
  obtain ⟨s, hs⟩ :=
    GaloisForLFunctions.HTGeometry.exists_finset_tsum_compl_lt
      summable_routeKPrimeRVMReciprocal_sq.hasSum hε
  let t : Finset ℕ := s.image nthPrimeEquiv.symm
  obtain ⟨M, hM⟩ := t.exists_nat_subset_range
  let N := max N₀ M
  have hsSub : s ⊆ routeKInitialPrimeFinset N := by
    intro p hp
    rw [mem_routeKInitialPrimeFinset_iff]
    have hpt : nthPrimeEquiv.symm p ∈ t := by
      exact Finset.mem_image.mpr ⟨p, hp, rfl⟩
    have hpM := hM hpt
    simp only [Finset.mem_range] at hpM
    exact hpM.trans_le (le_max_right _ _)
  refine ⟨N, le_max_left _ _, ?_⟩
  rw [hsNormSq_routeKRVMTailOperator]
  calc
    ∑' p : Nat.Primes,
        routeKRVMTailWeight (routeKInitialPrimeFinset N) p ^ 2
      ≤ ∑' p : Nat.Primes, routeKRVMTailWeight s p ^ 2 := by
        apply Summable.tsum_le_tsum
        · intro p
          by_cases hpN : p ∈ routeKInitialPrimeFinset N
          · rw [routeKRVMTailWeight, if_pos hpN]
            simpa using sq_nonneg (routeKRVMTailWeight s p)
          · have hps : p ∉ s := fun h => hpN (hsSub h)
            simp [routeKRVMTailWeight, hpN, hps]
        · exact summable_routeKRVMTailWeight_sq _
        · exact summable_routeKRVMTailWeight_sq _
    _ = ∑' p : {p : Nat.Primes // p ∉ s},
          routeKPrimeRVMReciprocal p ^ 2 := by
        calc
          (∑' p : Nat.Primes, routeKRVMTailWeight s p ^ 2) =
              ∑' p : Nat.Primes,
                ({p : Nat.Primes | p ∉ s}.indicator
                  (fun p => routeKPrimeRVMReciprocal p ^ 2)) p := by
            apply tsum_congr
            intro p
            by_cases hp : p ∈ s <;>
              simp [routeKRVMTailWeight, Set.indicator, hp]
          _ = _ := by
            exact
              (tsum_subtype {p : Nat.Primes | p ∉ s}
                (fun p => routeKPrimeRVMReciprocal p ^ 2)).symm
    _ < ε := by
      change
        (∑' p : {p : Nat.Primes // p ∉ s},
          routeKPrimeRVMReciprocal p ^ 2) < ε at hs
      exact hs

end

end RHTower
