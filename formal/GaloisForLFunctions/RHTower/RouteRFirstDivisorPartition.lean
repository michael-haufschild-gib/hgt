import GaloisForLFunctions.RHTower.RouteRSieveWeightIsEventMass

/-!
# The first-divisor events partition the prime-valuation sector

The events "the `n`-th tail prime is the first that divides" are pairwise disjoint and their masses
sum to one, so they partition the sector up to a null set.  The restarted Euler sieve profile is
therefore the law of an honest random index: the position of the first dividing prime in the tail.
-/

open MeasureTheory Set
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

/-! ## The first-divisor events partition the sector -/

theorem mem_sieveTailIndex (e : ℕ ≃ Nat.Primes) (N n k : ℕ) (hk : k ≤ n) :
    e (N + k) ∈ sieveTailIndex e N n := by
  simp only [sieveTailIndex, Finset.mem_image, Finset.mem_range]
  exact ⟨k, by omega, rfl⟩

theorem measurableSet_firstDivisorEvent (e : ℕ ≃ Nat.Primes) (N n : ℕ) :
    MeasurableSet (firstDivisorEvent e N n) :=
  MeasurableSet.pi (sieveTailIndex e N n).countable_toSet
    fun p _ => measurableSet_firstDivisorTarget e N n p

/-- Distinct first-divisor events are disjoint: they disagree about the valuation
at the earlier of the two distinguished primes. -/
theorem pairwise_disjoint_firstDivisorEvent (e : ℕ ≃ Nat.Primes) (N : ℕ) :
    Pairwise (Function.onFun Disjoint (firstDivisorEvent e N)) := by
  have key : ∀ m n : ℕ, m < n →
      Disjoint (firstDivisorEvent e N m) (firstDivisorEvent e N n) := by
    intro m n hmn
    rw [Set.disjoint_left]
    intro k hkm hkn
    have hne : e (N + m) ≠ e (N + n) := by
      intro h
      have := e.injective h
      omega
    have hm := hkm (e (N + m))
      (mem_sieveTailIndex e N m m (le_refl m))
    have hn := hkn (e (N + m))
      (mem_sieveTailIndex e N n m (le_of_lt hmn))
    rw [firstDivisorTarget, if_pos rfl] at hm
    rw [firstDivisorTarget, if_neg hne] at hn
    exact hm hn
  intro m n hmn
  rcases lt_or_gt_of_ne hmn with h | h
  · exact key m n h
  · exact (key n m h).symm

/-- **The first-divisor events partition the sector.**  Their union has full
measure: almost surely some tail prime divides, and the sieve profile is the law
of which one does so first. -/
theorem primeValuationMeasure_iUnion_firstDivisorEvent (e : ℕ ≃ Nat.Primes)
    (N : ℕ) :
    primeValuationMeasure (⋃ n, firstDivisorEvent e N n) = 1 := by
  have hunion := measure_iUnion (μ := primeValuationMeasure)
    (pairwise_disjoint_firstDivisorEvent e N)
    (measurableSet_firstDivisorEvent e N)
  have hfin : primeValuationMeasure (⋃ n, firstDivisorEvent e N n) ≠ ⊤ :=
    measure_ne_top _ _
  have htoReal := congrArg ENNReal.toReal hunion
  rw [ENNReal.tsum_toReal_eq (fun n => measure_ne_top _ _),
    (hasSum_toReal_primeValuationMeasure_firstDivisorEvent e N).tsum_eq]
    at htoReal
  rw [← ENNReal.ofReal_toReal hfin, htoReal, ENNReal.ofReal_one]

end

end RHTower
