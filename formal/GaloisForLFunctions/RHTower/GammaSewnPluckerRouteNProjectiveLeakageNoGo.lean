import GaloisForLFunctions.RHTower.GammaSewnPluckerNuclearRootBudget
import GaloisForLFunctions.RHTower.HedenmalmGammaSewnProjectiveParityLeakageBridge

/-!
# C1 nuclear-root incidence cannot carry Route-N projective leakage

The literal C1 Gamma-sewn Plucker root incidence is summable on the complete
prime-depth/four-coordinate grid.  The Route-N projective Weyl leakage, on the other hand, is
summable over all primes exactly at neutral grade.  This module makes the resulting source-level
obstruction precise: an injective, coefficient-faithful placement of all ordinary primes into the
positive C1 root incidence cannot uniformly majorize the non-neutral leakage.

The theorem does not exclude signed, non-nuclear, or label-colliding formation.  It identifies the
exact boundary of the existing positive nuclear C1 carrier, even when a producer distributes
primes arbitrarily among all four literal labels.  Those genuinely different producer classes are
the only remaining P/C1 directions.
-/

open Filter Topology

namespace RHTower

noncomputable section

open HedenmalmThetaSource

/-- Positive root incidence of the literal four-coordinate C1 Gamma-sewn Plucker carrier. -/
def gammaSewnCriticalPluckerRootIncidence
    (i : Fin 4) (z : ℕ × ℕ) : ℝ :=
  Real.sqrt (gammaSewnCriticalAdjacentPrime_PluckerBlockWeight z) *
    Real.sqrt (gammaSewnCriticalPrimeDepthPacket_node z.1
      (gammaSewnCriticalAdjacentPrime_lower z.2)
      (gammaSewnCriticalAdjacentPrime_upper z.2) i)

/-- Every coordinate of the literal positive C1 root carrier has globally summable incidence. -/
theorem summable_gammaSewnCriticalPluckerRootIncidence
    (i : Fin 4) :
    Summable (gammaSewnCriticalPluckerRootIncidence i) := by
  change Summable (fun z : ℕ × ℕ =>
    Real.sqrt (gammaSewnCriticalAdjacentPrime_PluckerBlockWeight z) *
      Real.sqrt (gammaSewnCriticalPrimeDepthPacket_node z.1
        (gammaSewnCriticalAdjacentPrime_lower z.2)
        (gammaSewnCriticalAdjacentPrime_upper z.2) i))
  exact HedenmalmThetaSource.summable_gammaSewnCriticalPluckerRootIncidence i

/-- Positive root incidence on the whole literal four-label C1 carrier. -/
def gammaSewnCriticalPluckerAllRootIncidence (iz : Fin 4 × (ℕ × ℕ)) : ℝ :=
  gammaSewnCriticalPluckerRootIncidence iz.1 iz.2

theorem gammaSewnCriticalPluckerAllRootIncidence_nonneg (iz : Fin 4 × (ℕ × ℕ)) :
    0 ≤ gammaSewnCriticalPluckerAllRootIncidence iz := by
  dsimp [gammaSewnCriticalPluckerAllRootIncidence,
    gammaSewnCriticalPluckerRootIncidence]
  positivity

/-- The disjoint union of all four literal C1 nuclear-root coordinates remains summable. -/
theorem summable_gammaSewnCriticalPluckerAllRootIncidence :
    Summable gammaSewnCriticalPluckerAllRootIncidence := by
  rw [summable_prod_of_nonneg gammaSewnCriticalPluckerAllRootIncidence_nonneg]
  constructor
  · intro i
    exact summable_gammaSewnCriticalPluckerRootIncidence i
  · exact (hasSum_fintype _).summable

private theorem summable_routeNGammaSewnProjectiveLeakage_of_C1RootIncidence_majorization
    (t : ℝ) (i : Fin 4) (place : Nat.Primes → ℕ × ℕ)
    (hplace : Function.Injective place) (c : ℝ)
    (hmajor : ∀ p : Nat.Primes,
      routeNGammaSewnProjectiveLeakage t p ≤
        c * gammaSewnCriticalPluckerRootIncidence i (place p)) :
    Summable (routeNGammaSewnProjectiveLeakage t) := by
  refine Summable.of_nonneg_of_le (fun p => ?_) hmajor ?_
  · rw [routeNGammaSewnProjectiveLeakage_eq_hGap_mul]
    exact mul_nonneg (by rw [primeValuationHellingerGap]; positivity)
      (le_trans (by norm_num) (one_third_le_routeNGammaSewnProjectiveLeakageFactor t p))
  · exact (summable_gammaSewnCriticalPluckerRootIncidence i).comp_injective hplace |>.mul_left c

private theorem summable_routeNGammaSewnProjectiveLeakage_of_C1AllRootIncidence_majorization
    (t : ℝ) (place : Nat.Primes → Fin 4 × (ℕ × ℕ))
    (hplace : Function.Injective place) (c : ℝ)
    (hmajor : ∀ p : Nat.Primes,
      routeNGammaSewnProjectiveLeakage t p ≤
        c * gammaSewnCriticalPluckerAllRootIncidence (place p)) :
    Summable (routeNGammaSewnProjectiveLeakage t) := by
  refine Summable.of_nonneg_of_le (fun p => ?_) hmajor ?_
  · rw [routeNGammaSewnProjectiveLeakage_eq_hGap_mul]
    exact mul_nonneg (by rw [primeValuationHellingerGap]; positivity)
      (le_trans (by norm_num) (one_third_le_routeNGammaSewnProjectiveLeakageFactor t p))
  · exact summable_gammaSewnCriticalPluckerAllRootIncidence.comp_injective hplace |>.mul_left c

/-- At non-neutral grade, no finite positive C1 nuclear-root incidence can be a
coefficient-faithful majorant for the literal Route-N projective leakage. -/
theorem not_exists_C1RootIncidence_projectiveLeakage_majorization
    (t : ℝ) (ht : t ≠ 0) (i : Fin 4) :
    ¬ ∃ (place : Nat.Primes → ℕ × ℕ) (c : ℝ),
      Function.Injective place ∧
        ∀ p : Nat.Primes,
          routeNGammaSewnProjectiveLeakage t p ≤
            c * gammaSewnCriticalPluckerRootIncidence i (place p) := by
  rintro ⟨place, c, hplace, hmajor⟩
  have hsum := summable_routeNGammaSewnProjectiveLeakage_of_C1RootIncidence_majorization
    t i place hplace c hmajor
  exact ht ((summable_routeNGammaSewnProjectiveLeakage_iff t).mp hsum)

/-- At non-neutral grade, no injective placement of ordinary primes into the full literal
four-label positive C1 nuclear-root carrier can pointwise majorize Route-N projective leakage.
Thus splitting a prime-faithful positive formation among its four retained labels does not evade
the C1 obstruction. -/
theorem not_exists_C1AllRootIncidence_projectiveLeakage_majorization
    (t : ℝ) (ht : t ≠ 0) :
    ¬ ∃ (place : Nat.Primes → Fin 4 × (ℕ × ℕ)) (c : ℝ),
      Function.Injective place ∧
        ∀ p : Nat.Primes,
          routeNGammaSewnProjectiveLeakage t p ≤
            c * gammaSewnCriticalPluckerAllRootIncidence (place p) := by
  rintro ⟨place, c, hplace, hmajor⟩
  have hsum := summable_routeNGammaSewnProjectiveLeakage_of_C1AllRootIncidence_majorization
    t place hplace c hmajor
  exact ht ((summable_routeNGammaSewnProjectiveLeakage_iff t).mp hsum)

end

end RHTower
