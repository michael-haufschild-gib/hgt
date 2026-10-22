import GaloisForLFunctions.RHTower.GammaSewnPluckerNuclearRootBudget
import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmGammaSewnProjectiveParityLeakageBridge

open Filter Topology

namespace RHTower

noncomputable section

open HedenmalmThetaSource

def gammaSewnCriticalPluckerRootIncidence
    (i : Fin 4) (z : ℕ × ℕ) : ℝ :=
  Real.sqrt (gammaSewnCriticalAdjacentPrime_PluckerBlockWeight z) *
    Real.sqrt (gammaSewnCriticalPrimeDepthPacket_node z.1
      (gammaSewnCriticalAdjacentPrime_lower z.2)
      (gammaSewnCriticalAdjacentPrime_upper z.2) i)

theorem summable_gammaSewnCriticalPluckerRootIncidence
    (i : Fin 4) :
    Summable (gammaSewnCriticalPluckerRootIncidence i) := by
  change Summable (fun z : ℕ × ℕ =>
    Real.sqrt (gammaSewnCriticalAdjacentPrime_PluckerBlockWeight z) *
      Real.sqrt (gammaSewnCriticalPrimeDepthPacket_node z.1
        (gammaSewnCriticalAdjacentPrime_lower z.2)
        (gammaSewnCriticalAdjacentPrime_upper z.2) i))
  exact HedenmalmThetaSource.summable_gammaSewnCriticalPluckerRootIncidence i

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

end

end RHTower
