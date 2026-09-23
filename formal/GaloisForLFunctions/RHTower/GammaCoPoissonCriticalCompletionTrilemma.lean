import GaloisForLFunctions.RHTower.GammaCoPoissonIntervalKreinNoGo
import GaloisForLFunctions.RHTower.SuzukiCriticalRootedBianchiCofinalNoGo

/-!
# Gamma/co-Poisson critical completion trilemma

Two exact source obstructions meet at the critical boundary:

* retaining the canonical interval reflection leaves a strictly negative
  two-character packet at every positive logarithmic action;
* activating the canonical rooted Gamma--Bianchi correction by any nonzero
  prime-independent scalar gives a feature whose squared prime norm is not
  summable.

Thus a scalar actionwise completion has only two possibilities.  The zero
scalar leaves the Krein obstruction unchanged; every nonzero scalar destroys
ordinary cofinal Hilbert summability.  A positive critical completion must
therefore cancel or mix prime coordinates before the cofinal Hilbert limit.

No RH premise, estimate, computation, or zero data are used.
-/

namespace RHTower

noncomputable section

/-- **Critical completion trilemma.**  Local reflection is strictly negative,
while the canonical critical rooted coordinate is square-summable after a
prime-independent scalar renormalization exactly for the trivial scalar. -/
theorem gammaCoPoissonCriticalCompletionTrilemma
    {L d : ℝ} (hL : 0 < L) (hd : 0 < d) :
    (gammaCoPoissonSymmetricPacketValue L d).re < 0 ∧
      ∀ c : ℝ,
        Summable (fun p : Nat.Primes =>
          (c * suzukiCriticalRootedBianchiPrimeAmplitude p) ^ (2 : ℕ)) ↔
            c = 0 := by
  exact ⟨gammaCoPoissonSymmetricPacketValue_re_neg hL hd,
    summable_const_mul_sq_suzukiCriticalRootedBianchiPrimeAmplitude_iff⟩

/-- Every nonzero scalar rooted correction fails cofinal Hilbert summability
while the uncorrected interval packet has a strict negative direction. -/
theorem gammaCoPoisson_no_nonzero_scalarCriticalHilbertCompletion
    {L d c : ℝ} (hL : 0 < L) (hd : 0 < d) (hc : c ≠ 0) :
    (gammaCoPoissonSymmetricPacketValue L d).re < 0 ∧
      ¬ Summable (fun p : Nat.Primes =>
        (c * suzukiCriticalRootedBianchiPrimeAmplitude p) ^ (2 : ℕ)) := by
  refine ⟨gammaCoPoissonSymmetricPacketValue_re_neg hL hd, ?_⟩
  rw [summable_const_mul_sq_suzukiCriticalRootedBianchiPrimeAmplitude_iff]
  exact hc

end

end RHTower
