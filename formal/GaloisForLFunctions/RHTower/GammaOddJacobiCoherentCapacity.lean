import GaloisForLFunctions.HTGeometry.AdaptiveMercerCapacity
import GaloisForLFunctions.RHTower.GammaOddJacobiCapacity

/-!
# Coherent all-prime odd Gamma-Jacobi capacity

The least odd-Jacobi rank may vary with the prime.  This file proves that those independently
chosen cutoffs are nevertheless restrictions of one positive cross-prime kernel: deleted modes
are zero-padded rather than reindexed, so every prime row retains the same absolute Jacobi-mode
coordinate.  Its weighted diagonal is the summable residual constructed from the exact Gamma
Mercer law.

This closes a coherence gap left by pointwise capacity selection.  It does not identify this
positive residual with Suzuki's singular/local finite Green--Schur term; that operator-placement
identity is the next source frontier.
-/

noncomputable section

open Filter Real
open scoped BigOperators Nat Real

namespace RHTower

/-- Actual odd Gamma-Jacobi feature row attached to a prime source label. -/
def gammaOddJacobiPrimeFeature (p : Nat.Primes) (k : ℕ) : ℝ :=
  gammaOddJacobiCoefficient k (Real.log (p : ℝ))

theorem summable_gammaOddJacobiPrimeFeature_sq (p : Nat.Primes) :
    Summable fun k => gammaOddJacobiPrimeFeature p k ^ 2 := by
  have hpLog : 0 < Real.log (p : ℝ) :=
    Real.log_pos (by exact_mod_cast p.prop.one_lt)
  have hsum := (hasSum_gammaOddJacobiCoefficient_mul hpLog hpLog).summable
  simpa only [gammaOddJacobiPrimeFeature, pow_two] using hsum

/-- Cross-prime residual kernel with prime-dependent cutoffs and a common absolute Jacobi index. -/
def gammaOddJacobiPrimeCoherentResidualKernel (p q : Nat.Primes) : ℝ :=
  HTGeometry.adaptiveMercerResidualKernel
    gammaOddJacobiPrimeFeature gammaOddJacobiPrimeCapacity p q

/-- Diagonal of the coherent kernel is exactly the already controlled source residual. -/
theorem gammaOddJacobiPrimeCoherentResidualKernel_self
    (p : Nat.Primes) :
    gammaOddJacobiPrimeCoherentResidualKernel p p =
      gammaOddJacobiResidualKernel (gammaOddJacobiPrimeCapacity p)
        (Real.log (p : ℝ)) (Real.log (p : ℝ)) := by
  have hpLog : 0 < Real.log (p : ℝ) :=
    Real.log_pos (by exact_mod_cast p.prop.one_lt)
  rw [gammaOddJacobiPrimeCoherentResidualKernel,
    HTGeometry.adaptiveMercerResidualKernel_self_eq_diagonalTail
      gammaOddJacobiPrimeFeature gammaOddJacobiPrimeCapacity p
      (summable_gammaOddJacobiPrimeFeature_sq p),
    gammaOddJacobiResidualKernel_eq_tail hpLog hpLog]
  unfold HTGeometry.adaptiveMercerDiagonalTail gammaOddJacobiPrimeFeature
  apply tsum_congr
  intro k
  ring

/-- **Coherent odd-capacity law.**  Independently chosen least prime cutoffs assemble into a
positive semidefinite kernel on every finite prime packet. -/
theorem gammaOddJacobiPrimeCoherentResidualKernel_psd
    (F : Finset Nat.Primes) (z : Nat.Primes → ℝ) :
    0 ≤ F.sum (fun p => F.sum (fun q =>
      z p * z q * gammaOddJacobiPrimeCoherentResidualKernel p q)) := by
  exact HTGeometry.adaptiveMercerResidualKernel_psd
    gammaOddJacobiPrimeFeature gammaOddJacobiPrimeCapacity
    summable_gammaOddJacobiPrimeFeature_sq F z

/-- Positive coherent cross-prime residual has summable Gamma-conductor-weighted diagonal. -/
theorem summable_gammaOddJacobiPrimeCoherentResidualDiagonal :
    Summable (fun p : Nat.Primes =>
      gammaConductorPrimeSchurCost p *
        gammaOddJacobiPrimeCoherentResidualKernel p p) := by
  convert summable_gammaOddJacobiPrimeResidualCost using 1
  funext p
  rw [gammaOddJacobiPrimeCoherentResidualKernel_self]
  rfl

/-- Finite-packet weighted diagonal is bounded by the same universal `p⁻²` budget. -/
theorem sum_gammaOddJacobiPrimeCoherentResidualDiagonal_le_tsum_inv_sq
    (F : Finset Nat.Primes) :
    ∑ p ∈ F,
        gammaConductorPrimeSchurCost p *
          gammaOddJacobiPrimeCoherentResidualKernel p p ≤
      ∑' n : ℕ, ((n : ℝ) ^ 2)⁻¹ := by
  simpa only [gammaOddJacobiPrimeCoherentResidualKernel_self,
    gammaOddJacobiPrimeResidualCost] using
      sum_gammaOddJacobiPrimeResidualCost_le_tsum_inv_sq F

end RHTower
