import GaloisForLFunctions.RHTower.GammaOddJacobiCapacity
import GaloisForLFunctions.RHTower.PrimeMellinJetResolvedChannelNoGo

/-!
# Adaptive Gamma-Jacobi capacity versus resolved Ward mixing

The same one-prime Gamma conductor cost drives two opposite all-prime phenomena.  Adaptive odd
Jacobi ranks reduce its protected diagonal to a uniformly summable residual.  Conversely, before
that adaptive mode deletion, every positive normalized resolved-channel block of fixed scalar
capacity must develop arbitrarily large off-diagonal commutator energy.  A single cofinal finite
prime packet witnesses both statements.
-/

open scoped BigOperators

namespace RHTower

noncomputable section

open HTGeometry

/-- **Adaptive-capacity/resolved-mixing dichotomy.**  At every positive scalar capacity and every
nonnegative energy threshold, one finite prime packet has adaptive Gamma-Jacobi residual trace
below the universal inverse-square budget while every positive normalized resolved-channel block
on that packet has commutator energy above the prescribed threshold. -/
theorem exists_primePacket_gammaOddResidual_bounded_and_resolvedWardEnergy_gt
    (B M : ℝ) (hB : 0 < B) (hM : 0 ≤ M) :
    ∃ F : Finset Nat.Primes,
      (∑ p ∈ F, gammaOddJacobiPrimeResidualCost p ≤
        ∑' n : ℕ, ((n : ℝ) ^ (2 : ℕ))⁻¹) ∧
      ∀ (K : Matrix (↑F) (↑F) ℝ),
        (∀ i, K i i = 1) →
        (∀ (x : ↑F → ℝ) (y : ℝ),
          0 ≤ (∑ i, ∑ j, K i j * x i * x j) +
            2 * y * (∑ i : ↑F,
              gammaConductorPrimeNormalizedCross (i : Nat.Primes) * x i) +
              B * y ^ (2 : ℕ)) →
        M < resolvedChannelTotalCommutatorEnergy (fun i j => (K i j : ℂ)) := by
  obtain ⟨F, hF⟩ := exists_primePacket_gammaConductor_resolvedWardEnergy_gt B M hB hM
  exact ⟨F, sum_gammaOddJacobiPrimeResidualCost_le_tsum_inv_sq F, hF⟩

/-- The finite-packet dichotomy is cofinal in energy while its adaptive residual budget remains
the same fixed constant. -/
theorem forall_energy_exists_gammaOddResidual_bounded_resolvedWardEnergy_gt
    (B : ℝ) (hB : 0 < B) :
    ∀ M : ℝ, 0 ≤ M →
      ∃ F : Finset Nat.Primes,
        (∑ p ∈ F, gammaOddJacobiPrimeResidualCost p ≤
          ∑' n : ℕ, ((n : ℝ) ^ (2 : ℕ))⁻¹) ∧
        ∀ (K : Matrix (↑F) (↑F) ℝ),
          (∀ i, K i i = 1) →
          (∀ (x : ↑F → ℝ) (y : ℝ),
            0 ≤ (∑ i, ∑ j, K i j * x i * x j) +
              2 * y * (∑ i : ↑F,
                gammaConductorPrimeNormalizedCross (i : Nat.Primes) * x i) +
                B * y ^ (2 : ℕ)) →
          M < resolvedChannelTotalCommutatorEnergy (fun i j => (K i j : ℂ)) := by
  intro M hM
  exact exists_primePacket_gammaOddResidual_bounded_and_resolvedWardEnergy_gt B M hB hM

end

end RHTower
