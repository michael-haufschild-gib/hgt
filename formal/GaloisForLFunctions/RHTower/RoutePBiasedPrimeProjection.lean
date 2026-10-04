import GaloisForLFunctions.RHTower.MobiusDivisorFixedCoreProfile
import GaloisForLFunctions.RHTower.MobiusDivisorCriticalCorrelationSource
import Mathlib.Data.Nat.Prime.Infinite

/-!
# Native sharpness of prime-biased two-channel projection

For bias `θ = 1 - 1/p`, the covariance of the native unit and prime
channels has the exact Schur remainder `(A_p - θ A_1)^2`.
The resulting projection bound cannot be improved by any fixed factor
less than one, even after discarding any finite set of primes and any
finite initial segment of the physical cutoff.

This concerns the native two-channel compression. It neither bounds the
full retained-fibre covariance nor resolves the Route P history debts.
-/

open Filter Topology

namespace RHTower

noncomputable def routePPrimeSelectionBias (p : Nat.Primes) : ℝ :=
  1 - 1 / (p : ℕ)

/-- Biased average of the unmerged and merged native unit/prime energies. -/
noncomputable def routePBiasedPrimePairEnergy (M : ℕ) (p : Nat.Primes) : ℝ :=
  (1 - routePPrimeSelectionBias p) *
      ((divisorUnsignedDilationChannel M 1)^2 +
        (divisorUnsignedDilationChannel M p)^2) +
    routePPrimeSelectionBias p *
      (divisorUnsignedDilationChannel M 1 - divisorUnsignedDilationChannel M p)^2

/-- The two coefficients are the actual signed Möbius dilation channels. -/
theorem routePBiasedPrimePairEnergy_eq_signed (M : ℕ) (p : Nat.Primes) :
    routePBiasedPrimePairEnergy M p =
      (1 - routePPrimeSelectionBias p) *
          ((mobiusDivisorDilationChannel M 1)^2 +
            (mobiusDivisorDilationChannel M p)^2) +
        routePPrimeSelectionBias p *
          (mobiusDivisorDilationChannel M 1 + mobiusDivisorDilationChannel M p)^2 := by
  simp [routePBiasedPrimePairEnergy,
    mobiusDivisorDilationChannel_eq_moebius_unsigned,
    ArithmeticFunction.moebius_apply_prime p.property, sub_eq_add_neg]

/-- Exact positive survivor of the attempted rare-selection contraction. -/
theorem routePBiasedPrimePairEnergy_decomposition (M : ℕ) (p : Nat.Primes) :
    routePBiasedPrimePairEnergy M p =
      (divisorUnsignedDilationChannel M p -
        routePPrimeSelectionBias p * divisorUnsignedDilationChannel M 1)^2 +
      (1 - (routePPrimeSelectionBias p)^2) *
        (divisorUnsignedDilationChannel M 1)^2 := by
  unfold routePBiasedPrimePairEnergy
  ring

theorem routePBiasedPrimePairEnergy_projection (M : ℕ) (p : Nat.Primes) :
    (1 - (routePPrimeSelectionBias p)^2) *
        (divisorUnsignedDilationChannel M 1)^2 ≤ routePBiasedPrimePairEnergy M p := by
  rw [routePBiasedPrimePairEnergy_decomposition]
  exact le_add_of_nonneg_left (sq_nonneg _)

private theorem routePBiasedPrimePairEnergy_normalized (M : ℕ) (p : Nat.Primes) :
    routePBiasedPrimePairEnergy M p / M =
      (1 - routePPrimeSelectionBias p) *
          ((divisorUnsignedDilationChannel M 1 / Real.sqrt M)^2 +
            (divisorUnsignedDilationChannel M p / Real.sqrt M)^2) +
        routePPrimeSelectionBias p *
          (divisorUnsignedDilationChannel M 1 / Real.sqrt M -
            divisorUnsignedDilationChannel M p / Real.sqrt M)^2 := by
  simp only [← sub_div, div_pow, Real.sq_sqrt (Nat.cast_nonneg M)]
  unfold routePBiasedPrimePairEnergy
  ring

private theorem routePUnitChannel_sq_normalized_tendsto :
    Tendsto (fun M : ℕ => (divisorUnsignedDilationChannel M 1)^2 / M)
      atTop (𝓝 (criticalCorrelationUnitMean^2)) := by
  have h := (tendsto_divisorUnsignedDilationChannel_div_sqrt 1 (by omega)).pow 2
  simpa only [criticalCorrelationUnitMean, div_pow,
    Real.sq_sqrt (Nat.cast_nonneg _)] using h

theorem routePBiasedPrimePairEnergy_normalized_tendsto (p : Nat.Primes) :
    Tendsto (fun M : ℕ => routePBiasedPrimePairEnergy M p / M)
      atTop (𝓝 (2 * criticalCorrelationUnitMean^2 / (p : ℕ))) := by
  have ha : Tendsto (fun M : ℕ => divisorUnsignedDilationChannel M 1 / Real.sqrt M)
      atTop (𝓝 criticalCorrelationUnitMean) :=
    tendsto_divisorUnsignedDilationChannel_div_sqrt 1 (by omega)
  have hb : Tendsto (fun M : ℕ => divisorUnsignedDilationChannel M p / Real.sqrt M)
      atTop (𝓝 criticalCorrelationUnitMean) :=
    tendsto_divisorUnsignedDilationChannel_div_sqrt p p.property.pos
  have h := (((ha.pow 2).add (hb.pow 2)).const_mul
      (1 - routePPrimeSelectionBias p)).add
    (((ha.sub hb).pow 2).const_mul (routePPrimeSelectionBias p))
  have heq : (1 - routePPrimeSelectionBias p) *
        (criticalCorrelationUnitMean^2 + criticalCorrelationUnitMean^2) +
      routePPrimeSelectionBias p *
        (criticalCorrelationUnitMean - criticalCorrelationUnitMean)^2 =
      2 * criticalCorrelationUnitMean^2 / (p : ℕ) := by
    unfold routePPrimeSelectionBias
    ring
  rw [heq] at h
  exact h.congr' (Eventually.of_forall fun M =>
    (routePBiasedPrimePairEnergy_normalized M p).symm)

private theorem routePBiasedPrimeProjectionGap_tendsto (p : Nat.Primes) (k : ℝ) :
    Tendsto (fun M : ℕ =>
      ((1 - (routePPrimeSelectionBias p)^2) *
          (divisorUnsignedDilationChannel M 1)^2 -
        k * routePBiasedPrimePairEnergy M p) / M)
      atTop (𝓝 ((1 - (routePPrimeSelectionBias p)^2) * criticalCorrelationUnitMean^2 -
        k * (2 * criticalCorrelationUnitMean^2 / (p : ℕ)))) := by
  have h := (routePUnitChannel_sq_normalized_tendsto.const_mul
      (1 - (routePPrimeSelectionBias p)^2)).sub
    ((routePBiasedPrimePairEnergy_normalized_tendsto p).const_mul k)
  exact h.congr' (Eventually.of_forall fun M => by ring)

/-- The projection coefficient is sharp on native channels, cofinally in
primes and eventually in the original physical cutoff. -/
theorem routePBiasedPrimeProjection_cofinally_sharp :
    ∀ k : ℝ, k < 1 → ∀ B : ℕ, ∃ p : Nat.Primes, B ≤ (p : ℕ) ∧
      ∀ᶠ M : ℕ in atTop,
        k * routePBiasedPrimePairEnergy M p <
          (1 - (routePPrimeSelectionBias p)^2) *
            (divisorUnsignedDilationChannel M 1)^2 := by
  intro k hk B
  obtain ⟨n, hn⟩ := exists_nat_gt (1 / (2 * (1 - k)))
  obtain ⟨q, hq, hprime⟩ := Nat.exists_infinite_primes (max B n)
  let p : Nat.Primes := ⟨q, hprime⟩
  refine ⟨p, (le_max_left B n).trans hq, ?_⟩
  have hqpos : 0 < (q : ℝ) := by exact_mod_cast hprime.pos
  have hnq : (n : ℝ) ≤ q := by exact_mod_cast (le_max_right B n).trans hq
  have hden : 0 < 2 * (1 - k) := by linarith
  have hlarge : 1 < (q : ℝ) * (2 * (1 - k)) :=
    (div_lt_iff₀ hden).mp (hn.trans_le hnq)
  have hgap : 0 < (1 - (routePPrimeSelectionBias p)^2) * criticalCorrelationUnitMean^2 -
      k * (2 * criticalCorrelationUnitMean^2 / (p : ℕ)) := by
    have heq : (1 - (routePPrimeSelectionBias p)^2) * criticalCorrelationUnitMean^2 -
        k * (2 * criticalCorrelationUnitMean^2 / (p : ℕ)) =
        criticalCorrelationUnitMean^2 * ((2 * (1 - k) * q - 1) / (q : ℝ)^2) := by
      dsimp [routePPrimeSelectionBias, p]
      field_simp
      ring
    rw [heq]
    exact mul_pos (pow_pos criticalCorrelationUnitMean_pos 2)
      (div_pos (by nlinarith) (pow_pos hqpos 2))
  have hevent := (routePBiasedPrimeProjectionGap_tendsto p k).eventually
    (eventually_gt_nhds hgap)
  filter_upwards [hevent, eventually_gt_atTop (0 : ℕ)] with M hM hMpos
  have hMpos' : 0 < (M : ℝ) := by exact_mod_cast hMpos
  have h := (lt_div_iff₀ hMpos').mp hM
  simpa only [zero_mul, sub_pos] using h

end RHTower
