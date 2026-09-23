import GaloisForLFunctions.RHTower.SoninKoplienkoSemilocalOrientationUniversalityLaw
import GaloisForLFunctions.RHTower.SoninPrimePowerWeakTomographyNoGo

/-!
# Sonin prime-power three-channel observability universality

One common narrow wavepacket exposes three simultaneous observability regimes across every
retained Sonin prime power.  Second-order Koplienko data lose coefficient orientation, the
semilocal logarithmic channel retains it linearly, and no sequence of finite combinations of
retained symmetric translation correlations can recover the identity correlation.
-/

open Set MeasureTheory Filter

namespace RHTower

noncomputable section

/-- **Sonin prime-power three-channel observability universality.**  For one narrow wavepacket
with nonzero self-correlation, every retained prime power is quadratically sign-blind,
semilocally sign-sensitive, and individually identity-blind; moreover arbitrary sequences of
finite retained-mode combinations remain unable to converge weakly to the identity
correlation. -/
theorem soninPrimePower_threeChannelObservabilityUniversality
    {lambda : ℝ} (hlambda : 1 < lambda) (hlambdaSq : lambda ^ (2 : ℕ) < 4)
    {f : ℝ → ℂ}
    (hf : Function.support f ⊆ Set.Icc (-Real.log lambda) (Real.log lambda))
    (hself : (∫ x, (starRingEnd ℂ) (f x) * f x) ≠ 0) :
    (∀ (a : ℝ) (pk : Nat.Primes × ℕ),
      soninLogPrimePowerCoefficient pk ≠ -soninLogPrimePowerCoefficient pk ∧
        centralSoninKoplienkoSecondOrderGram a (soninPrimePowerScale pk)
            (one_lt_soninPrimePowerScale pk) (soninLogPrimePowerCoefficient pk) =
          centralSoninKoplienkoSecondOrderGram a (soninPrimePowerScale pk)
            (one_lt_soninPrimePowerScale pk) (-soninLogPrimePowerCoefficient pk) ∧
        semilocalPrimeLogTailMode pk.1 0 pk.2 =
          -2 * (soninLogPrimePowerCoefficient pk).re ∧
        semilocalPrimeLogTailMode pk.1 0 pk.2 ≠
          2 * (soninLogPrimePowerCoefficient pk).re) ∧
    (∀ pk : Nat.Primes × ℕ,
      retainedPrimePowerSymmetricLogCorrelation f pk = 0 ∧
        retainedPrimePowerSymmetricLogCorrelation f pk ≠
          ∫ x, (starRingEnd ℂ) (f x) * f x) ∧
    ∀ (s : ℕ → Finset (Nat.Primes × ℕ))
      (c : ℕ → (Nat.Primes × ℕ) → ℂ),
      ¬ Tendsto
        (fun n => ∑ pk ∈ s n,
          c n pk * retainedPrimePowerSymmetricLogCorrelation f pk)
        atTop (nhds (∫ x, (starRingEnd ℂ) (f x) * f x)) := by
  refine ⟨?_, ?_, ?_⟩
  · exact centralSoninPrimePower_quadraticBlind_linearSemilocalOrientation
  · intro pk
    exact
      ⟨retainedPrimePower_symmetricLogCorrelation_eq_zero
          hlambda hlambdaSq hf pk,
        retainedPrimePower_symmetricLogCorrelation_ne_selfCorrelation
          hlambda hlambdaSq hf hself pk⟩
  · exact
      not_tendsto_finite_retainedPrimePowerLogCorrelations_to_selfCorrelation
        hlambda hlambdaSq hf hself

end

end RHTower
