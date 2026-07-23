import GaloisForLFunctions.RHTower.SoninKoplienkoSecondOrderNoGo
import GaloisForLFunctions.RHTower.SoninSemilocalMetricLog

/-!
# Sonin Koplienko--semilocal orientation universality

The prime-power Koplienko remainder depends only on the squared magnitude of the logarithmic Euler
coefficient.  The semilocal logarithmic metric retains that coefficient linearly.  At the central
spectral parameter this gives an exact orientation separation: `c` and `-c` have identical
second-order Gram data but opposite nonzero scalar logarithmic readouts.
-/

namespace RHTower

noncomputable section

/-- The prime-power Koplienko remainder cannot distinguish the actual logarithmic Euler
coefficient from its negative. -/
theorem centralSoninKoplienkoSecondOrderGram_logCoefficient_neg_invariant
    (a : ℝ) (pk : Nat.Primes × ℕ) :
    centralSoninKoplienkoSecondOrderGram a (soninPrimePowerScale pk)
        (one_lt_soninPrimePowerScale pk) (soninLogPrimePowerCoefficient pk) =
      centralSoninKoplienkoSecondOrderGram a (soninPrimePowerScale pk)
        (one_lt_soninPrimePowerScale pk) (-soninLogPrimePowerCoefficient pk) := by
  rw [centralSoninKoplienkoSecondOrderGram_eq_residualEnergy,
    centralSoninKoplienkoSecondOrderGram_eq_residualEnergy]
  simp

/-- At the central spectral parameter, the semilocal tail reads the same Euler coefficient
linearly, with its orientation intact. -/
theorem semilocalPrimeLogTailMode_zero_eq_neg_two_soninLogCoefficient_re
    (pk : Nat.Primes × ℕ) :
    semilocalPrimeLogTailMode pk.1 0 pk.2 =
      -2 * (soninLogPrimePowerCoefficient pk).re := by
  rw [semilocalPrimeLogTailMode_eq_soninCoefficient_phase]
  simp [MellinL2.mellinCharacter]

/-- **Koplienko--semilocal orientation law.**  The actual coefficient and its negative are
distinct but have identical second-order Gram remainder.  The central semilocal logarithmic
readout equals the actual linear orientation and differs from its sign reversal. -/
theorem centralSoninPrimePower_quadraticBlind_linearSemilocalOrientation
    (a : ℝ) (pk : Nat.Primes × ℕ) :
    soninLogPrimePowerCoefficient pk ≠ -soninLogPrimePowerCoefficient pk ∧
      centralSoninKoplienkoSecondOrderGram a (soninPrimePowerScale pk)
          (one_lt_soninPrimePowerScale pk) (soninLogPrimePowerCoefficient pk) =
        centralSoninKoplienkoSecondOrderGram a (soninPrimePowerScale pk)
          (one_lt_soninPrimePowerScale pk) (-soninLogPrimePowerCoefficient pk) ∧
      semilocalPrimeLogTailMode pk.1 0 pk.2 =
        -2 * (soninLogPrimePowerCoefficient pk).re ∧
      semilocalPrimeLogTailMode pk.1 0 pk.2 ≠
        2 * (soninLogPrimePowerCoefficient pk).re := by
  have hcpos : 0 < (soninLogPrimePowerCoefficient pk).re := by
    rw [soninLogPrimePowerCoefficient, Complex.ofReal_re]
    exact div_pos (Real.sqrt_pos.2 (soninPrimePowerTailEnergy_pos pk)) (by positivity)
  have horientation : soninLogPrimePowerCoefficient pk ≠
      -soninLogPrimePowerCoefficient pk := by
    intro h
    have hre : (soninLogPrimePowerCoefficient pk).re =
        -(soninLogPrimePowerCoefficient pk).re := by
      simpa using congrArg Complex.re h
    linarith
  have hread := semilocalPrimeLogTailMode_zero_eq_neg_two_soninLogCoefficient_re pk
  refine ⟨horientation,
    centralSoninKoplienkoSecondOrderGram_logCoefficient_neg_invariant a pk,
    hread, ?_⟩
  rw [hread]
  linarith

end

end RHTower
