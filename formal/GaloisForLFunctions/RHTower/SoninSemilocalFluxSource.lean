/-
# The semilocal Sonin coefficient is the von-Mangoldt source coefficient

The trace-density normalization isolated in `SoninSemilocalRelativeTrace` targets the static
logarithmic scale length `log(p^m)`.  Multiplying the logarithmic Euler coefficient
`p^(-m/2)/m` by that length gives `log(p) p^(-m/2)`, exactly the von-Mangoldt prime-power
coefficient.  This file connects the Sonin carrier to the already formalized arithmetic source;
the only remaining identity is the geometric response law itself.
-/
import GaloisForLFunctions.RHTower.SoninSemilocalRelativeTrace
import GaloisForLFunctions.RHTower.SeamFluxCochain

namespace RHTower

noncomputable section

theorem vonMangoldt_prime_pow_succ_eq_log (pk : Nat.Primes × ℕ) :
    ArithmeticFunction.vonMangoldt (pk.1 ^ (pk.2 + 1)) = Real.log pk.1 := by
  have h := vonMangoldt_eq_flux_over_length pk.1.prop
    (r := pk.2 + 1) (by omega)
  rw [flux_over_length_eq_log pk.1 (by omega)] at h
  exact h

/-- The target local Sonin flux coefficient is literally the von-Mangoldt coefficient times the
central reciprocal square-root prime-power amplitude. -/
theorem soninSemilocalPrimeFluxCoefficient_eq_vonMangoldt (pk : Nat.Primes × ℕ) :
    soninSemilocalPrimeFluxCoefficient pk =
      ((ArithmeticFunction.vonMangoldt (pk.1 ^ (pk.2 + 1)) : ℂ) *
        (((Real.sqrt (pk.1 : ℝ))⁻¹ ^ (pk.2 + 1) : ℝ) : ℂ)) := by
  rw [soninSemilocalPrimeFluxCoefficient_eq, vonMangoldt_prime_pow_succ_eq_log]
  norm_cast
  ring

/-- The finite von-Mangoldt source functional on compact-support prime-power tests. -/
def finiteVonMangoldtCentralTrace (f : SoninPrimePowerTest) : ℂ :=
  f.sum fun pk w => w *
    ((ArithmeticFunction.vonMangoldt (pk.1 ^ (pk.2 + 1)) : ℂ) *
      (((Real.sqrt (pk.1 : ℝ))⁻¹ ^ (pk.2 + 1) : ℝ) : ℂ))

theorem finitePrimeFluxTrace_eq_finiteVonMangoldtCentralTrace
    (f : SoninPrimePowerTest) :
    finitePrimeFluxTrace f = finiteVonMangoldtCentralTrace f := by
  rw [finitePrimeFluxTrace, finiteVonMangoldtCentralTrace]
  apply Finsupp.sum_congr
  intro pk hpk
  rw [soninSemilocalPrimeFluxCoefficient_eq_vonMangoldt]

/-- The remaining geometric normalization is exactly equivalent to equality of the canonical
Sonin trace and the finite von-Mangoldt source on every compact-support test. -/
theorem soninSemilocalFluxNormalization_iff_finiteTrace_eq_vonMangoldt :
    SoninSemilocalFluxNormalization ↔
      ∀ f : SoninPrimePowerTest,
        canonicalFiniteSoninSemilocalRelativeTrace f =
          finiteVonMangoldtCentralTrace f := by
  rw [soninSemilocalFluxNormalization_iff_finiteTrace_eq]
  constructor
  · intro h f
    rw [h f, finitePrimeFluxTrace_eq_finiteVonMangoldtCentralTrace]
  · intro h f
    rw [finitePrimeFluxTrace_eq_finiteVonMangoldtCentralTrace]
    exact h f

end

end RHTower
