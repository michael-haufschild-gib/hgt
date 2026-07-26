import GaloisForLFunctions.RHTower.DeningerCohomologicalResolventPassivityUniversalityLaw
import GaloisForLFunctions.RHTower.PrimeArchEntropyProductionResponseRH

/-!
# Deninger entropy-production thermodynamic-limit universality

Pointwise thermodynamic convergence of finite Hermitian KMS entropy-production responses to the
Deninger divisor resolvent automatically converges to the continued prime--archimedean source.
Finite entropy-production positivity then closes simultaneously to source and cohomological
passivity, the one-Cauchy gate, and RH.
-/

open Filter Topology GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

/--
The Deninger Lefschetz identity transports pointwise thermodynamic convergence from the
cohomological divisor resolvent to the continued prime--archimedean source.
-/
theorem finiteKMSEntropyProductionResponse_tendsto_continuedPrimeArch_of_tendsto_deninger
    (d : ℕ → ℕ) (β : ℕ → ℝ)
    (energy : ∀ N, Fin (d N + 1) → ℝ)
    (amplitude : ∀ N, Fin (d N + 1) → Fin (d N + 1) → ℂ)
    (hconvDeninger : ∀ z : ℂ, 0 < z.im → z.im < 1 / 2 →
      riemannZeta (1 / 2 + z * Complex.I) ≠ 0 →
        Tendsto (fun N ↦ HTGeometry.finiteTransitionPassiveResponse
          (finiteKMSEntropyProductionTransitionIntensity
            (β N) (energy N) (amplitude N)) (energy N) z)
          atTop (nhds (deningerDivisorRelativeResolventTrace z))) :
    ∀ z : ℂ, 0 < z.im → z.im < 1 / 2 →
      riemannZeta (1 / 2 + z * Complex.I) ≠ 0 →
        Tendsto (fun N ↦ HTGeometry.finiteTransitionPassiveResponse
          (finiteKMSEntropyProductionTransitionIntensity
            (β N) (energy N) (amplitude N)) (energy N) z)
          atTop (nhds (continuedPrimeArchSourceRelativeTrace z)) := by
  intro z hzpos hzhalf hzeta
  have hadm :=
    xiExplicitAdmissible_of_mem_centeredUpperHalfStrip hzpos hzhalf hzeta
  simpa only [deningerResolventLefschetzTrace hadm] using
    hconvDeninger z hzpos hzhalf hzeta

/--
**Deninger entropy-production thermodynamic-limit universality.**

Any pointwise thermodynamic limit of finite Hermitian KMS entropy-production responses that
realizes the Deninger divisor resolvent also realizes the arithmetic source and forces both
passivity formulations, the one-Cauchy gate, and RH.
-/
theorem deninger_entropyProductionThermodynamicLimitUniversality
    (d : ℕ → ℕ) (β : ℕ → ℝ)
    (energy : ∀ N, Fin (d N + 1) → ℝ)
    (amplitude : ∀ N, Fin (d N + 1) → Fin (d N + 1) → ℂ)
    (hHermitian : ∀ N a b, amplitude N b a = star (amplitude N a b))
    (hconvDeninger : ∀ z : ℂ, 0 < z.im → z.im < 1 / 2 →
      riemannZeta (1 / 2 + z * Complex.I) ≠ 0 →
        Tendsto (fun N ↦ HTGeometry.finiteTransitionPassiveResponse
          (finiteKMSEntropyProductionTransitionIntensity
            (β N) (energy N) (amplitude N)) (energy N) z)
          atTop (nhds (deningerDivisorRelativeResolventTrace z))) :
    (∀ z : ℂ, 0 < z.im → z.im < 1 / 2 →
      riemannZeta (1 / 2 + z * Complex.I) ≠ 0 →
        Tendsto (fun N ↦ HTGeometry.finiteTransitionPassiveResponse
          (finiteKMSEntropyProductionTransitionIntensity
            (β N) (energy N) (amplitude N)) (energy N) z)
          atTop (nhds (continuedPrimeArchSourceRelativeTrace z))) ∧
      ContinuedPrimeArchUpperAntiHerglotz ∧
      DeningerDivisorUpperAntiHerglotz ∧
      ContinuedPrimeArchUpperCauchyDiagonalNonnegative ∧
      RiemannHypothesis := by
  have hconvSource :=
    finiteKMSEntropyProductionResponse_tendsto_continuedPrimeArch_of_tendsto_deninger
      d β energy amplitude hconvDeninger
  have hsource :=
    continuedPrimeArchUpperAntiHerglotz_of_finiteKMSEntropyProductionResponse_tendsto
      d β energy amplitude hHermitian hconvSource
  have hdeninger :=
    deningerDivisorUpperAntiHerglotz_iff_continuedPrimeArchUpperAntiHerglotz.mpr hsource
  have hcauchy :=
    continuedPrimeArchUpperCauchyDiagonalNonnegative_of_finiteKMSEntropyProductionResponse_tendsto
      d β energy amplitude hHermitian hconvSource
  have hrh :=
    riemannHypothesis_of_finiteKMSEntropyProductionResponse_tendsto
      d β energy amplitude hHermitian hconvSource
  exact ⟨hconvSource, hsource, hdeninger, hcauchy, hrh⟩

end

end RHTower
