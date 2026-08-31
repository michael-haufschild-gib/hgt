import GaloisForLFunctions.RHTower.GammaSewnSynchronizedRecoveryDiffusePrimeWard
import GaloisForLFunctions.RHTower.SoninAllPrimeZerothMomentApertureSurjectivity

open Complex Filter Topology
open scoped BigOperators

noncomputable section

namespace RHTower

/-- Effective Sonin aperture carried by one diffuse local aperture, its full prime-log action,
and the canonical unit collar.  No Xi divisor enters this definition. -/
def gammaSewnDiffusePrimeEffectiveSoninAperture (τ : ℝ) (N : ℕ) : ℝ :=
  gammaSewnDiffusePrimeAperture τ N *
    (1 + ∑ p ∈ GaloisForLFunctions.primesBelowSubtype N,
      Real.log (p : ℝ))

theorem gammaSewnDiffusePrimeEffectiveSoninAperture_eq
    (τ : ℝ) (N : ℕ) :
    gammaSewnDiffusePrimeEffectiveSoninAperture τ N =
      gammaSewnDiffusePrimeAperture τ N +
        gammaSewnDiffusePrimeAperture τ N *
          ∑ p ∈ GaloisForLFunctions.primesBelowSubtype N,
            Real.log (p : ℝ) := by
  unfold gammaSewnDiffusePrimeEffectiveSoninAperture
  ring

theorem gammaSewnDiffusePrimeEffectiveSoninAperture_pos
    {τ : ℝ} (hτ : 0 < τ) (N : ℕ) :
    0 < gammaSewnDiffusePrimeEffectiveSoninAperture τ N := by
  have hsum : 0 ≤ ∑ p ∈ GaloisForLFunctions.primesBelowSubtype N,
      Real.log (p : ℝ) := by
    exact Finset.sum_nonneg fun p _ => Real.log_natCast_nonneg p
  unfold gammaSewnDiffusePrimeEffectiveSoninAperture
  exact mul_pos (gammaSewnDiffusePrimeAperture_pos hτ N) (by linarith)

/-- Vanishing local prime apertures retain a fixed positive collective Sonin aperture. -/
theorem tendsto_gammaSewnDiffusePrimeEffectiveSoninAperture
    (τ : ℝ) :
    Tendsto (gammaSewnDiffusePrimeEffectiveSoninAperture τ) atTop (nhds τ) := by
  have h := (tendsto_gammaSewnDiffusePrimeAperture_zero τ).add
    (tendsto_gammaSewnDiffusePrimeAperture_totalPhase τ)
  have heff : Tendsto (gammaSewnDiffusePrimeEffectiveSoninAperture τ)
      atTop (nhds (0 + τ)) :=
    h.congr' (Filter.Eventually.of_forall fun N =>
      (gammaSewnDiffusePrimeEffectiveSoninAperture_eq τ N).symm)
  simpa using heff

/-- Every intrinsic Sonin moment follows the collective, rather than local, diffuse aperture. -/
theorem tendsto_soninAllPrimeEnergyMoment_diffusePrimeEffective
    {τ : ℝ} (hτ : 0 < τ) (r : ℕ) :
    Tendsto
      (fun N => soninAllPrimeEnergyMoment
        (gammaSewnDiffusePrimeEffectiveSoninAperture τ N) r)
      atTop (nhds (soninAllPrimeEnergyMoment τ r)) := by
  exact tendsto_soninAllPrimeEnergyMoment_of_tendsto
    (gammaSewnDiffusePrimeEffectiveSoninAperture_pos hτ) hτ
    (tendsto_gammaSewnDiffusePrimeEffectiveSoninAperture τ) r

/-- Multi-gate source weld.  One source-selected positive collective aperture simultaneously
retains vanishing local apertures, exact zeroth completed-moment landing, unconditional Sonin
order, and locally faithful but collectively damped Gamma recovery. -/
theorem exists_gammaSewnDiffusePrime_soninOrder_coefficientFaithful_zerothWeld :
    ∃ τ : ℝ, 0 < τ ∧
      Tendsto (gammaSewnDiffusePrimeAperture τ) atTop (nhds 0) ∧
      (∀ N, 0 < gammaSewnDiffusePrimeEffectiveSoninAperture τ N) ∧
      Tendsto (gammaSewnDiffusePrimeEffectiveSoninAperture τ) atTop (nhds τ) ∧
      Tendsto
        (fun N => soninAllPrimeEnergyMoment
          (gammaSewnDiffusePrimeEffectiveSoninAperture τ N) 0)
        atTop (nhds ((normalizedPrimeArchMoment 0 : ℝ) : ℂ)) ∧
      (∀ N (P : Polynomial ℝ),
        0 ≤ (soninAllPrimeTraceHankel
          (gammaSewnDiffusePrimeEffectiveSoninAperture τ N) P).re) ∧
      ∀ (nu : Nat.Primes → ℝ), (∀ p, 0 < nu p) →
        (∀ p : Nat.Primes,
          Tendsto
            (fun N =>
              gammaSewnMobiusValuationContractionMultiplier
                  (gammaSewnDiffusePrimeAperture τ N) p *
                exponentialChordFactor
                  (gammaSewnDiffusePrimeAperture τ N * Real.log (p : ℝ)))
            atTop (nhds 1)) ∧
        Tendsto
          (fun N => gammaSewnSynchronizedRecoveryRatio nu
            (gammaSewnDiffusePrimeAperture τ N)
            (GaloisForLFunctions.primesBelowSubtype N))
          atTop (nhds (τ / (2 * Real.sinh (τ / 2)))) ∧
        0 < τ / (2 * Real.sinh (τ / 2)) ∧
          τ / (2 * Real.sinh (τ / 2)) < 1 := by
  obtain ⟨τ, hτ, hzero⟩ :=
    exists_positive_aperture_soninAllPrimeEnergyMoment_zero_eq_normalizedPrimeArchMoment
  refine ⟨τ, hτ, tendsto_gammaSewnDiffusePrimeAperture_zero τ,
    gammaSewnDiffusePrimeEffectiveSoninAperture_pos hτ,
    tendsto_gammaSewnDiffusePrimeEffectiveSoninAperture τ, ?_, ?_, ?_⟩
  · simpa [hzero] using
      (tendsto_soninAllPrimeEnergyMoment_diffusePrimeEffective hτ 0)
  · intro N P
    exact soninAllPrimeTraceHankel_re_nonneg _ P
  · intro nu hnu
    exact gammaSewnDiffusePrimeRecovery_localFaithful_collectivelyDamped nu hnu hτ

end RHTower
