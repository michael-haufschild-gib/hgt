import GaloisForLFunctions.SelbergClass.Primon.KestenLogLikelihood
import GaloisForLFunctions.SelbergClass.Primon.SemicircleLogarithmicAverage

/-!
# Exact expectations of the prime log-likelihoods

The inverse square-root prime fugacity turns the even local factor into
the denominator of the prime-to-semicircle density. The logarithmic
phase average therefore evaluates its expectation under every other
prime law, as well as under the semicircle law.
-/

open MeasureTheory Set
open GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.SelbergClass.Primon
noncomputable section

/-- Disk parameter whose fugacity is the inverse square root of the prime. -/
def primeSquareRootDiskParameter (p : Nat.Primes) : ℝ := (Real.sqrt (p : ℝ) - 1)⁻¹

/-- The chosen disk parameter realizes the inverse square-root prime fugacity. -/
theorem cavityDiskCoordinate_prime_sqrt_inverse (p : Nat.Primes) :
    cavityDiskCoordinate (primeSquareRootDiskParameter p) = (Real.sqrt (p : ℝ))⁻¹ := by
  have hp : 1 < (p : ℝ) := by exact_mod_cast p.property.one_lt
  have hp0 : 0 ≤ (p : ℝ) := by positivity
  have hs : 1 < Real.sqrt (p : ℝ) := by
    nlinarith only [Real.sqrt_nonneg (p : ℝ), Real.sq_sqrt hp0, hp]
  have hs0 : Real.sqrt (p : ℝ) ≠ 0 := ne_of_gt (by linarith only [hs])
  have hs1 : 0 < Real.sqrt (p : ℝ) - 1 := sub_pos.mpr hs
  unfold cavityDiskCoordinate primeSquareRootDiskParameter
  rw [abs_of_pos (inv_pos.mpr hs1)]
  field_simp [hs0, hs1.ne']
  ring

/-- Squaring the fugacity gives the prime Poisson radius. -/
theorem cavityDiskCoordinate_prime_sqrt_square (p : Nat.Primes) :
    cavityDiskCoordinate (primeSquareRootDiskParameter p) ^ 2 = (p : ℝ)⁻¹ := by
  rw [cavityDiskCoordinate_prime_sqrt_inverse, inv_pow, Real.sq_sqrt (by positivity)]

/-- In phase coordinates the rational beta weight has the prime Poisson denominator. -/
theorem kestenBetaWeight_phase_rational (p : Nat.Primes) (t : ℝ) :
    kestenBetaWeight p (heckeSquareCoordinate (2 * Real.cos (Real.pi * t))) =
      (1 + (p : ℝ)⁻¹) /
        (1 - 2 * (p : ℝ)⁻¹ * Real.cos (2 * Real.pi * t) + ((p : ℝ)⁻¹) ^ 2) := by
  have hp : 1 < (p : ℝ) := by exact_mod_cast p.property.one_lt
  have hp0 : 0 < (p : ℝ) := by linarith only [hp]
  have hp1 : (p : ℝ) - 1 ≠ 0 := ne_of_gt (by linarith only [hp])
  have hu := heckeSquareCoordinate_mem
    (⟨2 * Real.cos (Real.pi * t), by
      constructor
      · linarith only [Real.neg_one_le_cos (Real.pi * t)]
      · linarith only [Real.cos_le_one (Real.pi * t)]⟩ : Icc (-2 : ℝ) 2)
  have hE : 0 < 1 + 4 * kestenEdgeSlope p *
      (1 - heckeSquareCoordinate (2 * Real.cos (Real.pi * t))) := by
    have h := mul_nonneg
      (mul_nonneg (show (0 : ℝ) ≤ 4 by norm_num) (kestenEdgeSlope_pos p).le)
      (sub_nonneg.mpr hu.2)
    linarith only [h]
  have hr : |(p : ℝ)⁻¹| < 1 := by
    rw [abs_of_pos (inv_pos.mpr hp0)]
    exact (inv_lt_one₀ hp0).2 hp
  have hD := poissonKer_denom_pos hr (2 * Real.pi * t)
  rw [kestenBetaWeight_on_unit p ⟨_, hu⟩]
  rw [show 2 * Real.pi * t = 2 * (Real.pi * t) by ring, Real.cos_two_mul] at hD ⊢
  unfold kestenEdgeScale kestenEdgeSlope heckeSquareCoordinate at hE ⊢
  field_simp [hp0.ne', hp1, hE.ne', hD.ne']
  ring

/-- The spectral log-likelihood is a constant minus an even local-factor logarithm. -/
theorem kestenLogLikelihood_phase (p : Nat.Primes) (t : ℝ) :
    kestenLogLikelihood p (2 * Real.cos (Real.pi * t)) =
      Real.log (1 + (p : ℝ)⁻¹) - evenPhaseLogDenominator (primeSquareRootDiskParameter p) t := by
  have hp : 1 < (p : ℝ) := by exact_mod_cast p.property.one_lt
  have hp0 : 0 < (p : ℝ) := by linarith only [hp]
  have hr : |(p : ℝ)⁻¹| < 1 := by
    rw [abs_of_pos (inv_pos.mpr hp0)]
    exact (inv_lt_one₀ hp0).2 hp
  have hD := poissonKer_denom_pos hr (2 * Real.pi * t)
  have hN : 0 < 1 + (p : ℝ)⁻¹ := by positivity
  rw [kestenLogLikelihood, kestenBetaWeight_phase_rational, Real.log_div hN.ne' hD.ne',
    evenPhaseLogDenominator, cavityDiskCoordinate_prime_sqrt_square]

/-- Every prime log-likelihood has an explicit expectation under every prime law. -/
theorem integral_kestenLogLikelihood_cross (p q : Nat.Primes) :
    (∫ x, kestenLogLikelihood p x ∂(kestenSpectralLaw q : Measure ℝ)) =
      Real.log (1 + (p : ℝ)⁻¹) + ((q : ℝ) - 1) *
        Real.log (1 - ((p : ℝ) * (q : ℝ))⁻¹) := by
  have h := integral_kestenSpectralLaw q ⟨_, continuous_kestenLogLikelihood p⟩
  change (∫ x, kestenLogLikelihood p x ∂(kestenSpectralLaw q : Measure ℝ)) =
    ∫ t in Ioo (0 : ℝ) 1, kestenMcKayDensity q t *
      kestenLogLikelihood p (2 * Real.cos (Real.pi * t)) at h
  rw [h]
  have he (t : ℝ) : kestenMcKayDensity q t *
      kestenLogLikelihood p (2 * Real.cos (Real.pi * t)) =
      Real.log (1 + (p : ℝ)⁻¹) * kestenMcKayDensity q t -
        kestenMcKayDensity q t * evenPhaseLogDenominator (primeSquareRootDiskParameter p) t := by
    rw [kestenLogLikelihood_phase]
    ring
  simp_rw [he]
  have hi : IntegrableOn (kestenMcKayDensity q) (Ioo (0 : ℝ) 1) :=
    (continuous_kestenMcKayDensity q).continuousOn.integrableOn_Icc.mono_set Ioo_subset_Icc_self
  have hj : IntegrableOn (fun t => kestenMcKayDensity q t *
      evenPhaseLogDenominator (primeSquareRootDiskParameter p) t) (Ioo (0 : ℝ) 1) :=
    ((continuous_kestenMcKayDensity q).mul
      (continuous_evenPhaseLogDenominator _)).continuousOn.integrableOn_Icc.mono_set Ioo_subset_Icc_self
  rw [integral_sub (hi.const_mul _) hj, integral_const_mul, integral_kestenMcKayDensity,
    mul_one, integral_kesten_evenPhaseLog, cavityDiskCoordinate_prime_sqrt_square]
  have heq : (p : ℝ)⁻¹ / (q : ℝ) = ((p : ℝ) * (q : ℝ))⁻¹ := by
    ring
  rw [heq]
  ring

/-- The semicircle expectation of the prime log-likelihood is a logarithmic deficit. -/
theorem integral_semicircleLogLikelihood (p : Nat.Primes) :
    (∫ x, kestenLogLikelihood p x ∂(semicircleSpectralLaw : Measure ℝ)) =
      Real.log (1 + (p : ℝ)⁻¹) - (p : ℝ)⁻¹ := by
  have h := integral_semicircleSpectralLaw ⟨_, continuous_kestenLogLikelihood p⟩
  change (∫ x, kestenLogLikelihood p x ∂(semicircleSpectralLaw : Measure ℝ)) =
    ∫ t in Ioo (0 : ℝ) 1, semicirclePhaseDensity t *
      kestenLogLikelihood p (2 * Real.cos (Real.pi * t)) at h
  rw [h]
  have he (t : ℝ) : semicirclePhaseDensity t *
      kestenLogLikelihood p (2 * Real.cos (Real.pi * t)) =
      Real.log (1 + (p : ℝ)⁻¹) * semicirclePhaseDensity t -
        semicirclePhaseDensity t * evenPhaseLogDenominator (primeSquareRootDiskParameter p) t := by
    rw [kestenLogLikelihood_phase]
    ring
  simp_rw [he]
  have hc : Continuous semicirclePhaseDensity := by unfold semicirclePhaseDensity; fun_prop
  have hi : IntegrableOn semicirclePhaseDensity (Ioo (0 : ℝ) 1) :=
    hc.continuousOn.integrableOn_Icc.mono_set Ioo_subset_Icc_self
  have hj : IntegrableOn (fun t => semicirclePhaseDensity t *
      evenPhaseLogDenominator (primeSquareRootDiskParameter p) t) (Ioo (0 : ℝ) 1) :=
    (hc.mul (continuous_evenPhaseLogDenominator _)).continuousOn.integrableOn_Icc.mono_set
      Ioo_subset_Icc_self
  rw [integral_sub (hi.const_mul _) hj, integral_const_mul, integral_semicirclePhaseDensity,
    mul_one, integral_semicircle_evenPhaseLog, cavityDiskCoordinate_prime_sqrt_square]

/-- The self-expectation is the explicit prime-to-semicircle entropy expression. -/
theorem integral_kestenLogLikelihood_self (p : Nat.Primes) :
    (∫ x, kestenLogLikelihood p x ∂(kestenSpectralLaw p : Measure ℝ)) =
      Real.log (1 + (p : ℝ)⁻¹) + ((p : ℝ) - 1) * Real.log (1 - ((p : ℝ)⁻¹) ^ 2) := by
  rw [integral_kestenLogLikelihood_cross]
  congr 3
  rw [← pow_two, inv_pow]

end
end GaloisForLFunctions.SelbergClass.Primon
