import GaloisForLFunctions.SelbergClass.Primon.KestenBetaDeformation

/-!
# Squaring preserves relative entropy between prime spectral laws

Every likelihood ratio in the prime spectral family, including its
semicircle limit, factors through the normalized square coordinate.
The deterministic square observation preserves both directed relative
entropies. The discarded sign carries no information distinguishing
members of this family.
-/

open MeasureTheory ProbabilityTheory InformationTheory Filter
open GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.SelbergClass.Primon
noncomputable section

/-- The reciprocal square-dependent weight recovers the semicircle law from every prime law. -/
theorem semicircleSpectralLaw_eq_kesten_withDensity (p : Nat.Primes) :
    (semicircleSpectralLaw : Measure ℝ) = (kestenSpectralLaw p : Measure ℝ).withDensity
      ((fun u => ENNReal.ofReal ((kestenBetaWeight p u)⁻¹)) ∘ heckeSquareCoordinate) := by
  have hi : Measurable (fun u : ℝ => ENNReal.ofReal ((kestenBetaWeight p u)⁻¹)) :=
    (continuous_kestenBetaWeight p).measurable.inv.ennreal_ofReal
  rw [kestenSpectralLaw_eq_semicircle_withDensity,
    ← withDensity_mul _
      ((continuous_kestenBetaWeight p).measurable.ennreal_ofReal.comp
        continuous_heckeSquareCoordinate.measurable)
      (hi.comp continuous_heckeSquareCoordinate.measurable)]
  have he : ((fun u => ENNReal.ofReal (kestenBetaWeight p u)) ∘ heckeSquareCoordinate) *
      ((fun u => ENNReal.ofReal ((kestenBetaWeight p u)⁻¹)) ∘ heckeSquareCoordinate) =
        (fun _ => (1 : ENNReal)) := by
    funext x
    simp only [Pi.mul_apply, Function.comp_apply]
    rw [← ENNReal.ofReal_mul (kestenBetaWeight_pos p _).le,
      mul_inv_cancel₀ (kestenBetaWeight_pos p _).ne', ENNReal.ofReal_one]
  rw [he]
  change (semicircleSpectralLaw : Measure ℝ) = (semicircleSpectralLaw : Measure ℝ).withDensity 1
  exact withDensity_one.symm

/-- Squaring is sufficient for distinguishing a prime spectral law from the semicircle law. -/
theorem kestenSquare_isKLPairSufficient (p : Nat.Primes) :
    IsKLPairSufficient (kestenSpectralLaw p : Measure ℝ) (semicircleSpectralLaw : Measure ℝ)
      heckeSquareCoordinate :=
  isKLPairSufficient_of_density_comp continuous_heckeSquareCoordinate.measurable
    (continuous_kestenBetaWeight p).measurable.ennreal_ofReal
    (continuous_kestenBetaWeight p).measurable.inv.ennreal_ofReal
    (kestenSpectralLaw_eq_semicircle_withDensity p)
    (semicircleSpectralLaw_eq_kesten_withDensity p)

/-- The prime-to-semicircle relative entropy equals the rational-beta-to-beta relative entropy. -/
theorem kesten_klDiv_eq_square_beta (p : Nat.Primes) :
    klDiv (kestenSpectralLaw p : Measure ℝ) (semicircleSpectralLaw : Measure ℝ) =
      klDiv (kestenSquareLaw p : Measure ℝ) (betaMeasure (1 / 2) (3 / 2)) := by
  rw [← semicircleSquareLaw_eq_beta]
  exact (kestenSquare_isKLPairSufficient p).1.symm

/-- The reverse relative entropy is also preserved by the square observation. -/
theorem semicircle_klDiv_eq_beta_square (p : Nat.Primes) :
    klDiv (semicircleSpectralLaw : Measure ℝ) (kestenSpectralLaw p : Measure ℝ) =
      klDiv (betaMeasure (1 / 2) (3 / 2)) (kestenSquareLaw p : Measure ℝ) := by
  rw [← semicircleSquareLaw_eq_beta]
  exact (kestenSquare_isKLPairSufficient p).2.symm

/-- No directed relative-entropy imbalance is hidden in the discarded sign coordinate. -/
theorem kestenSquare_observerFibreChirality_zero (p : Nat.Primes) :
    observerFibreChirality (kestenSpectralLaw p : Measure ℝ) (semicircleSpectralLaw : Measure ℝ)
      heckeSquareCoordinate = 0 :=
  observerFibreChirality_eq_zero_of_pairSufficient _ _ _ (kestenSquare_isKLPairSufficient p)

/-- Likelihood ratios between any two prime laws are ratios of their rational beta weights. -/
theorem kestenSpectralLaw_eq_prime_withDensity (p q : Nat.Primes) :
    (kestenSpectralLaw p : Measure ℝ) = (kestenSpectralLaw q : Measure ℝ).withDensity
      ((fun u => ENNReal.ofReal (kestenBetaWeight p u / kestenBetaWeight q u)) ∘
        heckeSquareCoordinate) := by
  have hi : Measurable (fun u : ℝ => ENNReal.ofReal ((kestenBetaWeight q u)⁻¹)) :=
    (continuous_kestenBetaWeight q).measurable.inv.ennreal_ofReal
  rw [kestenSpectralLaw_eq_semicircle_withDensity p,
    semicircleSpectralLaw_eq_kesten_withDensity q,
    ← withDensity_mul _
      (hi.comp continuous_heckeSquareCoordinate.measurable)
      ((continuous_kestenBetaWeight p).measurable.ennreal_ofReal.comp
        continuous_heckeSquareCoordinate.measurable)]
  apply withDensity_congr_ae
  exact Eventually.of_forall fun x => by
    change ENNReal.ofReal ((kestenBetaWeight q (heckeSquareCoordinate x))⁻¹) *
      ENNReal.ofReal (kestenBetaWeight p (heckeSquareCoordinate x)) = _
    rw [← ENNReal.ofReal_mul (inv_nonneg.mpr (kestenBetaWeight_pos q _).le)]
    congr 1
    ring

/-- Squaring preserves both directed relative entropies between every pair of prime laws. -/
theorem primeSquare_isKLPairSufficient (p q : Nat.Primes) :
    IsKLPairSufficient (kestenSpectralLaw p : Measure ℝ) (kestenSpectralLaw q : Measure ℝ)
      heckeSquareCoordinate :=
  isKLPairSufficient_of_density_comp continuous_heckeSquareCoordinate.measurable
    ((continuous_kestenBetaWeight p).measurable.div
      (continuous_kestenBetaWeight q).measurable).ennreal_ofReal
    ((continuous_kestenBetaWeight q).measurable.div
      (continuous_kestenBetaWeight p).measurable).ennreal_ofReal
    (kestenSpectralLaw_eq_prime_withDensity p q)
    (kestenSpectralLaw_eq_prime_withDensity q p)

end
end GaloisForLFunctions.SelbergClass.Primon
