import GaloisForLFunctions.SelbergClass.Primon.KestenBetaDeformation
import GaloisForLFunctions.SelbergClass.Primon.KestenPowerTilt

/-!
# Exact beta representation of the power-weighted prime laws

Squaring the prime law weighted by `x^(2n)` gives `Beta(n+1/2,3/2)`
reweighted by the same rational function as in degree zero. Its normalizer
is exactly the prime moment divided by the Catalan moment.
-/

open MeasureTheory ProbabilityTheory Set Filter
open GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.SelbergClass.Primon
noncomputable section

/-- The square coordinate under the actual power-weighted prime probability law. -/
def kestenTiltedSquareLaw (p : Nat.Primes) (n : ℕ) : ProbabilityMeasure ℝ :=
  (kestenPowerTiltReal p n).map continuous_heckeSquareCoordinate.measurable.aemeasurable

private theorem interval_square_map (p : Nat.Primes) :
    Measure.map (fun x : Icc (-2 : ℝ) 2 => heckeSquareCoordinate x)
      (kestenIntervalLaw p : Measure (Icc (-2 : ℝ) 2)) = (kestenSquareLaw p : Measure ℝ) := by
  have hc : Continuous (fun x : Icc (-2 : ℝ) 2 => heckeSquareCoordinate x) :=
    continuous_heckeSquareCoordinate.comp continuous_subtype_val
  rw [kestenIntervalLaw, ProbabilityMeasure.toMeasure_map,
    Measure.map_map hc.measurable continuous_projIcc.measurable]
  change Measure.map _ (kestenSpectralLaw p : Measure ℝ) =
    Measure.map heckeSquareCoordinate (kestenSpectralLaw p : Measure ℝ)
  apply Measure.map_congr
  have ha : ∀ᵐ x ∂(kestenSpectralLaw p : Measure ℝ), x ∈ Icc (-2 : ℝ) 2 := by
    rw [ae_iff]
    exact kestenSpectralLaw_carried p
  filter_upwards [ha] with x hx
  simp only [Function.comp_apply, Set.projIcc_of_mem _ hx]

/-- Squaring commutes with normalized even-power weighting. -/
theorem kestenTiltedSquareLaw_eq_powerTilt (p : Nat.Primes) (n : ℕ) :
    (kestenTiltedSquareLaw p n : Measure ℝ) =
      (kestenSquareLaw p : Measure ℝ).withDensity
        (fun u => ENNReal.ofReal (u ^ n / (kestenMoment p (2 * n) / 4 ^ n))) := by
  have hc : Continuous (fun x : Icc (-2 : ℝ) 2 => heckeSquareCoordinate x) :=
    continuous_heckeSquareCoordinate.comp continuous_subtype_val
  change Measure.map heckeSquareCoordinate
    (Measure.map Subtype.val
      ((kestenIntervalLaw p : Measure (Icc (-2 : ℝ) 2)).withDensity
        (fun x => ENNReal.ofReal ((x : ℝ) ^ (2 * n) / kestenMoment p (2 * n))))) = _
  rw [Measure.map_map continuous_heckeSquareCoordinate.measurable continuous_subtype_val.measurable,
    ← interval_square_map p,
    ← map_withDensity_comp _ hc.measurable (by fun_prop)]
  congr 1
  apply withDensity_congr_ae
  exact Eventually.of_forall fun x => by
    change ENNReal.ofReal ((x : ℝ) ^ (2 * n) / kestenMoment p (2 * n)) =
      ENNReal.ofReal (heckeSquareCoordinate x ^ n / (kestenMoment p (2 * n) / 4 ^ n))
    congr 1
    simp only [heckeSquareCoordinate, div_pow, ← pow_mul]
    field_simp

/-- Exact finite-degree law: the beta shape shifts, while the rational prime weight is unchanged. -/
theorem kestenTiltedSquareLaw_eq_beta_withDensity (p : Nat.Primes) (n : ℕ) :
    (kestenTiltedSquareLaw p n : Measure ℝ) =
      (betaMeasure ((n : ℝ) + 1 / 2) (3 / 2)).withDensity
        (fun u => ENNReal.ofReal (kestenBetaWeight p u / kestenMomentRatio p n)) := by
  rw [kestenTiltedSquareLaw_eq_powerTilt, kestenSquareLaw_eq_beta_withDensity,
    ← semicircleSquareLaw_powerTilt n, semicircleSquareLaw_eq_beta,
    ← withDensity_mul _ (continuous_kestenBetaWeight p).measurable.ennreal_ofReal (by fun_prop),
    ← withDensity_mul _ (by fun_prop)
      ((continuous_kestenBetaWeight p).div_const _).measurable.ennreal_ofReal]
  apply withDensity_congr_ae
  filter_upwards [ae_mem_Ioo_betaMeasure (1 / 2) (3 / 2)] with u hu
  change ENNReal.ofReal (kestenBetaWeight p u) *
      ENNReal.ofReal (u ^ n / (kestenMoment p (2 * n) / 4 ^ n)) =
    ENNReal.ofReal (u ^ n / ((catalan n : ℝ) / 4 ^ n)) *
      ENNReal.ofReal (kestenBetaWeight p u / kestenMomentRatio p n)
  rw [← ENNReal.ofReal_mul (kestenBetaWeight_pos p u).le,
    ← ENNReal.ofReal_mul (div_nonneg (pow_nonneg hu.1.le n)
      (div_nonneg (catalan_real_pos n).le (by positivity)))]
  congr 1
  unfold kestenMomentRatio
  field_simp [(catalan_real_pos n).ne', (kestenMoment_even_pos p n).ne']

/-- The rational beta normalizer is exactly the prime-to-Catalan moment ratio. -/
theorem integral_kestenBetaWeight_tiltBeta (p : Nat.Primes) (n : ℕ) :
    (∫ u : ℝ, kestenBetaWeight p u ∂betaMeasure ((n : ℝ) + 1 / 2) (3 / 2)) =
      kestenMomentRatio p n := by
  have h : (∫ u : ℝ, kestenBetaWeight p u / kestenMomentRatio p n
      ∂betaMeasure ((n : ℝ) + 1 / 2) (3 / 2)) = 1 := by
    calc
      _ = ∫ _u : ℝ, (1 : ℝ) ∂(kestenTiltedSquareLaw p n : Measure ℝ) := by
        rw [kestenTiltedSquareLaw_eq_beta_withDensity,
          integral_withDensity_eq_integral_toReal_smul
            ((continuous_kestenBetaWeight p).div_const _).measurable.ennreal_ofReal
            (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
        apply integral_congr_ae
        exact Eventually.of_forall fun u => by
          simp only [smul_eq_mul, mul_one, ENNReal.toReal_ofReal
            (div_nonneg (kestenBetaWeight_pos p u).le (kestenMomentRatio_pos p n).le)]
      _ = 1 := by simp only [integral_const, probReal_univ, one_smul]
  rw [integral_div, div_eq_iff (kestenMomentRatio_pos p n).ne', one_mul] at h
  exact h

/-- Every actual tilted-square observable is a normalized rational beta integral. -/
theorem integral_kestenTiltedSquareLaw (p : Nat.Primes) (n : ℕ) (f : C(ℝ, ℝ)) :
    (∫ u : ℝ, f u ∂(kestenTiltedSquareLaw p n : Measure ℝ)) =
      (∫ u : ℝ, kestenBetaWeight p u * f u
        ∂betaMeasure ((n : ℝ) + 1 / 2) (3 / 2)) / kestenMomentRatio p n := by
  rw [kestenTiltedSquareLaw_eq_beta_withDensity,
    integral_withDensity_eq_integral_toReal_smul
      ((continuous_kestenBetaWeight p).div_const _).measurable.ennreal_ofReal
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top), ← integral_div]
  apply integral_congr_ae
  exact Eventually.of_forall fun u => by
    change (ENNReal.ofReal (kestenBetaWeight p u / kestenMomentRatio p n)).toReal * f u = _
    rw [ENNReal.toReal_ofReal
      (div_nonneg (kestenBetaWeight_pos p u).le (kestenMomentRatio_pos p n).le)]
    ring

/-- All moments of the rational beta family are shifted prime moments. -/
theorem integral_kestenTiltedSquareLaw_pow (p : Nat.Primes) (n k : ℕ) :
    (∫ u : ℝ, u ^ k ∂(kestenTiltedSquareLaw p n : Measure ℝ)) =
      kestenMoment p (2 * (n + k)) / (4 ^ k * kestenMoment p (2 * n)) := by
  have hc : Continuous (fun x : ℝ => heckeSquareCoordinate x ^ k) :=
    continuous_heckeSquareCoordinate.pow k
  rw [kestenTiltedSquareLaw, ProbabilityMeasure.toMeasure_map,
    integral_map continuous_heckeSquareCoordinate.measurable.aemeasurable (by fun_prop),
    kestenPowerTiltReal, ProbabilityMeasure.toMeasure_map,
    integral_map continuous_subtype_val.measurable.aemeasurable hc.aestronglyMeasurable]
  simp only [heckeSquareCoordinate, div_pow, ← pow_mul]
  rw [integral_div, integral_kestenPowerTilt_pow,
    show 2 * n + 2 * k = 2 * (n + k) by omega]
  ring

end
end GaloisForLFunctions.SelbergClass.Primon
