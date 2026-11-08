import GaloisForLFunctions.SelbergClass.Primon.PhaseSpectralLaw
import GaloisForLFunctions.SelbergClass.Primon.SemicircleEdgeMoments
import GaloisForLFunctions.HTGeometry.BetaGammaFactorization

/-!
# The squared semicircle coordinate is a beta variable

Compact moment determinacy identifies `x²/4` under the semicircle and scalar
Fock laws with `Beta(1/2,3/2)`. Power weighting shifts the first beta
parameter, giving exact finite-degree laws behind spectral edge scaling.
-/

open MeasureTheory ProbabilityTheory Set Filter
open GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.SelbergClass.Primon
noncomputable section

/-- Squared Hecke coordinate, normalized to the unit interval. -/
def heckeSquareCoordinate (x : ℝ) : ℝ := x ^ 2 / 4

/-- The normalized square coordinate is continuous. -/
theorem continuous_heckeSquareCoordinate : Continuous heckeSquareCoordinate := by
  unfold heckeSquareCoordinate
  fun_prop

/-- The Hecke interval maps into the unit interval. -/
theorem heckeSquareCoordinate_mem (x : Icc (-2 : ℝ) 2) :
    heckeSquareCoordinate x ∈ Icc (0 : ℝ) 1 := by
  refine ⟨div_nonneg (sq_nonneg _) (by norm_num), ?_⟩
  have h := mul_nonneg (sub_nonneg.mpr x.property.2)
    (show 0 ≤ (x : ℝ) + 2 by linarith only [x.property.1])
  change (x : ℝ) ^ 2 / 4 ≤ 1
  nlinarith only [h]

/-- Actual probability law of the normalized square of the semicircle coordinate. -/
def semicircleSquareLaw : ProbabilityMeasure ℝ :=
  semicircleSpectralLaw.map continuous_heckeSquareCoordinate.measurable.aemeasurable

private theorem squareCoordinate_pow (x : ℝ) (n : ℕ) :
    heckeSquareCoordinate x ^ n = x ^ (2 * n) / 4 ^ n := by
  simp only [heckeSquareCoordinate, div_pow, pow_mul]

/-- Every normalized square moment is integrable. -/
theorem integrable_semicircleSquareLaw_pow (n : ℕ) :
    Integrable (fun u : ℝ => u ^ n) (semicircleSquareLaw : Measure ℝ) := by
  rw [semicircleSquareLaw, ProbabilityMeasure.toMeasure_map,
    integrable_map_measure (by fun_prop) continuous_heckeSquareCoordinate.measurable.aemeasurable]
  change Integrable (fun x => heckeSquareCoordinate x ^ n) (semicircleSpectralLaw : Measure ℝ)
  simp_rw [squareCoordinate_pow]
  exact (semicircleSpectralLaw_hasMoments (2 * n)).1.div_const (4 ^ n)

/-- The normalized squared semicircle has Catalan moments divided by `4^n`. -/
theorem integral_semicircleSquareLaw_pow (n : ℕ) :
    (∫ u : ℝ, u ^ n ∂(semicircleSquareLaw : Measure ℝ)) = (catalan n : ℝ) / 4 ^ n := by
  rw [semicircleSquareLaw, ProbabilityMeasure.toMeasure_map,
    integral_map continuous_heckeSquareCoordinate.measurable.aemeasurable (by fun_prop)]
  simp_rw [squareCoordinate_pow]
  rw [integral_div, (semicircleSpectralLaw_hasMoments (2 * n)).2, semicircleMoment_even]

/-- The squared semicircle law is carried by the unit interval. -/
theorem semicircleSquareLaw_carried :
    (semicircleSquareLaw : Measure ℝ) (Icc (0 : ℝ) 1)ᶜ = 0 := by
  rw [semicircleSquareLaw, ProbabilityMeasure.toMeasure_map,
    Measure.map_apply continuous_heckeSquareCoordinate.measurable measurableSet_Icc.compl]
  apply measure_mono_null (t := (Icc (-2 : ℝ) 2)ᶜ) _ semicircleSpectralLaw_carried
  intro x hx hmem
  exact hx (heckeSquareCoordinate_mem ⟨x, hmem⟩)

private theorem catalan_normalized_succ (n : ℕ) :
    (catalan (n + 1) : ℝ) / 4 ^ (n + 1) =
      (((n : ℝ) + 1 / 2) / (n + 2)) * ((catalan n : ℝ) / 4 ^ n) := by
  have hc (k : ℕ) : (catalan k : ℝ) / 4 ^ k =
      normalizedCentralBinom k / ((k : ℝ) + 1) := by
    have hk : ((k : ℝ) + 1) * (catalan k : ℝ) = (Nat.centralBinom k : ℝ) := by
      exact_mod_cast succ_mul_catalan_eq_centralBinom k
    unfold normalizedCentralBinom
    have hk0 : (k : ℝ) + 1 ≠ 0 := by positivity
    field_simp [hk0]
    simpa only [mul_comm] using hk
  rw [hc (n + 1), hc n, normalizedCentralBinom_succ]
  push_cast
  have hn1 : (n : ℝ) + 1 ≠ 0 := by positivity
  have hn2 : (n : ℝ) + 2 ≠ 0 := by positivity
  have hn3 : 2 * (n : ℝ) + 2 ≠ 0 := by positivity
  field_simp [hn1, hn2, hn3]
  ring

/-- The beta law with parameters `1/2,3/2` has precisely the normalized Catalan moments. -/
theorem integral_semicircleBeta_pow (n : ℕ) :
    (∫ u : ℝ, u ^ n ∂betaMeasure (1 / 2) (3 / 2)) = (catalan n : ℝ) / 4 ^ n := by
  haveI := betaMeasure_isProbability (show (0 : ℝ) < 1 / 2 by norm_num)
    (show (0 : ℝ) < 3 / 2 by norm_num)
  induction n with
  | zero =>
    simp only [pow_zero, integral_const, probReal_univ, one_smul]
    norm_num
  | succ n ih =>
    rw [catalan_normalized_succ, ← ih]
    rw [integral_pow_betaMeasure (by norm_num) (by norm_num),
      integral_pow_betaMeasure (by norm_num) (by norm_num)]
    have ha : (1 / 2 : ℝ) + (n : ℝ) ≠ 0 := by positivity
    have hb : (2 : ℝ) + (n : ℝ) ≠ 0 := by positivity
    rw [show (1 / 2 : ℝ) + 3 / 2 = 2 by norm_num]
    push_cast
    rw [show (1 / 2 : ℝ) + ((n : ℝ) + 1) = (1 / 2 + n) + 1 by ring,
      show (2 : ℝ) + ((n : ℝ) + 1) = (2 + n) + 1 by ring,
      Real.Gamma_add_one ha, Real.Gamma_add_one hb]
    field_simp
    ring

/-- Exact measure identity: the squared semicircle coordinate is `Beta(1/2,3/2)`. -/
theorem semicircleSquareLaw_eq_beta :
    (semicircleSquareLaw : Measure ℝ) = betaMeasure (1 / 2) (3 / 2) := by
  haveI := betaMeasure_isProbability (show (0 : ℝ) < 1 / 2 by norm_num)
    (show (0 : ℝ) < 3 / 2 by norm_num)
  apply _root_.HTGeometry.measure_eq_of_moments_eq_of_one_carried
    (s := fun n => (catalan n : ℝ) / 4 ^ n) (c := 1 / 2) (r := 1 / 2) (by norm_num)
    (by simpa only [show (1 / 2 : ℝ) - 1 / 2 = 0 by norm_num,
      show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num] using semicircleSquareLaw_carried)
  · exact fun n => (integral_semicircleSquareLaw_pow n).symm
  · exact integrable_semicircleSquareLaw_pow
  · exact fun n => (integral_semicircleBeta_pow n).symm
  · exact fun n => integrable_pow_betaMeasure (by norm_num) (by norm_num) n

/-- The same beta law is the square-coordinate distribution of the scalar free Fock operator. -/
theorem scalarFock_square_eq_beta :
    Measure.map heckeSquareCoordinate (scalarFockSpectralLaw : Measure ℝ) =
      betaMeasure (1 / 2) (3 / 2) := by
  rw [← semicircleSpectralLaw_eq_scalarFockSpectralLaw]
  exact semicircleSquareLaw_eq_beta

/-- Weighting the squared semicircle law by its normalized `n`th power shifts its beta shape. -/
theorem semicircleSquareLaw_powerTilt (n : ℕ) :
    (semicircleSquareLaw : Measure ℝ).withDensity
      (fun u => ENNReal.ofReal (u ^ n / ((catalan n : ℝ) / 4 ^ n))) =
      betaMeasure ((n : ℝ) + 1 / 2) (3 / 2) := by
  rw [semicircleSquareLaw_eq_beta, ← integral_semicircleBeta_pow]
  simpa only [add_comm] using withDensity_pow_betaMeasure
    (show (0 : ℝ) < 1 / 2 by norm_num) (show (0 : ℝ) < 3 / 2 by norm_num) n

/-- Mean of the exact power-tilted beta family. -/
theorem integral_semicircleTiltBeta_id (n : ℕ) :
    (∫ u : ℝ, u ∂betaMeasure ((n : ℝ) + 1 / 2) (3 / 2)) =
      ((n : ℝ) + 1 / 2) / (n + 2) := by
  rw [integral_id_betaMeasure (by positivity) (by norm_num)]
  congr 1
  ring

/-- Variance of the exact power-tilted beta family. -/
theorem variance_semicircleTiltBeta (n : ℕ) :
    (∫ u : ℝ, (u - ((n : ℝ) + 1 / 2) / (n + 2)) ^ 2
      ∂betaMeasure ((n : ℝ) + 1 / 2) (3 / 2)) =
      (3 / 2 * ((n : ℝ) + 1 / 2)) / ((n + 2) ^ 2 * (n + 3)) := by
  have h := variance_betaMeasure (show (0 : ℝ) < (n : ℝ) + 1 / 2 by positivity)
    (show (0 : ℝ) < 3 / 2 by norm_num)
  rw [show (n : ℝ) + 1 / 2 + 3 / 2 = n + 2 by ring,
    show (n : ℝ) + 2 + 1 = n + 3 by ring] at h
  rw [h]
  ring

end
end GaloisForLFunctions.SelbergClass.Primon
