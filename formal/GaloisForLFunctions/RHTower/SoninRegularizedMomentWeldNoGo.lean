import GaloisForLFunctions.RHTower.SoninRegularizedMomentSpectrum

/-!
# Scoped retirement of the literal regularized F2 moment producer

Exact source moment matching forces the full Xi reciprocal singular sequence. The source
logarithmic prefix budget contradicts its squared-log Riemann--von Mangoldt growth.
The final exclusions are unconditional; they do not assert RH.
-/

open Filter Topology ContinuousLinearMap
open scoped BigOperators
namespace RHTower
noncomputable section

theorem nonneg_sequence_eq_of_summable_square_moments
    {a b : ℕ → ℝ} (ha : Summable (fun n => a n ^ 2))
    (hb : Summable (fun n => b n ^ 2))
    (ha0 : ∀ n, 0 ≤ a n) (hb0 : ∀ n, 0 ≤ b n)
    (haa : Antitone a) (hba : Antitone b)
    (hm : ∀ r : ℕ, ∑' n, ((a n ^ 2 : ℝ) : ℂ) ^ (r + 1) =
      ∑' n, ((b n ^ 2 : ℝ) : ℂ) ^ (r + 1)) : a = b := by
  have heq : (fun n => a n ^ 2) = (fun n => b n ^ 2) := by
    apply GaloisForLFunctions.HTGeometry.antitone_nonneg_eq_of_powerSums_eq ha hb
      (fun n => sq_nonneg _) (fun n => sq_nonneg _)
      (fun _ _ h => pow_le_pow_left₀ (ha0 _) (haa h) 2)
      (fun _ _ h => pow_le_pow_left₀ (hb0 _) (hba h) 2)
    intro r
    apply Complex.ofReal_injective
    rw [Complex.ofReal_tsum, Complex.ofReal_tsum]
    simpa only [Complex.ofReal_pow] using hm r
  funext n
  have hsq := congrFun heq n
  nlinarith [ha0 n, hb0 n]

theorem soninAllPrimeResidual_approxNumber_eq_orderedXi_of_exactMoments
    (a : ℝ) (ha : 0 < a)
    (hm : ∀ r : ℕ, soninAllPrimeEnergyMoment a r = (normalizedPrimeArchMoment r : ℂ)) :
    approxNumber (soninAllPrimeResidualOperator a ha) =
      approxNumber xiOrderedSignedPrimeOperator := by
  have hRH := riemannHypothesis_of_soninAllPrimeExactPositiveApertureMomentWeld ⟨a, ha, hm⟩
  have hAsq : Summable (fun n => approxNumber (soninAllPrimeResidualOperator a ha) n ^ 2) := by
    have h := (memSchattenClass_two_iff_isHilbertSchmidt _).mpr
      (soninAllPrimeResidualOperator_isHilbertSchmidt a ha)
    simpa [MemSchattenClass, Real.rpow_two] using h
  have hBsq : Summable (fun n => approxNumber xiOrderedSignedPrimeOperator n ^ 2) := by
    simpa [MemSchattenClass, Real.rpow_two] using xiOrderedSignedPrimeOperator_memSchattenClass_two
  apply nonneg_sequence_eq_of_summable_square_moments hAsq hBsq
    (approxNumber_nonneg _) (approxNumber_nonneg _)
    (approxNumber_antitone _) (approxNumber_antitone _)
  intro r
  rw [← soninAllPrimeEnergyMoment_eq_approxNumber_moments,
    ← normalizedPrimeArchMoment_eq_orderedXi_approxNumber_moments_of_rh hRH, hm r]

/-- No positive finite aperture of the literal regularized block-diagonal source can match
all prime--Gamma moments. The contradiction is spectral growth, not an RH assumption. -/
theorem not_soninAllPrime_exact_positive_aperture_moments
    (a : ℝ) (ha : 0 < a) :
    ¬ (∀ r : ℕ, soninAllPrimeEnergyMoment a r = (normalizedPrimeArchMoment r : ℂ)) := by
  intro hm
  have heq := soninAllPrimeResidual_approxNumber_eq_orderedXi_of_exactMoments a ha hm
  have hzero := tendsto_schattenOnePrefix_soninAllPrimeResidual_div_logSq a ha
  simp only [schattenPowerPartialSum, Real.rpow_one, heq] at hzero
  have hbad := tendsto_nhds_unique hzero
    tendsto_xiOrderedSignedPrimeOperator_approxNumber_partialSum_div_logSq
  have hp : (0 : ℝ) < 1 / (2 * Real.pi) := by positivity
  exact hp.ne hbad

/-- Scoped F2 retirement: compact-aperture capture plus the literal source spectral budget
excludes the existing all-prime regularized trace-moment weld. -/
theorem not_soninAllPrimeExactTraceMomentWeld : ¬ SoninAllPrimeExactTraceMomentWeld := by
  rw [soninAllPrimeExactTraceMomentWeld_iff_exists_exact_positive_aperture]
  rintro ⟨a, ha, hm⟩
  exact not_soninAllPrime_exact_positive_aperture_moments a ha hm

end
end RHTower
