import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.OccupationProbabilities.CoefficientLimits

/-! # The complete invariant of the surviving spectrum -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open ContinuousLinearMap Filter Topology

private theorem moments_eq_of_probability {v w : MissingWave} (h : occupationProbability v = occupationProbability w) :
    ∀ i j, mixedHeatMoment v i j = mixedHeatMoment w i j := by
  have hn (m : ℕ) : nativeVectorMoment v m = nativeVectorMoment w m := by
    rw [nativeVectorMoment_eq_sum,nativeVectorMoment_eq_sum]
    simp only [heatedMass_eq,h]
  intro i j
  induction j generalizing i with
  | zero => simpa only [mixedHeatMoment_zero] using hn i
  | succ j ih => rw [mixedHeatMoment_succ,mixedHeatMoment_succ,ih (i+1),hn i,ih 0]

private theorem levels_antitone (v : MissingWave) : Antitone (fun n => (missingSpectrum v n).val) :=
  antitone_nat_of_succ_le (fun n => (missingSpectrum v (n+1)).property.2.trans (missingSpectrum v n).property.1)

private theorem squared_levels_summable (v : MissingWave) : Summable (fun n => (missingSpectrum v n).val^2) := by
  simpa only [Real.rpow_two] using (summable_band_rpow_iff (missingSpectrum v) 2).mpr (by norm_num)

/-- The normalized Born law is the whole invariant of a rank-one surviving spectrum. -/
theorem missingSpectrum_eq_iff_probability (v w : MissingWave) :
    missingSpectrum v = missingSpectrum w ↔ occupationProbability v = occupationProbability w := by
  refine ⟨occupationProbability_eq_of_spectrum,?_⟩
  intro h
  have he := moments_eq_of_probability h
  have hpow (k : ℕ) : ∑' n, (missingSpectrum v n).val^(k+2) = ∑' n, (missingSpectrum w n).val^(k+2) := by
    apply Complex.ofReal_injective
    have ht : opTrace (squareHeat.val^(k+2)-survivingHeat v^(k+2)) =
        opTrace (squareHeat.val^(k+2)-survivingHeat w^(k+2)) := by
      rw [← mixedHeatMoment_sum v (k+1),← mixedHeatMoment_sum w (k+1)]
      exact Finset.sum_congr rfl (fun j _ => he _ _)
    rw [ordinary_gap_as_sum,ordinary_gap_as_sum] at ht
    linear_combination -ht
  have hsq (k : ℕ) : ∑' n, ((missingSpectrum v n).val^2)^(k+1) =
      ∑' n, ((missingSpectrum w n).val^2)^(k+1) := by
    simpa only [show 2*k+2 = 2*(k+1) by omega,pow_mul] using hpow (2*k)
  have hlev := HTGeometry.antitone_nonneg_eq_of_powerSums_eq (squared_levels_summable v) (squared_levels_summable w)
    (fun n => sq_nonneg _) (fun n => sq_nonneg _)
    (fun i j hij => pow_le_pow_left₀ (band_pos _ j).le (levels_antitone v hij) 2)
    (fun i j hij => pow_le_pow_left₀ (band_pos _ j).le (levels_antitone w hij) 2) hsq
  exact funext (fun n => Subtype.ext ((sq_eq_sq₀ (band_pos _ n).le (band_pos _ n).le).mp (congrFun hlev n)))

/-- A local relative Gibbs germ recovers each occupation probability, even at a zero or the zeta pole. -/
theorem omission_germ_iff_probability (v w : MissingWave) {z : ℂ} (hz : 0 < z.re) :
    omissionPartition v =ᶠ[𝓝 z] omissionPartition w ↔ occupationProbability v = occupationProbability w := by
  rw [← missingSpectrum_eq_iff_probability]
  have h := ordered_germ_iff_levels _ _ (levels_antitone v) (levels_antitone w) hz
  exact ⟨fun hg => funext (fun n => Subtype.ext (h.mp hg n)),fun hs => h.mpr (fun n => congrArg (fun b : SpectralBand 1 => (b n).val) hs)⟩

/-- At the pole the recovered law gives the expected inverse occupation. -/
theorem omission_pole_as_born_mean (v : MissingWave) :
    omissionPartition v 1 = ((∑' n, occupationWeight n*occupationProbability v (number n):ℝ):ℂ) := by
  rw [omissionPartition_pole,← defectVector_norm_sq,← (heatedMass_sum v).tsum_eq]
  simp only [heatedMass_eq]

#print axioms missingSpectrum_eq_iff_probability
#print axioms omission_germ_iff_probability
#print axioms omission_pole_as_born_mean

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
