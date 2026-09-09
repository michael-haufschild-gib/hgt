import GaloisForLFunctions.HTGeometry.GomesCanonicalMomentGeometry
import GaloisForLFunctions.HTGeometry.GomesMomentMassScale

/-!
Mass characters of full internal-frame observations. This applies the distinction
between invariant scalar data and covariant tensor data in Gomes, arXiv:2404.10461,
arXiv:2509.25276v7, and arXiv:2607.24901v1, to actual moment sources.
Monic frames forget mass, while weighted Gram and flux tensors transform with its
inverse character. The flux's exact stabilizer also detects the real boundary.
These are corpus applications, not numbered paper transcriptions.
-/
open scoped Matrix ComplexOrder
noncomputable section
namespace GaloisForLFunctions.HTGeometry
open _root_.HTGeometry

/-- Positive mass rescaling realized inside the closed concrete-model interface. -/
def gomesMassScaledModel (M : GomesMomentModel) (r : ℝ) : GomesMomentModel :=
  gomesCanonicalMomentModel (gomesMomentMassScale r M.moments)

/-- The scaled model retains the exact rescaled source. -/
theorem gomesMassScaledModel_moments (M : GomesMomentModel) (r : ℝ) :
    (gomesMassScaledModel M r).moments = gomesMomentMassScale r M.moments :=
  (gomesCanonicalMomentModel_moments_iff _).mpr
    ((gomesMomentMassScale_positive_iff r _).mpr (gomesMomentModel_positive M))

/-- Zero logarithmic mass acts identically on the exact source. -/
theorem gomesMassScaledModel_zero (M : GomesMomentModel) :
    (gomesMassScaledModel M 0).moments = M.moments := by
  rw [gomesMassScaledModel_moments]
  funext n
  simp [gomesMomentMassScale]

/-- Successive positive mass changes compose by addition of logarithmic mass. -/
theorem gomesMassScaledModel_comp (M : GomesMomentModel) (r t : ℝ) :
    (gomesMassScaledModel (gomesMassScaledModel M r) t).moments =
      (gomesMassScaledModel M (r+t)).moments := by
  simp only [gomesMassScaledModel_moments]
  funext n
  simp only [gomesMomentMassScale,Real.exp_add]
  ring

/-- Entire complex frames are invariant under arbitrary positive mass rescaling. -/
theorem gomesMassScaledModel_frame (M : GomesMomentModel) (r : ℝ) (n : ℕ) (z : ℂ) :
    gomesMomentComplexFrame (gomesMassScaledModel M r) n z = gomesMomentComplexFrame M n z := by
  simp only [gomesMomentComplexFrame,gomesMassScaledModel_moments,
    gomesMomentMassScale_monicOrthoC,gomesMomentMassScale_secondKindC]

/-- Projective polynomial observations are invariant under positive mass. -/
theorem gomesMassScaledModel_quotient (M : GomesMomentModel) (r : ℝ) (n : ℕ) (z : ℂ) :
    gomesMomentQuotient (gomesMassScaledModel M r) n z = gomesMomentQuotient M n z := by
  simp only [gomesMomentQuotient,gomesMassScaledModel_moments,gomesMomentMassScale_monicOrthoC]

/-- Every unweighted wave observation forgets the mass character. -/
theorem gomesMassScaledModel_wave (M : GomesMomentModel) (r : ℝ) (v : Fin 2 → ℂ) (n : ℕ) (z : ℂ) :
    gomesMomentWave (gomesMassScaledModel M r) v n z = gomesMomentWave M v n z := by
  simp only [gomesMomentWave,gomesMassScaledModel_moments,
    gomesMomentMassScale_monicOrthoC,gomesMomentMassScale_secondKindC]

/-- Weighted wave energy carries the inverse mass character. -/
theorem gomesMassScaledModel_energy (M : GomesMomentModel) (r : ℝ) (v : Fin 2 → ℂ) (n : ℕ) (z : ℂ) :
    gomesMomentWaveEnergy (gomesMassScaledModel M r) v n z =
      Real.exp (-r)*gomesMomentWaveEnergy M v n z := by
  simp only [gomesMomentWaveEnergy,gomesMassScaledModel_wave,gomesMassScaledModel_moments,
    gomesMomentMassScale_monicOrtho,gomesMomentMassScale_inner]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  simp only [Real.exp_neg,div_eq_mul_inv,mul_inv_rev]
  ring

/-- The complete observation Gram tensor carries the same inverse mass character. -/
theorem gomesMassScaledModel_gram (M : GomesMomentModel) (r : ℝ) (n : ℕ) (z : ℂ) :
    gomesMomentObservationGram (gomesMassScaledModel M r) n z =
      Real.exp (-r) • gomesMomentObservationGram M n z := by
  simp only [gomesMomentObservationGram,gomesMassScaledModel_moments,
    gomesMomentMassScale_monicOrtho,gomesMomentMassScale_monicOrthoC,
    gomesMomentMassScale_secondKindC,gomesMomentMassScale_inner]
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Real.exp_neg,smul_smul,mul_inv_rev,mul_comm]

/-- The full normalized flux tensor carries the inverse mass character. -/
theorem gomesMassScaledModel_flux (M : GomesMomentModel) (r : ℝ) (n : ℕ) (z : ℂ) :
    gomesMomentNormalizedFlux (gomesMassScaledModel M r) n z =
      Real.exp (-r) • gomesMomentNormalizedFlux M n z := by
  simp only [gomesMomentNormalizedFlux,gomesMassScaledModel_frame,gomesMassScaledModel_moments,
    gomesMomentMassScale_monicOrtho,gomesMomentMassScale_inner]
  simp only [Real.exp_neg,mul_inv_rev,smul_add,smul_smul]
  congr 1 <;> rw [mul_comm]

/-- Full moment observations distinguish every logarithmic mass parameter. -/
theorem gomesMassScaledModel_source_injective (M : GomesMomentModel) (r t : ℝ) :
    (gomesMassScaledModel M r).moments = (gomesMassScaledModel M t).moments ↔ r = t := by
  constructor
  · intro h
    rw [gomesMassScaledModel_moments,gomesMassScaledModel_moments] at h
    have h0 := congrFun h 0
    have hm : M.moments 0 ≠ 0 := by
      have hp := gomesMomentModel_norm_pos M 0
      simpa [momentInner_def,momentFunctional_one] using hp.ne'
    apply Real.exp_injective
    exact mul_right_cancel₀ hm h0
  · rintro rfl
    rfl

/-- A flux observation forgets mass exactly on the real boundary; elsewhere its mass stabilizer is trivial. -/
theorem gomesMassScaledModel_flux_stabilizer (M : GomesMomentModel) (r : ℝ) (n : ℕ) (z : ℂ) :
    gomesMomentNormalizedFlux (gomesMassScaledModel M r) n z = gomesMomentNormalizedFlux M n z ↔
      r = 0 ∨ z.im = 0 := by
  rw [gomesMassScaledModel_flux]
  constructor
  · intro h
    by_cases hz : z.im = 0
    · exact Or.inr hz
    · left
      have hd : gomesMomentNormalizedFlux M n z ≠ 0 := by
        intro he
        exact hz ((gomesMomentNormalizedFlux_eq_zero_iff M n z).mp he)
      have he : Real.exp (-r) = 1 := (smul_left_injective ℝ hd) (by simpa using h)
      have hr := Real.exp_injective (he.trans (Real.exp_zero.symm))
      linarith
  · rintro (rfl|hz)
    · simp
    · rw [(gomesMomentNormalizedFlux_eq_zero_iff M n z).mpr hz,smul_zero]

end GaloisForLFunctions.HTGeometry
