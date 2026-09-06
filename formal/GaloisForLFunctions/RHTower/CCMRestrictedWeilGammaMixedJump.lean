import GaloisForLFunctions.RHTower.CCMActualHeadGammaAutocorrelationEnergy

/-!
# Complex mixed pairings for the exact Gamma translation jumps

Absolute integrability of the four polarized translation energies upgrades the
quadratic Gamma identity to the complete complex form pairing. The mixed jump integral
is exactly the difference between the weighted form inner product and the physical
aperture inner product. Translation unitarity and adjoint aperture compression identify
the integrand with the literal symmetric Gamma increment.
-/

open Complex MeasureTheory Set Filter
open scoped ENNReal InnerProduct
noncomputable section
namespace RHTower

private def delta (a : SuzukiPositiveAperture) (h : ℝ) :
    CCMArchimedeanFormDomain a →L[ℂ] SoninL2 :=
  (logTranslationCLM h - 1) ∘L ccmArchimedeanFormEmbedding a

private def energy (a : SuzukiPositiveAperture) (u : CCMArchimedeanFormDomain a) (h : ℝ) : ℝ :=
  ccmGammaTranslationDensity h * ‖delta a h u‖ ^ 2

private theorem energy_meas (a : SuzukiPositiveAperture) (u : CCMArchimedeanFormDomain a) :
    AEStronglyMeasurable (energy a u) (volume.restrict (Ioi (0:ℝ))) := by
  have hρ : Measurable ccmGammaTranslationDensity := by
    unfold ccmGammaTranslationDensity
    fun_prop
  have hc : Continuous (fun h => delta a h u) :=
    (continuous_logTranslationCLM (ccmArchimedeanFormEmbedding a u)).sub continuous_const
  exact (hρ.aestronglyMeasurable.mul (hc.aestronglyMeasurable.norm.pow 2))

private theorem energy_nonneg (a : SuzukiPositiveAperture) (u : CCMArchimedeanFormDomain a) :
    0 ≤ᵐ[volume.restrict (Ioi (0:ℝ))] energy a u := by
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with h hh
  exact mul_nonneg (ccmGammaTranslationDensity_pos hh).le (sq_nonneg _)

private theorem energy_integrable (a : SuzukiPositiveAperture) (u : CCMArchimedeanFormDomain a) :
    IntegrableOn (energy a u) (Ioi (0:ℝ)) := by
  apply (lintegral_ofReal_ne_top_iff_integrable (energy_meas a u) (energy_nonneg a u)).mp
  change ccmActualHeadGammaAutocorrelationEnergyL (ccmArchimedeanFormToAperture a u) ≠ ⊤
  rw [ccmActualHeadGammaAutocorrelationEnergyL_formDomain]
  exact ENNReal.ofReal_ne_top

private theorem energy_integral (a : SuzukiPositiveAperture) (u : CCMArchimedeanFormDomain a) :
    (∫ h in Ioi (0:ℝ), energy a u h) = ‖u‖ ^ 2 - ‖ccmArchimedeanFormToAperture a u‖ ^ 2 := by
  rw [integral_eq_lintegral_of_nonneg_ae (energy_nonneg a u) (energy_meas a u)]
  exact ccmActualHeadGammaAutocorrelationEnergy_formDomain a u

private def energyC (a : SuzukiPositiveAperture) (u : CCMArchimedeanFormDomain a) (h : ℝ) : ℂ :=
  (energy a u h : ℂ)

private theorem energyC_integrable (a : SuzukiPositiveAperture) (u : CCMArchimedeanFormDomain a) :
    IntegrableOn (energyC a u) (Ioi (0:ℝ)) :=
  Complex.ofRealCLM.integrable_comp (energy_integrable a u)

private theorem energyC_integral (a : SuzukiPositiveAperture) (u : CCMArchimedeanFormDomain a) :
    (∫ h in Ioi (0:ℝ), energyC a u h) =
      ((‖u‖ ^ 2 - ‖ccmArchimedeanFormToAperture a u‖ ^ 2 : ℝ) : ℂ) := by
  unfold energyC
  rw [integral_complex_ofReal, energy_integral]

private theorem mixed_polarization (a : SuzukiPositiveAperture)
    (u v : CCMArchimedeanFormDomain a) (h : ℝ) :
    (ccmGammaTranslationDensity h : ℂ) * inner ℂ (delta a h u) (delta a h v) =
      ((energyC a (u+v) h - energyC a (u-v) h) +
        (energyC a (u-I•v) h - energyC a (u+I•v) h)*I)/4 := by
  rw [inner_eq_sum_norm_sq_div_four]
  simp only [energyC, energy, map_add, map_sub, map_smul]
  push_cast
  change (ccmGammaTranslationDensity h : ℂ) *
    ((↑‖delta a h u + delta a h v‖ ^ 2 - ↑‖delta a h u - delta a h v‖ ^ 2 +
      (↑‖delta a h u-I•delta a h v‖ ^ 2 - ↑‖delta a h u+I•delta a h v‖ ^ 2)*I)/4) = _
  ring

/-- The Gamma translation-difference mixed pairing is absolutely integrable on the complete form domain. -/
theorem integrableOn_ccmGammaTranslationMixed (a : SuzukiPositiveAperture)
    (u v : CCMArchimedeanFormDomain a) :
    IntegrableOn (fun h => (ccmGammaTranslationDensity h : ℂ) *
      inner ℂ (logTranslationCLM h (ccmArchimedeanFormEmbedding a u) - ccmArchimedeanFormEmbedding a u)
        (logTranslationCLM h (ccmArchimedeanFormEmbedding a v) - ccmArchimedeanFormEmbedding a v))
      (Ioi (0:ℝ)) := by
  have h := ((energyC_integrable a (u+v)).sub (energyC_integrable a (u-v))).add
    (((energyC_integrable a (u-I•v)).sub (energyC_integrable a (u+I•v))).mul_const I)
  refine (h.div_const 4).congr (Eventually.of_forall fun h => ?_)
  exact (mixed_polarization a u v h).symm

/-- Exact complex polarization of the Gamma energy, on the actual complete form domain. -/
theorem integral_ccmGammaTranslationMixed (a : SuzukiPositiveAperture)
    (u v : CCMArchimedeanFormDomain a) :
    (∫ h in Ioi (0:ℝ), (ccmGammaTranslationDensity h : ℂ) *
      inner ℂ (logTranslationCLM h (ccmArchimedeanFormEmbedding a u) - ccmArchimedeanFormEmbedding a u)
        (logTranslationCLM h (ccmArchimedeanFormEmbedding a v) - ccmArchimedeanFormEmbedding a v)) =
      inner ℂ u v - inner ℂ (ccmArchimedeanFormToAperture a u) (ccmArchimedeanFormToAperture a v) := by
  have hpoint := fun h => mixed_polarization a u v h
  change (∫ h in Ioi (0:ℝ), (ccmGammaTranslationDensity h : ℂ) *
    inner ℂ (delta a h u) (delta a h v)) = _
  simp_rw [hpoint]
  have ha := integral_add
    ((energyC_integrable a (u+v)).sub (energyC_integrable a (u-v)))
    (((energyC_integrable a (u-I•v)).sub (energyC_integrable a (u+I•v))).mul_const I)
  have hs := integral_sub (energyC_integrable a (u+v)) (energyC_integrable a (u-v))
  have ht := integral_sub (energyC_integrable a (u-I•v)) (energyC_integrable a (u+I•v))
  simp only [Pi.sub_apply] at ha hs ht
  rw [integral_div, ha, integral_mul_const, hs, ht]
  rw [energyC_integral, energyC_integral, energyC_integral, energyC_integral,
    inner_eq_sum_norm_sq_div_four u v,
    inner_eq_sum_norm_sq_div_four (ccmArchimedeanFormToAperture a u) (ccmArchimedeanFormToAperture a v)]
  simp only [map_add, map_sub, map_smul]
  push_cast
  simp only [show (RCLike.I : ℂ) = I from rfl]
  ring!

/-- The compressed symmetric Gamma jump has the full translation-difference pairing. -/
theorem inner_ccmGammaCompressedJump (a : SuzukiPositiveAperture) (h : ℝ)
    (f g : suzukiApertureHilbert a) :
    inner ℂ ((ccmGammaTranslationDensity h : ℂ) •
      ((2:ℂ) • f - ccmApertureCompression a (ccmSymmetricLogTranslation h) f)) g =
      (ccmGammaTranslationDensity h : ℂ) *
        inner ℂ (logTranslationCLM h f.1 - f.1) (logTranslationCLM h g.1 - g.1) := by
  rw [inner_smul_left ((2:ℂ) • f - ccmApertureCompression a (ccmSymmetricLogTranslation h) f)
    g (ccmGammaTranslationDensity h : ℂ), Complex.conj_ofReal]
  congr 1
  rw [inner_sub_left, inner_smul_left f g (2:ℂ), inner_ccmApertureCompression]
  change (starRingEnd ℂ) (2:ℂ) * inner ℂ f.1 g.1 -
    inner ℂ (logTranslationCLM h f.1 + logTranslationCLM (-h) f.1) g.1 = _
  rw [inner_add_left, inner_sub_left, inner_sub_right, inner_sub_right]
  have hiso : inner ℂ (logTranslationCLM h f.1) (logTranslationCLM h g.1) =
      inner ℂ f.1 g.1 :=
    (MellinL2.additiveTranslationUnitary h).inner_map_map _ _
  have hadj := inner_logTranslationCLM (-h) f.1 g.1
  simp only [neg_neg] at hadj
  rw [hiso, ← hadj, map_ofNat]
  ring!

/-- Absolute integrability of the actual compressed Gamma jump paired with any form vector. -/
theorem integrableOn_ccmGammaCompressedJump_pair (a : SuzukiPositiveAperture)
    (u v : CCMArchimedeanFormDomain a) :
    IntegrableOn (fun h => inner ℂ ((ccmGammaTranslationDensity h : ℂ) •
      ((2:ℂ) • ccmArchimedeanFormToAperture a u -
        ccmApertureCompression a (ccmSymmetricLogTranslation h) (ccmArchimedeanFormToAperture a u)))
          (ccmArchimedeanFormToAperture a v)) (Ioi (0:ℝ)) := by
  simpa only [inner_ccmGammaCompressedJump, ccmArchimedeanFormToAperture_coe] using
    integrableOn_ccmGammaTranslationMixed a u v

/-- Exact complete-domain form identity for the actual compressed Gamma jumps. -/
theorem integral_ccmGammaCompressedJump_pair (a : SuzukiPositiveAperture)
    (u v : CCMArchimedeanFormDomain a) :
    (∫ h in Ioi (0:ℝ), inner ℂ ((ccmGammaTranslationDensity h : ℂ) •
      ((2:ℂ) • ccmArchimedeanFormToAperture a u -
        ccmApertureCompression a (ccmSymmetricLogTranslation h) (ccmArchimedeanFormToAperture a u)))
          (ccmArchimedeanFormToAperture a v)) =
      inner ℂ u v - inner ℂ (ccmArchimedeanFormToAperture a u) (ccmArchimedeanFormToAperture a v) := by
  simpa only [inner_ccmGammaCompressedJump, ccmArchimedeanFormToAperture_coe] using
    integral_ccmGammaTranslationMixed a u v
end RHTower
