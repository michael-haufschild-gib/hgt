import GaloisForLFunctions.RHTower.Suzuki.SuzukiCriticalL2Cusp
import Mathlib.Topology.Instances.EReal.Lemmas

/-!
# Extended primary first variation on the whole real L² space

At each positive admissible shift the compensated integral is finite and equals
an exact mass-corrected cusp quotient. Its extended energy limit, together with
the Gamma mass derivative, gives the actual primary first variation. Infinite
energy remains positive infinity throughout this identity.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal


namespace RHTower
open ArchimedeanAnomaly ArchimedeanExactForm
noncomputable section

/-- The normalized compensated integral is finite at every positive admissible shift. -/
theorem integrableOn_suzukiCriticalCompensatedAutocorr {f : ℝ → ℝ} (hf : MemLp f 2 volume)
    {omega : ℝ} (homega : 0 < omega) (homega5 : omega < 5/2) :
    IntegrableOn (fun t => (autocorr f 0-autocorr f t) *
      (suzukiCriticalPrimaryDensity omega t / omega)) (Ioi 0) := by
  have hB := integrableOn_suzukiCriticalPrimaryDensity homega homega5
  have hC := integrableOn_suzukiCriticalPrimaryCusp_integrand_of_memLp hf homega homega5 0
  simp only [zero_add] at hC
  have hi := ((hB.const_mul (autocorr f 0)).sub hC).div_const omega
  apply hi.congr
  exact Eventually.of_forall fun t => by
    dsimp only [Pi.sub_apply]
    ring

/-- Compensation subtracts the exact primary mass before division by the shift. -/
theorem integral_suzukiCriticalCompensatedAutocorr {f : ℝ → ℝ} (hf : MemLp f 2 volume)
    {omega : ℝ} (homega : 0 < omega) (homega5 : omega < 5/2) :
    (∫ t in Ioi 0, (autocorr f 0-autocorr f t) *
      (suzukiCriticalPrimaryDensity omega t / omega)) =
      (suzukiCriticalPrimaryMass omega * autocorr f 0-
        suzukiCriticalPrimaryCusp f omega 0) / omega := by
  have hB := integrableOn_suzukiCriticalPrimaryDensity homega homega5
  have hC := integrableOn_suzukiCriticalPrimaryCusp_integrand_of_memLp hf homega homega5 0
  simp only [zero_add] at hC
  have he : (fun t => (autocorr f 0-autocorr f t) *
      (suzukiCriticalPrimaryDensity omega t / omega)) =
      fun t => (autocorr f 0 * suzukiCriticalPrimaryDensity omega t -
        autocorr f t * suzukiCriticalPrimaryDensity omega t) / omega := by
    funext t
    ring
  rw [he, integral_div, integral_sub (hB.const_mul _) hC,
    integral_const_mul, integral_suzukiCriticalPrimaryDensity homega homega5,
    suzukiCriticalPrimaryCusp]
  simp only [zero_add]
  ring

/-- The nonnegative integral and the ordinary finite-shift quotient agree in extended reals. -/
theorem coe_suzukiCriticalCompensatedEnergy_autocorr {f : ℝ → ℝ} (hf : MemLp f 2 volume)
    {omega : ℝ} (homega : 0 < omega) (homega5 : omega < 5/2) :
    (suzukiCriticalCompensatedEnergy (fun t => autocorr f 0-autocorr f t) omega : EReal) =
      (((suzukiCriticalPrimaryMass omega * autocorr f 0-
        suzukiCriticalPrimaryCusp f omega 0) / omega : ℝ) : EReal) := by
  have hnn : ∀ᵐ t ∂volume.restrict (Ioi 0),
      0 ≤ (autocorr f 0-autocorr f t) * (suzukiCriticalPrimaryDensity omega t / omega) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact mul_nonneg (AutocorrelationKrein.deficit_nonneg hf t)
      (div_nonneg (suzukiCriticalPrimaryDensity_pos homega ht).le homega.le)
  rw [suzukiCriticalCompensatedEnergy,
    ← ofReal_integral_eq_lintegral_ofReal (integrableOn_suzukiCriticalCompensatedAutocorr hf homega homega5) hnn,
    EReal.coe_ennreal_ofReal, max_eq_left (integral_nonneg_of_ae hnn),
    integral_suzukiCriticalCompensatedAutocorr hf homega homega5]

/-- Every real L² source has the actual extended primary first variation, including infinite energy. -/
theorem tendsto_suzukiCriticalPrimaryCusp_extended_firstVariation {f : ℝ → ℝ} (hf : MemLp f 2 volume) :
    Tendsto (fun omega : ℝ => (((autocorr f 0-suzukiCriticalPrimaryCusp f omega 0) /
      omega : ℝ) : EReal)) (𝓝[>] 0)
      (𝓝 ((suzukiCriticalLimitingCompensatedEnergy
        (fun t => autocorr f 0-autocorr f t) : EReal) +
        (((Complex.digamma ((5/4 : ℝ) : ℂ)).re-Real.log Real.pi) * autocorr f 0 : ℝ))) := by
  have hE := continuous_coe_ennreal_ereal.continuousAt.tendsto.comp
    (tendsto_suzukiCriticalCompensatedEnergy_autocorr hf)
  have hM := continuous_coe_real_ereal.continuousAt.tendsto.comp
    ((tendsto_suzukiCriticalPrimaryMass_secant.neg).mul_const (autocorr f 0))
  have hlim := (EReal.continuousAt_add (Or.inr (EReal.coe_ne_bot _))
    (Or.inr (EReal.coe_ne_top _))).tendsto.comp (hE.prodMk_nhds hM)
  have hneg : -(Real.log Real.pi-(Complex.digamma ((5/4 : ℝ) : ℂ)).re) =
      (Complex.digamma ((5/4 : ℝ) : ℂ)).re-Real.log Real.pi := by ring
  rw [hneg] at hlim
  apply hlim.congr'
  have ho : ∀ᶠ omega : ℝ in 𝓝[>] 0, omega < 2 :=
    mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (by norm_num : (0 : ℝ)<2))
  filter_upwards [self_mem_nhdsWithin, ho] with omega homega ho
  change 0 < omega at homega
  change (suzukiCriticalCompensatedEnergy (fun t => autocorr f 0-autocorr f t) omega : EReal) +
    ((-((suzukiCriticalPrimaryMass omega-1)/omega)*autocorr f 0 : ℝ) : EReal) =
      (((autocorr f 0-suzukiCriticalPrimaryCusp f omega 0)/omega : ℝ) : EReal)
  rw [coe_suzukiCriticalCompensatedEnergy_autocorr hf homega (by linarith), ← EReal.coe_add]
  congr 1
  field_simp [ne_of_gt homega]
  ring

end
end RHTower

