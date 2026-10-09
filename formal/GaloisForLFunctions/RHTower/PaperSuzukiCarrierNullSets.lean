import GaloisForLFunctions.RHTower.RiemannGaussian.RiemannXiSuzukiCarrierCayleySynthesisOperator
import GaloisForLFunctions.RHTower.RiemannGaussian.GaussianZetaGeometry

/-! # The Suzuki carrier retains the full Lebesgue almost-everywhere information

The arithmetic density is positive away from a countable spectral-node set.
Consequently the carrier and Lebesgue measures have exactly the same null sets.
The native reference inclusion and bilateral coefficient synthesis are injective.
-/

namespace RiemannGaussian
noncomputable section
open MeasureTheory Filter Set
open scoped ENNReal lp

/-- The literal arithmetic carrier density is strictly positive almost everywhere. -/
theorem paperSuzukiCarrierDensity_ae_pos :
    ∀ᵐ t ∂volume, 0 < suzukiXiRealAxisArithmeticCarrierDensity t := by
  let Z := Set.range (fun rho : NontrivialZetaZero => (zetaSpectralCoordinate rho.1).re)
  have hZ : volume Z = 0 := (Set.countable_range _).measure_zero volume
  filter_upwards [compl_mem_ae_iff.mpr hZ] with t ht
  have hxi : riemannXiSpectral (t : ℂ) ≠ 0 := by
    intro hzero
    obtain ⟨rho, hrho⟩ := (riemannXiSpectral_eq_zero_iff_exists_zetaZero (t : ℂ)).mp hzero
    exact ht ⟨rho, by simpa only [Complex.ofReal_re] using (congrArg Complex.re hrho).symm⟩
  have hre : (riemannXiSpectral (t : ℂ)).re ≠ 0 := by
    intro h
    apply hxi
    apply Complex.ext
    · simpa only [Complex.zero_re] using h
    · simpa only [Complex.zero_im] using riemannXiSpectral_ofReal_im t
  unfold suzukiXiRealAxisArithmeticCarrierDensity
  split
  · norm_num
  · exact div_pos (sq_pos_of_ne_zero hre)
      (suzukiXiRealAxisSpectralEnergy_pos_of_E_ne_zero t ‹_›)

theorem paperSuzukiCarrierWeight_ae_pos :
    ∀ᵐ t ∂volume, 0 < suzukiXiCarrierNevanlinnaWeight t := by
  filter_upwards [paperSuzukiCarrierDensity_ae_pos] with t ht
  exact div_pos ht (by positivity)

/-- No positive-Lebesgue-measure region is lost by passing to the arithmetic carrier measure. -/
theorem paperSuzukiVolume_absolutelyContinuous_carrier :
    volume ≪ suzukiXiCarrierNevanlinnaMeasure := by
  apply withDensity_absolutelyContinuous'
  · exact measurable_suzukiXiCarrierNevanlinnaWeight.ennreal_ofReal.aemeasurable
  · filter_upwards [paperSuzukiCarrierWeight_ae_pos] with t ht
    simpa only [ne_eq, ENNReal.ofReal_eq_zero, not_le] using ht

/-- Carrier-null and Lebesgue-null are exactly the same condition. -/
theorem paperSuzukiCarrier_null_iff (E : Set ℝ) :
    suzukiXiCarrierNevanlinnaMeasure E = 0 ↔ volume E = 0 :=
  ⟨fun h => paperSuzukiVolume_absolutelyContinuous_carrier h,
    fun h => withDensity_absolutelyContinuous volume _ h⟩

/-- Native reference-to-carrier inclusion preserves all vector information. -/
theorem paperSuzukiReferenceToCarrier_injective :
    Function.Injective suzukiXiCarrierCayleyReferenceToCarrier := by
  intro f g hfg
  have hac : suzukiXiCarrierCayleyReferenceMeasure ≪ suzukiXiCarrierNevanlinnaMeasure :=
    (withDensity_absolutelyContinuous volume _).trans paperSuzukiVolume_absolutelyContinuous_carrier
  apply Lp.ext
  apply hac.ae_eq
  filter_upwards [suzukiXiCarrierCayleyReferenceToCarrier_ae f,
    suzukiXiCarrierCayleyReferenceToCarrier_ae g] with t hf hg
  rw [← hf, ← hg, hfg]

/-- Distinct bilateral square-summable coefficients give distinct actual carrier outputs. -/
theorem paperSuzukiBilateralSynthesis_injective :
    Function.Injective suzukiXiCarrierCayleyBilateralSynthesisOperator := by
  intro a b hab
  have href : suzukiXiCarrierCayleyReferenceSynthesisOperator a =
      suzukiXiCarrierCayleyReferenceSynthesisOperator b :=
    paperSuzukiReferenceToCarrier_injective hab
  have hpi : (Real.sqrt Real.pi : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr Real.pi_pos).ne'
  apply suzukiXiCarrierCayleyNormalizedReferenceSynthesisIsometry.injective
  have h := congrArg (fun v : Lp ℂ 2 suzukiXiCarrierCayleyReferenceMeasure =>
    (Real.sqrt Real.pi : ℂ)⁻¹ • v) href
  simpa only [suzukiXiCarrierCayleyReferenceSynthesisOperator, smul_apply,
    smul_smul, inv_mul_cancel₀ hpi, one_smul, LinearIsometry.coe_toContinuousLinearMap] using h

end
end RiemannGaussian
