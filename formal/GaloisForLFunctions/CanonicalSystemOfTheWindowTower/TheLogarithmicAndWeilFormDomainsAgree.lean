import GaloisForLFunctions.CanonicalSystemOfTheWindowTower.TheWeilRieszEquationIsALogarithmicDirichletEquation
import GaloisForLFunctions.CanonicalSystemOfTheWindowTower.TheLogarithmicFormHasItsMixedJumpPairing
import GaloisForLFunctions.RHTower.CCM.CCMConnesConsaniHilbertOne
import GaloisForLFunctions.RHTower.CCM.CCMRestrictedWeilGroundParity

/-!
# The complete logarithmic and Weil form domains agree

The exact bounded Fourier-weight correction identifies both domains. Every
supported finite-energy test therefore enters the actual Weil Riesz equation.
-/

open MeasureTheory Set Filter Topology Complex
open scoped FourierTransform ENNReal InnerProductSpace
noncomputable section
namespace GaloisForLFunctions.CanonicalSystemOfTheWindowTower
open _root_.RHTower HTGeometry

private theorem integrable_logarithmicWeightCorrection (f : RealLineL2) :
    Integrable (fun ξ : ℝ => (logarithmicFormScalar - (𝓕 (archLogEvenSource : ℝ → ℂ) ξ).re) *
      ‖fourierUnitary f ξ‖ ^ 2) := by
  have hsq : Integrable (fun ξ : ℝ => ‖fourierUnitary f ξ‖ ^ 2) :=
    (Lp.memLp (fourierUnitary f)).integrable_norm_pow (by norm_num)
  have hm : AEStronglyMeasurable (fun ξ : ℝ =>
      logarithmicFormScalar - (𝓕 (archLogEvenSource : ℝ → ℂ) ξ).re) volume :=
    (continuous_const.sub (Complex.continuous_re.comp
      (continuous_fourier_of_integrable' archLogEvenSource.integrable))).aestronglyMeasurable
  have hr (z : ℂ) : ‖z.re‖ ≤ ‖z‖ := by
    rw [Real.norm_eq_abs]
    rcases abs_cases z.re with ⟨he, _⟩ | ⟨he, _⟩
    · rw [he]
      exact Complex.re_le_norm z
    · rw [he]
      simpa using Complex.re_le_norm (-z)
  have hb : ∀ᵐ ξ ∂volume, ‖logarithmicFormScalar - (𝓕 (archLogEvenSource : ℝ → ℂ) ξ).re‖ ≤
      |logarithmicFormScalar| + ∫ x : ℝ, ‖archLogEvenSource x‖ := by
    filter_upwards with ξ
    calc
      _ ≤ ‖logarithmicFormScalar‖ + ‖(𝓕 (archLogEvenSource : ℝ → ℂ) ξ).re‖ := norm_sub_le _ _
      _ ≤ _ := by
        simpa only [Real.norm_eq_abs] using add_le_add_right ((hr _).trans
          (norm_fourier_apply_le_integral_norm (archLogEvenSource : ℝ → ℂ) ξ))
          ‖logarithmicFormScalar‖
  exact ((hsq.mul_bdd hm hb).congr (Eventually.of_forall fun ξ => mul_comm _ _))

/-- The exact Gamma and positive logarithmic Fourier weights define the same whole-line form domain. -/
theorem hasLogarithmicEnergy_iff_ccm_weight (f : RealLineL2) :
    HasLogarithmicEnergy f ↔ Integrable (fun ξ : ℝ => ccmArchimedeanFormWeight ξ *
      ‖fourierUnitary f ξ‖ ^ 2) := by
  rw [hasLogarithmicEnergy_iff_integrable]
  change Integrable (fun ξ : ℝ => positiveLogarithmicSymbol (2 * Real.pi * ξ) *
    ‖fourierUnitary f ξ‖ ^ 2) ↔ Integrable (fun ξ : ℝ => ccmArchimedeanFormWeight ξ *
      ‖fourierUnitary f ξ‖ ^ 2)
  have hb := integrable_logarithmicWeightCorrection f
  constructor
  · intro h
    refine (h.add hb).congr (Eventually.of_forall fun ξ => ?_)
    change positiveLogarithmicSymbol (2 * Real.pi * ξ) * ‖fourierUnitary f ξ‖ ^ 2 +
      (logarithmicFormScalar - (𝓕 (archLogEvenSource : ℝ → ℂ) ξ).re) * ‖fourierUnitary f ξ‖ ^ 2 =
        ccmArchimedeanFormWeight ξ * ‖fourierUnitary f ξ‖ ^ 2
    rw [ccmArchimedeanFormWeight_eq_logarithmic]
    ring
  · intro h
    refine (h.sub hb).congr (Eventually.of_forall fun ξ => ?_)
    change ccmArchimedeanFormWeight ξ * ‖fourierUnitary f ξ‖ ^ 2 -
      (logarithmicFormScalar - (𝓕 (archLogEvenSource : ℝ → ℂ) ξ).re) * ‖fourierUnitary f ξ‖ ^ 2 =
        positiveLogarithmicSymbol (2 * Real.pi * ξ) * ‖fourierUnitary f ξ‖ ^ 2
    rw [ccmArchimedeanFormWeight_eq_logarithmic]
    ring

/-- Weighted L² admission is exactly the literal logarithmic multiplier graph condition. -/
theorem hasLogarithmicEnergy_iff_ccm_memLp (f : RealLineL2) :
    HasLogarithmicEnergy f ↔ MemLp (fourierUnitary f : ℝ → ℂ) 2 ccmArchimedeanFormMeasure := by
  rw [hasLogarithmicEnergy_iff_ccm_weight,
    memLp_two_iff_integrable_sq_norm (Lp.stronglyMeasurable (fourierUnitary f)).aestronglyMeasurable]
  change _ ↔ Integrable (fun ξ : ℝ => ‖fourierUnitary f ξ‖ ^ 2)
    (volume.withDensity fun ξ => (Real.toNNReal (ccmArchimedeanFormWeight ξ) : ℝ≥0∞))
  rw [integrable_withDensity_iff_integrable_smul measurable_ccmArchimedeanFormWeightNNReal]
  simp only [NNReal.smul_def, smul_eq_mul, coe_ccmArchimedeanFormWeightNNReal]

/-- Every actual complete aperture form vector has finite logarithmic Fourier energy. -/
theorem hasLogarithmicEnergy_ccm_form (a : SuzukiPositiveAperture) (u : CCMArchimedeanFormDomain a) :
    HasLogarithmicEnergy (ccmArchimedeanFormEmbedding a u) := by
  rw [hasLogarithmicEnergy_iff_ccm_memLp]
  change MemLp (fourierUnitary (ccmArchimedeanFourierToTime u.1) : ℝ → ℂ) 2 _
  rw [fourierUnitary_ccmArchimedeanFourierToTime]
  exact (memLp_congr_ae ((ccmArchimedeanWeightedToL2_coeFn u.1).filter_mono
    ccmArchimedeanFormMeasure_absolutelyContinuous_volume.ae_le)).mpr (Lp.memLp u.1)

/-- Support in an aperture and finite logarithmic energy admit the source to its complete Weil form domain. -/
theorem exists_ccm_form_of_logarithmicEnergy (a : SuzukiPositiveAperture)
    (f : suzukiApertureHilbert a) (hf : HasLogarithmicEnergy (f : RealLineL2)) :
    ∃ u : CCMArchimedeanFormDomain a, ccmArchimedeanFormToAperture a u = f :=
  exists_ccmArchimedeanFormDomain_of_fourier_memLp a f
    ((hasLogarithmicEnergy_iff_ccm_memLp f).mp hf)

/-- The complete aperture form and whole-line physical Fourier form agree literally. -/
theorem logarithmicFullForm_ccm_embedding (a : SuzukiPositiveAperture)
    (u v : CCMArchimedeanFormDomain a) :
    logarithmicFullForm (ccmArchimedeanFormEmbedding a u) (ccmArchimedeanFormEmbedding a v) =
      logarithmicDirichletForm a u v := by
  unfold logarithmicFullForm logarithmicDirichletForm
  change (∫ ξ : ℝ, (positiveLogarithmicSymbol (2 * Real.pi * ξ) : ℂ) *
    star (fourierUnitary (ccmArchimedeanFourierToTime u.1) ξ) *
      fourierUnitary (ccmArchimedeanFourierToTime v.1) ξ) = _
  rw [fourierUnitary_ccmArchimedeanFourierToTime, fourierUnitary_ccmArchimedeanFourierToTime]
  apply integral_congr_ae
  filter_upwards [ccmArchimedeanWeightedToL2_coeFn u.1,
    ccmArchimedeanWeightedToL2_coeFn v.1] with ξ hu hv
  rw [hu, hv]

private theorem logarithmicFrequencyWeight_neg (ξ : ℝ) :
    positiveLogarithmicSymbol (2 * Real.pi * (-ξ)) = positiveLogarithmicSymbol (2 * Real.pi * ξ) := by
  unfold positiveLogarithmicSymbol
  rw [show (2 * Real.pi * (-ξ)) ^ 2 = (2 * Real.pi * ξ) ^ 2 by ring]

/-- Reflection preserves the literal logarithmic graph domain. -/
theorem hasLogarithmicEnergy_reflection {f : RealLineL2} (hf : HasLogarithmicEnergy f) :
    HasLogarithmicEnergy (l2Reflection f) := by
  rw [hasLogarithmicEnergy_iff_integrable] at hf ⊢
  change Integrable (fun ξ : ℝ => positiveLogarithmicSymbol (2 * Real.pi * ξ) *
    ‖fourierUnitary (l2Reflection f) ξ‖ ^ 2)
  rw [fourierUnitary_l2Reflection]
  apply hf.comp_neg.congr
  filter_upwards [l2Reflection_ae (fourierUnitary f)] with ξ hξ
  change positiveLogarithmicSymbol (2 * Real.pi * (-ξ)) * ‖fourierUnitary f (-ξ)‖ ^ 2 = _
  rw [hξ, logarithmicFrequencyWeight_neg]

/-- Reflection preserves the entire complex logarithmic form. -/
theorem logarithmicFullForm_reflection (u v : RealLineL2) :
    logarithmicFullForm (l2Reflection u) (l2Reflection v) = logarithmicFullForm u v := by
  unfold logarithmicFullForm
  rw [fourierUnitary_l2Reflection, fourierUnitary_l2Reflection]
  calc
    _ = ∫ ξ : ℝ, (positiveLogarithmicSymbol (2 * Real.pi * (-ξ)) : ℂ) *
        star (fourierUnitary u (-ξ)) * fourierUnitary v (-ξ) := by
      apply integral_congr_ae
      filter_upwards [l2Reflection_ae (fourierUnitary u), l2Reflection_ae (fourierUnitary v)] with ξ hu hv
      rw [hu, hv, logarithmicFrequencyWeight_neg]
    _ = _ := integral_neg_eq_self (fun ξ : ℝ =>
      (positiveLogarithmicSymbol (2 * Real.pi * ξ) : ℂ) *
        star (fourierUnitary u ξ) * fourierUnitary v ξ) volume

namespace WeilHilbertBeforeContact

/-- The actual Riesz equation admits every supported finite-logarithmic-energy test. -/
theorem evalVector_logarithmic_fullForm (a : PrecontactAperture) (z : ℂ)
    (f : suzukiApertureHilbert a.1) (hf : HasLogarithmicEnergy (f : RealLineL2)) :
    logarithmicFullForm (f : RealLineL2)
      (ccmArchimedeanFormEmbedding a.1 (toForm a (evalVector a z))) =
        inner ℂ (f : RealLineL2) (logarithmicForcing a z : RealLineL2) := by
  obtain ⟨u, hu⟩ := exists_ccm_form_of_logarithmicEnergy a.1 f hf
  have he := evalVector_logarithmic_form a z u
  rw [← logarithmicFullForm_ccm_embedding] at he
  have hc := congrArg (star : ℂ → ℂ) he
  rw [logarithmicFullForm_conj] at hc
  have hinner : star (inner ℂ (logarithmicForcing a z) (ccmArchimedeanFormToAperture a.1 u)) =
      inner ℂ (ccmArchimedeanFormToAperture a.1 u) (logarithmicForcing a z) :=
    inner_conj_symm (𝕜 := ℂ) (E := suzukiApertureHilbert a.1)
      (ccmArchimedeanFormToAperture a.1 u) (logarithmicForcing a z)
  rw [hinner] at hc
  change logarithmicFullForm (ccmArchimedeanFormToAperture a.1 u : RealLineL2)
    (ccmArchimedeanFormEmbedding a.1 (toForm a (evalVector a z))) =
      inner ℂ (ccmArchimedeanFormToAperture a.1 u : RealLineL2)
        (logarithmicForcing a z : RealLineL2) at hc
  simpa only [hu] using hc

end WeilHilbertBeforeContact

#print axioms WeilHilbertBeforeContact.evalVector_logarithmic_fullForm
#print axioms hasLogarithmicEnergy_iff_ccm_memLp
#print axioms exists_ccm_form_of_logarithmicEnergy
#print axioms logarithmicFullForm_ccm_embedding
#print axioms hasLogarithmicEnergy_reflection
#print axioms logarithmicFullForm_reflection
end GaloisForLFunctions.CanonicalSystemOfTheWindowTower
