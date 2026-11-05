import GaloisForLFunctions.CanonicalSystemOfTheWindowTower.TheWeilSymbolIsALogarithmicMultiplierPlusABoundedKernel
import GaloisForLFunctions.CanonicalSystemOfTheWindowTower.TheLogarithmicPoissonFactorHasItsExactNormalization
import GaloisForLFunctions.CanonicalSystemOfTheWindowTower.TheWeilRieszVectorsSolveTheLiteralOperatorEquation
import GaloisForLFunctions.CanonicalSystemOfTheWindowTower.TheCompletedWeilRieszVectorsAreBounded
import GaloisForLFunctions.RHTower.CCM.CCMRestrictedWeilMixedSourceForm
import GaloisForLFunctions.RHTower.CCM.CCMRestrictedWeilRemainderMultiplier

/-!
# The positive logarithmic Dirichlet equation for Weil Riesz vectors

The exact archimedean symbol separates into `1+(1/2)log(1+ξ²)` and
an integrable convolution plus a scalar. This identifies the restricted
logarithmic form on the complete Weil form domain. Actual evaluation vectors
belong to its operator domain, and their forcing is essentially bounded:
every prime translation, polar convolution, and scalar term is retained.
-/

open MeasureTheory Set Filter Complex
open scoped FourierTransform InnerProductSpace ENNReal NNReal
noncomputable section

namespace GaloisForLFunctions.CanonicalSystemOfTheWindowTower
open _root_.RHTower GaloisForLFunctions.HTGeometry

/-- The finite scalar between the complete archimedean norm and the logarithmic form. -/
def logarithmicFormScalar : ℝ :=
  2 * ∫ t in Ioi (0 : ℝ), archLogRemainder t

theorem ccmArchimedeanFormWeight_eq_logarithmic (ξ : ℝ) :
    ccmArchimedeanFormWeight ξ =
      positiveLogarithmicSymbol (2 * Real.pi * ξ) + logarithmicFormScalar -
        (𝓕 (archLogEvenSource : ℝ → ℂ) ξ).re := by
  have h := gammaHardyPhaseRate_eq_log_reference_fourier ξ
  rw [ccmArchimedean_density_eq_formWeight_add_scalar] at h
  unfold archLogScalar at h
  unfold logarithmicFormScalar positiveLogarithmicSymbol
  linarith only [h]

private theorem fourier_archLogConvolution_ae (f : SoninL2) :
    (fourierUnitary (archLogConvolution f) : ℝ → ℂ) =ᵐ[volume]
      fun ξ => 𝓕 (archLogEvenSource : ℝ → ℂ) ξ * fourierUnitary f ξ := by
  have he : fourierUnitary (archLogConvolution f) =
      lpBoundedMulCLM (p := 2) (μ := (volume : Measure ℝ))
        (continuous_fourier_of_integrable' archLogEvenSource.integrable).measurable
        (integral_nonneg fun x => norm_nonneg (archLogEvenSource x))
        (norm_fourier_apply_le_integral_norm (archLogEvenSource : ℝ → ℂ))
        (fourierUnitary f) := by
    change fourierL2 ℝ (archLogConvolution f) = _
    rw [archLogConvolution, convolutionKernel_op_eq_fourierMulCLM,
      fourierMulCLM_apply, fourierL2_fourierL2inv]
    rfl
  rw [he]
  exact lpBoundedMulCLM_coeFn (p := 2) (μ := (volume : Measure ℝ))
    (continuous_fourier_of_integrable' archLogEvenSource.integrable).measurable
    (integral_nonneg fun x => norm_nonneg (archLogEvenSource x))
    (norm_fourier_apply_le_integral_norm (archLogEvenSource : ℝ → ℂ)) (fourierUnitary f)

private theorem archLogEvenSource_fourier_real (ξ : ℝ) :
    star (𝓕 (archLogEvenSource : ℝ → ℂ) ξ) =
      (((𝓕 (archLogEvenSource : ℝ → ℂ) ξ).re : ℝ) : ℂ) := by
  rw [archLogEvenSource_fourier, Complex.ofReal_re]
  exact Complex.conj_ofReal _

private theorem physical_fourier_eq (a : SuzukiPositiveAperture)
    (u : CCMArchimedeanFormDomain a) :
    fourierUnitary (ccmArchimedeanFormToAperture a u : SoninL2) =
      ccmArchimedeanWeightedToL2 u.1 :=
  fourierUnitary.apply_symm_apply _

private theorem weighted_inner_integral (f g : CCMArchimedeanFourierL2) :
    Integrable (fun ξ : ℝ => (ccmArchimedeanFormWeight ξ : ℂ) * star (f ξ) * g ξ) ∧
      (∫ ξ : ℝ, (ccmArchimedeanFormWeight ξ : ℂ) * star (f ξ) * g ξ) = inner ℂ f g := by
  have hi := (integrable_withDensity_iff_integrable_smul
    measurable_ccmArchimedeanFormWeightNNReal).mp (L2.integrable_inner (𝕜 := ℂ) f g)
  constructor
  · refine hi.congr ?_
    filter_upwards with ξ
    change (((Real.toNNReal (ccmArchimedeanFormWeight ξ) : ℝ≥0) : ℝ) : ℂ) *
      inner ℂ (f ξ) (g ξ) = _
    rw [coe_ccmArchimedeanFormWeightNNReal]
    simp only [RCLike.inner_apply, starRingEnd_apply]
    ring
  · rw [L2.inner_def]
    change _ = ∫ ξ : ℝ, inner ℂ (f ξ) (g ξ)
      ∂(volume.withDensity fun ξ => (Real.toNNReal (ccmArchimedeanFormWeight ξ) : ℝ≥0∞))
    rw [integral_withDensity_eq_integral_smul measurable_ccmArchimedeanFormWeightNNReal]
    apply integral_congr_ae
    filter_upwards with ξ
    change _ = (((Real.toNNReal (ccmArchimedeanFormWeight ξ) : ℝ≥0) : ℝ) : ℂ) *
      inner ℂ (f ξ) (g ξ)
    rw [coe_ccmArchimedeanFormWeightNNReal]
    simp only [RCLike.inner_apply, starRingEnd_apply]
    ring

private theorem plain_inner_integral (a : SuzukiPositiveAperture)
    (u v : CCMArchimedeanFormDomain a) :
    Integrable (fun ξ : ℝ => star (u.1 ξ) * v.1 ξ) ∧
      (∫ ξ : ℝ, star (u.1 ξ) * v.1 ξ) =
        inner ℂ (ccmArchimedeanFormToAperture a u) (ccmArchimedeanFormToAperture a v) := by
  have he : (fun ξ : ℝ => inner ℂ (ccmArchimedeanWeightedToL2 u.1 ξ)
      (ccmArchimedeanWeightedToL2 v.1 ξ)) =ᵐ[volume]
      (fun ξ : ℝ => star (u.1 ξ) * v.1 ξ) := by
    filter_upwards [ccmArchimedeanWeightedToL2_coeFn u.1,
      ccmArchimedeanWeightedToL2_coeFn v.1] with ξ hu hv
    simp only [RCLike.inner_apply, starRingEnd_apply]
    rw [hu, hv]
    ring
  refine ⟨(L2.integrable_inner (𝕜 := ℂ) _ _).congr he, ?_⟩
  rw [inner_ccmArchimedeanFormToAperture, L2.inner_def]
  exact integral_congr_ae he.symm

private theorem convolution_inner_integral (a : SuzukiPositiveAperture)
    (u v : CCMArchimedeanFormDomain a) :
    Integrable (fun ξ : ℝ => ((𝓕 (archLogEvenSource : ℝ → ℂ) ξ).re : ℂ) *
      star (u.1 ξ) * v.1 ξ) ∧
      (∫ ξ : ℝ, ((𝓕 (archLogEvenSource : ℝ → ℂ) ξ).re : ℂ) * star (u.1 ξ) * v.1 ξ) =
        inner ℂ (archLogConvolution (ccmArchimedeanFormToAperture a u))
          (ccmArchimedeanFormToAperture a v : SoninL2) := by
  let f : SoninL2 := ccmArchimedeanFormToAperture a u
  let g : SoninL2 := ccmArchimedeanFormToAperture a v
  have he : (fun ξ : ℝ => inner ℂ (fourierUnitary (archLogConvolution f) ξ)
      (fourierUnitary g ξ)) =ᵐ[volume]
      (fun ξ : ℝ => ((𝓕 (archLogEvenSource : ℝ → ℂ) ξ).re : ℂ) *
        star (u.1 ξ) * v.1 ξ) := by
    have hcf := fourier_archLogConvolution_ae f
    change (fourierUnitary (archLogConvolution f) : ℝ → ℂ) =ᵐ[volume]
      fun ξ => 𝓕 (archLogEvenSource : ℝ → ℂ) ξ *
        fourierUnitary (ccmArchimedeanFormToAperture a u : SoninL2) ξ at hcf
    rw [physical_fourier_eq] at hcf
    filter_upwards [hcf, ccmArchimedeanWeightedToL2_coeFn u.1,
      ccmArchimedeanWeightedToL2_coeFn v.1] with ξ hc hu hv
    change inner ℂ (fourierUnitary (archLogConvolution f) ξ)
      (fourierUnitary (ccmArchimedeanFormToAperture a v : SoninL2) ξ) = _
    rw [hc, physical_fourier_eq, hu, hv]
    simp only [RCLike.inner_apply, starRingEnd_apply, star_mul,
      archLogEvenSource_fourier_real]
    ring
  refine ⟨(L2.integrable_inner (𝕜 := ℂ) _ _).congr he, ?_⟩
  rw [← fourierUnitary.inner_map_map (archLogConvolution f) g, L2.inner_def]
  exact integral_congr_ae he.symm

/-- The literal compressed form of `1+(1/2)log(1-D²)`. -/
def logarithmicDirichletForm (a : SuzukiPositiveAperture)
    (u v : CCMArchimedeanFormDomain a) : ℂ :=
  ∫ ξ : ℝ, (positiveLogarithmicSymbol (2 * Real.pi * ξ) : ℂ) * star (u.1 ξ) * v.1 ξ

/-- The logarithmic reference is the same complete form domain with an explicit bounded correction. -/
theorem logarithmicDirichletForm_eq (a : SuzukiPositiveAperture)
    (u v : CCMArchimedeanFormDomain a) :
    logarithmicDirichletForm a u v = inner ℂ u v -
      (logarithmicFormScalar : ℂ) *
        inner ℂ (ccmArchimedeanFormToAperture a u) (ccmArchimedeanFormToAperture a v) +
      inner ℂ (ccmApertureCompression a archLogConvolution (ccmArchimedeanFormToAperture a u))
        (ccmArchimedeanFormToAperture a v) := by
  obtain ⟨hw, hwval⟩ := weighted_inner_integral u.1 v.1
  obtain ⟨hm, hmval⟩ := plain_inner_integral a u v
  obtain ⟨hr, hrval⟩ := convolution_inner_integral a u v
  have hpoint (ξ : ℝ) :
      (positiveLogarithmicSymbol (2 * Real.pi * ξ) : ℂ) * star (u.1 ξ) * v.1 ξ =
        ((ccmArchimedeanFormWeight ξ : ℂ) * star (u.1 ξ) * v.1 ξ -
          (logarithmicFormScalar : ℂ) * (star (u.1 ξ) * v.1 ξ)) +
        ((𝓕 (archLogEvenSource : ℝ → ℂ) ξ).re : ℂ) * star (u.1 ξ) * v.1 ξ := by
    rw [ccmArchimedeanFormWeight_eq_logarithmic]
    push_cast
    ring
  have hsub : Integrable (fun ξ : ℝ =>
      (ccmArchimedeanFormWeight ξ : ℂ) * star (u.1 ξ) * v.1 ξ -
        (logarithmicFormScalar : ℂ) * (star (u.1 ξ) * v.1 ξ)) :=
    hw.sub (hm.const_mul (logarithmicFormScalar : ℂ))
  have hsubval : (∫ ξ : ℝ,
      (ccmArchimedeanFormWeight ξ : ℂ) * star (u.1 ξ) * v.1 ξ -
        (logarithmicFormScalar : ℂ) * (star (u.1 ξ) * v.1 ξ)) =
      (∫ ξ : ℝ, (ccmArchimedeanFormWeight ξ : ℂ) * star (u.1 ξ) * v.1 ξ) -
        (logarithmicFormScalar : ℂ) * ∫ ξ : ℝ, star (u.1 ξ) * v.1 ξ := by
    rw [integral_sub hw (hm.const_mul _), integral_const_mul]
  unfold logarithmicDirichletForm
  simp_rw [hpoint]
  rw [integral_add hsub hr, hsubval, hwval, hmval, hrval, inner_ccmApertureCompression]
  rfl

/-- The finite correction producing the positive logarithmic reference form. -/
def logarithmicDirichletAdjustment (a : SuzukiPositiveAperture) :
    suzukiApertureHilbert a →L[ℂ] suzukiApertureHilbert a :=
  (-logarithmicFormScalar : ℂ) • 1 + ccmApertureCompression a archLogConvolution

theorem logarithmicDirichletAdjustment_isSelfAdjoint (a : SuzukiPositiveAperture) :
    IsSelfAdjoint (logarithmicDirichletAdjustment a) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff']
  unfold logarithmicDirichletAdjustment
  rw [ContinuousLinearMap.adjoint.map_add, ContinuousLinearMap.adjoint.map_smulₛₗ,
    ContinuousLinearMap.adjoint_one]
  have h := ccmApertureCompression_isSelfAdjoint a archLogConvolution_isSelfAdjoint
  rw [ContinuousLinearMap.isSelfAdjoint_iff'] at h
  rw [h]
  congr 2
  simp only [map_neg, Complex.conj_ofReal]

theorem logarithmicDirichletForm_eq_adjustment (a : SuzukiPositiveAperture)
    (u v : CCMArchimedeanFormDomain a) :
    logarithmicDirichletForm a u v = inner ℂ u v +
      inner ℂ (logarithmicDirichletAdjustment a (ccmArchimedeanFormToAperture a u))
        (ccmArchimedeanFormToAperture a v) := by
  rw [logarithmicDirichletForm_eq]
  simp only [logarithmicDirichletAdjustment, add_apply,
    smul_apply, one_apply_eq_self, inner_add_left,
    inner_smul_left (E := suzukiApertureHilbert a),
    map_neg, Complex.conj_ofReal]
  ring

/-- The canonical restricted operator of the literal positive logarithmic form. -/
def logarithmicDirichletOperator (a : SuzukiPositiveAperture) :
    suzukiApertureHilbert a →ₗ.[ℂ] suzukiApertureHilbert a :=
  boundedPerturbedFriedrichsOperator (ccmArchimedeanFormToAperture a)
    (logarithmicDirichletAdjustment a) (logarithmicDirichletAdjustment_isSelfAdjoint a)

private def PhysicalBounded (f : SoninL2) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ᵐ x ∂volume, ‖f x‖ ≤ C

private theorem physicalBounded_zero : PhysicalBounded (0 : SoninL2) := by
  refine ⟨0, le_rfl, ?_⟩
  filter_upwards [Lp.coeFn_zero ℂ 2 volume] with x hx
  rw [hx, Pi.zero_apply, norm_zero]

private theorem physicalBounded_add {f g : SoninL2}
    (hf : PhysicalBounded f) (hg : PhysicalBounded g) : PhysicalBounded (f + g) := by
  obtain ⟨C, hC, hf⟩ := hf
  obtain ⟨D, hD, hg⟩ := hg
  refine ⟨C + D, add_nonneg hC hD, ?_⟩
  filter_upwards [Lp.coeFn_add f g, hf, hg] with x hx hfx hgx
  rw [hx, Pi.add_apply]
  exact (norm_add_le _ _).trans (add_le_add hfx hgx)

private theorem physicalBounded_smul (c : ℂ) {f : SoninL2}
    (hf : PhysicalBounded f) : PhysicalBounded (c • f) := by
  obtain ⟨C, hC, hf⟩ := hf
  refine ⟨‖c‖ * C, mul_nonneg (norm_nonneg _) hC, ?_⟩
  filter_upwards [Lp.coeFn_smul c f, hf] with x hx hfx
  rw [hx, Pi.smul_apply, norm_smul]
  exact mul_le_mul_of_nonneg_left hfx (norm_nonneg _)

private theorem physicalBounded_sub {f g : SoninL2}
    (hf : PhysicalBounded f) (hg : PhysicalBounded g) : PhysicalBounded (f - g) := by
  simpa only [neg_one_smul, sub_eq_add_neg] using
    physicalBounded_add hf (physicalBounded_smul (-1) hg)

private theorem physicalBounded_sum (S : Finset ℕ) (f : ℕ → SoninL2)
    (h : ∀ n ∈ S, PhysicalBounded (f n)) : PhysicalBounded (∑ n ∈ S, f n) := by
  classical
  revert h
  induction S using Finset.induction_on with
  | empty => intro _; simpa only [Finset.sum_empty] using physicalBounded_zero
  | @insert n S hn ih =>
    intro h
    rw [Finset.sum_insert hn]
    exact physicalBounded_add (h n (Finset.mem_insert_self _ _))
      (ih fun k hk => h k (Finset.mem_insert_of_mem hk))

private theorem physicalBounded_translation (t : ℝ) {f : SoninL2}
    (hf : PhysicalBounded f) : PhysicalBounded (logTranslationCLM t f) := by
  obtain ⟨C, hC, hf⟩ := hf
  refine ⟨C, hC, ?_⟩
  have ht := (MellinL2.realTranslation_measurePreserving t).quasiMeasurePreserving.tendsto_ae.eventually hf
  have he : (logTranslationCLM t f : ℝ → ℂ) =ᵐ[volume] fun x => f (x + t) :=
    Lp.coeFn_compMeasurePreserving f (MellinL2.realTranslation_measurePreserving t)
  filter_upwards [he, ht] with x hx hb
  rw [hx]
  exact hb

private theorem physicalBounded_compression (a : SuzukiPositiveAperture)
    (A : SoninL2 →L[ℂ] SoninL2) (f : suzukiApertureHilbert a)
    (hf : PhysicalBounded (A f.1)) : PhysicalBounded (ccmApertureCompression a A f) := by
  obtain ⟨C, hC, hf⟩ := hf
  refine ⟨C, hC, ?_⟩
  rw [ccmApertureCompression_val]
  filter_upwards [indicatorCutoff_ae (centralInterval a.1)
    (measurableSet_centralInterval a.1) (A f.1), hf] with x hx hb
  rw [hx]
  by_cases hxmem : x ∈ centralInterval a.1
  · rwa [indicator_of_mem hxmem]
  · rw [indicator_of_notMem hxmem, norm_zero]
    exact hC

private theorem physicalBounded_convolution (k : ℝ → ℂ) (hkm : Measurable k)
    (hk : Integrable k) {f : SoninL2} (hf : PhysicalBounded f) :
    PhysicalBounded ((convolutionKernel k hkm hk).op f) := by
  obtain ⟨C, hC, hf⟩ := hf
  refine ⟨(∫ t : ℝ, ‖k t‖) * C,
    mul_nonneg (integral_nonneg fun t => norm_nonneg _) hC, ?_⟩
  filter_upwards [(convolutionKernel k hkm hk).op_coeFn f] with x hx
  rw [hx]
  calc
    _ ≤ ∫ y : ℝ, ‖k (x - y)‖ * C := by
      apply norm_integral_le_of_norm_le ((hk.comp_sub_left x).norm.mul_const C)
      filter_upwards [hf] with y hy
      change ‖k (x - y) * f y‖ ≤ _
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left hy (norm_nonneg _)
    _ = _ := by
      rw [integral_mul_const]
      congr 1
      exact integral_sub_left_eq_self (fun t : ℝ => ‖k t‖) volume x

private theorem physicalBounded_fullPrime (a : SuzukiPositiveAperture)
    {f : SoninL2} (hf : PhysicalBounded f) : PhysicalBounded (ccmFullLinePrimeOperator a f) := by
  simp only [ccmFullLinePrimeOperator, sum_apply, smul_apply,
    ccmSymmetricLogTranslation, add_apply]
  apply physicalBounded_sum
  intro n _
  exact physicalBounded_smul _
    (physicalBounded_add (physicalBounded_translation _ hf) (physicalBounded_translation _ hf))

private theorem physicalBounded_polar (a : SuzukiPositiveAperture)
    {f : SoninL2} (hf : PhysicalBounded f) : PhysicalBounded (ccmPolarConvolution a f) :=
  physicalBounded_convolution (ccmPolarConvolutionProfile a)
    (measurable_ccmPolarConvolutionProfile a) (integrable_ccmPolarConvolutionProfile a) hf

private theorem physicalBounded_weilRemainder (a : SuzukiPositiveAperture)
    (f : suzukiApertureHilbert a) (hf : PhysicalBounded f.1) :
    PhysicalBounded (ccmRestrictedWeilBoundedRemainder a f) := by
  rw [ccmRestrictedWeilBoundedRemainder_eq_compressed_fullLine]
  apply physicalBounded_compression
  simp only [ccmFullLineBoundedRemainder, sub_apply, add_apply, smul_apply, one_apply_eq_self]
  exact physicalBounded_sub
    (physicalBounded_add (physicalBounded_smul _ hf) (physicalBounded_polar a hf))
    (physicalBounded_fullPrime a hf)

private theorem physicalBounded_logarithmicAdjustment (a : SuzukiPositiveAperture)
    (f : suzukiApertureHilbert a) (hf : PhysicalBounded f.1) :
    PhysicalBounded (logarithmicDirichletAdjustment a f) := by
  change PhysicalBounded ((-logarithmicFormScalar : ℂ) • f.1 +
    (ccmApertureCompression a archLogConvolution f : SoninL2))
  apply physicalBounded_add (physicalBounded_smul _ hf)
  apply physicalBounded_compression
  exact physicalBounded_convolution archLogEvenSource measurable_archLogEvenSource
    archLogEvenSource.integrable hf

namespace WeilHilbertBeforeContact

/-- The actual reference forcing, including all finite prime translations and both polar terms. -/
def logarithmicForcing (a : PrecontactAperture) (z : ℂ) : suzukiApertureHilbert a.1 :=
  evaluationForcing a.1 z +
    (logarithmicDirichletAdjustment a.1 - ccmRestrictedWeilBoundedRemainder a.1)
      (ccmArchimedeanFormToAperture a.1 (toForm a (evalVector a z)))

theorem evalVector_logarithmic_form (a : PrecontactAperture) (z : ℂ)
    (u : CCMArchimedeanFormDomain a.1) :
    logarithmicDirichletForm a.1 (toForm a (evalVector a z)) u =
      inner ℂ (logarithmicForcing a z) (ccmArchimedeanFormToAperture a.1 u) := by
  have h := evalVector_represents_operator a z u
  rw [ccmRestrictedWeilForm] at h
  rw [logarithmicDirichletForm_eq_adjustment]
  simp only [logarithmicForcing, inner_add_left, sub_apply, inner_sub_left]
  linear_combination h

theorem evalVector_logarithmic_operator_domain_and_apply (a : PrecontactAperture) (z : ℂ) :
    ∃ hmem : ccmArchimedeanFormToAperture a.1 (toForm a (evalVector a z)) ∈
        (logarithmicDirichletOperator a.1).domain,
      logarithmicDirichletOperator a.1
        ⟨ccmArchimedeanFormToAperture a.1 (toForm a (evalVector a z)), hmem⟩ =
          logarithmicForcing a z := by
  apply boundedPerturbedFriedrichsOperator_mem_domain_of_represents
    (ccmArchimedeanFormToAperture a.1) (logarithmicDirichletAdjustment a.1)
    (logarithmicDirichletAdjustment_isSelfAdjoint a.1)
    (ccmArchimedeanFormToAperture_injective a.1) (denseRange_ccmArchimedeanFormToAperture a.1)
  intro u
  rw [← logarithmicDirichletForm_eq_adjustment]
  exact evalVector_logarithmic_form a z u

/-- The actual logarithmic Dirichlet forcing is bounded, with every prime term retained. -/
theorem evalVector_logarithmicForcing_bounded (a : PrecontactAperture) (z : ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᵐ x ∂volume, ‖(logarithmicForcing a z : SoninL2) x‖ ≤ C := by
  let u : suzukiApertureHilbert a.1 :=
    ccmArchimedeanFormToAperture a.1 (toForm a (evalVector a z))
  have hu : PhysicalBounded u.1 := evalVector_physical_essentially_bounded a z
  have he : PhysicalBounded (evaluationForcing a.1 z) :=
    ⟨Real.exp (a.1.1 * |z.im|), (Real.exp_pos _).le, evaluationForcing_bounded a.1 z⟩
  change PhysicalBounded ((evaluationForcing a.1 z : SoninL2) +
    ((logarithmicDirichletAdjustment a.1 u : SoninL2) -
      (ccmRestrictedWeilBoundedRemainder a.1 u : SoninL2)))
  exact physicalBounded_add he (physicalBounded_sub
    (physicalBounded_logarithmicAdjustment a.1 u hu) (physicalBounded_weilRemainder a.1 u hu))

end WeilHilbertBeforeContact

#print axioms logarithmicDirichletForm_eq
#print axioms WeilHilbertBeforeContact.evalVector_logarithmic_operator_domain_and_apply
#print axioms WeilHilbertBeforeContact.evalVector_logarithmicForcing_bounded

end GaloisForLFunctions.CanonicalSystemOfTheWindowTower
