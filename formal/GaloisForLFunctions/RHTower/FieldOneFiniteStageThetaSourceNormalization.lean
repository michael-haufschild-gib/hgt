import GaloisForLFunctions.RHTower.FieldOneFiniteStageThetaEulerSourceIdentification

namespace GaloisForLFunctions.RHTower

noncomputable section

open MeasureTheory IsDedekindDomain
open scoped BigOperators NNReal

theorem fieldOneEvenToPositiveUnitsHaarUnitary_ae
    (g : SchwartzMap ℝ ℂ) :
    fieldOneEvenToPositiveUnitsHaarUnitary
        (RHTower.ccmEvenSchwartzSource g) =ᵐ[fieldOnePositiveUnitsHaarMeasure]
      fun u =>
        (GaloisForLFunctions.HTGeometry.sqrtWeight
          fieldOnePositiveUnitsHaarLogWeight u)⁻¹ *
        (((RHTower.logEvenUnitary
          (RHTower.ccmEvenSchwartzSource g) : Lp (α := ℝ) ℂ 2) : ℝ → ℂ)
            (fieldOnePositiveUnitsExpHomeomorph.symm u)) := by
  let h : Lp (α := ℝ) ℂ 2 :=
    RHTower.logEvenUnitary (RHTower.ccmEvenSchwartzSource g)
  let j : Lp ℂ 2 fieldOnePositiveUnitsLogHaarMeasure :=
    fieldOnePositiveUnitsLogPullbackUnitary.symm h
  have hpull : j =ᵐ[fieldOnePositiveUnitsLogHaarMeasure]
      fun u => h (fieldOnePositiveUnitsExpHomeomorph.symm u) := by
    exact Lp.coeFn_compMeasurePreserving h
      fieldOnePositiveUnitsExp_measurePreserving.symm
  have hdiv :
      GaloisForLFunctions.HTGeometry.densityDiv
          fieldOnePositiveUnitsHaarLogWeight
          fieldOnePositiveUnitsHaarLogWeight_measurable
          fieldOnePositiveUnitsHaarLogWeight_pos j =ᵐ[fieldOnePositiveUnitsLogHaarMeasure]
        fun u =>
          (GaloisForLFunctions.HTGeometry.sqrtWeight
            fieldOnePositiveUnitsHaarLogWeight u)⁻¹ * j u :=
    GaloisForLFunctions.HTGeometry.densityDiv_ae
      fieldOnePositiveUnitsHaarLogWeight
      fieldOnePositiveUnitsHaarLogWeight_measurable
      fieldOnePositiveUnitsHaarLogWeight_pos j
  have hplain :
      GaloisForLFunctions.HTGeometry.densityDiv
          fieldOnePositiveUnitsHaarLogWeight
          fieldOnePositiveUnitsHaarLogWeight_measurable
          fieldOnePositiveUnitsHaarLogWeight_pos j =ᵐ[fieldOnePositiveUnitsLogHaarMeasure]
        fun u =>
          (GaloisForLFunctions.HTGeometry.sqrtWeight
            fieldOnePositiveUnitsHaarLogWeight u)⁻¹ *
            h (fieldOnePositiveUnitsExpHomeomorph.symm u) := by
    filter_upwards [hdiv, hpull] with u hdivu hpullu
    rw [hdivu, hpullu]
  have hweighted :
      GaloisForLFunctions.HTGeometry.densityDiv
          fieldOnePositiveUnitsHaarLogWeight
          fieldOnePositiveUnitsHaarLogWeight_measurable
          fieldOnePositiveUnitsHaarLogWeight_pos j =ᵐ[fieldOnePositiveUnitsHaarMeasure]
        fun u =>
          (GaloisForLFunctions.HTGeometry.sqrtWeight
            fieldOnePositiveUnitsHaarLogWeight u)⁻¹ *
            h (fieldOnePositiveUnitsExpHomeomorph.symm u) := by
    rw [fieldOnePositiveUnitsHaar_eq_withDensity]
    exact (GaloisForLFunctions.HTGeometry.withDensity_realDensity_ae_eq
      fieldOnePositiveUnitsHaarLogWeight_measurable
      fieldOnePositiveUnitsHaarLogWeight_pos).mpr hplain
  simpa [fieldOneEvenToPositiveUnitsHaarUnitary,
    fieldOnePositiveUnitsHaarToLogUnitary,
    fieldOnePositiveUnitsLogPullbackUnitary,
    GaloisForLFunctions.HTGeometry.weightedDensityUnitary_symm_apply,
    h, j] using hweighted

theorem logEvenUnitary_ccmEvenSchwartzSource_ae_of_even
    (g : SchwartzMap ℝ ℂ) (hg : ∀ x : ℝ, g (-x) = g x) :
    RHTower.logEvenUnitary (RHTower.ccmEvenSchwartzSource g) =ᵐ[volume]
      fun t => (((Real.sqrt 2 * Real.exp (t / 2) : ℝ) : ℂ) *
        g (Real.exp t)) := by
  have hlog := RHTower.logEvenUnitary_ae (RHTower.ccmEvenSchwartzSource g)
  have hsource := (RHTower.ccmEvenSchwartzSource_coeFn g).comp_tendsto
    RHTower.realExp_quasiMeasurePreserving.tendsto_ae
  filter_upwards [hlog, hsource] with t hlogt hsourcet
  rw [hlogt]
  have hsource' :
      ((RHTower.ccmEvenSchwartzSource g : RHTower.evenSubspace) : RHTower.SoninL2)
          (Real.exp t) = RHTower.schwartzEvenPart g (Real.exp t) := by
    simpa only [Function.comp_apply] using hsourcet
  rw [hsource']
  have hevenPart : RHTower.schwartzEvenPart g (Real.exp t) = g (Real.exp t) := by
    rw [RHTower.schwartzEvenPart_apply, hg]
    ring
  rw [hevenPart]

theorem fieldOneEvenToPositiveUnitsHaarUnitary_ae_of_even
    (g : SchwartzMap ℝ ℂ) (hg : ∀ x : ℝ, g (-x) = g x) :
    fieldOneEvenToPositiveUnitsHaarUnitary
        (RHTower.ccmEvenSchwartzSource g) =ᵐ[fieldOnePositiveUnitsHaarMeasure]
      fun u =>
        (GaloisForLFunctions.HTGeometry.sqrtWeight
          fieldOnePositiveUnitsHaarLogWeight u)⁻¹ *
        (((Real.sqrt 2 *
          Real.exp (fieldOnePositiveUnitsExpHomeomorph.symm u / 2) : ℝ) : ℂ) *
          g (Real.exp (fieldOnePositiveUnitsExpHomeomorph.symm u))) := by
  have hunitary := fieldOneEvenToPositiveUnitsHaarUnitary_ae g
  have hlog := fieldOnePositiveUnitsExp_measurePreserving.symm.quasiMeasurePreserving.ae_eq_comp
    (logEvenUnitary_ccmEvenSchwartzSource_ae_of_even g hg)
  have hlogHaar :
      (fun u =>
        (((RHTower.logEvenUnitary
          (RHTower.ccmEvenSchwartzSource g) : Lp (α := ℝ) ℂ 2) : ℝ → ℂ)
            (fieldOnePositiveUnitsExpHomeomorph.symm u))) =ᵐ[
              fieldOnePositiveUnitsHaarMeasure]
        fun u =>
          (((Real.sqrt 2 *
            Real.exp (fieldOnePositiveUnitsExpHomeomorph.symm u / 2) : ℝ) : ℂ) *
            g (Real.exp (fieldOnePositiveUnitsExpHomeomorph.symm u))) := by
    rw [fieldOnePositiveUnitsHaar_eq_withDensity]
    apply (GaloisForLFunctions.HTGeometry.withDensity_realDensity_ae_eq
      fieldOnePositiveUnitsHaarLogWeight_measurable
      fieldOnePositiveUnitsHaarLogWeight_pos).mpr
    simpa only [Function.comp_apply] using hlog
  filter_upwards [hunitary, hlogHaar] with u hu hlogu
  rw [hu, hlogu]

theorem fieldOneFiniteStageThetaEulerSchwartz_even
    (S : Finset (HeightOneSpectrum ℤ)) (f : SchwartzMap ℝ ℂ)
    (hf : ∀ x : ℝ, f (-x) = f x) (x : ℝ) :
    fieldOneFiniteStageThetaEulerSchwartz S f (-x) =
      fieldOneFiniteStageThetaEulerSchwartz S f x := by
  rw [fieldOneFiniteStageThetaEulerSchwartz_apply_eq_positiveEulerValue,
    fieldOneFiniteStageThetaEulerSchwartz_apply_eq_positiveEulerValue]
  unfold fieldOneFiniteStageThetaPositiveEulerValue
  apply Finset.sum_congr rfl
  intro n hn
  rw [show -x *
      ((((fieldOneSUnitProduct S n : ℚˣ) : ℚ) : ℝ)) =
        -(x * ((((fieldOneSUnitProduct S n : ℚˣ) : ℚ) : ℝ))) by ring,
    hf]

/-- Exact scalar relating full signed periodization to normalized even-L²
logarithmic coordinates with canonical positive-unit Haar. -/
def fieldOneThetaSourceNormalization : ℂ :=
  (Real.sqrt 2 : ℂ) *
    (Real.sqrt (fieldOnePositiveUnitsHaarLogWeight (1 : ℝ≥0ˣ)) : ℂ)

theorem fieldOneThetaSourceNormalization_ne_zero :
    fieldOneThetaSourceNormalization ≠ 0 := by
  apply mul_ne_zero
  · exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne'
  · exact_mod_cast (Real.sqrt_pos.mpr
      (fieldOnePositiveUnitsHaarLogWeight_pos (1 : ℝ≥0ˣ))).ne'

theorem fieldOneFiniteStageThetaBruhatHalfDensity_eq_normalization_smul_radialEuler
    (S : Finset (HeightOneSpectrum ℤ)) (f : SchwartzMap ℝ ℂ)
    (hf : ∀ x : ℝ, f (-x) = f x) :
    fieldOneFiniteStageBruhatHalfDensityLinearMap S
        (fieldOneFiniteStageThetaBruhatCoreLinearMap S f) =
      fieldOneThetaSourceNormalization •
        fieldOneFiniteStageRadialInclusion S
          (fieldOneEvenToPositiveUnitsHaarUnitary
            (fieldOneFiniteStageThetaEulerOperator S
              (RHTower.ccmEvenSchwartzSource f))) := by
  rw [fieldOneFiniteStageThetaEulerOperator_ccmEvenSchwartzSource]
  change fieldOneFiniteStageBruhatHalfDensityL2 S
      (fieldOneFiniteStageThetaBruhatCoreLinearMap S f) = _
  apply Lp.ext
  let g := fieldOneFiniteStageThetaEulerSchwartz S f
  have hg : ∀ x : ℝ, g (-x) = g x :=
    fieldOneFiniteStageThetaEulerSchwartz_even S f hf
  have hleft := fieldOneFiniteStageBruhatHalfDensityL2_ae S
    (fieldOneFiniteStageThetaBruhatCoreLinearMap S f)
  have hradial := fieldOneFiniteStageRadialInclusion_ae S
    (fieldOneEvenToPositiveUnitsHaarUnitary (RHTower.ccmEvenSchwartzSource g))
  have hsmul := Lp.coeFn_smul fieldOneThetaSourceNormalization
    (fieldOneFiniteStageRadialInclusion S
      (fieldOneEvenToPositiveUnitsHaarUnitary (RHTower.ccmEvenSchwartzSource g)))
  have harch := fieldOneEvenToPositiveUnitsHaarUnitary_ae_of_even g hg
  have harchProd :=
    (measurePreserving_snd
      (μ := fieldOneFiniteStageModuleOneProbabilityHaarMeasure S)
      (ν := fieldOnePositiveUnitsHaarMeasure)).quasiMeasurePreserving.ae_eq_comp harch
  filter_upwards [hleft, hradial, hsmul, harchProd]
      with z hleftz hradialz hsmulz harchz
  rw [hleftz, hsmulz]
  simp only [Pi.smul_apply]
  rw [hradialz]
  have harchz' :
      fieldOneEvenToPositiveUnitsHaarUnitary
          (RHTower.ccmEvenSchwartzSource g) z.2 =
        (GaloisForLFunctions.HTGeometry.sqrtWeight
          fieldOnePositiveUnitsHaarLogWeight z.2)⁻¹ *
        (((Real.sqrt 2 *
          Real.exp (fieldOnePositiveUnitsExpHomeomorph.symm z.2 / 2) : ℝ) : ℂ) *
          g (Real.exp (fieldOnePositiveUnitsExpHomeomorph.symm z.2))) := by
    simpa only [Function.comp_apply] using harchz
  rw [harchz']
  unfold fieldOneFiniteStageBruhatSplitHalfDensity
  rw [fieldOneFiniteStageThetaBruhatCore_logHalfDensity_eq_exponentEuler]
  rw [fieldOneFiniteStageThetaEulerSchwartz_apply_eq_positiveEulerValue]
  unfold fieldOneThetaSourceNormalization
  unfold GaloisForLFunctions.HTGeometry.sqrtWeight
  unfold fieldOnePositiveUnitsHaarLogWeight
  have hc : 0 < haarScalarFactor fieldOnePositiveUnitsHaarMeasure
      fieldOnePositiveUnitsLogHaarMeasure :=
    fieldOnePositiveUnitsHaar_logScalar_pos
  have hsqrtc : Real.sqrt (haarScalarFactor fieldOnePositiveUnitsHaarMeasure
      fieldOnePositiveUnitsLogHaarMeasure) ≠ 0 := (Real.sqrt_pos.mpr hc).ne'
  have hsqrt2 : (Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ) = 2 := by
    norm_cast
    rw [Real.mul_self_sqrt (by norm_num)]
  rw [← mul_assoc,
    inv_mul_cancel₀ (show (Real.sqrt
      (haarScalarFactor fieldOnePositiveUnitsHaarMeasure
        fieldOnePositiveUnitsLogHaarMeasure) : ℂ) ≠ 0 by exact_mod_cast hsqrtc),
    one_mul, ← mul_assoc, hsqrt2]
  ring

theorem fieldOneFiniteStageClassToSplitProduct_sourceUnitary
    (S : Finset (HeightOneSpectrum ℤ))
    (x : fieldOneFiniteStageClassModuleOneInvariantSubmodule S) :
    fieldOneFiniteStageClassToSplitProductL2Unitary S x.1 =
      fieldOneFiniteStageRadialInclusion S
        (fieldOneFiniteStageSourceUnitary S x) := by
  let y : FieldOnePositiveUnitsL2 := fieldOneFiniteStageSourceUnitary S x
  have hy : fieldOneFiniteStagePositiveClassInvariantUnitary S y =
      fieldOneFiniteStageClassSplitInvariantUnitary S x := by
    simp [y, fieldOneFiniteStageSourceUnitary]
  have hprod := congrArg
    (fun z : fieldOneFiniteStageSplitClassModuleOneInvariantSubmodule S =>
      fieldOneFiniteStageClassProductInvariantUnitary S z) hy
  have hval := congrArg Subtype.val hprod
  simpa [y, fieldOneFiniteStagePositiveClassInvariantUnitary,
    fieldOneFiniteStagePositiveProductInvariantUnitary,
    fieldOneFiniteStagePositiveToProductInvariants,
    fieldOneFiniteStageClassProductInvariantUnitary,
    fieldOneFiniteStageClassInvariantsToProductInvariants,
    fieldOneFiniteStageClassSplitInvariantUnitary,
    fieldOneFiniteStageClassInvariantToSplitInvariant,
    fieldOneFiniteStageClassToSplitProductL2Unitary] using hval.symm

/-- **Dense-core literal/candidate identification with the forced source
normalization exposed.** -/
theorem fieldOneFiniteStageThetaInvariantBruhatCore_eq_normalization_smul_transport
    (S : Finset (HeightOneSpectrum ℤ)) (f : SchwartzMap ℝ ℂ)
    (hf : ∀ x : ℝ, f (-x) = f x) :
    fieldOneFiniteStageThetaInvariantBruhatCoreLinearMap S f =
      fieldOneThetaSourceNormalization •
        fieldOneFiniteStageThetaTransportEquiv S
          (RHTower.ccmEvenSchwartzSource f) := by
  apply Subtype.ext
  apply (fieldOneFiniteStageClassToSplitProductL2Unitary S).injective
  change fieldOneFiniteStageClassToSplitProductL2Unitary S
      (fieldOneFiniteStageThetaClassBruhatCoreLinearMap S f) =
    fieldOneFiniteStageClassToSplitProductL2Unitary S
      ((fieldOneThetaSourceNormalization •
        fieldOneFiniteStageThetaTransportEquiv S
          (RHTower.ccmEvenSchwartzSource f) :
            fieldOneFiniteStageClassModuleOneInvariantSubmodule S).1)
  rw [fieldOneFiniteStageThetaClassBruhatCoreLinearMap_apply,
    fieldOneFiniteStageClassToSplitProductL2Unitary_classBruhat,
    map_smul,
    fieldOneFiniteStageClassToSplitProduct_sourceUnitary,
    map_smul,
    fieldOneFiniteStageSourceUnitary_thetaTransport]
  exact fieldOneFiniteStageThetaBruhatHalfDensity_eq_normalization_smul_radialEuler
    S f hf

/-- Whole-L² transport corrected by the forced full-sign/Haar scalar. -/
def fieldOneFiniteStageLiteralThetaTransportEquiv
    (S : Finset (HeightOneSpectrum ℤ)) :
    RHTower.evenSubspace ≃L[ℂ]
      fieldOneFiniteStageClassModuleOneInvariantSubmodule S :=
  (fieldOneFiniteStageThetaTransportEquiv S).trans
    (ContinuousLinearEquiv.smulLeft
      (Units.mk0 fieldOneThetaSourceNormalization
        fieldOneThetaSourceNormalization_ne_zero))

@[simp] theorem fieldOneFiniteStageLiteralThetaTransportEquiv_apply
    (S : Finset (HeightOneSpectrum ℤ)) (f : RHTower.evenSubspace) :
    fieldOneFiniteStageLiteralThetaTransportEquiv S f =
      fieldOneThetaSourceNormalization •
        fieldOneFiniteStageThetaTransportEquiv S f := by
  rfl

theorem fieldOneFiniteStageThetaInvariantBruhatCore_eq_literalTransport
    (S : Finset (HeightOneSpectrum ℤ)) (f : SchwartzMap ℝ ℂ)
    (hf : ∀ x : ℝ, f (-x) = f x) :
    fieldOneFiniteStageThetaInvariantBruhatCoreLinearMap S f =
      fieldOneFiniteStageLiteralThetaTransportEquiv S
        (RHTower.ccmEvenSchwartzSource f) := by
  rw [fieldOneFiniteStageLiteralThetaTransportEquiv_apply]
  exact fieldOneFiniteStageThetaInvariantBruhatCore_eq_normalization_smul_transport
    S f hf

def FieldOneEvenSchwartzSource :=
  {f : SchwartzMap ℝ ℂ // ∀ x : ℝ, f (-x) = f x}

theorem ccmEvenSchwartzSource_schwartzEvenPart
    (f : SchwartzMap ℝ ℂ) :
    RHTower.ccmEvenSchwartzSource (RHTower.schwartzEvenPart f) =
      RHTower.ccmEvenSchwartzSource f := by
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [RHTower.ccmEvenSchwartzSource_coeFn
      (RHTower.schwartzEvenPart f),
    RHTower.ccmEvenSchwartzSource_coeFn f] with x hleft hright
  rw [hleft, hright]
  rw [RHTower.schwartzEvenPart_apply]
  rw [RHTower.schwartzEvenPart_even]
  ring

theorem fieldOneEvenSchwartzSource_denseRange :
    DenseRange (fun f : FieldOneEvenSchwartzSource =>
      RHTower.ccmEvenSchwartzSource f.1) := by
  apply RHTower.ccmEvenSchwartzSource_denseRange.mono
  rintro y ⟨f, rfl⟩
  refine ⟨⟨RHTower.schwartzEvenPart f,
    RHTower.schwartzEvenPart_even f⟩, ?_⟩
  exact ccmEvenSchwartzSource_schwartzEvenPart f

/-- Literal theta cores from even Schwartz functions are dense in the actual
finite-stage invariant class space.  Thus the corrected transport is the
unique whole-L² extension of the literal source construction. -/
theorem fieldOneFiniteStageThetaInvariantBruhatCore_even_denseRange
    (S : Finset (HeightOneSpectrum ℤ)) :
    DenseRange (fun f : FieldOneEvenSchwartzSource =>
      fieldOneFiniteStageThetaInvariantBruhatCoreLinearMap S f.1) := by
  have htransport : DenseRange (fieldOneFiniteStageLiteralThetaTransportEquiv S) :=
    (fieldOneFiniteStageLiteralThetaTransportEquiv S).surjective.denseRange
  have hcomp := htransport.comp fieldOneEvenSchwartzSource_denseRange
    (fieldOneFiniteStageLiteralThetaTransportEquiv S).continuous
  simpa only [Function.comp_apply,
    fieldOneFiniteStageThetaInvariantBruhatCore_eq_literalTransport]
    using hcomp

end

end GaloisForLFunctions.RHTower
