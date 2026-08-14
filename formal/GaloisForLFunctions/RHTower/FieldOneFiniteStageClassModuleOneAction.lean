import GaloisForLFunctions.RHTower.FieldOneFiniteStageClassHalfDensity

/-!
# Literal module-one action on the finite-stage class-space `L²`

The compact module-one idele classes `K_S` act on the literal additive
quotient `X_S` by scaling.  This file proves that action preserves the source
additive quotient measure.  It therefore supplies the actual left-regular
unitaries whose fixed vectors define `L²(X_S)^{K_S}`.
-/

open scoped ENNReal NNReal

namespace GaloisForLFunctions.RHTower

noncomputable section

open IsDedekindDomain MeasureTheory Set

/-- Push a measurable density through a measurable self-equivalence. -/
private theorem map_withDensity_selfMeasurableEquiv
    {α : Type*} [MeasurableSpace α]
    (e : α ≃ᵐ α) (μ : Measure α) (f : α → ℝ≥0∞)
    (hf : Measurable f) :
    Measure.map e (μ.withDensity f) =
      (Measure.map e μ).withDensity (f ∘ e.symm) := by
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply e.measurable hs,
    withDensity_apply _ (hs.preimage e.measurable),
    withDensity_apply _ hs]
  let g : α → ℝ≥0∞ := s.indicator (f ∘ e.symm)
  have hg : Measurable g :=
    (hf.comp e.symm.measurable).indicator hs
  calc
    (∫⁻ x in e ⁻¹' s, f x ∂μ) =
        ∫⁻ x, (e ⁻¹' s).indicator f x ∂μ :=
      (lintegral_indicator (hs.preimage e.measurable) _).symm
    _ = ∫⁻ x, g (e x) ∂μ := by
      apply lintegral_congr
      intro x
      by_cases hx : e x ∈ s <;> simp [g, hx]
    _ = ∫⁻ y, g y ∂Measure.map e μ :=
      (lintegral_map hg e.measurable).symm
    _ = ∫⁻ y in s, f (e.symm y) ∂Measure.map e μ :=
      lintegral_indicator hs _

/-- Module-one translation preserves the weighted additive measure
`|c| d*c` on the idele class group. -/
theorem fieldOneFiniteStageIdeleClassAdditiveMeasure_map_mulLeft_moduleOne
    (S : Finset (HeightOneSpectrum ℤ))
    (k : FieldOneFiniteStageModuleOneClass S) :
    Measure.map (k.1 * ·)
        (fieldOneFiniteStageIdeleClassAdditiveMeasure S) =
      fieldOneFiniteStageIdeleClassAdditiveMeasure S := by
  let e : FieldOneFiniteStageIdeleClassGroup S ≃ᵐ
      FieldOneFiniteStageIdeleClassGroup S :=
    (Homeomorph.mulLeft k.1).toMeasurableEquiv
  have hdensity : Measurable
      (GaloisForLFunctions.HTGeometry.realDensity
        (fieldOneFiniteStageIdeleClassModuleReal S)) :=
    GaloisForLFunctions.HTGeometry.measurable_realDensity
      (fieldOneFiniteStageIdeleClassModuleReal_measurable S)
  have hk : fieldOneFiniteStageIdeleClassModule S k.1 = 1 := by
    have hkUnits := congrArg
      (fun u : ℝ≥0ˣ => (u : ℝ≥0)) k.2
    simpa [fieldOneFiniteStageIdeleClassUnitModule] using hkUnits
  have hhaar : Measure.map e
      (fieldOneFiniteStageSplitHaarMeasure S) =
        fieldOneFiniteStageSplitHaarMeasure S := by
    change Measure.map (k.1 * ·)
      (fieldOneFiniteStageSplitHaarMeasure S) = _
    exact (measurePreserving_mul_left
      (fieldOneFiniteStageSplitHaarMeasure S) k.1).map_eq
  change Measure.map e
      ((fieldOneFiniteStageSplitHaarMeasure S).withDensity
        (GaloisForLFunctions.HTGeometry.realDensity
          (fieldOneFiniteStageIdeleClassModuleReal S))) = _
  rw [map_withDensity_selfMeasurableEquiv e _ _ hdensity, hhaar]
  change (fieldOneFiniteStageSplitHaarMeasure S).withDensity
      (_ ∘ e.symm) =
    (fieldOneFiniteStageSplitHaarMeasure S).withDensity _
  apply withDensity_congr_ae
  filter_upwards with c
  have hmodule :
      fieldOneFiniteStageIdeleClassModuleReal S (e.symm c) =
        fieldOneFiniteStageIdeleClassModuleReal S c := by
    change (fieldOneFiniteStageIdeleClassModule S (k.1⁻¹ * c) : ℝ) =
      (fieldOneFiniteStageIdeleClassModule S c : ℝ)
    rw [map_mul, map_inv, hk]
    simp
  exact congrArg
    (fun r : ℝ => ENNReal.ofReal r) hmodule

/-- Multiplication on `C_S` agrees with scaling its image in `X_S`. -/
theorem fieldOneFiniteStageIdeleClassToClassSpace_mul
    (S : Finset (HeightOneSpectrum ℤ))
    (c d : FieldOneFiniteStageIdeleClassGroup S) :
    fieldOneFiniteStageIdeleClassToClassSpace S (c * d) =
      c • fieldOneFiniteStageIdeleClassToClassSpace S d := by
  refine Quotient.inductionOn' c ?_
  intro u
  refine Quotient.inductionOn' d ?_
  intro v
  change fieldOneFiniteStageIdeleClassToClassSpace S
      (QuotientGroup.mk' (fieldOneFiniteStageSUnitImage S) (u * v)) =
    (QuotientGroup.mk' (fieldOneFiniteStageSUnitImage S) u :
        FieldOneFiniteStageIdeleClassGroup S) •
      fieldOneFiniteStageIdeleClassToClassSpace S
        (QuotientGroup.mk' (fieldOneFiniteStageSUnitImage S) v)
  rw [fieldOneFiniteStageIdeleClassGroup_mk_smul]
  change (Quotient.mk _ (fieldOneFiniteStageIdeleVal S (u * v)) :
      FieldOneFiniteStageClassSpace S) =
    Quotient.mk _ (u • fieldOneFiniteStageIdeleVal S v)
  rw [fieldOneFiniteStageIdeleVal_mul]

/-- Literal scaling by a module-one class preserves the source additive
quotient measure on `X_S`. -/
theorem fieldOneFiniteStageClassAdditiveMeasure_map_smul_moduleOne
    (S : Finset (HeightOneSpectrum ℤ))
    (k : FieldOneFiniteStageModuleOneClass S) :
    Measure.map (k.1 • ·)
        (fieldOneFiniteStageClassAdditiveMeasure S) =
      fieldOneFiniteStageClassAdditiveMeasure S := by
  have hiMeas : Measurable
      (fieldOneFiniteStageIdeleClassToClassSpace S) :=
    (fieldOneFiniteStageIdeleClassToClassSpace_continuous S).measurable
  have haMeas : Measurable
      (fun x : FieldOneFiniteStageClassSpace S => k.1 • x) :=
    (fieldOneFiniteStageIdeleClassGroup_const_smul_continuous S k.1).measurable
  have hmMeas : Measurable
      (fun c : FieldOneFiniteStageIdeleClassGroup S => k.1 * c) :=
    (continuous_const.mul continuous_id).measurable
  have hcomm :
      (fun x : FieldOneFiniteStageClassSpace S => k.1 • x) ∘
          fieldOneFiniteStageIdeleClassToClassSpace S =
        fieldOneFiniteStageIdeleClassToClassSpace S ∘
          (fun c : FieldOneFiniteStageIdeleClassGroup S => k.1 * c) := by
    funext c
    exact (fieldOneFiniteStageIdeleClassToClassSpace_mul S k.1 c).symm
  rw [fieldOneFiniteStageClassAdditiveMeasure,
    Measure.map_map haMeas hiMeas, hcomm,
    ← Measure.map_map hiMeas hmMeas,
    fieldOneFiniteStageIdeleClassAdditiveMeasure_map_mulLeft_moduleOne]

/-- Measure-preserving module-one scaling on the literal class space. -/
theorem fieldOneFiniteStageClassAdditiveMeasurePreserving_smul_moduleOne
    (S : Finset (HeightOneSpectrum ℤ))
    (k : FieldOneFiniteStageModuleOneClass S) :
    MeasurePreserving (k.1 • ·)
      (fieldOneFiniteStageClassAdditiveMeasure S)
      (fieldOneFiniteStageClassAdditiveMeasure S) where
  measurable :=
    (fieldOneFiniteStageIdeleClassGroup_const_smul_continuous S k.1).measurable
  map_eq := fieldOneFiniteStageClassAdditiveMeasure_map_smul_moduleOne S k

end

end GaloisForLFunctions.RHTower
