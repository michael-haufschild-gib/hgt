import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.PoissonBoundariesAreDenseInOriginMass
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.MeyerNumericalRadicalAndMultiplicity
import GaloisForLFunctions.RHTower.XiRealCriticalPointSignLaw

/-!
# Origin Hilbert space cannot realize faithful Meyer cohomology

Every continuous cohomology-invariant reading of origin L2 is constant. Actual
finite causal classes are nonzero, so no faithful reading of genuine cohomology
can extend continuously through this completion. This applies both to compact-open
Xi cohomology and to the actual full-Hasse convolution representation.
-/

noncomputable section
open Complex MeasureTheory Set RHTower
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri

private theorem exists_nonzero_source_class :
    ∃ g : DeningerMeyerStrongLogTarget,
      (Submodule.Quotient.mk g : DeningerMeyerStrongLogCohomology) ≠ 0 := by
  obtain ⟨q, _⟩ := exists_xiZeroCopy_re_eq_half
  refine ⟨meyerPointSource q.1, ?_⟩
  intro hz
  have hv := congrArg
    (deningerMeyerXiSupportJetEvaluationLM q.1 ⟨0, xiSupportMultiplicity_pos q.1⟩) hz
  rw [deningerMeyerXiSupportJetEvaluationLM_mk, map_zero] at hv
  change deningerMeyerStrongLogMellin (meyerPointSource q.1) (q.1 : ℂ) = 0 at hv
  rw [meyerPointSource_values, if_pos rfl] at hv
  exact one_ne_zero hv

/-- No faithful cohomological reading admits a continuous origin-Hilbert realization. -/
theorem no_continuous_faithful_meyer_class_reading
    {Y : Type*} [TopologicalSpace Y] [T2Space Y]
    (E : DeningerMeyerStrongLogCohomology → Y) (hE : Function.Injective E) :
    ¬ ∃ F : Lp ℂ 2 (volume : Measure ℝ) → Y,
      Continuous F ∧ ∀ g : DeningerMeyerStrongLogTarget,
        F (deningerMeyerHalfDensityL2LM g) = E (Submodule.Quotient.mk g) := by
  rintro ⟨F, hF, hmatch⟩
  have hc : ∀ x, F x = F 0 :=
    (meyerHalfDensity_continuous_class_reading_iff_constant F hF).mp (by
      intro g h he
      rw [hmatch, hmatch, he])
  obtain ⟨g, hg⟩ := exists_nonzero_source_class
  apply hg
  apply hE
  calc
    E (Submodule.Quotient.mk g) = F (deningerMeyerHalfDensityL2LM g) := (hmatch g).symm
    _ = F 0 := hc _
    _ = E 0 := by
      have h0 := hmatch 0
      change F (deningerMeyerHalfDensityL2LM 0) =
        E ((LinearMap.range deningerMeyerStrongLogSumLM).mkQ 0) at h0
      simpa only [map_zero] using h0

/-- Actual global Xi division makes the compact-open quotient Hausdorff. -/
theorem meyerCompactOpenXiCohomology_t2Space : T2Space DeningerArithmeticCompactOpenH1 := by
  letI : IsClosed (deningerCompactOpenXiRange.toAddSubgroup : Set DeningerCompactOpenEntire) :=
    deningerArithmeticXiRangeClosed
  infer_instance

/-- The existing faithful compact-open Xi comparison cannot factor continuously through origin L2. -/
theorem no_continuous_origin_compactOpenXi_realization :
    ¬ ∃ F : Lp ℂ 2 (volume : Measure ℝ) → DeningerArithmeticCompactOpenH1,
      Continuous F ∧ ∀ g : DeningerMeyerStrongLogTarget,
        F (deningerMeyerHalfDensityL2LM g) =
          deningerArithmeticCompactOpenH1Class (deningerMeyerCenteredMellin g) := by
  letI := meyerCompactOpenXiCohomology_t2Space
  simpa only [deningerMeyerCompactOpenXiComparison_mk] using
    no_continuous_faithful_meyer_class_reading
      deningerMeyerCompactOpenXiComparison deningerMeyerCompactOpenXiComparison_injective

/-- No continuous, even nonlinear, origin-Hilbert map recovers every actual convolution operator. -/
theorem no_continuous_origin_convolution_realization :
    ¬ ∃ F : Lp ℂ 2 (volume : Measure ℝ) →
        (DeningerArithmeticJetHilbert →L[ℂ] DeningerArithmeticJetHilbert),
      Continuous F ∧ ∀ g : DeningerMeyerStrongLogTarget,
        F (deningerMeyerHalfDensityL2LM g) = deningerMeyerHilbertConvolution g := by
  exact no_continuous_faithful_meyer_class_reading
    deningerMeyerConvolutionRepresentationLM deningerMeyerConvolutionRepresentation_injective

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri

#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.no_continuous_faithful_meyer_class_reading
#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.meyerCompactOpenXiCohomology_t2Space
#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.no_continuous_origin_compactOpenXi_realization
#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.no_continuous_origin_convolution_realization
