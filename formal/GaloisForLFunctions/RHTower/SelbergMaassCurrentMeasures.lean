import GaloisForLFunctions.RHTower.SelbergMaassCurrentFunctional

/-!
# Exact positive measure split of the original Maass curvature

The actual compact-test current limit and its positive residual define regular
measures. Their sum is the original curvature measure. The residual is exactly
the weak limit of the literal regulator-gradient integrals, whose integrability
is proved from the original pointwise split. No residual-support theorem,
pointwise-to-integral interchange, or spectral quarter bound is assumed.
-/

open Set Filter Topology MeasureTheory UpperHalfPlane
open scoped ContDiff CompactlySupported
namespace GaloisForLFunctions.RHTower.SelbergMaassCurrentMeasures
open SelbergMaassCurrentFunctional SelbergMaassCurvatureMeasure SelbergMaassContinuousCurvature
  SelbergMaassCurrentTests SelbergMaassRegulatorMass SelbergMaassWeakCurvature
  SelbergUpperHalfPlaneCompactTests SelbergMaassCurrentCurvature
noncomputable section

variable (N : ℕ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam)

/-- The regular measure represented by the proved actual current-test limits. -/
def currentMeasure : Measure ℍ := RealRMK.rieszMeasure (currentPositiveFunctional N f)

/-- The regular measure represented by the positive difference from full source curvature. -/
def residualMeasure : Measure ℍ := RealRMK.rieszMeasure (residualPositiveFunctional N f)

/-- The constructed current measure is regular. -/
instance currentMeasure_regular : (currentMeasure N f).Regular := by
  unfold currentMeasure
  infer_instance

/-- The constructed residual measure is regular. -/
instance residualMeasure_regular : (residualMeasure N f).Regular := by
  unfold residualMeasure
  infer_instance

/-- The actual current measure is finite on compact sets. -/
instance currentMeasure_finiteOnCompacts : IsFiniteMeasureOnCompacts (currentMeasure N f) := by
  infer_instance

/-- The actual residual measure is finite on compact sets. -/
instance residualMeasure_finiteOnCompacts : IsFiniteMeasureOnCompacts (residualMeasure N f) := by
  infer_instance

/-- Every actual compact continuous test is integrable for the current measure. -/
theorem current_test_integrable (g : C_c(ℍ, ℝ)) : Integrable g (currentMeasure N f) :=
  g.continuous.integrable_of_hasCompactSupport g.hasCompactSupport

/-- Every actual compact continuous test is integrable for the residual measure. -/
theorem residual_test_integrable (g : C_c(ℍ, ℝ)) : Integrable g (residualMeasure N f) :=
  g.continuous.integrable_of_hasCompactSupport g.hasCompactSupport

/-- Integration against the current measure recovers the literal regulator-test limit. -/
theorem integral_current_test (g : C_c(ℍ, ℝ)) :
    (∫ z, g z ∂currentMeasure N f) = currentValue N f g :=
  RealRMK.integral_rieszMeasure (currentPositiveFunctional N f) g

/-- Integration against the residual measure recovers the exact positive functional difference. -/
theorem integral_residual_test (g : C_c(ℍ, ℝ)) :
    (∫ z, g z ∂residualMeasure N f) =
      continuousCurvature N f (zeroExtend g) - currentValue N f g :=
  RealRMK.integral_rieszMeasure (residualPositiveFunctional N f) g

/-- The two actual positive measures sum exactly to the original source curvature measure. -/
theorem curvatureMeasure_eq_add :
    curvatureMeasure N f = currentMeasure N f + residualMeasure N f := by
  letI : IsFiniteMeasureOnCompacts (currentMeasure N f + residualMeasure N f) := ⟨by
    intro K hK
    rw [Measure.add_apply]
    exact ENNReal.add_lt_top.mpr ⟨hK.measure_lt_top, hK.measure_lt_top⟩⟩
  symm
  apply curvatureMeasure_unique N f (currentMeasure N f + residualMeasure N f)
  intro g
  rw [integral_add_measure (current_test_integrable N f g) (residual_test_integrable N f g),
    integral_current_test, integral_residual_test]
  ring

/-- The original regulated current integrals converge to the constructed current measure on every compact test. -/
theorem current_limit_integral (g : C_c(ℍ, ℝ)) :
    Tendsto (fun e : Ioi (0 : ℝ) => testedCurrent N f e (zeroExtend g)) regulatorAtZero
      (𝓝 (∫ z, g z ∂currentMeasure N f)) := by
  rw [integral_current_test]
  exact current_limit N f g

/-- The exact remainder of actual regulated test integrals converges to the residual measure. -/
theorem residual_limit_integral (g : C_c(ℍ, ℝ)) :
    Tendsto (fun e : Ioi (0 : ℝ) => testedCurvature N f e (zeroExtend g) -
      testedCurrent N f e (zeroExtend g)) regulatorAtZero (𝓝 (∫ z, g z ∂residualMeasure N f)) := by
  rw [integral_residual_test]
  exact (continuousCurvature_limit N f (zeroExtend_continuous g)
    (zeroExtend_compact g) (zeroExtend_support g)).sub (current_limit N f g)

private theorem regulator_test_eq (g : C_c(ℍ, ℝ)) (e : Ioi (0 : ℝ)) :
    (fun z => zeroExtend g z * regulatorGradientWeight N f e z) =
      (fun z => zeroExtend g z * curvatureWeight N f e z - zeroExtend g z * currentWeight N f e z) := by
  funext z
  by_cases hz : 0 < z.im
  · have he := curvatureWeight_split N f e (ofComplex z)
    rw [ofComplex_apply_of_im_pos hz] at he
    rw [he]
    ring
  · simp only [zeroExtend, if_neg hz, zero_mul, sub_zero]

/-- The literal regulator-gradient contribution is genuinely integrable on every compact source test. -/
theorem regulator_test_integrable (g : C_c(ℍ, ℝ)) (e : Ioi (0 : ℝ)) :
    Integrable (fun z => zeroExtend g z * regulatorGradientWeight N f e z) := by
  rw [regulator_test_eq]
  exact (test_curvature_integrable N f (zeroExtend_continuous g)
    (zeroExtend_compact g) (zeroExtend_support g) e).sub
      (test_current_integrable N f (zeroExtend_continuous g)
        (zeroExtend_compact g) (zeroExtend_support g) e)

/-- The exact residual of regulated integrals is the literal regulator-gradient integral. -/
theorem regulator_integral_eq (g : C_c(ℍ, ℝ)) (e : Ioi (0 : ℝ)) :
    (∫ z, zeroExtend g z * regulatorGradientWeight N f e z) =
      testedCurvature N f e (zeroExtend g) - testedCurrent N f e (zeroExtend g) := by
  rw [regulator_test_eq]
  exact integral_sub (test_curvature_integrable N f (zeroExtend_continuous g)
    (zeroExtend_compact g) (zeroExtend_support g) e)
      (test_current_integrable N f (zeroExtend_continuous g)
        (zeroExtend_compact g) (zeroExtend_support g) e)

/-- The residual measure is the actual weak limit of the retained regulator-gradient term, including any nodal concentration. -/
theorem regulator_limit_integral (g : C_c(ℍ, ℝ)) :
    Tendsto (fun e : Ioi (0 : ℝ) => ∫ z, zeroExtend g z * regulatorGradientWeight N f e z)
      regulatorAtZero (𝓝 (∫ z, g z ∂residualMeasure N f)) := by
  simp only [regulator_integral_eq]
  exact residual_limit_integral N f g

end
end GaloisForLFunctions.RHTower.SelbergMaassCurrentMeasures
