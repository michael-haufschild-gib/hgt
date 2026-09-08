import GaloisForLFunctions.RHTower.SelbergMaassContinuousCurvature
import GaloisForLFunctions.RHTower.SelbergUpperHalfPlaneCompactTests
import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real

/-!
# The actual retained-curvature measure of a congruence Maass source

The proved continuous compact-test limit defines a positive real linear map on
actual upper-half-plane compact tests. Riesz--Markov constructs its unique regular
measure, finite on compact sets. Genuine integration recovers the original C²
weak-curvature formula and the quantitative regulator error. No pointwise
curvature-limit interchange or quotient-boundary nullity is assumed.
-/

open Set Filter Topology MeasureTheory UpperHalfPlane
open scoped ContDiff CompactlySupported
namespace GaloisForLFunctions.RHTower.SelbergMaassCurvatureMeasure
open SelbergMaassMean SelbergMaassWeakCurvature SelbergMaassRegulatorMass
  SelbergMaassContinuousCurvature SelbergUpperHalfPlaneCompactTests
noncomputable section

variable (N : ℕ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam)

/-- The actual continuous-test curvature limit as a real linear functional on compact upper-half-plane tests. -/
def compactFunctional : C_c(ℍ, ℝ) →ₗ[ℝ] ℝ where
  toFun g := continuousCurvature N f (zeroExtend g)
  map_add' g h := by
    rw [zeroExtend_add]
    exact continuousCurvature_add N f (zeroExtend_continuous g) (zeroExtend_compact g) (zeroExtend_support g)
      (zeroExtend_continuous h) (zeroExtend_compact h) (zeroExtend_support h)
  map_smul' c g := by
    change continuousCurvature N f (zeroExtend (c • g)) = c * continuousCurvature N f (zeroExtend g)
    rw [zeroExtend_smul]
    exact continuousCurvature_const_mul N f (zeroExtend_continuous g) (zeroExtend_compact g)
      (zeroExtend_support g) c

/-- The original source generates a positive real linear compact-test functional. -/
def compactPositiveFunctional : C_c(ℍ, ℝ) →ₚ[ℝ] ℝ :=
  PositiveLinearMap.mk (compactFunctional N f) (by
    intro g h hgh
    exact continuousCurvature_mono N f (zeroExtend_continuous g) (zeroExtend_compact g) (zeroExtend_support g)
      (zeroExtend_continuous h) (zeroExtend_compact h) (zeroExtend_support h) (zeroExtend_mono hgh))

/-- The regular upper-half-plane measure represented by the actual source curvature functional. -/
def curvatureMeasure : Measure ℍ := RealRMK.rieszMeasure (compactPositiveFunctional N f)

/-- The constructed source curvature measure is regular. -/
instance curvatureMeasure_regular : (curvatureMeasure N f).Regular := by
  unfold curvatureMeasure
  infer_instance

/-- The constructed source curvature measure is finite on every compact set. -/
instance curvatureMeasure_finiteOnCompacts : IsFiniteMeasureOnCompacts (curvatureMeasure N f) := by
  infer_instance

/-- Every original compact continuous upper-half-plane test is genuinely integrable for the source curvature measure. -/
theorem compact_test_integrable (g : C_c(ℍ, ℝ)) : Integrable g (curvatureMeasure N f) :=
  g.continuous.integrable_of_hasCompactSupport g.hasCompactSupport

/-- The source measure represents the actual continuous-test curvature limit exactly. -/
theorem integral_compact_test (g : C_c(ℍ, ℝ)) :
    (∫ z, g z ∂curvatureMeasure N f) = continuousCurvature N f (zeroExtend g) :=
  RealRMK.integral_rieszMeasure (compactPositiveFunctional N f) g

/-- Every admissible planar continuous test restricts to a genuinely integrable source-measure test. -/
theorem original_test_integrable {phi : ℂ → ℝ} (hp : Continuous phi)
    (hc : HasCompactSupport phi) (hs : tsupport phi ⊆ {z : ℂ | 0 < z.im}) :
    Integrable (fun z : ℍ => phi z) (curvatureMeasure N f) :=
  compact_test_integrable N f (restrictCompact phi hp hc hs)

/-- The source measure integrates an admissible planar continuous test to its actual regulator limit. -/
theorem integral_original_continuous_test {phi : ℂ → ℝ} (hp : Continuous phi)
    (hc : HasCompactSupport phi) (hs : tsupport phi ⊆ {z : ℂ | 0 < z.im}) :
    (∫ z : ℍ, phi z ∂curvatureMeasure N f) = continuousCurvature N f phi := by
  have h := integral_compact_test N f (restrictCompact phi hp hc hs)
  rw [zeroExtend_restrictCompact] at h
  exact h

/-- The source measure recovers the original C² weak-curvature formula with both derivatives on the test. -/
theorem integral_original_test {phi : ℂ → ℝ} (hp : ContDiff ℝ 2 phi)
    (hc : HasCompactSupport phi) (hs : tsupport phi ⊆ {z : ℂ | 0 < z.im}) :
    (∫ z : ℍ, phi z ∂curvatureMeasure N f) = weakCurvature N f phi := by
  rw [integral_original_continuous_test N f hp.continuous hc hs,
    continuousCurvature_eq_weak N f hp hc hs]

/-- The original regularized source integrals converge to integration against the constructed measure on every compact continuous upper-half-plane test. -/
theorem testedCurvature_limit_integral (g : C_c(ℍ, ℝ)) :
    Tendsto (fun e : Ioi (0 : ℝ) => testedCurvature N f e (zeroExtend g))
      regulatorAtZero (𝓝 (∫ z, g z ∂curvatureMeasure N f)) := by
  rw [integral_compact_test]
  exact continuousCurvature_limit N f (zeroExtend_continuous g) (zeroExtend_compact g) (zeroExtend_support g)

/-- Every compact upper-half-plane region has finite actual curvature measure. -/
theorem measure_compact_lt_top {K : Set ℍ} (hK : IsCompact K) : curvatureMeasure N f K < ⊤ :=
  hK.measure_lt_top

/-- Any regular measure representing the actual continuous-test source limits equals the constructed curvature measure. -/
theorem curvatureMeasure_unique (μ : Measure ℍ) [μ.Regular]
    (h : ∀ g : C_c(ℍ, ℝ), (∫ z, g z ∂μ) = continuousCurvature N f (zeroExtend g)) :
    μ = curvatureMeasure N f := by
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro g
  rw [h g, integral_compact_test N f g]

/-- The actual measure representation retains the explicit regulator error on every admissible C² test. -/
theorem testedCurvature_error_le_integral {phi : ℂ → ℝ} (hp : ContDiff ℝ 2 phi)
    (hc : HasCompactSupport phi) (hs : tsupport phi ⊆ {z : ℂ | 0 < z.im}) (e : Ioi (0 : ℝ)) :
    ‖testedCurvature N f e phi - ∫ z : ℍ, phi z ∂curvatureMeasure N f‖ ≤ (e : ℝ) * testBudget lam phi := by
  rw [integral_original_test N f hp hc hs]
  exact testedCurvature_error_le N f hp hc hs e

/-- The original source determines a unique regular measure representing all its continuous compact-test regulator limits. -/
theorem existsUnique_curvatureMeasure :
    ∃! μ : Measure ℍ, μ.Regular ∧ ∀ g : C_c(ℍ, ℝ),
      (∫ z, g z ∂μ) = continuousCurvature N f (zeroExtend g) := by
  refine ⟨curvatureMeasure N f, ⟨inferInstance, integral_compact_test N f⟩, ?_⟩
  intro μ hμ
  letI : μ.Regular := hμ.1
  exact curvatureMeasure_unique N f μ hμ.2

end
end GaloisForLFunctions.RHTower.SelbergMaassCurvatureMeasure
