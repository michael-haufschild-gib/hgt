import GaloisForLFunctions.RHTower.SelbergMaassCurvatureMeasure
import GaloisForLFunctions.RHTower.SelbergMaassCurvatureCovariance
import Mathlib.Analysis.Complex.UpperHalfPlane.Measure
import Mathlib.MeasureTheory.Group.Integral

/-!
# Modular invariance of the actual Maass curvature measure

The full regularized curvature density is invariant relative to hyperbolic
volume. Literal chart change of variables therefore preserves every original
compact-test regulator integral. Their already established limits identify the
pushforward of the actual regular curvature measure by uniqueness.

The result retains all measurable boundary charge. No fundamental-domain
indicator limit, vanishing seam mass, or quarter spectral comparison is assumed.
-/

open Set Filter Topology MeasureTheory UpperHalfPlane ModularGroup
open scoped MatrixGroups ContDiff CompactlySupported NNReal ENNReal
namespace GaloisForLFunctions.RHTower.SelbergMaassCurvatureTransport
open SelbergMaassWeakCurvature SelbergMaassCurvatureMeasure SelbergUpperHalfPlaneCompactTests
  SelbergMaassCurvatureCovariance
noncomputable section

/-- The actual hyperbolic area density in the complex chart. -/
def chartDensity (z : ℂ) : ℝ≥0 := (1 / ‖z.im‖₊) ^ 2

/-- The literal chart pushforward of hyperbolic volume, on every measurable set. -/
theorem map_volume_chart : Measure.map UpperHalfPlane.coe (volume : Measure ℍ) =
    ((volume : Measure ℂ).restrict {z : ℂ | 0 < z.im}).withDensity
      (fun z => (chartDensity z : ℝ≥0∞)) := by
  apply Measure.ext
  intro s hs
  rw [Measure.map_apply UpperHalfPlane.measurable_coe hs, UpperHalfPlane.volume_eq_lintegral,
    withDensity_apply _ hs, Measure.restrict_restrict hs]
  rw [Set.image_preimage_eq_inter_range, UpperHalfPlane.range_coe]
  rfl

/-- Squared height cancels the actual hyperbolic volume density for real integrals. -/
theorem integral_height_sq_chart (F : ℂ → ℝ) :
    (∫ z : ℍ, z.im ^ 2 * F z) = ∫ z in {z : ℂ | 0 < z.im}, F z := by
  have hm : Measurable chartDensity := by unfold chartDensity; fun_prop
  have hi (G : ℂ → ℝ) : (∫ z : ℍ, G z) =
      ∫ z in {z : ℂ | 0 < z.im}, chartDensity z • G z := by
    rw [← UpperHalfPlane.measurableEmbedding_coe.integral_map, map_volume_chart,
      integral_withDensity_eq_integral_smul hm]
  change (∫ z : ℍ, (z : ℂ).im ^ 2 * F z) = _
  rw [hi (fun z => z.im ^ 2 * F z)]
  apply setIntegral_congr_fun isOpen_upperHalfPlaneSet.measurableSet
  intro z hz
  change 0 < z.im at hz
  simp only [chartDensity, NNReal.smul_def, NNReal.coe_pow, NNReal.coe_div, NNReal.coe_one,
    coe_nnnorm, Real.norm_eq_abs, abs_of_pos hz, smul_eq_mul]
  field_simp

/-- Modular pullback preserves continuity and compact support of actual half-plane tests. -/
def pullTest (A : SL2Z) (g : C_c(ℍ, ℝ)) : C_c(ℍ, ℝ) :=
  g.comp (Homeomorph.smul (A : GL (Fin 2) ℝ)).toCocompactMap

/-- The compact test pullback is the literal modular action. -/
theorem pullTest_apply (A : SL2Z) (g : C_c(ℍ, ℝ)) (z : ℍ) :
    pullTest A g z = g (A • z) := rfl

variable (N : ℕ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam)

/-- Actual planar regulator tests equal their literal hyperbolic-density integrals. -/
theorem testedCurvature_eq_hyperbolic (e : Ioi (0 : ℝ)) (g : C_c(ℍ, ℝ)) :
    testedCurvature N f e (zeroExtend g) = ∫ z : ℍ, g z * hyperbolicCurvature N f e z := by
  calc
    testedCurvature N f e (zeroExtend g) =
        ∫ z in {z : ℂ | 0 < z.im}, zeroExtend g z * curvatureWeight N f e z := by
      symm
      apply setIntegral_eq_integral_of_forall_compl_eq_zero
      intro z hz
      have hzero : zeroExtend g z = 0 :=
        image_eq_zero_of_notMem_tsupport (fun h => hz (zeroExtend_support g h))
      rw [hzero, zero_mul]
    _ = ∫ z : ℍ, z.im ^ 2 * (zeroExtend g z * curvatureWeight N f e z) :=
      (integral_height_sq_chart _).symm
    _ = _ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun z => by dsimp only; rw [zeroExtend_apply]; unfold hyperbolicCurvature; ring)

/-- Every original regularized compact-test pairing is invariant under modular pullback. -/
theorem testedCurvature_pullTest (e : Ioi (0 : ℝ)) (A : SL2Z) (g : C_c(ℍ, ℝ)) :
    testedCurvature N f e (zeroExtend (pullTest A g)) = testedCurvature N f e (zeroExtend g) := by
  rw [testedCurvature_eq_hyperbolic, testedCurvature_eq_hyperbolic]
  have h := integral_smul_eq_self (μ := (volume : Measure ℍ)) (g := (A : GL (Fin 2) ℝ))
    (fun z : ℍ => g z * hyperbolicCurvature N f e z)
  change (∫ z : ℍ, g (A • z) * hyperbolicCurvature N f e (A • z)) = _ at h
  simpa only [hyperbolicCurvature_invariant, pullTest_apply] using h

/-- The constructed curvature measure has invariant pairings with every compact continuous test. -/
theorem integral_pullTest (A : SL2Z) (g : C_c(ℍ, ℝ)) :
    (∫ z, pullTest A g z ∂curvatureMeasure N f) = ∫ z, g z ∂curvatureMeasure N f := by
  have h := testedCurvature_limit_integral N f (pullTest A g)
  simp only [testedCurvature_pullTest] at h
  exact tendsto_nhds_unique h (testedCurvature_limit_integral N f g)

/-- The actual regular curvature measure is invariant under every integral modular action. -/
theorem curvatureMeasure_map (A : SL2Z) :
    Measure.map (fun z : ℍ => A • z) (curvatureMeasure N f) = curvatureMeasure N f := by
  let e : ℍ ≃ₜ ℍ := Homeomorph.smul (A : GL (Fin 2) ℝ)
  haveI : (Measure.map e (curvatureMeasure N f)).Regular := Measure.Regular.map e
  change Measure.map e (curvatureMeasure N f) = _
  apply curvatureMeasure_unique N f
  intro g
  rw [e.measurableEmbedding.integral_map]
  change (∫ z, pullTest A g z ∂curvatureMeasure N f) = _
  rw [integral_pullTest, integral_compact_test]

/-- Modular preimages preserve the actual curvature of every measurable half-plane set. -/
theorem curvatureMeasure_preimage (A : SL2Z) {s : Set ℍ} (hs : MeasurableSet s) :
    curvatureMeasure N f ((fun z : ℍ => A • z) ⁻¹' s) = curvatureMeasure N f s := by
  have hm : Measurable (fun z : ℍ => A • z) :=
    (Homeomorph.smul (A : GL (Fin 2) ℝ)).continuous.measurable
  have h := congrArg (fun μ : Measure ℍ => μ s) (curvatureMeasure_map N f A)
  rw [Measure.map_apply hm hs] at h
  exact h

/-- Change of variables for all real integrals against the actual curvature measure. -/
theorem integral_modular (A : SL2Z) (F : ℍ → ℝ) :
    (∫ z, F (A • z) ∂curvatureMeasure N f) = ∫ z, F z ∂curvatureMeasure N f := by
  let e : ℍ ≃ₜ ℍ := Homeomorph.smul (A : GL (Fin 2) ℝ)
  have h := e.measurableEmbedding.integral_map (μ := curvatureMeasure N f) F
  change (∫ z, F z ∂Measure.map (fun w : ℍ => A • w) (curvatureMeasure N f)) = _ at h
  rw [curvatureMeasure_map] at h
  exact h.symm

end
end GaloisForLFunctions.RHTower.SelbergMaassCurvatureTransport
