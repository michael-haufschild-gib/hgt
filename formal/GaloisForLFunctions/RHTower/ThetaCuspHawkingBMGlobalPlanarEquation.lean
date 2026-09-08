import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMGlobalPlanarLift

/-!
The actual full-forcing response satisfies its lifted planar equation against every compact positive-height test.
-/

open MeasureTheory Set Filter Topology UpperHalfPlane ModularGroup
open scoped ContDiff ComplexConjugate
namespace RHTower.D4BMModularCore
open D4BMGlobalAngularResponse
noncomputable section

/-- Inverse height powers preserve every compact positive-height planar test. -/
def PlanarChartTest.divHeight (g : PlanarChartTest) (n : ℕ) : PlanarChartTest where
  field z := g.field z/(z.im : ℂ)^n
  smooth := by
    apply contDiff_iff_contDiffAt.mpr
    intro z
    by_cases hz : z ∈ tsupport g.field
    · have hy : (z.im : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt (g.support hz))
      have hp : ContDiffAt ℝ ∞ (fun w : ℂ => (w.im : ℂ)^n) z :=
        ((Complex.ofRealCLM.contDiff.comp Complex.imCLM.contDiff).pow n).contDiffAt
      simpa only [div_eq_mul_inv] using g.smooth.contDiffAt.mul (hp.fun_inv (pow_ne_zero n hy))
    · apply (contDiffAt_const (c := (0:ℂ))).congr_of_eventuallyEq
      filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hz] with w hw
      simp [image_eq_zero_of_notMem_tsupport hw]
  compact := g.compact.mono (by intro z hz he; exact hz (by simp [he]))
  support := (closure_mono (by intro z hz he; exact hz (by simp [he]))).trans g.support

/-- The literal Euclidean Laplacian of a compact positive-height chart test. -/
def PlanarChartTest.planarLaplacian (g : PlanarChartTest) (z : ℂ) : ℂ :=
  ∑ i : Fin 2, fderiv ℝ (g.derivative (direction i)).field z (direction i)

private theorem PlanarChartTest.planar_support (g : PlanarChartTest) :
    Function.support g.planarLaplacian ⊆ tsupport g.field := by
  intro z hz
  by_contra hn
  have he (i : Fin 2) : fderiv ℝ (g.derivative (direction i)).field z (direction i) = 0 := by
    apply image_eq_zero_of_notMem_tsupport
      (f := fun x : ℂ => fderiv ℝ (g.derivative (direction i)).field x (direction i))
    intro hs
    exact hn ((tsupport_fderiv_apply_subset ℝ (direction i)).trans
      (tsupport_fderiv_apply_subset ℝ (direction i)) hs)
  exact hz (by simp only [PlanarChartTest.planarLaplacian,he,Finset.sum_const_zero])

/-- The Euclidean Laplacian retains the test's compact positive-height support. -/
def PlanarChartTest.laplacianTest (g : PlanarChartTest) : PlanarChartTest where
  field := g.planarLaplacian
  smooth := ContDiff.sum (fun i _ => ((g.derivative (direction i)).derivative (direction i)).smooth)
  compact := HasCompactSupport.of_support_subset_isCompact g.compact g.planar_support
  support := (closure_minimal g.planar_support isClosed_closure).trans g.support

private theorem PlanarChartTest.local_integral_halfplane (g : PlanarChartTest) (u : Space) :
    (∫ z in {z : ℂ | 0 < z.im}, g.localValue u z) = ∫ z : ℂ, g.localValue u z := by
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro z hz
  have hn : z ∉ tsupport g.field := fun hg => hz (g.support hg)
  simp [PlanarChartTest.localValue,image_eq_zero_of_notMem_tsupport hn]

/-- Squared height converts an actual full hyperbolic moment to its planar localization. -/
theorem PlanarChartTest.height_sq_planar (g : PlanarChartTest) (u : Space) :
    (∫ z : UpperHalfPlane, (z.im : ℂ)^2*g.field z*globalLift u z) =
      ∫ z : ℂ, g.localValue u z := by
  rw [← g.local_integral_halfplane,← integral_volume_height_sq_chart]
  apply integral_congr_ae
  filter_upwards [] with z
  simp only [PlanarChartTest.localValue,ofComplex_apply,mul_assoc]

/-- The native scalar moment retains its exact inverse-square height density in the plane. -/
theorem PlanarChartTest.scalar_planar (g : PlanarChartTest) (u : Space) :
    (∫ z : UpperHalfPlane, g.field z*globalLift u z) =
      ∫ z : ℂ, (g.divHeight 2).localValue u z := by
  rw [← (g.divHeight 2).height_sq_planar]
  apply integral_congr_ae
  filter_upwards [] with z
  have hy : (z.im : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr z.im_ne_zero
  simp only [PlanarChartTest.divHeight,coe_im]
  field_simp

/-- The actual lifted full-forcing response obeys its literal planar distributional
equation on all positive-height charts, including charts crossing modular seams. -/
theorem full_response_global_planar_equation (q : XiZeroCopy) (minusBranch : Bool)
    (g : PlanarChartTest) :
    (∫ z : ℂ, g.laplacianTest.localValue (embedding (weakResponse q minusBranch)) z) -
      parameter q minusBranch*(∫ z : ℂ, (g.divHeight 2).localValue
        (embedding (weakResponse q minusBranch)) z) =
      ∫ z : ℂ, (g.divHeight 2).localValue (forcingVector q minusBranch) z := by
  have he := full_response_lifted_test_equation q minusBranch g
  rw [g.scalar_planar,g.scalar_planar] at he
  rw [← g.laplacianTest.height_sq_planar]
  convert he using 1
  congr 1
  apply integral_congr_ae
  filter_upwards [] with z
  rw [g.laplaceTest_field]
  rfl

end
end RHTower.D4BMModularCore
