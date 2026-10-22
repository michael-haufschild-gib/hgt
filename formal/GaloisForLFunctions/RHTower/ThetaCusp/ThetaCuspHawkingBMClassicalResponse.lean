import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMClassicalGreen

/-!
The constructed globally smooth response satisfies its original differential equation pointwise throughout the upper half-plane. Compact test separation transfers the existing distribution equation without a new regularity premise.
-/

open MeasureTheory Set Filter Topology UpperHalfPlane ModularGroup
open GaloisForLFunctions.HTGeometry
open scoped ContDiff
namespace RHTower.D4BMModularCore
open D4BMGlobalAngularResponse
noncomputable section

/-- Every actual scalar localization equals the localization of the constructed smooth response. -/
theorem PlanarChartTest.globalResponse_localValue_ae (g : PlanarChartTest)
    (q : XiZeroCopy) (branch : Bool) :
    g.localValue (embedding (weakResponse q branch)) =ᵐ[(volume : Measure ℂ)]
      (fun z => g.field z*globalResponse q branch (ofComplex z)) := by
  have he := (ae_restrict_iff' isOpen_upperHalfPlaneSet.measurableSet).mp
    (full_response_global_planar_smooth q branch).choose_spec.2
  filter_upwards [he] with z hz
  by_cases hy : 0 < z.im
  · have hh := hz hy
    change g.field z*globalLift (embedding (weakResponse q branch)) (ofComplex z) = _
    rw [← hh]
    simp only [globalResponse,ofComplex_apply_of_im_pos hy]
  · have hg : g.field z = 0 := image_eq_zero_of_notMem_tsupport (fun h => hy (g.support h))
    simp [PlanarChartTest.localValue,hg]

/-- The exact full planar test equation holds for the actual smooth representatives. -/
theorem full_response_smooth_planar_test (q : XiZeroCopy) (branch : Bool) (g : PlanarChartTest) :
    (∫ z : ℂ, g.laplacianTest.field z*globalResponse q branch (ofComplex z)) -
      parameter q branch*(∫ z : ℂ, (g.divHeight 2).field z*globalResponse q branch (ofComplex z)) =
      ∫ z : ℂ, (g.divHeight 2).field z*globalForcing q branch (ofComplex z) := by
  have hR (a : PlanarChartTest) := integral_congr_ae (a.globalResponse_localValue_ae q branch)
  have hF := integral_congr_ae ((g.divHeight 2).globalForcing_localValue_ae q branch)
  have h := full_response_global_planar_equation q branch g
  rw [hR,hR,hF] at h
  exact h

private def responseResidual (q : XiZeroCopy) (branch : Bool) (z : ℂ) : ℂ :=
  planarLaplacian (globalResponse q branch ∘ ofComplex) z -
    (parameter q branch*globalResponse q branch (ofComplex z)+globalForcing q branch (ofComplex z)) /
      (z.im : ℂ)^(2 : ℕ)

private theorem responseResidual_continuousOn (q : XiZeroCopy) (branch : Bool) :
    ContinuousOn (responseResidual q branch) {z : ℂ | 0 < z.im} := by
  have hR := (globalResponse_smooth q branch).planar_contDiffOn
  have hF := (globalForcing_smooth q branch).planar_contDiffOn
  apply (planarLaplacian_contDiffOn hR).continuousOn.sub
  exact ((continuousOn_const.mul hR.continuousOn).add hF.continuousOn).div
    ((Complex.ofRealCLM.continuous.comp Complex.continuous_im).pow 2).continuousOn
    (fun z hz => pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr (ne_of_gt hz)))

private theorem responseResidual_test_zero (q : XiZeroCopy) (branch : Bool) (g : PlanarChartTest) :
    (∫ z : ℂ, g.field z*responseResidual q branch z) = 0 := by
  let R := globalResponse q branch ∘ ofComplex
  let F := globalForcing q branch ∘ ofComplex
  have hR := (globalResponse_smooth q branch).planar_contDiffOn
  have hF := (globalForcing_smooth q branch).planar_contDiffOn
  have h0 := g.integrable_mul_planar (planarLaplacian R) (planarLaplacian_contDiffOn hR).continuousOn
  have h1 := (g.divHeight 2).integrable_mul_planar R hR.continuousOn
  have h2 := (g.divHeight 2).integrable_mul_planar F hF.continuousOn
  have h01 : Integrable (fun z : ℂ => planarLaplacian R z*g.field z -
      parameter q branch*(R z*(g.divHeight 2).field z)) volume :=
    h0.sub (h1.const_mul (parameter q branch))
  have he := full_response_smooth_planar_test q branch g
  change (∫ z : ℂ, g.laplacianTest.field z*R z) -
    parameter q branch*(∫ z : ℂ, (g.divHeight 2).field z*R z) =
    ∫ z : ℂ, (g.divHeight 2).field z*F z at he
  rw [g.laplacian_green R hR] at he
  have he' : (∫ z : ℂ, planarLaplacian R z*g.field z) -
      parameter q branch*(∫ z : ℂ, R z*(g.divHeight 2).field z) -
      (∫ z : ℂ, F z*(g.divHeight 2).field z) = 0 := by
    simpa only [sub_eq_zero,mul_comm,R,F,Function.comp_apply] using he
  calc
    _ = ∫ z : ℂ, (planarLaplacian R z*g.field z -
        parameter q branch*(R z*(g.divHeight 2).field z)) - F z*(g.divHeight 2).field z := by
      apply integral_congr_ae
      filter_upwards [] with z
      simp only [responseResidual,PlanarChartTest.divHeight,R,F,Function.comp_apply]
      ring
    _ = _ := by
      rw [integral_sub h01 h2,integral_sub h0 (h1.const_mul (parameter q branch)),
        integral_const_mul]
      exact he'

/-- The reconstructed response satisfies the classical equation at every positive-height point. -/
theorem globalResponse_classical_planar (q : XiZeroCopy) (branch : Bool) (z : ℂ) (hz : 0 < z.im) :
    planarLaplacian (globalResponse q branch ∘ ofComplex) z =
      (parameter q branch*globalResponse q branch (ofComplex z)+globalForcing q branch (ofComplex z)) /
        (z.im : ℂ)^(2 : ℕ) := by
  have hc := responseResidual_continuousOn q branch
  have ha := isOpen_upperHalfPlaneSet.ae_eq_zero_of_integral_contDiff_smul_eq_zero
    (hc.locallyIntegrableOn isOpen_upperHalfPlaneSet.measurableSet) (fun b hb hk hs => by
      let g : PlanarChartTest := ⟨Complex.ofRealCLM ∘ b,Complex.ofRealCLM.contDiff.comp hb,
        hk.comp_left rfl,(closure_mono (by intro w hw; simpa using hw)).trans hs⟩
      simpa only [g,Function.comp_apply,Complex.ofRealCLM_apply,Complex.real_smul] using
        responseResidual_test_zero q branch g)
  have har : responseResidual q branch =ᵐ[volume.restrict {z : ℂ | 0 < z.im}] (fun _ => 0) :=
    (ae_restrict_iff' isOpen_upperHalfPlaneSet.measurableSet).mpr ha
  have hp := Measure.eqOn_open_of_ae_eq har isOpen_upperHalfPlaneSet hc continuousOn_const
  exact sub_eq_zero.mp (hp hz)

/-- The literal hyperbolic Laplacian of an upper-half-plane chart field. -/
def chartLaplacian (f : UpperHalfPlane → ℂ) (z : UpperHalfPlane) : ℂ :=
  (z.im : ℂ)^(2 : ℕ)*planarLaplacian (f ∘ ofComplex) (z:ℂ)

/-- The original complete forcing drives the actual smooth response pointwise on the entire half-plane. -/
theorem globalResponse_classical_equation (q : XiZeroCopy) (branch : Bool) (z : UpperHalfPlane) :
    chartLaplacian (globalResponse q branch) z - parameter q branch*globalResponse q branch z =
      globalForcing q branch z := by
  have h := globalResponse_classical_planar q branch (z:ℂ) z.im_pos
  simp only [ofComplex_apply,coe_im] at h
  rw [chartLaplacian,h]
  field_simp [Complex.ofReal_ne_zero.mpr z.im_ne_zero]
  ring

end
end RHTower.D4BMModularCore
