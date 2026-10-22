import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMGlobalSmoothResponse

/-!
Compact planar Green identities for the actual smooth chart fields. Both integrations by parts retain all terms and establish integrability before separating the classical residual.
-/

open MeasureTheory Set Filter Topology UpperHalfPlane ModularGroup
open GaloisForLFunctions.HTGeometry
open scoped ContDiff
namespace RHTower.D4BMModularCore
noncomputable section

/-- Chart smoothness gives all ordinary planar derivatives throughout positive height. -/
theorem ChartSmooth.planar_contDiffOn {f : UpperHalfPlane → ℂ} (hf : ChartSmooth f) :
    ContDiffOn ℝ ∞ (f ∘ ofComplex) {z : ℂ | 0 < z.im} := by
  intro z hz
  exact (hf ⟨z,hz⟩).contDiffWithinAt

/-- The planar derivative retains smoothness on the full positive-height chart. -/
theorem planar_derivative_contDiffOn {f : ℂ → ℂ}
    (hf : ContDiffOn ℝ ∞ f {z : ℂ | 0 < z.im}) (v : ℂ) :
    ContDiffOn ℝ ∞ (fun z => fderiv ℝ f z v) {z : ℂ | 0 < z.im} := by
  intro z hz
  exact (((hf.contDiffAt (isOpen_upperHalfPlaneSet.mem_nhds hz)).fderiv_right
    (m := ∞) (by simp)).clm_apply contDiffAt_const).contDiffWithinAt

/-- Compact positive-height tests pair integrably with every continuous chart field. -/
theorem PlanarChartTest.integrable_mul_planar (g : PlanarChartTest) (f : ℂ → ℂ)
    (hf : ContinuousOn f {z : ℂ | 0 < z.im}) :
    Integrable (fun z => f z*g.field z) (volume : Measure ℂ) := by
  apply (integrableOn_iff_integrable_of_support_subset
    ((Function.support_mul_subset_right f g.field).trans (subset_tsupport g.field))).mp
  exact ((hf.mono g.support).mul g.smooth.continuous.continuousOn).integrableOn_compact g.compact

/-- Both actual directional derivatives move from a compact test to the smooth chart field. -/
theorem PlanarChartTest.second_green (g : PlanarChartTest) (f : ℂ → ℂ)
    (hf : ContDiffOn ℝ ∞ f {z : ℂ | 0 < z.im}) (v : ℂ) :
    (∫ z : ℂ, f z*fderiv ℝ (g.derivative v).field z v) =
      ∫ z : ℂ, fderiv ℝ (fun w => fderiv ℝ f w v) z v*g.field z := by
  have hd := planar_derivative_contDiffOn hf v
  have hdd := planar_derivative_contDiffOn hd v
  have h1 := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    ((g.derivative v).integrable_mul_planar _ hd.continuousOn)
    (((g.derivative v).derivative v).integrable_mul_planar _ hf.continuousOn)
    ((g.derivative v).integrable_mul_planar _ hf.continuousOn)
    (fun z hz => (hf.contDiffAt (isOpen_upperHalfPlaneSet.mem_nhds
      ((g.derivative v).support hz))).differentiableAt (by simp))
    (fun z _ => (g.derivative v).smooth.differentiable (by simp) z)
  have h2 := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (g.integrable_mul_planar _ hdd.continuousOn)
    ((g.derivative v).integrable_mul_planar _ hd.continuousOn)
    (g.integrable_mul_planar _ hd.continuousOn)
    (fun z hz => (hd.contDiffAt (isOpen_upperHalfPlaneSet.mem_nhds
      (g.support hz))).differentiableAt (by simp))
    (fun z _ => g.smooth.differentiable (by simp) z)
  change (∫ z : ℂ, f z*fderiv ℝ (g.derivative v).field z v) = _ at h1
  rw [h1]
  change (∫ z : ℂ, fderiv ℝ f z v*(g.derivative v).field z) = _ at h2
  rw [h2,neg_neg]

/-- The actual planar Laplacian of a chart field. -/
def planarLaplacian (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  ∑ i : Fin 2, fderiv ℝ (fun w => fderiv ℝ f w (direction i)) z (direction i)

/-- The Laplacian of a smooth chart field remains smooth throughout positive height. -/
theorem planarLaplacian_contDiffOn {f : ℂ → ℂ}
    (hf : ContDiffOn ℝ ∞ f {z : ℂ | 0 < z.im}) :
    ContDiffOn ℝ ∞ (planarLaplacian f) {z : ℂ | 0 < z.im} :=
  ContDiffOn.sum (fun i _ => planar_derivative_contDiffOn
    (planar_derivative_contDiffOn hf (direction i)) (direction i))

/-- Full classical planar Green identity on arbitrary compact positive-height charts. -/
theorem PlanarChartTest.laplacian_green (g : PlanarChartTest) (f : ℂ → ℂ)
    (hf : ContDiffOn ℝ ∞ f {z : ℂ | 0 < z.im}) :
    (∫ z : ℂ, g.laplacianTest.field z*f z) = ∫ z : ℂ, g.field z*D4BMModularCore.planarLaplacian f z := by
  have hi (i : Fin 2) := (((g.derivative (direction i)).derivative (direction i)).integrable_mul_planar
    f hf.continuousOn)
  have hj (i : Fin 2) := g.integrable_mul_planar _
    (planar_derivative_contDiffOn (planar_derivative_contDiffOn hf (direction i))
      (direction i)).continuousOn
  simp only [PlanarChartTest.laplacianTest,PlanarChartTest.planarLaplacian,D4BMModularCore.planarLaplacian,
    Finset.sum_mul,Finset.mul_sum]
  rw [integral_finsetSum _ (fun i _ => by simpa only [mul_comm,PlanarChartTest.derivative] using hi i),
    integral_finsetSum _ (fun i _ => by simpa only [mul_comm] using hj i)]
  apply Finset.sum_congr rfl
  intro i _
  simpa only [mul_comm] using g.second_green f hf (direction i)

end
end RHTower.D4BMModularCore
