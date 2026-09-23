import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMCuspDominantCoefficient
import GaloisForLFunctions.HTGeometry.IntervalMeanSquareMoment

/-! Transfer of the actual modular energy norm to the full cusp mean-square density. -/

open MeasureTheory Set Filter Topology UpperHalfPlane ModularGroup
open GaloisForLFunctions.HTGeometry
open scoped ContDiff
namespace RHTower.D4BMCuspResponse
open D4BMModularCore D4BMCuspProjection D4BMGlobalAngularResponse
noncomputable section

/-- The actual smooth response retains square-integrability in the original native measure. -/
theorem globalResponse_native_square_integrable (q : XiZeroCopy) (branch : Bool) :
    Integrable (fun z : UpperHalfPlane => ‖globalResponse q branch z‖^(2 : ℕ)) measure := by
  have hi := (Lp.memLp (embedding (weakResponse q branch))).integrable_norm_pow
    (by norm_num : (2:ℕ) ≠ 0)
  apply hi.congr
  filter_upwards [globalResponse_native_ae q branch] with z hz
  rw [hz]

/-- The actual horizontal mean square, before taking the square of the mean. -/
def responseMeanSquare (q : XiZeroCopy) (branch : Bool) (y : ℝ) : ℝ :=
  ∫ x in Ioc (-1/2:ℝ) (1/2), ‖responsePlanar q branch (point x y)‖^(2 : ℕ)

private def normRectangle : Set ℂ := {z | z.re ∈ Icc (-1/2) (1/2) ∧ 2 < z.im}

private theorem normRectangle_subset : normRectangle ⊆ cellChart := by
  intro z hz
  have hy : 0 < z.im := lt_trans (by norm_num) hz.2
  refine ⟨⟨z,hy⟩,?_,rfl⟩
  constructor
  · rw [Complex.normSq_apply]
    nlinarith [sq_nonneg z.re,hz.2]
  · change |z.re| ≤ 1/2
    exact abs_le.mpr (by simpa only [mem_Icc,neg_div] using hz.1)

/-- Transport of the full original native norm to the literal cusp rectangle
proves integrability of the horizontal mean-square density. -/
theorem responseMeanSquare_density_integrable (q : XiZeroCopy) (branch : Bool) :
    IntegrableOn (fun y : ℝ => responseMeanSquare q branch y/y^(2 : ℕ)) (Ioi (2:ℝ)) := by
  let F : ℂ → ℝ := fun z => ‖responsePlanar q branch z‖^(2 : ℕ)
  have hi : Integrable (fun z : UpperHalfPlane => F z) measure := by
    simpa only [F,responsePlanar,Function.comp_apply,ofComplex_apply] using
      globalResponse_native_square_integrable q branch
  have hmap : Integrable F (Measure.map UpperHalfPlane.coe measure) :=
    UpperHalfPlane.measurableEmbedding_coe.integrable_map_iff.mpr hi
  rw [map_measure_eq] at hmap
  have hd : IntegrableOn (fun z => chartDensity z • F z) cellChart :=
    (integrable_withDensity_iff_integrable_smul (show Measurable chartDensity by
      unfold chartDensity; fun_prop)).mp hmap
  have hrect : IntegrableOn (fun z : ℂ => F z/z.im^(2 : ℕ)) normRectangle := by
    apply (hd.mono_set normRectangle_subset).congr_fun
    · intro z hz
      have hp : 0 < z.im := lt_trans (by norm_num) hz.2
      simp only [chartDensity,NNReal.smul_def,NNReal.coe_pow,NNReal.coe_div,NNReal.coe_one,
        coe_nnnorm,Real.norm_eq_abs,abs_of_pos hp,smul_eq_mul]
      ring
    · exact (isClosed_Icc.preimage Complex.continuous_re).measurableSet.inter
        (isOpen_lt continuous_const Complex.continuous_im).measurableSet
  let G : ℝ × ℝ → ℝ := fun xy => F (Complex.measurableEquivRealProd.symm xy)/xy.2^(2 : ℕ)
  have hG : IntegrableOn G (Icc (-1/2:ℝ) (1/2) ×ˢ Ioi (2:ℝ))
      ((volume : Measure ℝ).prod volume) := by
    rw [← Measure.volume_eq_prod]
    apply (Complex.volume_preserving_equiv_real_prod.integrableOn_comp_preimage
      Complex.measurableEquivRealProd.measurableEmbedding).mp
    change IntegrableOn (fun z : ℂ => F z/z.im^(2 : ℕ)) normRectangle
    exact hrect
  have hp : Integrable G
      ((volume.restrict (Icc (-1/2:ℝ) (1/2))).prod (volume.restrict (Ioi (2:ℝ)))) := by
    simpa only [Measure.prod_restrict,IntegrableOn] using hG
  apply hp.integral_prod_right.congr
  filter_upwards with y
  dsimp [G]
  rw [integral_div,integral_Icc_eq_integral_Ioc]
  have he (x : ℝ) : (⟨x,y⟩:ℂ) = point x y := by
    apply Complex.ext <;> simp [point]
  simp only [F,responseMeanSquare,he]

end
end RHTower.D4BMCuspResponse
