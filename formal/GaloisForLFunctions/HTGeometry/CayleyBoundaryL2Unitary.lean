import GaloisForLFunctions.HTGeometry.CayleyBoundaryL2

open MeasureTheory Complex Filter
open scoped ENNReal NNReal lp InnerProductSpace

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Pullback by the real Cayley embedding is onto after the target's null endpoint is ignored. -/
theorem circleCayleyWeightedPullback_surjective :
    Function.Surjective circleCayleyWeightedPullback := by
  intro g
  let hfun : Circle → ℂ := Function.extend circleCayley (fun x => g x) 0
  have hfun_measurable : Measurable hfun :=
    (continuous_circleCayley.measurableEmbedding injective_circleCayley).measurable_extend
      (Lp.stronglyMeasurable g).measurable measurable_zero
  have hfun_comp : hfun ∘ circleCayley = fun x => g x := by
    exact Function.extend_comp injective_circleCayley (fun x => g x) 0
  have hfun_memLp : MemLp hfun 2 circleLebesgue := by
    rw [← circleCayley_weighted_measurePreserving.map_eq]
    refine (memLp_map_measure_iff hfun_measurable.aestronglyMeasurable
      continuous_circleCayley.measurable.aemeasurable).2 ?_
    rw [hfun_comp]
    exact Lp.memLp g
  let f : Lp ℂ 2 circleLebesgue := hfun_memLp.toLp hfun
  refine ⟨f, ?_⟩
  change Lp.compMeasurePreserving circleCayley
      circleCayley_weighted_measurePreserving f = g
  rw [show f = hfun_memLp.toLp hfun from rfl,
    Lp.toLp_compMeasurePreserving]
  apply Lp.ext
  filter_upwards [
    (hfun_memLp.comp_measurePreserving
      circleCayley_weighted_measurePreserving).coeFn_toLp]
      with x hx
  rw [hx]
  exact congrFun hfun_comp x

/-- The explicit circle-to-line Cayley half-density is onto. -/
theorem circleLineCayleyIsometry_surjective :
    Function.Surjective circleLineCayleyIsometry := by
  intro g
  let Uphase : RealLineL2 ≃ₗᵢ[ℂ] RealLineL2 :=
    RHTower.unimodularMulUnitary cayleyHardyPhase
    continuous_cayleyHardyPhase.aestronglyMeasurable norm_cayleyHardyPhase
  let Udensity :
      WeightedL2 (μ := (volume : Measure ℝ)) standardCauchyWeight ≃ₗᵢ[ℂ] RealLineL2 :=
    weightedDensityUnitary (μ := (volume : Measure ℝ)) standardCauchyWeight
      measurable_standardCauchyWeight standardCauchyWeight_pos
  obtain ⟨f, hf⟩ := circleCayleyWeightedPullback_surjective
    (Udensity.symm (Uphase.symm g))
  refine ⟨f, ?_⟩
  change Uphase (Udensity (circleCayleyWeightedPullback f)) = g
  rw [hf]
  rw [Udensity.apply_symm_apply]
  exact Uphase.apply_symm_apply g

/-- Exact full-space Cayley unitary from circle `L²` to line `L²`. -/
def circleLineCayleyUnitary :
    Lp ℂ 2 circleLebesgue ≃ₗᵢ[ℂ] RealLineL2 :=
  LinearIsometryEquiv.ofSurjective circleLineCayleyIsometry
    circleLineCayleyIsometry_surjective

@[simp] theorem circleLineCayleyUnitary_apply (f : Lp ℂ 2 circleLebesgue) :
    circleLineCayleyUnitary f = circleLineCayleyIsometry f := rfl

end

end GaloisForLFunctions.HTGeometry
