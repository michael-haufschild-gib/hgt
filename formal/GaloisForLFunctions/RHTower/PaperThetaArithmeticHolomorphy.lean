import GaloisForLFunctions.RHTower.PaperThetaUniformCutControl
import GaloisForLFunctions.RHTower.CHMDComplexJumpGraph
import GaloisForLFunctions.RHTower.ThetaBVArithmeticAdmission
import GaloisForLFunctions.RHTower.AnalyticDominatedL2Derivatives
import Mathlib.Analysis.Complex.TaylorSeries

/-! # Entire theta families in the complete arithmetic graph

The literal cut modes, with both native tails and their actual jump, are
entire in the full mass-and-edge graph norm. Every graph derivative is the
class of the corresponding literal parameter jet. Consequently their
Taylor series converge in that complete arithmetic norm, at every center
and every complex parameter, with all prime powers retained.
-/

noncomputable section
open MeasureTheory Set Filter Topology Complex Metric

namespace RHTower.PaperThetaEndpoint
open CHMDDoobGraph DominatedL2Sections GaloisForLFunctions.HTGeometry

/-- The original complete source and edge measures, now with complex coefficients. -/
abbrev ComplexArithmeticGraph := CHMDComplexJump.graph massMeasure edgeMeasure left right
  nonsingular_left nonsingular_right

def cutMassFamily (a : ℝ) : Family massMeasure where
  domain := univ
  isOpen_domain := isOpen_univ
  value z x := cutQuotient z a x
  measurable z _ := (measurable_cutQuotient z a).aestronglyMeasurable
  holomorphic x := (differentiable_cutQuotient_parameter a x).differentiableOn
  local_bound z _ := by
    refine ⟨1, one_pos, subset_univ _, (fun _ => cutControlSize z a + 1), memLp_const _, ?_⟩
    exact fun x w hw => cutQuotient_norm_ball z a x hw

def cutEdgeFamily (a : ℝ) : Family edgeMeasure where
  domain := univ
  isOpen_domain := isOpen_univ
  value z e := cutQuotient z a (left e) - cutQuotient z a (right e)
  measurable z _ := by
    exact (((measurable_cutQuotient z a).comp measurable_snd).sub
      ((measurable_cutQuotient z a).comp (measurable_snd.add measurable_fst))).aestronglyMeasurable
  holomorphic e := ((differentiable_cutQuotient_parameter a (left e)).sub
    (differentiable_cutQuotient_parameter a (right e))).differentiableOn
  local_bound z _ := by
    refine ⟨1, one_pos, subset_univ _,
      (fun e => |cutVariationControl z a (left e) - cutVariationControl z a (right e)|), ?_, ?_⟩
    · simpa only [difference, Real.norm_eq_abs] using
        (bv_memLp_difference (boundedVariationOn_cutVariationControl z a)).norm
    · exact fun e w hw => cutQuotient_difference_ball z a (left e) (right e) hw

/-- Actual source admission is proved, rather than supplied as a premise. -/
def cutArithmeticSection (a : ℝ) (z : ℂ) : ComplexArithmeticGraph := by
  refine ⟨WithLp.toLp 2 ((cutMassFamily a).section z, (cutEdgeFamily a).section z), ?_⟩
  filter_upwards [(cutEdgeFamily a).section_coe (mem_univ z),
    nonsingular_left.ae ((cutMassFamily a).section_coe (mem_univ z)),
    nonsingular_right.ae ((cutMassFamily a).section_coe (mem_univ z))] with e he hl hr
  change (cutEdgeFamily a).section z e =
    (cutMassFamily a).section z (left e) - (cutMassFamily a).section z (right e)
  rw [he, hl, hr]
  rfl

theorem cutArithmeticSection_source (a : ℝ) (z : ℂ) :
    ((cutArithmeticSection a z).val.fst : ℝ → ℂ) =ᵐ[massMeasure] cutQuotient z a :=
  (cutMassFamily a).section_coe (mem_univ z)

theorem cutArithmeticSection_edge (a : ℝ) (z : ℂ) :
    ((cutArithmeticSection a z).val.snd : ℝ × ℝ → ℂ) =ᵐ[edgeMeasure]
      (fun e => cutQuotient z a (left e) - cutQuotient z a (right e)) :=
  (cutEdgeFamily a).section_coe (mem_univ z)

/-- Strong holomorphy in the genuine complete arithmetic graph, including the cut. -/
theorem differentiable_cutArithmeticSection (a : ℝ) :
    Differentiable ℂ (cutArithmeticSection a) := by
  intro z
  apply CHMDComplexJump.differentiableAt_of_coe
  exact ((WithLp.prodContinuousLinearEquiv 2 ℂ
    (Lp ℂ 2 massMeasure) (Lp ℂ 2 edgeMeasure)).symm.hasFDerivAt.comp_hasDerivAt z
      (((cutMassFamily a).hasDerivAt_section (mem_univ z)).prodMk
        ((cutEdgeFamily a).hasDerivAt_section (mem_univ z)))).differentiableAt

/-- Every strong graph jet has the literal theta jet as its source representative. -/
theorem cutArithmeticSection_jet_source (n : ℕ) (a : ℝ) (z : ℂ) :
    ((iteratedDeriv n (cutArithmeticSection a) z).val.fst : ℝ → ℂ) =ᵐ[massMeasure]
      cutParameterJet n z a := by
  have he := iteratedDeriv_clm_comp_eqOn isOpen_univ
    (CHMDComplexJump.sourceMap massMeasure edgeMeasure left right
      nonsingular_left nonsingular_right)
    (differentiable_cutArithmeticSection a).differentiableOn n (mem_univ z)
  change iteratedDeriv n (cutMassFamily a).section z =
    (iteratedDeriv n (cutArithmeticSection a) z).val.fst at he
  rw [← he]
  exact (cutMassFamily a).coe_iteratedDeriv_section n (mem_univ z)

/-- Every strong graph jet retains its literal full edge difference. -/
theorem cutArithmeticSection_jet_edge (n : ℕ) (a : ℝ) (z : ℂ) :
    ((iteratedDeriv n (cutArithmeticSection a) z).val.snd : ℝ × ℝ → ℂ) =ᵐ[edgeMeasure]
      (fun e => cutParameterJet n z a (left e) - cutParameterJet n z a (right e)) := by
  filter_upwards [(iteratedDeriv n (cutArithmeticSection a) z).property,
    nonsingular_left.ae (cutArithmeticSection_jet_source n a z),
    nonsingular_right.ae (cutArithmeticSection_jet_source n a z)] with e he hl hr
  exact he.trans (congrArg₂ (· - ·) hl hr)

/-- Entire Taylor synthesis is admitted in the full arithmetic graph norm. -/
theorem hasSum_cutArithmeticSection_taylor (a : ℝ) (c z : ℂ) :
    HasSum (fun n : ℕ => (n.factorial : ℂ)⁻¹ • (z-c)^n •
      iteratedDeriv n (cutArithmeticSection a) c) (cutArithmeticSection a z) :=
  Complex.hasSum_taylorSeries_of_entire (differentiable_cutArithmeticSection a) c z

end RHTower.PaperThetaEndpoint
