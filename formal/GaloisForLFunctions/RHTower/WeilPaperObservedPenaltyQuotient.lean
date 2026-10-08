import GaloisForLFunctions.RHTower.WeilPaperGammaValueStability
import Mathlib.Topology.ContinuousMap.Bounded.Normed

/-!
# Exact observation directions in the gamma variational problem

Every finite complex combination of prescribed observations has fixed real
expectation throughout the actual observed completion. Adding its real part
therefore shifts the attained value exactly and preserves all minimizers.
The uniform perturbation bound improves after subtracting any such direction.
-/

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal BoundedContinuousFunction
noncomputable section
namespace RHTower.WeilWorkPBAP

variable {ι : Type*}

/-- Real part of a finite complex linear combination of bounded spectral observables. -/
def paperFiniteSpectralPenalty (F : ι → ℝ →ᵇ ℂ) (s : Finset ι) (a : ι → ℂ) : ℝ →ᵇ ℝ :=
  Complex.reCLM.compLeftContinuousBounded ℝ (∑ i ∈ s, a i • F i)

theorem paperFiniteSpectralPenalty_apply
    (F : ι → ℝ →ᵇ ℂ) (s : Finset ι) (a : ι → ℂ) (ξ : ℝ) :
    paperFiniteSpectralPenalty F s a ξ = (∑ i ∈ s, a i * F i ξ).re := by
  change ((BoundedContinuousFunction.evalCLM ℂ ξ) (∑ i ∈ s, a i • F i)).re = _
  rw [map_sum]
  congr 1

/-- The exact expectation formula holds for every real probability law. -/
theorem integral_paperFiniteSpectralPenalty (μ : ProbabilityMeasure ℝ)
    (F : ι → ℝ →ᵇ ℂ) (s : Finset ι) (a : ι → ℂ) :
    (∫ ξ, paperFiniteSpectralPenalty F s a ξ ∂(μ : Measure ℝ)) =
      (∑ i ∈ s, a i * ∫ ξ, F i ξ ∂(μ : Measure ℝ)).re := by
  let U : ℝ →ᵇ ℂ := ∑ i ∈ s, a i • F i
  have he (ξ : ℝ) : U ξ = ∑ i ∈ s, a i * F i ξ := by
    change (BoundedContinuousFunction.evalCLM ℂ ξ) (∑ i ∈ s, a i • F i) = _
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rfl
  change (∫ ξ, (U ξ).re ∂(μ : Measure ℝ)) = _
  have hr : (∫ ξ, (U ξ).re ∂(μ : Measure ℝ)) =
      (∫ ξ, U ξ ∂(μ : Measure ℝ)).re :=
    Complex.reCLM.integral_comp_comm (U.integrable (μ : Measure ℝ))
  rw [hr]
  congr 1
  simp_rw [he]
  rw [integral_finsetSum s (fun i _ => ((F i).integrable (μ : Measure ℝ)).const_mul (a i))]
  apply Finset.sum_congr rfl
  intro i _
  exact integral_const_mul (a i) _

/-- The known scalar expectation of an observation-generated penalty. -/
def paperObservedPenaltyShift (c : ComplexNullMixture) (F : ι → ℝ →ᵇ ℂ)
    (s : Finset ι) (a : ι → ℂ) : ℝ :=
  (∑ i ∈ s, a i * ∫ ξ, F i ξ ∂(spectralProbability c.1 : Measure ℝ)).re

/-- Every completed feasible law has exactly the prescribed finite penalty expectation. -/
theorem integral_paperFiniteSpectralPenalty_observed
    (c : ComplexNullMixture) (F : ι → ℝ →ᵇ ℂ)
    (μ : PaperObservedSpectralCompletion c F) (s : Finset ι) (a : ι → ℂ) :
    (∫ ξ, paperFiniteSpectralPenalty F s a ξ ∂(μ.1 : Measure ℝ)) =
      paperObservedPenaltyShift c F s a := by
  rw [integral_paperFiniteSpectralPenalty]
  unfold paperObservedPenaltyShift
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [paperObservedSpectralCompletion_observation c F μ i]

/-- Adding a bounded penalty adds its actual expectation to the objective. -/
theorem paperPerturbedGammaExpectation_add (μ : ProbabilityMeasure ℝ) (G H : ℝ →ᵇ ℝ) :
    paperPerturbedGammaExpectation (G + H) μ =
      paperPerturbedGammaExpectation G μ + ∫ ξ, H ξ ∂(μ : Measure ℝ) := by
  unfold paperPerturbedGammaExpectation
  change (∫ ξ, paperSpectralGammaWeight ξ ∂(μ : Measure ℝ)) +
    (∫ ξ, G ξ + H ξ ∂(μ : Measure ℝ)) = _
  rw [integral_add (G.integrable _) (H.integrable _)]
  ring

/-- Observation-generated penalties shift every feasible objective by one fixed scalar. -/
theorem paperPerturbedGammaExpectation_add_observedPenalty
    (c : ComplexNullMixture) (F : ι → ℝ →ᵇ ℂ)
    (μ : PaperObservedSpectralCompletion c F) (G : ℝ →ᵇ ℝ) (s : Finset ι) (a : ι → ℂ) :
    paperPerturbedGammaExpectation (G + paperFiniteSpectralPenalty F s a) μ.1 =
      paperPerturbedGammaExpectation G μ.1 + paperObservedPenaltyShift c F s a := by
  rw [paperPerturbedGammaExpectation_add, integral_paperFiniteSpectralPenalty_observed c F μ]

/-- The variational value transforms exactly along every finite prescribed-observation direction. -/
theorem paperObservedGammaValue_add_observedPenalty
    (c : ComplexNullMixture) (F : ι → ℝ →ᵇ ℂ) (G : ℝ →ᵇ ℝ) (s : Finset ι) (a : ι → ℂ) :
    paperObservedGammaValue c F (G + paperFiniteSpectralPenalty F s a) =
      paperObservedGammaValue c F G + paperObservedPenaltyShift c F s a := by
  apply le_antisymm
  · calc
      _ ≤ paperPerturbedGammaExpectation (G + paperFiniteSpectralPenalty F s a)
          (paperObservedGammaMinimizer c F G).1 := paperObservedGammaValue_le c F _ _
      _ = _ := paperPerturbedGammaExpectation_add_observedPenalty c F _ G s a
  · have h := paperObservedGammaValue_le c F G
      (paperObservedGammaMinimizer c F (G + paperFiniteSpectralPenalty F s a))
    have he : paperObservedGammaValue c F (G + paperFiniteSpectralPenalty F s a) =
        paperPerturbedGammaExpectation G
          (paperObservedGammaMinimizer c F (G + paperFiniteSpectralPenalty F s a)).1 +
            paperObservedPenaltyShift c F s a :=
      paperPerturbedGammaExpectation_add_observedPenalty c F _ G s a
    linarith

/-- Every pairwise objective comparison is unchanged along prescribed-observation directions. -/
theorem paperObservedGammaPenalty_order_iff
    (c : ComplexNullMixture) (F : ι → ℝ →ᵇ ℂ)
    (μ ν : PaperObservedSpectralCompletion c F) (G : ℝ →ᵇ ℝ) (s : Finset ι) (a : ι → ℂ) :
    paperPerturbedGammaExpectation (G + paperFiniteSpectralPenalty F s a) μ.1 ≤
        paperPerturbedGammaExpectation (G + paperFiniteSpectralPenalty F s a) ν.1 ↔
      paperPerturbedGammaExpectation G μ.1 ≤ paperPerturbedGammaExpectation G ν.1 := by
  rw [paperPerturbedGammaExpectation_add_observedPenalty c F μ,
    paperPerturbedGammaExpectation_add_observedPenalty c F ν]
  exact add_le_add_iff_right _

/-- Every chosen optimizer remains optimal after adding any prescribed-observation penalty. -/
theorem paperObservedGammaMinimizer_add_observedPenalty
    (c : ComplexNullMixture) (F : ι → ℝ →ᵇ ℂ) (G : ℝ →ᵇ ℝ) (s : Finset ι) (a : ι → ℂ)
    (μ : PaperObservedSpectralCompletion c F) :
    paperPerturbedGammaExpectation (G + paperFiniteSpectralPenalty F s a)
        (paperObservedGammaMinimizer c F G).1 ≤
      paperPerturbedGammaExpectation (G + paperFiniteSpectralPenalty F s a) μ.1 :=
  (paperObservedGammaPenalty_order_iff c F _ μ G s a).mpr (paperObservedGammaValue_le c F G μ)

/-- Stability improves after removing any known observation direction from the penalty difference. -/
theorem paperObservedGammaValue_observation_quotient_bound
    (c : ComplexNullMixture) (F : ι → ℝ →ᵇ ℂ) (G H : ℝ →ᵇ ℝ) (s : Finset ι) (a : ι → ℂ) :
    |paperObservedGammaValue c F G - paperObservedGammaValue c F H -
        paperObservedPenaltyShift c F s a| ≤ ‖G - H - paperFiniteSpectralPenalty F s a‖ := by
  have h := abs_paperObservedGammaValue_sub_le c F G (H + paperFiniteSpectralPenalty F s a)
  rw [paperObservedGammaValue_add_observedPenalty] at h
  calc
    _ = |paperObservedGammaValue c F G -
        (paperObservedGammaValue c F H + paperObservedPenaltyShift c F s a)| :=
      congrArg abs (by ring)
    _ ≤ ‖G - (H + paperFiniteSpectralPenalty F s a)‖ := h
    _ = _ := congrArg norm (by abel)

end RHTower.WeilWorkPBAP
