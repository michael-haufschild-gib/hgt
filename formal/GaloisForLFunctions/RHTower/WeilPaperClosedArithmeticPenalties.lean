import GaloisForLFunctions.RHTower.WeilPaperArithmeticPenaltyInvariance
import Mathlib.Analysis.Normed.Group.Quotient

/-!
# Closed arithmetic directions in gamma-energy optimization

Real linear combinations and uniform limits of integer logarithmic penalties
remain invisible to every actual observed spectral completion. This closed
submodule gives a complete normed quotient of bounded continuous penalties.
The actual gamma objective and its attained value are constant on its cosets.
-/

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal BoundedContinuousFunction
noncomputable section
namespace RHTower.WeilWorkPBAP
open WeilOneSided

/-- Probability expectation as a continuous real linear functional on bounded penalties. -/
def paperSpectralExpectationCLM (μ : ProbabilityMeasure ℝ) : (ℝ →ᵇ ℝ) →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := fun G => ∫ ξ, G ξ ∂(μ : Measure ℝ)
      map_add' := fun G H => integral_add (G.integrable _) (H.integrable _)
      map_smul' := fun a G => integral_smul a G }
    1 (fun G => by
      change ‖∫ ξ, G ξ ∂(μ : Measure ℝ)‖ ≤ 1 * ‖G‖
      simpa only [one_mul] using G.norm_integral_le_norm (μ : Measure ℝ))

@[simp] theorem paperSpectralExpectationCLM_apply (μ : ProbabilityMeasure ℝ) (G : ℝ →ᵇ ℝ) :
    paperSpectralExpectationCLM μ G = ∫ ξ, G ξ ∂(μ : Measure ℝ) := rfl

/-- The closed real linear span of all finite integer logarithmic penalties. -/
def paperClosedArithmeticPenalties : Submodule ℝ (ℝ →ᵇ ℝ) :=
  (Submodule.span ℝ (Set.range (fun p : Finset LogIndex × (LogIndex → ℂ) =>
    paperArithmeticSpectralPenalty p.1 p.2))).topologicalClosure

instance : IsClosed (paperClosedArithmeticPenalties : Set (ℝ →ᵇ ℝ)) :=
  Submodule.isClosed_topologicalClosure _

/-- Every finite arithmetic penalty belongs to the closed invisible subspace. -/
theorem paperArithmeticSpectralPenalty_mem_closed (s : Finset LogIndex) (a : LogIndex → ℂ) :
    paperArithmeticSpectralPenalty s a ∈ paperClosedArithmeticPenalties :=
  Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨(s, a), rfl⟩)

/-- The closed arithmetic subspace lies in every feasible expectation kernel. -/
theorem paperClosedArithmeticPenalties_le_expectation_ker
    {ι : Type*} (c : ComplexNullMixture) (F : ι → ℝ →ᵇ ℂ)
    (μ : PaperObservedSpectralCompletion c F) :
    paperClosedArithmeticPenalties ≤ (paperSpectralExpectationCLM μ.1).ker := by
  apply Submodule.topologicalClosure_minimal
  · apply Submodule.span_le.mpr
    rintro G ⟨⟨s, a⟩, rfl⟩
    exact integral_paperArithmeticSpectralPenalty_zero c F μ s a
  · exact (paperSpectralExpectationCLM μ.1).isClosed_ker

/-- Uniform limits and real linear combinations preserve zero arithmetic expectation. -/
theorem integral_paperClosedArithmeticPenalty_zero
    {ι : Type*} (c : ComplexNullMixture) (F : ι → ℝ →ᵇ ℂ)
    (μ : PaperObservedSpectralCompletion c F) (P : paperClosedArithmeticPenalties) :
    (∫ ξ, P.1 ξ ∂(μ.1 : Measure ℝ)) = 0 :=
  paperClosedArithmeticPenalties_le_expectation_ker c F μ P.2

/-- The actual gamma objective ignores the entire closed arithmetic subspace. -/
theorem paperPerturbedGammaExpectation_add_closedArithmeticPenalty
    {ι : Type*} (c : ComplexNullMixture) (F : ι → ℝ →ᵇ ℂ)
    (μ : PaperObservedSpectralCompletion c F) (G : ℝ →ᵇ ℝ)
    (P : paperClosedArithmeticPenalties) :
    paperPerturbedGammaExpectation (G + P.1) μ.1 = paperPerturbedGammaExpectation G μ.1 := by
  rw [paperPerturbedGammaExpectation_add, integral_paperClosedArithmeticPenalty_zero c F μ P,
    add_zero]

/-- The attained value is unchanged by every closed arithmetic direction. -/
theorem paperObservedGammaValue_add_closedArithmeticPenalty
    {ι : Type*} (c : ComplexNullMixture) (F : ι → ℝ →ᵇ ℂ) (G : ℝ →ᵇ ℝ)
    (P : paperClosedArithmeticPenalties) :
    paperObservedGammaValue c F (G + P.1) = paperObservedGammaValue c F G := by
  apply le_antisymm
  · calc
      _ ≤ paperPerturbedGammaExpectation (G + P.1) (paperObservedGammaMinimizer c F G).1 :=
        paperObservedGammaValue_le c F _ _
      _ = _ := paperPerturbedGammaExpectation_add_closedArithmeticPenalty c F _ G P
  · have h := paperObservedGammaValue_le c F G (paperObservedGammaMinimizer c F (G + P.1))
    have he : paperObservedGammaValue c F (G + P.1) =
        paperPerturbedGammaExpectation G (paperObservedGammaMinimizer c F (G + P.1)).1 :=
      paperPerturbedGammaExpectation_add_closedArithmeticPenalty c F _ G P
    exact h.trans_eq he.symm

/-- Removing closed arithmetic directions yields a real Banach space of spectral penalties. -/
abbrev PaperArithmeticPenaltyQuotient := (ℝ →ᵇ ℝ) ⧸ paperClosedArithmeticPenalties

/-- The canonical linear projection to effective penalty classes. -/
def paperArithmeticPenaltyClass : (ℝ →ᵇ ℝ) →ₗ[ℝ] PaperArithmeticPenaltyQuotient :=
  paperClosedArithmeticPenalties.mkQ

/-- Cosets are exactly differences in the closed arithmetic span. -/
theorem paperArithmeticPenaltyClass_eq_iff (G H : ℝ →ᵇ ℝ) :
    paperArithmeticPenaltyClass G = paperArithmeticPenaltyClass H ↔
      G - H ∈ paperClosedArithmeticPenalties :=
  Submodule.Quotient.eq _

/-- Every feasible objective is a well-defined function of the penalty class. -/
theorem paperPerturbedGammaExpectation_eq_of_class_eq
    {ι : Type*} (c : ComplexNullMixture) (F : ι → ℝ →ᵇ ℂ)
    (μ : PaperObservedSpectralCompletion c F) (G H : ℝ →ᵇ ℝ)
    (h : paperArithmeticPenaltyClass G = paperArithmeticPenaltyClass H) :
    paperPerturbedGammaExpectation G μ.1 = paperPerturbedGammaExpectation H μ.1 := by
  have hz := integral_paperClosedArithmeticPenalty_zero c F μ
    ⟨G - H, (paperArithmeticPenaltyClass_eq_iff G H).mp h⟩
  have hd := paperPerturbedGammaExpectation_sub μ.1 G H
  dsimp only at hz
  linarith

/-- Equal penalty classes have equal attained gamma values. -/
theorem paperObservedGammaValue_eq_of_class_eq
    {ι : Type*} (c : ComplexNullMixture) (F : ι → ℝ →ᵇ ℂ) (G H : ℝ →ᵇ ℝ)
    (h : paperArithmeticPenaltyClass G = paperArithmeticPenaltyClass H) :
    paperObservedGammaValue c F G = paperObservedGammaValue c F H := by
  have he := paperObservedGammaValue_add_closedArithmeticPenalty c F H
    ⟨G - H, (paperArithmeticPenaltyClass_eq_iff G H).mp h⟩
  have hadd : H + (G - H) = G := by abel
  change paperObservedGammaValue c F (H + (G - H)) = paperObservedGammaValue c F H at he
  rw [hadd] at he
  exact he

end RHTower.WeilWorkPBAP
