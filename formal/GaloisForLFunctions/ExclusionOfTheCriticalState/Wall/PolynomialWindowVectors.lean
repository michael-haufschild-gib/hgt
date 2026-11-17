import GaloisForLFunctions.ExclusionOfTheCriticalState.Wall.PolynomialTailFilters
import Mathlib.Analysis.Normed.Group.Bounded

/-!
# Square-integrable polynomial windows

Bounded interval indicators give actual L² vectors. Disjoint windows have zero cross products.
-/

open MeasureTheory Set Polynomial
noncomputable section
namespace GaloisForLFunctions.ExclusionOfTheCriticalState

/-- A polynomial-coordinate test restricted to one bounded interval. -/
def polynomialWindow (a b : ℝ) (P : ℝ[X]) : ℝ → ℝ :=
  (Ico a b).indicator (fun u => P.eval (Real.exp (u - b)))

/-- Bounded polynomial windows belong to every finite-measure square-integrable space. -/
theorem memLp_polynomialWindow (μ : Measure ℝ) [IsFiniteMeasure μ]
    (a b : ℝ) (P : ℝ[X]) : MemLp (polynomialWindow a b P) 2 μ := by
  have hc : Continuous (fun u : ℝ => P.eval (Real.exp (u - b))) :=
    P.continuous.comp (by fun_prop)
  obtain ⟨C, hC⟩ := (isCompact_Icc : IsCompact (Icc a b)).exists_bound_of_continuousOn hc.continuousOn
  apply MemLp.of_bound (hc.measurable.indicator measurableSet_Ico).aestronglyMeasurable (max C 0)
  filter_upwards [] with u
  by_cases hu : u ∈ Ico a b
  · rw [Set.indicator_of_mem hu]
    exact (hC u ⟨hu.1, hu.2.le⟩).trans (le_max_left _ _)
  · rw [Set.indicator_of_notMem hu, norm_zero]
    exact le_max_right _ _

/-- The actual square-integrable vector of a bounded polynomial window. -/
def polynomialWindowLp (μ : Measure ℝ) [IsFiniteMeasure μ]
    (a b : ℝ) (P : ℝ[X]) : Lp ℝ 2 μ :=
  (memLp_polynomialWindow μ a b P).toLp (polynomialWindow a b P)

theorem polynomialWindowLp_ae (μ : Measure ℝ) [IsFiniteMeasure μ]
    (a b : ℝ) (P : ℝ[X]) :
    polynomialWindowLp μ a b P =ᵐ[μ] polynomialWindow a b P :=
  (memLp_polynomialWindow μ a b P).coeFn_toLp

/-- Disjoint windows have identically vanishing cross products. -/
theorem polynomialWindow_mul_eq_zero {a b c d : ℝ} (P Q : ℝ[X])
    (h : Disjoint (Ico a b) (Ico c d)) (u : ℝ) :
    polynomialWindow a b P u * polynomialWindow c d Q u = 0 := by
  simp only [polynomialWindow]
  by_cases hu : u ∈ Ico a b
  · have hv : u ∉ Ico c d := fun hv => Set.disjoint_left.mp h hu hv
    rw [Set.indicator_of_notMem hv, mul_zero]
  · rw [Set.indicator_of_notMem hu, zero_mul]

/-- The same disjointness holds for their actual square-integrable representatives. -/
theorem polynomialWindowLp_disjoint (μ : Measure ℝ) [IsFiniteMeasure μ]
    {a b c d : ℝ} (P Q : ℝ[X]) (h : Disjoint (Ico a b) (Ico c d)) :
    ∀ᵐ u ∂μ, polynomialWindowLp μ a b P u * polynomialWindowLp μ c d Q u = 0 := by
  filter_upwards [polynomialWindowLp_ae μ a b P, polynomialWindowLp_ae μ c d Q] with u hu hv
  rw [hu, hv]
  exact polynomialWindow_mul_eq_zero P Q h u

#print axioms polynomialWindowLp_disjoint
end GaloisForLFunctions.ExclusionOfTheCriticalState
