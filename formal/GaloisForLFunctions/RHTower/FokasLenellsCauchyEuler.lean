import GaloisForLFunctions.RHTower.FokasLenellsCauchyLinfty
import GaloisForLFunctions.RHTower.LiteralEulerHalfDensityContractionNoGo

/-!
# Cauchy compression of the existing finite Euler operators

The Cauchy projection mechanism from the Fokas--Lenells paper preserves the
literal Euler operator's exact finite-product norm. Thus projection alone
does not produce bounded completion. Dividing by the exact budget does
produce a family whose norm is exactly one.
-/

open MeasureTheory Filter Topology
open scoped ENNReal
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.RHTower
namespace RHTower.FokasLenells
noncomputable section

private def eulerLinfty (N : ℕ) : Lp ℂ ∞ (volume : Measure ℝ) :=
  (memLp_top_of_bound (literalEulerHalfDensitySymbol_continuous N).aestronglyMeasurable
    (literalEulerHalfDensityBudget N) (.of_forall (norm_literalEulerHalfDensitySymbol_le N))).toLp _

private theorem euler_eq_linfty (N : ℕ) :
    literalEulerHalfDensityOperator N = lineLinftyMultiplier (eulerLinfty N) := by
  apply ContinuousLinearMap.ext
  intro u
  apply Lp.ext
  filter_upwards [lpBoundedMulCLM_coeFn (p := 2) (μ := (volume : Measure ℝ))
    (literalEulerHalfDensitySymbol_continuous N).measurable
    (literalEulerHalfDensityBudget_nonneg N) (norm_literalEulerHalfDensitySymbol_le N) u,
    lineLinftyMultiplier_ae (eulerLinfty N) u,
    (memLp_top_of_bound (literalEulerHalfDensitySymbol_continuous N).aestronglyMeasurable
      (literalEulerHalfDensityBudget N) (.of_forall (norm_literalEulerHalfDensitySymbol_le N))).coeFn_toLp]
    with z h0 h1 h2
  change literalEulerHalfDensityOperator N u z = literalEulerHalfDensitySymbol N z * u z at h0
  change eulerLinfty N z = literalEulerHalfDensitySymbol N z at h2
  rw [h0, h1, h2]

/-- The paper's signed Cauchy projection applied to the existing literal Euler operator. -/
def cauchyEulerFamily (N : ℕ) : SoninL2 →L[ℂ] SoninL2 :=
  negativeCauchy.comp (literalEulerHalfDensityOperator N)

/-- Exact finite-product norm survives Cauchy compression. -/
theorem norm_cauchyEulerFamily (N : ℕ) :
    ‖cauchyEulerFamily N‖ = literalEulerHalfDensityBudget N := by
  have he : ‖eulerLinfty N‖ = literalEulerHalfDensityBudget N := by
    rw [← norm_lineLinftyMultiplier, ← euler_eq_linfty, norm_literalEulerHalfDensityOperator]
  change ‖negativeCauchy.comp (literalEulerHalfDensityOperator N)‖ = _
  rw [euler_eq_linfty, norm_negativeCauchy_comp_lineLinftyMultiplier, he]

/-- Projection preserves the existing divergence of the finite Euler budgets. -/
theorem tendsto_norm_cauchyEulerFamily_atTop :
    Tendsto (fun N => ‖cauchyEulerFamily N‖) atTop atTop := by
  simpa only [norm_cauchyEulerFamily] using tendsto_literalEulerHalfDensityBudget_atTop

/-- At least one actual L2 vector sees unbounded compressed Euler outputs. -/
theorem cauchyEulerFamily_unbounded_vector :
    ∃ u : SoninL2, ∀ C : ℝ, ∃ N : ℕ, C < ‖cauchyEulerFamily N u‖ := by
  by_contra hn
  push Not at hn
  obtain ⟨C, hC⟩ := banach_steinhaus hn
  obtain ⟨N, hN⟩ := (tendsto_norm_cauchyEulerFamily_atTop.eventually (eventually_gt_atTop C)).exists
  exact hN.not_ge (hC N)

/-- No bounded operator is a strong limit of the actual compressed Euler family. -/
theorem cauchyEulerFamily_no_strong_bounded_completion :
    ¬ ∃ T : SoninL2 →L[ℂ] SoninL2,
      ∀ u, Tendsto (fun N => cauchyEulerFamily N u) atTop (𝓝 (T u)) := by
  rintro ⟨T, hT⟩
  obtain ⟨u, hu⟩ := cauchyEulerFamily_unbounded_vector
  obtain ⟨C, hC⟩ := (hT u).norm.bddAbove_range
  obtain ⟨N, hN⟩ := hu C
  exact hN.not_ge (hC ⟨N, rfl⟩)

private theorem euler_budget_pos (N : ℕ) : 0 < literalEulerHalfDensityBudget N := by
  unfold literalEulerHalfDensityBudget
  apply Finset.prod_pos
  intro p hp
  linarith [literalEulerHalfDensityWeight_pos (p : Nat.Primes)]

/-- Normalization by the exact budget, with no smallness assumption on the original family. -/
def normalizedCauchyEulerFamily (N : ℕ) : SoninL2 →L[ℂ] SoninL2 :=
  ((literalEulerHalfDensityBudget N)⁻¹ : ℂ) • cauchyEulerFamily N

/-- The positive replacement is sharp: every normalized compressed Euler operator has norm one. -/
theorem norm_normalizedCauchyEulerFamily (N : ℕ) : ‖normalizedCauchyEulerFamily N‖ = 1 := by
  rw [normalizedCauchyEulerFamily, norm_smul, norm_cauchyEulerFamily,
    norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (euler_budget_pos N)]
  exact inv_mul_cancel₀ (euler_budget_pos N).ne'

/-- The normalized family is contractive on every actual L2 vector. -/
theorem normalizedCauchyEulerFamily_bound (N : ℕ) (u : SoninL2) :
    ‖normalizedCauchyEulerFamily N u‖ ≤ ‖u‖ := by
  simpa only [norm_normalizedCauchyEulerFamily, one_mul] using
    (normalizedCauchyEulerFamily N).le_opNorm u

end
end RHTower.FokasLenells
