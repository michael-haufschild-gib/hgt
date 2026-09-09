import GaloisForLFunctions.HTGeometry.FokasLenellsCutoffPhaseLimit
import GaloisForLFunctions.RHTower.FokasLenellsCauchyPhaseDistance

/-!
# Sharp cutoff stability survives the actual Cauchy projection

The paper's signed Cauchy compression preserves all cutoff-evolution
operator distances and the exact time-generator norm. It therefore preserves
the optimal stability constant and its divergence when the cutoff is removed.
-/

open MeasureTheory Filter Topology
open GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.HTGeometry.FokasLenells
namespace RHTower.FokasLenells
noncomputable section

/-- Actual signed Cauchy compression of the unitary cutoff evolution. -/
def cutoffCauchyEvolution (a t : ℝ) : SoninL2 →L[ℂ] SoninL2 :=
  negativeCauchy.comp (cutoffEvolution a t)

/-- Actual bounded time generator after signed Cauchy compression. -/
def cutoffCauchyTimeOperator (a t : ℝ) : SoninL2 →L[ℂ] SoninL2 :=
  negativeCauchy.comp (cutoffEvolutionTimeOperator a t)

/-- The cutoff Cauchy family is the existing L-infinity Cauchy representation. -/
theorem cutoffCauchyEvolution_eq_cauchyLinfty (a t : ℝ) :
    cutoffCauchyEvolution a t = cauchyLinftyMultiplier (cutoffPhaseLinfty a t) := by
  rw [cutoffCauchyEvolution,cutoffEvolution_eq_lineLinftyMultiplier,cauchyLinftyMultiplier_apply]

/-- Cauchy compression preserves the complete cutoff operator norm. -/
theorem norm_cutoffCauchyEvolution_eq_uncompressed (a t : ℝ) :
    ‖cutoffCauchyEvolution a t‖ = ‖cutoffEvolution a t‖ := by
  rw [cutoffCauchyEvolution_eq_cauchyLinfty,cutoffEvolution_eq_lineLinftyMultiplier,
    norm_cauchyLinftyMultiplier,norm_lineLinftyMultiplier]

/-- Cauchy compression preserves distances across arbitrary times and cutoff widths. -/
theorem norm_cutoffCauchyEvolution_sub_eq_uncompressed (a b s t : ℝ) :
    ‖cutoffCauchyEvolution a s - cutoffCauchyEvolution b t‖ =
      ‖cutoffEvolution a s - cutoffEvolution b t‖ := by
  rw [cutoffCauchyEvolution_eq_cauchyLinfty,cutoffCauchyEvolution_eq_cauchyLinfty,
    cutoffEvolution_eq_lineLinftyMultiplier,cutoffEvolution_eq_lineLinftyMultiplier,
    ← map_sub,← map_sub,norm_cauchyLinftyMultiplier,norm_lineLinftyMultiplier]

/-- The signed Cauchy projection preserves the exact cutoff time-generator norm. -/
theorem norm_cutoffCauchyTimeOperator (a t : ℝ) :
    ‖cutoffCauchyTimeOperator a t‖ = cutoffPhaseBudget a := by
  change ‖negativeCauchy.comp (lineLinftyMultiplier (cutoffPhaseTimeLinfty a t))‖ = _
  rw [norm_negativeCauchy_comp_lineLinftyMultiplier,norm_cutoffPhaseTimeLinfty]

/-- Every actual Cauchy-compressed vector orbit has its concrete strong time derivative. -/
theorem cutoffCauchyEvolution_hasDerivAt (a t : ℝ) (u : SoninL2) :
    HasDerivAt (fun s => cutoffCauchyEvolution a s u) (cutoffCauchyTimeOperator a t u) t :=
  (negativeCauchy.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t (cutoffEvolution_hasDerivAt a t u)

/-- The optimal global time Lipschitz constant is unchanged by Cauchy compression. -/
theorem cutoffCauchyEvolution_lipschitz_iff (a L : ℝ) :
    (∀ s t, ‖cutoffCauchyEvolution a s - cutoffCauchyEvolution a t‖ ≤ L * ‖s-t‖) ↔
      cutoffPhaseBudget a ≤ L := by
  simp_rw [norm_cutoffCauchyEvolution_sub_eq_uncompressed]
  exact cutoffEvolution_lipschitz_iff a L

/-- The Cauchy family attains its best global time Lipschitz constant. -/
theorem norm_cutoffCauchyEvolution_sub_le (a s t : ℝ) :
    ‖cutoffCauchyEvolution a s - cutoffCauchyEvolution a t‖ ≤ cutoffPhaseBudget a * ‖s-t‖ :=
  (cutoffCauchyEvolution_lipschitz_iff a (cutoffPhaseBudget a)).2 le_rfl s t

/-- Shrinking the cutoff recovers the raw Cauchy evolution strongly on each actual vector. -/
theorem cutoffCauchyEvolution_tendsto_atBot (t : ℝ) (u : SoninL2) :
    Tendsto (fun a => cutoffCauchyEvolution a t u) atBot (𝓝 (cauchyEvolution t u)) :=
  negativeCauchy.continuous.continuousAt.tendsto.comp (cutoffEvolution_tendsto_atBot t u)

/-- No finite time Lipschitz bound survives uniformly across all compressed cutoff widths. -/
theorem cutoffCauchyEvolution_no_uniform_lipschitz_constant (L : ℝ) :
    ¬ ∀ a s t : ℝ, ‖cutoffCauchyEvolution a s - cutoffCauchyEvolution a t‖ ≤ L * ‖s-t‖ := by
  simpa only [norm_cutoffCauchyEvolution_sub_eq_uncompressed] using
    cutoffEvolution_no_uniform_lipschitz_constant L

end
end RHTower.FokasLenells
