import GaloisForLFunctions.RHTower.FokasLenellsCauchyLinfty

/-!
# Sharp Cauchy norm laws for the existing Schwartz multipliers

The quantized-calculus multiplier and the resolvent's small multiplier are
identified with the same L-infinity representation. Cauchy compression
preserves their exact norm and detects the full Schwartz symbol.
-/

open MeasureTheory
open scoped ENNReal
open GaloisForLFunctions.HTGeometry
namespace RHTower.FokasLenells
noncomputable section

/-- The existing Schwartz multiplier is exactly Holder multiplication by its L-infinity class. -/
theorem ccmSchwartzMultiplier_eq_lineLinftyMultiplier (f : SchwartzMap ℝ ℂ) :
    ccmSchwartzMultiplier f = lineLinftyMultiplier (f.toLp ∞ volume) := by
  apply ContinuousLinearMap.ext
  intro u
  apply Lp.ext
  filter_upwards [ccmSchwartzMultiplier_coeFn f u,
    lineLinftyMultiplier_ae (f.toLp ∞ volume) u, f.coeFn_toLp ∞ volume] with z h0 h1 h2
  rw [h0, h1, h2]

/-- Exact norm of the quantized-calculus Schwartz multiplier. -/
theorem norm_ccmSchwartzMultiplier_eq_linfty (f : SchwartzMap ℝ ℂ) :
    ‖ccmSchwartzMultiplier f‖ = ‖f.toLp ∞ volume‖ := by
  rw [ccmSchwartzMultiplier_eq_lineLinftyMultiplier, norm_lineLinftyMultiplier]

/-- Its signed Cauchy compression has the same exact norm. -/
theorem norm_negativeCauchy_comp_ccmSchwartzMultiplier (f : SchwartzMap ℝ ℂ) :
    ‖negativeCauchy.comp (ccmSchwartzMultiplier f)‖ = ‖ccmSchwartzMultiplier f‖ := by
  rw [ccmSchwartzMultiplier_eq_lineLinftyMultiplier,
    norm_negativeCauchy_comp_lineLinftyMultiplier, norm_lineLinftyMultiplier]

/-- The Cauchy operator retains every Schwartz symbol, pointwise rather than merely almost everywhere. -/
theorem negativeCauchy_comp_ccmSchwartzMultiplier_injective :
    Function.Injective (fun f : SchwartzMap ℝ ℂ => negativeCauchy.comp (ccmSchwartzMultiplier f)) := by
  intro f g h
  change negativeCauchy.comp (ccmSchwartzMultiplier f) =
    negativeCauchy.comp (ccmSchwartzMultiplier g) at h
  rw [ccmSchwartzMultiplier_eq_lineLinftyMultiplier,
    ccmSchwartzMultiplier_eq_lineLinftyMultiplier] at h
  exact SchwartzMap.injective_toLp ∞ volume (cauchyLinftyMultiplier_injective h)

/-- The compressed distance is the exact essential-supremum distance between the existing symbols. -/
theorem dist_negativeCauchy_comp_ccmSchwartzMultiplier (f g : SchwartzMap ℝ ℂ) :
    dist (negativeCauchy.comp (ccmSchwartzMultiplier f))
      (negativeCauchy.comp (ccmSchwartzMultiplier g)) =
        dist (f.toLp ∞ volume) (g.toLp ∞ volume) := by
  rw [ccmSchwartzMultiplier_eq_lineLinftyMultiplier,
    ccmSchwartzMultiplier_eq_lineLinftyMultiplier]
  exact dist_cauchyLinftyMultiplier _ _

private theorem small_scale_nonneg (f : SchwartzMap ℝ ℂ) :
    0 ≤ (4 * (1 + SchwartzMap.seminorm ℂ 0 0 f))⁻¹ := by
  positivity

/-- Sharp norm of the paper's existing small Schwartz multiplier. -/
theorem norm_smallMultiplier_eq_linfty (f : SchwartzMap ℝ ℂ) :
    ‖smallMultiplier f‖ = (4 * (1 + SchwartzMap.seminorm ℂ 0 0 f))⁻¹ * ‖f.toLp ∞ volume‖ := by
  rw [smallMultiplier, norm_smul, norm_ccmSchwartzMultiplier_eq_linfty,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (small_scale_nonneg f)]

/-- Cauchy compression does not improve the actual small-multiplier budget. -/
theorem norm_negativeCauchy_comp_smallMultiplier (f : SchwartzMap ℝ ℂ) :
    ‖negativeCauchy.comp (smallMultiplier f)‖ = ‖smallMultiplier f‖ := by
  rw [smallMultiplier, ContinuousLinearMap.comp_smul, norm_smul, norm_smul,
    norm_negativeCauchy_comp_ccmSchwartzMultiplier]

/-- The Neumann-series coefficient has an exact norm after projection as well. -/
theorem norm_negativeCauchy_comp_smallMultiplier_eq_linfty (f : SchwartzMap ℝ ℂ) :
    ‖negativeCauchy.comp (smallMultiplier f)‖ =
      (4 * (1 + SchwartzMap.seminorm ℂ 0 0 f))⁻¹ * ‖f.toLp ∞ volume‖ := by
  rw [norm_negativeCauchy_comp_smallMultiplier, norm_smallMultiplier_eq_linfty]

end
end RHTower.FokasLenells
