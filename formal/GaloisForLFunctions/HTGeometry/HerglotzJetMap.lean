import GaloisForLFunctions.HTGeometry.WeightedJetControlSurjective

/-!
# The Herglotz jet map on bounded parameters

The parameter of the Herglotz chart is a bounded reweighting `u`, and the associated measure has
density `exp u * w` against the base measure, where `w` carries the Nevanlinna growth condition.

Boundedness of `u` is exactly what keeps that density integrable for *every* parameter: `exp u` is
bounded by `exp ‖u‖`, so integrability of `w` is inherited with no further hypothesis.  The jet map
sends a parameter to the finite vector of Cauchy jets of its measure.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory

open scoped ENNReal

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
/-- A bounded parameter keeps the exponential density integrable. -/
theorem integrable_exp_Lp_top_mul (μ : Measure ℝ) (u : Lp ℝ ⊤ μ)
    (w : ℝ → ℝ) (hw : Integrable w μ) :
    Integrable (fun t => Real.exp (u t) * w t) μ := by
  refine Integrable.mono' ((hw.abs).const_mul (Real.exp ‖u‖)) ?_ ?_
  · exact (Real.continuous_exp.comp_aestronglyMeasurable
      (Lp.aestronglyMeasurable u)).mul hw.aestronglyMeasurable
  · filter_upwards [ae_norm_le_norm_Lp_top μ u] with t ht
    have hbound : u t ≤ ‖u‖ :=
      le_trans (le_abs_self _) (by simpa [Real.norm_eq_abs] using ht)
    have hexp : Real.exp (u t) ≤ Real.exp ‖u‖ := Real.exp_le_exp.mpr hbound
    calc ‖Real.exp (u t) * w t‖
        = Real.exp (u t) * |w t| := by
          rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      _ ≤ Real.exp ‖u‖ * |w t| :=
          mul_le_mul_of_nonneg_right hexp (abs_nonneg _)

omit [Fintype ι] [DecidableEq ι] in
/-- The exponential density of a bounded parameter is strictly positive wherever the base density
is. -/
theorem exp_mul_pos (u : ℝ → ℝ) {w : ℝ → ℝ} (hw : ∀ t, 0 < w t) (t : ℝ) :
    0 < Real.exp (u t) * w t :=
  mul_pos (Real.exp_pos _) (hw t)

/-- The Herglotz jet map: a bounded parameter is sent to the Cauchy jets of its measure. -/
def herglotzJetMap (μ : Measure ℝ) (w : ℝ → ℝ)
    (x : ι → ℂ) (n : ι → ℕ) (u : Lp ℝ ⊤ μ) : jetIndex n → ℂ :=
  fun s => ∫ t, ((Real.exp (u t) * w t : ℝ) : ℂ) * cauchyJetKernel x n t s ∂μ

set_option linter.unusedSectionVars false in
@[simp]
theorem herglotzJetMap_apply (μ : Measure ℝ) (w : ℝ → ℝ)
    (x : ι → ℂ) (n : ι → ℕ) (u : Lp ℝ ⊤ μ) (s : jetIndex n) :
    herglotzJetMap μ w x n u s =
      ∫ t, ((Real.exp (u t) * w t : ℝ) : ℂ) * cauchyJetKernel x n t s ∂μ :=
  rfl

/-- **Surjectivity of the tangent control at every parameter.**  The weighted control map of the
density of any bounded parameter is surjective, so the reachability argument has a surjective linear
part at every base point. -/
theorem surjective_weightedJetControl_expDensity
    (μ : Measure ℝ) (hsupp : μ.support.Infinite)
    (w : ℝ → ℝ) (hw : Integrable w μ) (hwpos : ∀ t, 0 < w t)
    (x : ι → ℂ) (hx : Function.Injective x) (hupper : ∀ i, 0 < (x i).im)
    (n : ι → ℕ) (u : Lp ℝ ⊤ μ) :
    Function.Surjective
      (weightedJetControl μ (fun t => Real.exp (u t) * w t)
        (integrable_exp_Lp_top_mul μ u w hw) x
        (fun i => ne_of_gt (hupper i)) n) :=
  surjective_weightedJetControl μ hsupp _
    (integrable_exp_Lp_top_mul μ u w hw)
    (fun t => exp_mul_pos (fun t => u t) hwpos t) x hx hupper n

end

end GaloisForLFunctions.HTGeometry
