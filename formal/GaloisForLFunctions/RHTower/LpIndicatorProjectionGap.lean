import GaloisForLFunctions.RHTower.FiniteTimeBandFourierCompact

open MeasureTheory Set
open scoped symmDiff

namespace RHTower

noncomputable section

variable {X : Type*} [MeasurableSpace X]

/-- Orthogonal cutoff onto functions supported in a measurable set. -/
def lpIndicatorProjection (μ : Measure X) (E : Set X) (hE : MeasurableSet E) :
    Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ :=
  lpSetCutoffCLM (F := ℝ) (𝕜 := ℝ) μ 2 E hE

theorem lpIndicatorProjection_apply_ae
    (μ : Measure X) (E : Set X) (hE : MeasurableSet E) (f : Lp ℝ 2 μ) :
    lpIndicatorProjection μ E hE f =ᵐ[μ] E.indicator fun x => f x :=
  lpSetCutoffCLM_coeFn (F := ℝ) (𝕜 := ℝ) μ 2 E hE f

theorem lpIndicatorProjection_idempotent
    (μ : Measure X) (E : Set X) (hE : MeasurableSet E) :
    IsIdempotentElem (lpIndicatorProjection μ E hE) := by
  rw [isIdempotentElem_iff]
  ext f
  simp only [mul_apply_eq_comp]
  filter_upwards [lpIndicatorProjection_apply_ae μ E hE
      (lpIndicatorProjection μ E hE f),
    lpIndicatorProjection_apply_ae μ E hE f] with x h1 h2
  rw [h1]
  by_cases hx : x ∈ E
  · rw [Set.indicator_of_mem hx]
  · rw [Set.indicator_of_notMem hx]
    simpa [hx] using h2.symm

theorem lpIndicatorProjection_symmetric
    (μ : Measure X) (E : Set X) (hE : MeasurableSet E) :
    (lpIndicatorProjection μ E hE).toLinearMap.IsSymmetric := by
  intro f g
  rw [MeasureTheory.L2.inner_def, MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards [lpIndicatorProjection_apply_ae μ E hE f,
    lpIndicatorProjection_apply_ae μ E hE g] with x hf hg
  change inner ℝ (lpIndicatorProjection μ E hE f x) (g x) =
    inner ℝ (f x) (lpIndicatorProjection μ E hE g x)
  rw [hf, hg]
  by_cases hx : x ∈ E <;> simp [hx]

theorem lpIndicatorProjection_isStarProjection
    (μ : Measure X) (E : Set X) (hE : MeasurableSet E) :
    IsStarProjection (lpIndicatorProjection μ E hE) := by
  rw [ContinuousLinearMap.isStarProjection_iff_isSymmetricProjection]
  exact ⟨ContinuousLinearMap.IsIdempotentElem.toLinearMap
      (lpIndicatorProjection_idempotent μ E hE),
    lpIndicatorProjection_symmetric μ E hE⟩

theorem lpIndicatorProjection_sub_apply_norm_ae
    (μ : Measure X) (E F : Set X) (hE : MeasurableSet E) (hF : MeasurableSet F)
    (f : Lp ℝ 2 μ) :
    ∀ᵐ x ∂μ,
      ‖(lpIndicatorProjection μ E hE - lpIndicatorProjection μ F hF) f x‖ ≤ ‖f x‖ := by
  filter_upwards [Lp.coeFn_sub (lpIndicatorProjection μ E hE f)
      (lpIndicatorProjection μ F hF f),
    lpIndicatorProjection_apply_ae μ E hE f,
    lpIndicatorProjection_apply_ae μ F hF f] with x hsub hEf hFf
  rw [sub_apply, hsub, Pi.sub_apply, hEf, hFf]
  by_cases hxE : x ∈ E <;> by_cases hxF : x ∈ F <;> simp [hxE, hxF]

/-- Difference of two hard support projections is always a contraction. -/
theorem norm_lpIndicatorProjection_sub_le_one
    (μ : Measure X) (E F : Set X) (hE : MeasurableSet E) (hF : MeasurableSet F) :
    ‖lpIndicatorProjection μ E hE - lpIndicatorProjection μ F hF‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro f
  rw [one_mul, Lp.norm_def, Lp.norm_def]
  exact ENNReal.toReal_mono (Lp.eLpNorm_ne_top f)
    (eLpNorm_mono_ae (lpIndicatorProjection_sub_apply_norm_ae μ E F hE hF f))

theorem norm_lpIndicatorProjection_sub_apply_indicator_symmDiff
    (μ : Measure X) (E F : Set X) (hE : MeasurableSet E) (hF : MeasurableSet F)
    (hfin : μ (E ∆ F) ≠ ⊤) :
    ‖(lpIndicatorProjection μ E hE - lpIndicatorProjection μ F hF)
        (indicatorConstLp 2 (hE.symmDiff hF) hfin (1 : ℝ))‖ =
      ‖indicatorConstLp 2 (hE.symmDiff hF) hfin (1 : ℝ)‖ := by
  rw [Lp.norm_def, Lp.norm_def]
  congr 1
  apply eLpNorm_congr_norm_ae
  filter_upwards [Lp.coeFn_sub
      (lpIndicatorProjection μ E hE (indicatorConstLp 2 (hE.symmDiff hF) hfin (1 : ℝ)))
      (lpIndicatorProjection μ F hF (indicatorConstLp 2 (hE.symmDiff hF) hfin (1 : ℝ))),
    lpIndicatorProjection_apply_ae μ E hE
      (indicatorConstLp 2 (hE.symmDiff hF) hfin (1 : ℝ)),
    lpIndicatorProjection_apply_ae μ F hF
      (indicatorConstLp 2 (hE.symmDiff hF) hfin (1 : ℝ)),
    indicatorConstLp_coeFn (p := 2) (hs := hE.symmDiff hF)
      (hμs := hfin) (c := (1 : ℝ))] with x hsub hcutE hcutF hind
  rw [sub_apply, hsub, Pi.sub_apply, hcutE, hcutF]
  by_cases hxE : x ∈ E <;> by_cases hxF : x ∈ F <;>
    simp [Set.mem_symmDiff, hxE, hxF, hind]

/-- A non-null hard-cutoff motion has operator gap exactly one. -/
theorem norm_lpIndicatorProjection_sub_eq_one_of_symmDiff_pos
    (μ : Measure X) (E F : Set X) (hE : MeasurableSet E) (hF : MeasurableSet F)
    (hfin : μ (E ∆ F) ≠ ⊤) (hpos : 0 < μ.real (E ∆ F)) :
    ‖lpIndicatorProjection μ E hE - lpIndicatorProjection μ F hF‖ = 1 := by
  apply le_antisymm (norm_lpIndicatorProjection_sub_le_one μ E F hE hF)
  let f : Lp ℝ 2 μ := indicatorConstLp 2 (hE.symmDiff hF) hfin (1 : ℝ)
  have hfnorm : 0 < ‖f‖ := by
    change 0 < ‖indicatorConstLp 2 (hE.symmDiff hF) hfin (1 : ℝ)‖
    rw [norm_indicatorConstLp (by norm_num) (by norm_num), norm_one, one_mul]
    exact Real.rpow_pos_of_pos hpos _
  have happly := norm_lpIndicatorProjection_sub_apply_indicator_symmDiff
    μ E F hE hF hfin
  change ‖(lpIndicatorProjection μ E hE - lpIndicatorProjection μ F hF) f‖ = ‖f‖ at happly
  have hop := (lpIndicatorProjection μ E hE - lpIndicatorProjection μ F hF).le_opNorm f
  rw [happly] at hop
  nlinarith

/-- Null-equivalent apertures have identical support projections. -/
theorem lpIndicatorProjection_eq_of_ae_eq
    (μ : Measure X) (E F : Set X) (hE : MeasurableSet E) (hF : MeasurableSet F)
    (hEF : E =ᵐ[μ] F) :
    lpIndicatorProjection μ E hE = lpIndicatorProjection μ F hF := by
  ext f
  filter_upwards [lpIndicatorProjection_apply_ae μ E hE f,
    lpIndicatorProjection_apply_ae μ F hF f, hEF] with x hEfx hFfx hx
  rw [hEfx, hFfx]
  have hxiff : x ∈ E ↔ x ∈ F := by
    change E x ↔ F x
    exact iff_of_eq hx
  by_cases hxE : x ∈ E
  · have hxF : x ∈ F := hxiff.mp hxE
    simp [hxE, hxF]
  · have hxF : x ∉ F := fun h => hxE (hxiff.mpr h)
    simp [hxE, hxF]

theorem norm_lpIndicatorProjection_sub_eq_zero_of_ae_eq
    (μ : Measure X) (E F : Set X) (hE : MeasurableSet E) (hF : MeasurableSet F)
    (hEF : E =ᵐ[μ] F) :
    ‖lpIndicatorProjection μ E hE - lpIndicatorProjection μ F hF‖ = 0 := by
  rw [lpIndicatorProjection_eq_of_ae_eq μ E F hE hF hEF, sub_self, norm_zero]

end
end RHTower
