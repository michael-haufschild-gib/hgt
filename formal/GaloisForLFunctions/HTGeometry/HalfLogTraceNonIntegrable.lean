import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Integral

/-!
# A nonzero half-log trace is incompatible with square integrability

A profile with the half-log asymptotic `F(L) = L^{-1/2} β + O(L^{-1})` and `β ≠ 0` is bounded below
by `‖β‖/(2√L)` on a terminal ray, so its square dominates `‖β‖²/(4L)`, whose ray integral diverges.
This is the exact converse direction of the corona sequence: zero trace is not merely sufficient
for physical square integrability, it is necessary.
-/

open MeasureTheory Set

namespace GaloisForLFunctions.HTGeometry

/-- **The half-log lower bound.**  Past the comparison scale the profile is at least half of its
leading term. -/
theorem norm_ge_of_halfLog_asymptotic {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {F : ℝ → X} {β : X} {C L : ℝ} (hβ : β ≠ 0) (hL : 0 < L)
    (hC : 2 * C ≤ ‖β‖ * Real.sqrt L)
    (hasymp : ‖F L - (1 / Real.sqrt L) • β‖ ≤ C / L) :
    ‖β‖ / (2 * Real.sqrt L) ≤ ‖F L‖ := by
  have hsq : 0 < Real.sqrt L := Real.sqrt_pos.mpr hL
  have hlead : ‖(1 / Real.sqrt L) • β‖ = ‖β‖ / Real.sqrt L := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
    field_simp
  have hrev : ‖(1 / Real.sqrt L) • β‖ - ‖F L‖ ≤ ‖F L - (1 / Real.sqrt L) • β‖ := by
    have := norm_sub_norm_le ((1 / Real.sqrt L) • β) (F L)
    calc ‖(1 / Real.sqrt L) • β‖ - ‖F L‖ ≤ ‖(1 / Real.sqrt L) • β - F L‖ := this
      _ = ‖F L - (1 / Real.sqrt L) • β‖ := by rw [norm_sub_rev]
  rw [hlead] at hrev
  have hCL : C / L ≤ ‖β‖ / (2 * Real.sqrt L) := by
    rw [div_le_div_iff₀ hL (by positivity)]
    have hLval : L = Real.sqrt L * Real.sqrt L := (Real.mul_self_sqrt hL.le).symm
    nlinarith [hC, hsq, norm_nonneg β]
  have hstep : ‖β‖ / Real.sqrt L - ‖F L‖ ≤ ‖β‖ / (2 * Real.sqrt L) :=
    le_trans (le_trans hrev hasymp) hCL
  have hhalf : ‖β‖ / Real.sqrt L - ‖β‖ / (2 * Real.sqrt L) = ‖β‖ / (2 * Real.sqrt L) := by
    field_simp
    ring
  linarith [hstep, hhalf]

/-- **A nonzero half-log trace destroys square integrability.** -/
theorem not_integrableOn_sq_of_halfLog_trace {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {F : ℝ → X} {β : X} {C L₁ : ℝ} (hβ : β ≠ 0) (hL₁ : 0 < L₁)
    (hasymp : ∀ L ∈ Ioi L₁, ‖F L - (1 / Real.sqrt L) • β‖ ≤ C / L) :
    ¬ IntegrableOn (fun L => ‖F L‖ ^ 2) (Ioi L₁) volume := by
  intro hint
  have hβ0 : 0 < ‖β‖ := norm_pos_iff.mpr hβ
  set L₂ : ℝ := max L₁ (1 + (2 * C / ‖β‖) ^ 2) with hL₂
  have hL₂pos : 0 < L₂ := lt_of_lt_of_le hL₁ (le_max_left _ _)
  have hL₂ge : L₁ ≤ L₂ := le_max_left _ _
  have hlower : ∀ L ∈ Ioi L₂, ‖β‖ ^ 2 / (4 * L) ≤ ‖F L‖ ^ 2 := by
    intro L hL
    have hL2 : L₂ < L := hL
    have hLpos : 0 < L := lt_trans hL₂pos hL2
    have hLbig : 1 + (2 * C / ‖β‖) ^ 2 ≤ L := le_trans (le_max_right _ _) hL2.le
    have hsq : 0 < Real.sqrt L := Real.sqrt_pos.mpr hLpos
    have hC : 2 * C ≤ ‖β‖ * Real.sqrt L := by
      rcases le_or_gt C 0 with hC0 | hC0
      · nlinarith [hsq, hβ0]
      · have hsqrtge : 2 * C / ‖β‖ ≤ Real.sqrt L := by
          have hnn : 0 ≤ 2 * C / ‖β‖ := by positivity
          have hle : (2 * C / ‖β‖) ^ 2 ≤ L := by linarith
          nlinarith [Real.sq_sqrt hLpos.le, Real.sqrt_nonneg L, hle, hnn]
        rw [div_le_iff₀ hβ0] at hsqrtge
        linarith
    have hin : L ∈ Ioi L₁ := lt_of_le_of_lt hL₂ge hL2
    have hnorm := norm_ge_of_halfLog_asymptotic hβ hLpos hC (hasymp L hin)
    have hval : ‖β‖ ^ 2 / (4 * L) = (‖β‖ / (2 * Real.sqrt L)) ^ 2 := by
      rw [div_pow, mul_pow, Real.sq_sqrt hLpos.le]
      ring_nf
    rw [hval]
    exact pow_le_pow_left₀ (by positivity) hnorm 2
  have hintL₂ : IntegrableOn (fun L => ‖F L‖ ^ 2) (Ioi L₂) volume :=
    hint.mono_set (Ioi_subset_Ioi hL₂ge)
  have hminor : IntegrableOn (fun L => ‖β‖ ^ 2 / (4 * L)) (Ioi L₂) volume := by
    refine Integrable.mono' hintL₂ ?_ ?_
    · apply Measurable.aestronglyMeasurable
      fun_prop
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with L hL
      have hLpos : 0 < L := lt_trans hL₂pos hL
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact hlower L hL
  have hinv : IntegrableOn (fun L : ℝ => L⁻¹) (Ioi L₂) volume := by
    have hscale : IntegrableOn (fun L : ℝ => 4 / ‖β‖ ^ 2 * (‖β‖ ^ 2 / (4 * L)))
        (Ioi L₂) volume := hminor.const_mul (4 / ‖β‖ ^ 2)
    refine hscale.congr_fun (fun L hL => ?_) measurableSet_Ioi
    have hLpos : 0 < L := lt_trans hL₂pos hL
    have hβ2 : ‖β‖ ^ 2 ≠ 0 := by positivity
    field_simp
  exact not_integrableOn_Ioi_inv hinv

end GaloisForLFunctions.HTGeometry
