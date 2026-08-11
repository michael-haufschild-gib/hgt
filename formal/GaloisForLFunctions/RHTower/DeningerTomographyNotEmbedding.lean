import GaloisForLFunctions.RHTower.DeningerCircleTopology
import GaloisForLFunctions.RHTower.DeningerTomographyNonstrict

/-!
# The compact tomography is not a topological embedding

The damped translates have compact traces that tend to zero in every `C^r` seminorm of the circle —
the trace is a rotation of the original trace scaled by `e^{-as}` — while their Meyer seminorm stays
bounded below independently of the escape parameter.  So the periodization has a discontinuous
inverse on its range.

* `deningerEscape_trace_le` : **the trace seminorms carry the damping factor.**
* `deningerEscape_trace_tendsto_zero` : the traces tend to zero.
* `deningerPeriodization_not_isEmbedding` : **the source seminorm does not follow.**
-/

namespace RHTower

open SchwartzMap Filter Topology

noncomputable section

/-- **Every circle seminorm of the escaped trace carries the damping factor.** -/
theorem deningerEscape_trace_le {L : ℝ} (hL : 0 < L) {a : ℝ} (s : ℝ) (r : ℕ)
    (h : DeningerExpSchwartz) :
    deningerPeriodicSup r (deningerPeriodizationMap hL (deningerEscapeFamily a s h))
      ≤ Real.exp (-(a * s)) * deningerPeriodicSup r (deningerPeriodizationMap hL h) := by
  have hshift : ((deningerPeriodizationMap hL (deningerEscapeFamily a s h) :
        DeningerSmoothPeriodic L) : ℝ → ℂ)
      = fun t => ((Real.exp (-(a * s)) : ℝ) : ℂ)
        * ((deningerPeriodizationMap hL h : DeningerSmoothPeriodic L) : ℝ → ℂ) (t - s) := by
    funext t
    exact deningerEscapeFamily_periodizationSum a s L t h
  refine ciSup_le fun t => ?_
  rw [hshift]
  have hcomp : iteratedFDeriv ℝ r
      (fun t : ℝ => ((Real.exp (-(a * s)) : ℝ) : ℂ)
        * ((deningerPeriodizationMap hL h : DeningerSmoothPeriodic L) : ℝ → ℂ) (t - s)) t
      = ((Real.exp (-(a * s)) : ℝ) : ℂ) •
        iteratedFDeriv ℝ r
          ((deningerPeriodizationMap hL h : DeningerSmoothPeriodic L) : ℝ → ℂ) (t - s) := by
    have hsmul : (fun t : ℝ => ((Real.exp (-(a * s)) : ℝ) : ℂ)
        * ((deningerPeriodizationMap hL h : DeningerSmoothPeriodic L) : ℝ → ℂ) (t - s))
        = ((Real.exp (-(a * s)) : ℝ) : ℂ) •
          (fun t : ℝ => ((deningerPeriodizationMap hL h : DeningerSmoothPeriodic L) : ℝ → ℂ)
            (t + (-s))) := by
      funext u
      show _ = ((Real.exp (-(a * s)) : ℝ) : ℂ) * _
      rw [sub_eq_add_neg]
    rw [hsmul, iteratedFDeriv_const_smul_apply, iteratedFDeriv_comp_add_right, sub_eq_add_neg]
    exact ((deningerSmoothPeriodic_contDiff (deningerPeriodizationMap hL h)).comp
      (contDiff_id.add contDiff_const)).of_le (by exact_mod_cast le_top) |>.contDiffAt
  rw [hcomp, norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact mul_le_mul_of_nonneg_left
    (deningerPeriodicSup_le hL r (deningerPeriodizationMap hL h) (t - s)) (Real.exp_pos _).le

/-- **The compact traces of the escape family tend to zero.** -/
theorem deningerEscape_trace_tendsto_zero {L : ℝ} (hL : 0 < L) {a : ℝ} (ha : 0 < a) (r : ℕ)
    (h : DeningerExpSchwartz) :
    Tendsto (fun n : ℕ =>
        deningerPeriodicSup r (deningerPeriodizationMap hL (deningerEscapeFamily a (n : ℝ) h)))
      atTop (𝓝 0) := by
  have hnn : ∀ n : ℕ, 0 ≤ deningerPeriodicSup r
      (deningerPeriodizationMap hL (deningerEscapeFamily a (n : ℝ) h)) :=
    fun n => deningerPeriodicSup_nonneg hL r _
  have hdecay : Tendsto (fun n : ℕ =>
      Real.exp (-(a * (n : ℝ))) * deningerPeriodicSup r (deningerPeriodizationMap hL h))
      atTop (𝓝 0) := by
    have hexp : Tendsto (fun n : ℕ => Real.exp (-(a * (n : ℝ)))) atTop (𝓝 0) := by
      have hlin : Tendsto (fun n : ℕ => -(a * (n : ℝ))) atTop atBot :=
        tendsto_neg_atTop_atBot.comp
          (Filter.Tendsto.const_mul_atTop ha tendsto_natCast_atTop_atTop)
      exact Real.tendsto_exp_atBot.comp hlin
    simpa using hexp.mul_const (deningerPeriodicSup r (deningerPeriodizationMap hL h))
  exact squeeze_zero hnn (fun n => deningerEscape_trace_le hL (n : ℝ) r h) hdecay

/-- **The periodization is not a topological embedding.**  The traces of the escape family tend to
zero in every circle seminorm, but the Meyer seminorm of the family is bounded below by a positive
constant, uniformly in the escape parameter. -/
theorem deningerPeriodization_not_isEmbedding {L : ℝ} (hL : 0 < L) {a u : ℝ} (ha : 0 < a)
    {h : DeningerExpSchwartz} (hu : ((h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) u ≠ 0) (hu0 : 0 ≤ u) :
    (∀ r : ℕ, Tendsto (fun n : ℕ =>
        deningerPeriodicSup r (deningerPeriodizationMap hL (deningerEscapeFamily a (n : ℝ) h)))
      atTop (𝓝 0))
      ∧ 0 < Real.exp (a * u) * ‖((h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) u‖
      ∧ ∀ n : ℕ, Real.exp (a * u) * ‖((h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) u‖
          ≤ deningerMeyerSeminormFun a 0 (deningerEscapeFamily a (n : ℝ) h) := by
  refine ⟨fun r => deningerEscape_trace_tendsto_zero hL ha r h, ?_, fun n => ?_⟩
  · have h1 : (0 : ℝ) < Real.exp (a * u) := Real.exp_pos _
    have h2 : (0 : ℝ) < ‖((h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) u‖ := norm_pos_iff.2 hu
    positivity
  · refine deningerEscapeFamily_meyer_ge ?_ h
    positivity

end

end RHTower
