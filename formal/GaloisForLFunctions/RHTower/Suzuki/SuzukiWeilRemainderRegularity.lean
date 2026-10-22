import GaloisForLFunctions.RHTower.Suzuki.SuzukiWeilPositionTorqueCurvature
import Mathlib.Analysis.Calculus.LHopital

/-!
# Regularity of Suzuki's exact smooth Weil remainder

Suzuki's restricted-Weil decomposition contains the source term

`r''(t) = -2 cosh(t/2) + exp(t/2)/(2 sinh t) - 1/(2t)` for `t > 0`.

The displayed expression has a removable singularity at zero.  Two exact l'Hôpital steps give
the missing value `-7/4`.  This file installs that value, proves continuity of the resulting
even source kernel on the whole line, and derives its unconditional boundedness on every finite
aperture.  Thus the smooth block of the restricted Weil form is now literal source data rather
than a free bounded-kernel premise.
-/

open Filter Set Topology

namespace RHTower

noncomputable section

private theorem tendsto_suzukiWeilRemainderQuotient_zero :
    Tendsto
      (fun t : ℝ =>
        (t * Real.exp (t / 2) - Real.sinh t) /
          (2 * t * Real.sinh t))
      (𝓝[≠] 0) (𝓝 (1 / 4 : ℝ)) := by
  let N : ℝ → ℝ := fun t => t * Real.exp (t / 2) - Real.sinh t
  let D : ℝ → ℝ := fun t => 2 * t * Real.sinh t
  let N' : ℝ → ℝ := fun t =>
    Real.exp (t / 2) + t * (Real.exp (t / 2) / 2) - Real.cosh t
  let D' : ℝ → ℝ := fun t => 2 * Real.sinh t + 2 * t * Real.cosh t
  let N'' : ℝ → ℝ := fun t =>
    Real.exp (t / 2) + t * (Real.exp (t / 2) / 4) - Real.sinh t
  let D'' : ℝ → ℝ := fun t => 4 * Real.cosh t + 2 * t * Real.sinh t
  have hN : ∀ t : ℝ, HasDerivAt N (N' t) t := by
    intro t
    dsimp only [N, N']
    have he : HasDerivAt (fun x : ℝ => Real.exp (x / 2))
        (Real.exp (t / 2) / 2) t := by
      convert ((hasDerivAt_id t).div_const 2).exp using 1 <;>
        simp <;> ring
    have hraw := ((hasDerivAt_id t).mul he).sub (Real.hasDerivAt_sinh t)
    have heq : (fun x : ℝ => x * Real.exp (x / 2) - Real.sinh x) =ᶠ[𝓝 t]
        ((id * fun x : ℝ => Real.exp (x / 2)) - Real.sinh) :=
      Filter.Eventually.of_forall fun _ => rfl
    exact (hraw.congr_of_eventuallyEq heq).congr_deriv (by simp only [id_eq]; ring)
  have hD : ∀ t : ℝ, HasDerivAt D (D' t) t := by
    intro t
    dsimp only [D, D']
    have hraw := ((hasDerivAt_id t).const_mul 2).mul (Real.hasDerivAt_sinh t)
    have heq : (fun x : ℝ => 2 * x * Real.sinh x) =ᶠ[𝓝 t]
        ((fun x : ℝ => 2 * x) * Real.sinh) :=
      Filter.Eventually.of_forall fun _ => by simp only [Pi.mul_apply]
    exact (hraw.congr_of_eventuallyEq heq).congr_deriv (by simp only [id_eq]; ring)
  have hN' : ∀ t : ℝ, HasDerivAt N' (N'' t) t := by
    intro t
    dsimp only [N', N'']
    have he : HasDerivAt (fun x : ℝ => Real.exp (x / 2))
        (Real.exp (t / 2) / 2) t := by
      convert ((hasDerivAt_id t).div_const 2).exp using 1 <;>
        simp <;> ring
    have hte := (hasDerivAt_id t).mul (he.div_const 2)
    have hraw := (he.add hte).sub (Real.hasDerivAt_cosh t)
    have heq :
        (fun x : ℝ => Real.exp (x / 2) + x * (Real.exp (x / 2) / 2) - Real.cosh x) =ᶠ[𝓝 t]
          ((fun x : ℝ => Real.exp (x / 2)) +
            (id * fun x : ℝ => Real.exp (x / 2) / 2) - Real.cosh) :=
      Filter.Eventually.of_forall fun _ => rfl
    exact (hraw.congr_of_eventuallyEq heq).congr_deriv (by simp only [id_eq]; ring)
  have hD' : ∀ t : ℝ, HasDerivAt D' (D'' t) t := by
    intro t
    dsimp only [D', D'']
    have h1 := (Real.hasDerivAt_sinh t).const_mul 2
    have h2 := ((hasDerivAt_id t).mul (Real.hasDerivAt_cosh t)).const_mul 2
    have hraw := h1.add h2
    have heq :
        (fun x : ℝ => 2 * Real.sinh x + 2 * x * Real.cosh x) =ᶠ[𝓝 t]
          ((fun x : ℝ => 2 * Real.sinh x) +
            fun x : ℝ => 2 * ((id : ℝ → ℝ) * Real.cosh) x) :=
      Filter.Eventually.of_forall fun _ => by
        simp only [Pi.add_apply, Pi.mul_apply, id_eq]
        ring
    exact (hraw.congr_of_eventuallyEq heq).congr_deriv (by simp only [id_eq]; ring)
  have hsecond : Tendsto (fun t => N'' t / D'' t)
      (𝓝[≠] 0) (𝓝 (1 / 4 : ℝ)) := by
    have hNlim : Tendsto N'' (𝓝 0) (𝓝 1) := by
      have hc : ContinuousAt N'' 0 := by
        dsimp only [N'']
        fun_prop
      simpa [N''] using hc.tendsto
    have hDlim : Tendsto D'' (𝓝 0) (𝓝 4) := by
      have hc : ContinuousAt D'' 0 := by
        dsimp only [D'']
        fun_prop
      simpa [D''] using hc.tendsto
    have hdiv := hNlim.div hDlim (by norm_num : (4 : ℝ) ≠ 0)
    change Tendsto (N'' / D'') (𝓝[≠] 0) (𝓝 (1 / 4 : ℝ))
    exact hdiv.mono_left nhdsWithin_le_nhds
  have hD''ne : ∀ᶠ t in 𝓝[≠] (0 : ℝ), D'' t ≠ 0 := by
    filter_upwards with t
    dsimp only [D'']
    have hcosh : 0 < Real.cosh t := Real.cosh_pos t
    have htsinh : 0 ≤ t * Real.sinh t := by
      rcases le_total 0 t with ht | ht
      · exact mul_nonneg ht (Real.sinh_nonneg_iff.mpr ht)
      · exact mul_nonneg_of_nonpos_of_nonpos ht (Real.sinh_nonpos_iff.mpr ht)
    nlinarith
  have hfirst : Tendsto (fun t => N' t / D' t)
      (𝓝[≠] 0) (𝓝 (1 / 4 : ℝ)) := by
    refine HasDerivAt.lhopital_zero_nhdsNE
      (f' := N'') (g' := D'') ?_ ?_ hD''ne ?_ ?_ hsecond
    · exact Filter.Eventually.of_forall hN'
    · exact Filter.Eventually.of_forall hD'
    · have hc : ContinuousAt N' 0 := by
        dsimp only [N']
        fun_prop
      have ht : Tendsto N' (𝓝 0) (𝓝 0) := by
        simpa [N'] using hc.tendsto
      exact ht.mono_left nhdsWithin_le_nhds
    · have hc : ContinuousAt D' 0 := by
        dsimp only [D']
        fun_prop
      have ht : Tendsto D' (𝓝 0) (𝓝 0) := by
        simpa [D'] using hc.tendsto
      exact ht.mono_left nhdsWithin_le_nhds
  have hD'ne : ∀ᶠ t in 𝓝[≠] (0 : ℝ), D' t ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    simp only [mem_compl_iff, mem_singleton_iff] at ht
    dsimp only [D']
    rcases lt_or_gt_of_ne ht with htneg | htpos
    · have hsinh : Real.sinh t < 0 := (Real.sinh_neg_iff).2 htneg
      have hcosh : 0 < Real.cosh t := Real.cosh_pos t
      nlinarith
    · have hsinh : 0 < Real.sinh t := (Real.sinh_pos_iff).2 htpos
      have hcosh : 0 < Real.cosh t := Real.cosh_pos t
      nlinarith
  refine HasDerivAt.lhopital_zero_nhdsNE
    (f' := N') (g' := D') ?_ ?_ hD'ne ?_ ?_ hfirst
  · exact Filter.Eventually.of_forall hN
  · exact Filter.Eventually.of_forall hD
  · have hc : ContinuousAt N 0 := by
      dsimp only [N]
      fun_prop
    have ht : Tendsto N (𝓝 0) (𝓝 0) := by
      simpa [N] using hc.tendsto
    exact ht.mono_left nhdsWithin_le_nhds
  · have hc : ContinuousAt D 0 := by
      dsimp only [D]
      fun_prop
    have ht : Tendsto D (𝓝 0) (𝓝 0) := by
      simpa [D] using hc.tendsto
    exact ht.mono_left nhdsWithin_le_nhds

/-- The positive-lag formula has the finite source limit `-7/4` at the origin. -/
theorem tendsto_suzukiWeilRemainderSecondDerivative_zero :
    Tendsto suzukiWeilRemainderSecondDerivative (𝓝[≠] 0) (𝓝 (-7 / 4 : ℝ)) := by
  have hq := tendsto_suzukiWeilRemainderQuotient_zero
  have hcosh : Tendsto (fun t : ℝ => -2 * Real.cosh (t / 2))
      (𝓝[≠] 0) (𝓝 (-2 : ℝ)) := by
    have hc : ContinuousAt (fun t : ℝ => -2 * Real.cosh (t / 2)) 0 := by fun_prop
    simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
  have hsum := hcosh.add hq
  have hsum' : Tendsto
      (fun t : ℝ =>
        -2 * Real.cosh (t / 2) +
          (t * Real.exp (t / 2) - Real.sinh t) /
            (2 * t * Real.sinh t))
      (𝓝[≠] 0) (𝓝 (-7 / 4 : ℝ)) := by
    convert hsum using 1 <;> norm_num
  apply hsum'.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  simp only [mem_compl_iff, mem_singleton_iff] at ht
  have hsinh : Real.sinh t ≠ 0 := Real.sinh_ne_zero.mpr ht
  rw [suzukiWeilRemainderSecondDerivative]
  have hrewrite :
      Real.exp (t / 2) / (2 * Real.sinh t) - 1 / (2 * t) =
        (t * Real.exp (t / 2) - Real.sinh t) / (2 * t * Real.sinh t) := by
    field_simp [ht, hsinh]
  rw [← hrewrite]
  ring

/-- Continuous removal of the apparent singularity in Suzuki's remainder. -/
def suzukiWeilRemainderSecondDerivativeContinuous : ℝ → ℝ :=
  Function.update suzukiWeilRemainderSecondDerivative 0 (-7 / 4)

theorem continuousAt_suzukiWeilRemainderSecondDerivative_of_ne {t : ℝ} (ht : t ≠ 0) :
    ContinuousAt suzukiWeilRemainderSecondDerivative t := by
  unfold suzukiWeilRemainderSecondDerivative
  have hsinh : Real.sinh t ≠ 0 := Real.sinh_ne_zero.mpr ht
  have hhalf : ContinuousAt (fun x : ℝ => x / 2) t := continuousAt_id.div_const 2
  have hcosh : ContinuousAt (fun x : ℝ => Real.cosh (x / 2)) t := by
    simpa only [Function.comp_def] using Real.continuous_cosh.continuousAt.comp hhalf
  have hexp : ContinuousAt (fun x : ℝ => Real.exp (x / 2)) t := by
    simpa only [Function.comp_def] using Real.continuous_exp.continuousAt.comp hhalf
  have hsinhc : ContinuousAt Real.sinh t := Real.continuous_sinh.continuousAt
  exact ((continuousAt_const.mul hcosh).add
    (hexp.div (continuousAt_const.mul hsinhc) (mul_ne_zero (by norm_num) hsinh))).sub
      (continuousAt_const.div (continuousAt_const.mul continuousAt_id)
        (mul_ne_zero (by norm_num) ht))

theorem continuous_suzukiWeilRemainderSecondDerivativeContinuous :
    Continuous suzukiWeilRemainderSecondDerivativeContinuous := by
  rw [continuous_iff_continuousAt]
  intro t
  rcases eq_or_ne t 0 with rfl | ht
  · rw [suzukiWeilRemainderSecondDerivativeContinuous, continuousAt_update_same]
    exact tendsto_suzukiWeilRemainderSecondDerivative_zero
  · have hbase := continuousAt_suzukiWeilRemainderSecondDerivative_of_ne ht
    apply hbase.congr_of_eventuallyEq
    filter_upwards [eventually_ne_nhds ht] with x hx
    simp [suzukiWeilRemainderSecondDerivativeContinuous, Function.update, hx]

theorem suzukiWeilRemainderSecondDerivativeContinuous_eq_of_ne
    {t : ℝ} (ht : t ≠ 0) :
    suzukiWeilRemainderSecondDerivativeContinuous t =
      suzukiWeilRemainderSecondDerivative t := by
  simp [suzukiWeilRemainderSecondDerivativeContinuous, Function.update, ht]

/-- Literal even second derivative `r''(|t|)` used by the restricted Weil convolution block. -/
def suzukiWeilRemainderKernel (t : ℝ) : ℝ :=
  suzukiWeilRemainderSecondDerivativeContinuous |t|

theorem continuous_suzukiWeilRemainderKernel :
    Continuous suzukiWeilRemainderKernel :=
  continuous_suzukiWeilRemainderSecondDerivativeContinuous.comp continuous_abs

theorem suzukiWeilRemainderKernel_neg (t : ℝ) :
    suzukiWeilRemainderKernel (-t) = suzukiWeilRemainderKernel t := by
  simp [suzukiWeilRemainderKernel]

theorem suzukiWeilRemainderKernel_eq_source_of_ne {t : ℝ} (ht : t ≠ 0) :
    suzukiWeilRemainderKernel t =
      suzukiWeilRemainderSecondDerivative |t| := by
  exact suzukiWeilRemainderSecondDerivativeContinuous_eq_of_ne (abs_ne_zero.mpr ht)

/-- The actual smooth remainder is bounded on every finite difference aperture. -/
theorem exists_abs_suzukiWeilRemainderKernel_le (a : ℝ) :
    ∃ C : ℝ, ∀ t ∈ Icc (-2 * |a|) (2 * |a|),
      |suzukiWeilRemainderKernel t| ≤ C := by
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn
    continuous_suzukiWeilRemainderKernel.continuousOn
  exact ⟨C, fun t ht => by simpa [Real.norm_eq_abs] using hC t ht⟩

/-- In particular, Suzuki's literal smooth remainder is integrable on every finite aperture. -/
theorem intervalIntegrable_suzukiWeilRemainderKernel (a b : ℝ) :
    IntervalIntegrable suzukiWeilRemainderKernel MeasureTheory.volume a b :=
  continuous_suzukiWeilRemainderKernel.intervalIntegrable a b

end
end RHTower
