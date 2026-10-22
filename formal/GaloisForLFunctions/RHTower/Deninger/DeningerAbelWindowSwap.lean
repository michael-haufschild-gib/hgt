import GaloisForLFunctions.RHTower.Deninger.DeningerAbelTonelli

/-!
# Exchanging the order of integration over the dilation window

The indicator of the dilation window is a measurable function of the pair, so the two orders of
integration agree.  Fixing `u` first, the slice is the interval `[u/(i+1), u/i]`, whose measure is
`u/(i(i+1))`; that is the whole content of the exchange.

* `deningerWindowKernel` : the window indicator, weighted by the derivative.
* `deningerWindowKernel_slice` : the `u`-slice integrates to `‖H_h'(u)‖ · u/(i(i+1))`.
* `deningerWindowKernel_swap` : **the two orders of integration agree.**
-/

namespace RHTower

open MeasureTheory SchwartzMap ENNReal

noncomputable section

/-- The dilation window, as a set of the plane. -/
def deningerWindow (i : ℕ) : Set (ℝ × ℝ) :=
  {p : ℝ × ℝ | (i : ℝ) * p.1 ≤ p.2 ∧ p.2 ≤ ((i : ℝ) + 1) * p.1}

theorem deningerWindow_measurableSet (i : ℕ) : MeasurableSet (deningerWindow i) :=
  deningerAbelWindow_measurableSet i

/-- The window indicator, weighted by the derivative of the pullback. -/
def deningerWindowKernel (h : 𝓢(ℝ, ℂ)) (i : ℕ) (x u : ℝ) : ℝ≥0∞ :=
  (deningerWindow i).indicator (fun p : ℝ × ℝ => ‖deningerLogPullDeriv h p.2‖ₑ) (x, u)

theorem deningerLogPullDeriv_measurable (h : 𝓢(ℝ, ℂ)) :
    Measurable (deningerLogPullDeriv h) := by
  have hderiv : Continuous (deriv (h : ℝ → ℂ)) := h.smooth'.continuous_deriv (by simp)
  refine Measurable.mul ?_ ?_
  · exact hderiv.measurable.comp Real.measurable_log
  · exact Complex.measurable_ofReal.comp (measurable_id.inv)

theorem deningerWindowKernel_measurable (h : 𝓢(ℝ, ℂ)) (i : ℕ) :
    Measurable (Function.uncurry (deningerWindowKernel h i)) := by
  have hbase : Measurable fun p : ℝ × ℝ => ‖deningerLogPullDeriv h p.2‖ₑ :=
    ((deningerLogPullDeriv_measurable h).comp measurable_snd).enorm
  exact hbase.indicator (deningerWindow_measurableSet i)

/-- **The `u`-slice of the window kernel.**  For `u > 0` the slice is the interval
`[u/(i+1), u/i]`, so the inner integral is the derivative times `u/(i(i+1))`. -/
theorem deningerWindowKernel_slice (h : 𝓢(ℝ, ℂ)) {i : ℕ} (hi : 0 < i) {u : ℝ} (hu : 0 < u) :
    (∫⁻ x in Set.Ioi (0 : ℝ), deningerWindowKernel h i x u)
      = ‖deningerLogPullDeriv h u‖ₑ * ENNReal.ofReal (u / ((i : ℝ) * ((i : ℝ) + 1))) := by
  have hir : (0 : ℝ) < (i : ℝ) := by exact_mod_cast hi
  have hi1 : (0 : ℝ) < (i : ℝ) + 1 := by linarith
  set S : Set ℝ := {x : ℝ | (i : ℝ) * x ≤ u ∧ u ≤ ((i : ℝ) + 1) * x} with hS
  have hSeq : S = Set.Icc (u / ((i : ℝ) + 1)) (u / (i : ℝ)) :=
    deningerAbelWindow_volume hi u
  have hSmeas : MeasurableSet S := by
    rw [hSeq]
    exact measurableSet_Icc
  have hSsub : S ⊆ Set.Ioi 0 := by
    rw [hSeq]
    intro x hx
    exact lt_of_lt_of_le (div_pos hu hi1) hx.1
  have hfun : ∀ x : ℝ, deningerWindowKernel h i x u
      = S.indicator (fun _ : ℝ => ‖deningerLogPullDeriv h u‖ₑ) x := by
    intro x
    by_cases hx : x ∈ S
    · rw [Set.indicator_of_mem hx, deningerWindowKernel,
        Set.indicator_of_mem (show (x, u) ∈ deningerWindow i from hx)]
    · rw [Set.indicator_of_notMem hx, deningerWindowKernel,
        Set.indicator_of_notMem (show (x, u) ∉ deningerWindow i from hx)]
  rw [lintegral_congr hfun, lintegral_indicator hSmeas, Measure.restrict_restrict hSmeas,
    Set.inter_eq_left.mpr hSsub, setLIntegral_const]
  congr 1
  exact deningerAbelWindow_measure hi u

/-- **The two orders of integration agree.** -/
theorem deningerWindowKernel_swap (h : 𝓢(ℝ, ℂ)) (i : ℕ) :
    (∫⁻ x in Set.Ioi (0 : ℝ), ∫⁻ u in Set.Ioi (0 : ℝ), deningerWindowKernel h i x u)
      = ∫⁻ u in Set.Ioi (0 : ℝ), ∫⁻ x in Set.Ioi (0 : ℝ), deningerWindowKernel h i x u := by
  refine lintegral_lintegral_swap ?_
  exact (deningerWindowKernel_measurable h i).aemeasurable

end

end RHTower
