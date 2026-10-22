import GaloisForLFunctions.RHTower.Deninger.DeningerAbelWindowSwap
import GaloisForLFunctions.RHTower.Deninger.DeningerHigherCoefficient

/-!
# The order-`r` window exchange

Weighting the dilation variable by `x^r` changes nothing structural: the kernel is still a
measurable indicator, its `u`-slice is still the derivative times a window moment, and the two
orders of integration still agree.  Only the moment changes, from the window length `u/(i(i+1))` to
`(u^{r+1}/(r+1))(i^{-(r+1)} - (i+1)^{-(r+1)})`.

* `deningerWindowKernelPow` : the `x^r`-weighted window kernel.
* `deningerWindowKernelPow_slice` : **its `u`-slice is the derivative times the window moment.**
* `deningerWindowKernelPow_swap` : the two orders of integration agree.
-/

namespace RHTower

open MeasureTheory SchwartzMap ENNReal

noncomputable section

/-- The `x^r`-weighted window kernel. -/
def deningerWindowKernelPow (h : 𝓢(ℝ, ℂ)) (i r : ℕ) (x u : ℝ) : ℝ≥0∞ :=
  (deningerWindow i).indicator
    (fun p : ℝ × ℝ => ENNReal.ofReal (p.1 ^ r) * ‖deningerLogPullDeriv h p.2‖ₑ) (x, u)

theorem deningerWindowKernelPow_measurable (h : 𝓢(ℝ, ℂ)) (i r : ℕ) :
    Measurable (Function.uncurry (deningerWindowKernelPow h i r)) := by
  have h1 : Measurable fun p : ℝ × ℝ => ENNReal.ofReal (p.1 ^ r) :=
    ((measurable_fst : Measurable fun p : ℝ × ℝ => p.1).pow_const r).ennreal_ofReal
  have h2 : Measurable fun p : ℝ × ℝ => ‖deningerLogPullDeriv h p.2‖ₑ :=
    ((deningerLogPullDeriv_measurable h).comp measurable_snd).enorm
  exact (h1.mul h2).indicator (deningerWindow_measurableSet i)

/-- **The `u`-slice of the weighted kernel is the derivative times the window moment.** -/
theorem deningerWindowKernelPow_slice (h : 𝓢(ℝ, ℂ)) {i : ℕ} (hi : 0 < i) (r : ℕ) {u : ℝ}
    (hu : 0 < u) :
    (∫⁻ x in Set.Ioi (0 : ℝ), deningerWindowKernelPow h i r x u)
      = ‖deningerLogPullDeriv h u‖ₑ *
        ENNReal.ofReal (u ^ (r + 1) / ((r : ℝ) + 1) *
          (1 / (i : ℝ) ^ (r + 1) - 1 / ((i : ℝ) + 1) ^ (r + 1))) := by
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
  have hfun : ∀ x : ℝ, deningerWindowKernelPow h i r x u
      = S.indicator (fun y : ℝ =>
        ENNReal.ofReal (y ^ r) * ‖deningerLogPullDeriv h u‖ₑ) x := by
    intro x
    by_cases hx : x ∈ S
    · rw [Set.indicator_of_mem hx, deningerWindowKernelPow,
        Set.indicator_of_mem (show (x, u) ∈ deningerWindow i from hx)]
    · rw [Set.indicator_of_notMem hx, deningerWindowKernelPow,
        Set.indicator_of_notMem (show (x, u) ∉ deningerWindow i from hx)]
  rw [lintegral_congr hfun, lintegral_indicator hSmeas, Measure.restrict_restrict hSmeas,
    Set.inter_eq_left.mpr hSsub, lintegral_mul_const' _ _ enorm_ne_top, hSeq,
    Measure.restrict_congr_set Ioc_ae_eq_Icc.symm, deningerWindowPow_lintegral hi r hu,
    mul_comm]

/-- **The two orders of integration agree** for the weighted kernel. -/
theorem deningerWindowKernelPow_swap (h : 𝓢(ℝ, ℂ)) (i r : ℕ) :
    (∫⁻ x in Set.Ioi (0 : ℝ), ∫⁻ u in Set.Ioi (0 : ℝ), deningerWindowKernelPow h i r x u)
      = ∫⁻ u in Set.Ioi (0 : ℝ), ∫⁻ x in Set.Ioi (0 : ℝ),
        deningerWindowKernelPow h i r x u :=
  lintegral_lintegral_swap (deningerWindowKernelPow_measurable h i r).aemeasurable

end

end RHTower
