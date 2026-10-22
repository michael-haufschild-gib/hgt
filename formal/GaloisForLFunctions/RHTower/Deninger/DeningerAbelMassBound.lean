import GaloisForLFunctions.RHTower.Deninger.DeningerAbelWindowSwap

/-!
# The mass of one Abel difference

Putting the fundamental theorem of calculus, the window exchange and the slice measure together:
one Abel difference has total mass at most `1/(i(i+1))` times the first weighted moment of the
pullback derivative.

This is the last analytic step of the `L¹` estimate for the canonical Möbius preimage — summing it
against `|M(i)|` lands on the already-proved inverse-square series.

* `deningerAbelDifference_enorm_le` : the pointwise bound by the window kernel.
* `deningerAbelDifference_mass_le` : **one Abel difference costs `1/(i(i+1))`.**
-/

namespace RHTower

open MeasureTheory SchwartzMap ENNReal

noncomputable section

/-- The pointwise bound: the Abel difference is dominated by the window kernel. -/
theorem deningerAbelDifference_enorm_le (h : 𝓢(ℝ, ℂ)) {i : ℕ} (hi : 0 < i) {x : ℝ}
    (hx : 0 < x) :
    ‖deningerLogPull h (((i : ℝ) + 1) * x) - deningerLogPull h ((i : ℝ) * x)‖ₑ
      ≤ ∫⁻ u in Set.Ioi (0 : ℝ), deningerWindowKernel h i x u := by
  have hir : (0 : ℝ) < (i : ℝ) := by exact_mod_cast hi
  have hlo : (0 : ℝ) < (i : ℝ) * x := mul_pos hir hx
  have hsub : Set.Ioc ((i : ℝ) * x) (((i : ℝ) + 1) * x) ⊆ Set.Ioi 0 := fun y hy =>
    lt_trans hlo hy.1
  rw [deningerAbelDifference_eq h hi hx]
  refine le_trans (enorm_integral_le_lintegral_enorm _) ?_
  have hcongr : ∀ u ∈ Set.Ioc ((i : ℝ) * x) (((i : ℝ) + 1) * x),
      ‖deningerLogPullDeriv h u‖ₑ = deningerWindowKernel h i x u := by
    intro u hu
    rw [deningerWindowKernel, Set.indicator_of_mem]
    exact ⟨le_of_lt hu.1, hu.2⟩
  rw [setLIntegral_congr_fun measurableSet_Ioc hcongr]
  exact lintegral_mono_set hsub

/-- **One Abel difference costs the coefficient `1/(i(i+1))`.** -/
theorem deningerAbelDifference_mass_le (h : 𝓢(ℝ, ℂ)) {i : ℕ} (hi : 0 < i) :
    (∫⁻ x in Set.Ioi (0 : ℝ),
        ‖deningerLogPull h (((i : ℝ) + 1) * x) - deningerLogPull h ((i : ℝ) * x)‖ₑ)
      ≤ ENNReal.ofReal (1 / ((i : ℝ) * ((i : ℝ) + 1))) *
        ∫⁻ u in Set.Ioi (0 : ℝ), ENNReal.ofReal (u * ‖deningerLogPullDeriv h u‖) := by
  have hir : (0 : ℝ) < (i : ℝ) := by exact_mod_cast hi
  have hi1 : (0 : ℝ) < (i : ℝ) + 1 := by linarith
  have hstep1 : (∫⁻ x in Set.Ioi (0 : ℝ),
      ‖deningerLogPull h (((i : ℝ) + 1) * x) - deningerLogPull h ((i : ℝ) * x)‖ₑ)
      ≤ ∫⁻ x in Set.Ioi (0 : ℝ), ∫⁻ u in Set.Ioi (0 : ℝ), deningerWindowKernel h i x u := by
    refine setLIntegral_mono' measurableSet_Ioi fun x hx => ?_
    exact deningerAbelDifference_enorm_le h hi hx
  have hstep2 : (∫⁻ x in Set.Ioi (0 : ℝ), ∫⁻ u in Set.Ioi (0 : ℝ),
      deningerWindowKernel h i x u)
      = ∫⁻ u in Set.Ioi (0 : ℝ), ‖deningerLogPullDeriv h u‖ₑ *
        ENNReal.ofReal (u / ((i : ℝ) * ((i : ℝ) + 1))) := by
    rw [deningerWindowKernel_swap h i]
    refine setLIntegral_congr_fun measurableSet_Ioi fun u hu => ?_
    exact deningerWindowKernel_slice h hi hu
  have hstep3 : (∫⁻ u in Set.Ioi (0 : ℝ), ‖deningerLogPullDeriv h u‖ₑ *
      ENNReal.ofReal (u / ((i : ℝ) * ((i : ℝ) + 1))))
      = ENNReal.ofReal (1 / ((i : ℝ) * ((i : ℝ) + 1))) *
        ∫⁻ u in Set.Ioi (0 : ℝ), ENNReal.ofReal (u * ‖deningerLogPullDeriv h u‖) := by
    rw [← lintegral_const_mul' _ _ (by simp)]
    refine setLIntegral_congr_fun measurableSet_Ioi fun u hu => ?_
    have hu0 : (0 : ℝ) < u := hu
    have hsplit : u / ((i : ℝ) * ((i : ℝ) + 1))
        = (1 / ((i : ℝ) * ((i : ℝ) + 1))) * u := by ring
    rw [hsplit, ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_mul (le_of_lt hu0), ← ofReal_norm]
    ring
  calc (∫⁻ x in Set.Ioi (0 : ℝ),
      ‖deningerLogPull h (((i : ℝ) + 1) * x) - deningerLogPull h ((i : ℝ) * x)‖ₑ)
      ≤ ∫⁻ x in Set.Ioi (0 : ℝ), ∫⁻ u in Set.Ioi (0 : ℝ),
        deningerWindowKernel h i x u := hstep1
    _ = ∫⁻ u in Set.Ioi (0 : ℝ), ‖deningerLogPullDeriv h u‖ₑ *
        ENNReal.ofReal (u / ((i : ℝ) * ((i : ℝ) + 1))) := hstep2
    _ = ENNReal.ofReal (1 / ((i : ℝ) * ((i : ℝ) + 1))) *
        ∫⁻ u in Set.Ioi (0 : ℝ), ENNReal.ofReal (u * ‖deningerLogPullDeriv h u‖) := hstep3

end

end RHTower
