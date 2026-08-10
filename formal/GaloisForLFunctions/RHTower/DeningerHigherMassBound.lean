import GaloisForLFunctions.RHTower.DeningerWindowSwapPow
import GaloisForLFunctions.RHTower.DeningerAbelMassBound

/-!
# The mass of one Abel difference at order `r`

The weighted window kernel is the unweighted one times `x^r`, a factor that does not depend on the
integration variable of the slice.  So the order-`r` mass bound is the order-`0` one with the
window length `u/(i(i+1))` replaced by the window moment
`(u^{r+1}/(r+1)) (i^{-(r+1)} - (i+1)^{-(r+1)})`, and the first weighted moment replaced by the
`(r+1)`-st.

* `deningerWindowKernelPow_eq` : the weighted kernel factors.
* `deningerAbelDifferencePow_mass_le` : **one Abel difference costs the order-`r` bracket.**
-/

namespace RHTower

open MeasureTheory SchwartzMap ENNReal

noncomputable section

/-- **The weighted kernel factors** as `x^r` times the unweighted one. -/
theorem deningerWindowKernelPow_eq (h : 𝓢(ℝ, ℂ)) (i r : ℕ) (x u : ℝ) :
    deningerWindowKernelPow h i r x u
      = ENNReal.ofReal (x ^ r) * deningerWindowKernel h i x u := by
  rw [deningerWindowKernelPow, deningerWindowKernel]
  by_cases hx : (x, u) ∈ deningerWindow i
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, mul_zero]

/-- The pointwise bound at order `r`: the weighted Abel difference is dominated by the weighted
window kernel. -/
theorem deningerAbelDifferencePow_enorm_le (h : 𝓢(ℝ, ℂ)) {i : ℕ} (hi : 0 < i) (r : ℕ) {x : ℝ}
    (hx : 0 < x) :
    ENNReal.ofReal (x ^ r) *
        ‖deningerLogPull h (((i : ℝ) + 1) * x) - deningerLogPull h ((i : ℝ) * x)‖ₑ
      ≤ ∫⁻ u in Set.Ioi (0 : ℝ), deningerWindowKernelPow h i r x u := by
  have hfac : (∫⁻ u in Set.Ioi (0 : ℝ), deningerWindowKernelPow h i r x u)
      = ENNReal.ofReal (x ^ r) * ∫⁻ u in Set.Ioi (0 : ℝ), deningerWindowKernel h i x u := by
    rw [← lintegral_const_mul' _ _ ofReal_ne_top]
    exact lintegral_congr fun u => deningerWindowKernelPow_eq h i r x u
  rw [hfac]
  exact mul_le_mul_right (deningerAbelDifference_enorm_le h hi hx) _

/-- **One Abel difference costs the order-`r` bracket.**  The dilation-window exchange at order `r`
turns the weighted mass of one difference into the order-`r` window bracket times the `(r+1)`-st
weighted moment of the pullback derivative. -/
theorem deningerAbelDifferencePow_mass_le (h : 𝓢(ℝ, ℂ)) {i : ℕ} (hi : 0 < i) (r : ℕ) :
    (∫⁻ x in Set.Ioi (0 : ℝ), ENNReal.ofReal (x ^ r) *
        ‖deningerLogPull h (((i : ℝ) + 1) * x) - deningerLogPull h ((i : ℝ) * x)‖ₑ)
      ≤ ENNReal.ofReal ((1 / ((r : ℝ) + 1)) *
          (1 / (i : ℝ) ^ (r + 1) - 1 / ((i : ℝ) + 1) ^ (r + 1))) *
        ∫⁻ u in Set.Ioi (0 : ℝ),
          ENNReal.ofReal (u ^ (r + 1) * ‖deningerLogPullDeriv h u‖) := by
  have hir : (0 : ℝ) < (i : ℝ) := by exact_mod_cast hi
  have hi1 : (0 : ℝ) < (i : ℝ) + 1 := by linarith
  have hbr : 0 ≤ 1 / (i : ℝ) ^ (r + 1) - 1 / ((i : ℝ) + 1) ^ (r + 1) := by
    have hmono : (i : ℝ) ^ (r + 1) ≤ ((i : ℝ) + 1) ^ (r + 1) :=
      pow_le_pow_left₀ hir.le (by linarith) _
    have := one_div_le_one_div_of_le (by positivity : (0 : ℝ) < (i : ℝ) ^ (r + 1)) hmono
    linarith
  have hstep1 : (∫⁻ x in Set.Ioi (0 : ℝ), ENNReal.ofReal (x ^ r) *
      ‖deningerLogPull h (((i : ℝ) + 1) * x) - deningerLogPull h ((i : ℝ) * x)‖ₑ)
      ≤ ∫⁻ x in Set.Ioi (0 : ℝ), ∫⁻ u in Set.Ioi (0 : ℝ),
        deningerWindowKernelPow h i r x u := by
    refine setLIntegral_mono' measurableSet_Ioi fun x hx => ?_
    exact deningerAbelDifferencePow_enorm_le h hi r hx
  have hstep2 : (∫⁻ x in Set.Ioi (0 : ℝ), ∫⁻ u in Set.Ioi (0 : ℝ),
      deningerWindowKernelPow h i r x u)
      = ∫⁻ u in Set.Ioi (0 : ℝ), ‖deningerLogPullDeriv h u‖ₑ *
        ENNReal.ofReal (u ^ (r + 1) / ((r : ℝ) + 1) *
          (1 / (i : ℝ) ^ (r + 1) - 1 / ((i : ℝ) + 1) ^ (r + 1))) := by
    rw [deningerWindowKernelPow_swap h i r]
    refine setLIntegral_congr_fun measurableSet_Ioi fun u hu => ?_
    exact deningerWindowKernelPow_slice h hi r hu
  have hstep3 : (∫⁻ u in Set.Ioi (0 : ℝ), ‖deningerLogPullDeriv h u‖ₑ *
      ENNReal.ofReal (u ^ (r + 1) / ((r : ℝ) + 1) *
        (1 / (i : ℝ) ^ (r + 1) - 1 / ((i : ℝ) + 1) ^ (r + 1))))
      = ENNReal.ofReal ((1 / ((r : ℝ) + 1)) *
          (1 / (i : ℝ) ^ (r + 1) - 1 / ((i : ℝ) + 1) ^ (r + 1))) *
        ∫⁻ u in Set.Ioi (0 : ℝ),
          ENNReal.ofReal (u ^ (r + 1) * ‖deningerLogPullDeriv h u‖) := by
    rw [← lintegral_const_mul' _ _ ofReal_ne_top]
    refine setLIntegral_congr_fun measurableSet_Ioi fun u hu => ?_
    have hu0 : (0 : ℝ) < u := hu
    have hsplit : u ^ (r + 1) / ((r : ℝ) + 1) *
        (1 / (i : ℝ) ^ (r + 1) - 1 / ((i : ℝ) + 1) ^ (r + 1))
        = ((1 / ((r : ℝ) + 1)) *
            (1 / (i : ℝ) ^ (r + 1) - 1 / ((i : ℝ) + 1) ^ (r + 1))) * u ^ (r + 1) := by
      ring
    rw [hsplit, ENNReal.ofReal_mul (mul_nonneg (by positivity) hbr),
      ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ u ^ (r + 1)), ← ofReal_norm]
    ring
  calc (∫⁻ x in Set.Ioi (0 : ℝ), ENNReal.ofReal (x ^ r) *
      ‖deningerLogPull h (((i : ℝ) + 1) * x) - deningerLogPull h ((i : ℝ) * x)‖ₑ)
      ≤ ∫⁻ x in Set.Ioi (0 : ℝ), ∫⁻ u in Set.Ioi (0 : ℝ),
        deningerWindowKernelPow h i r x u := hstep1
    _ = ∫⁻ u in Set.Ioi (0 : ℝ), ‖deningerLogPullDeriv h u‖ₑ *
        ENNReal.ofReal (u ^ (r + 1) / ((r : ℝ) + 1) *
          (1 / (i : ℝ) ^ (r + 1) - 1 / ((i : ℝ) + 1) ^ (r + 1))) := hstep2
    _ = ENNReal.ofReal ((1 / ((r : ℝ) + 1)) *
          (1 / (i : ℝ) ^ (r + 1) - 1 / ((i : ℝ) + 1) ^ (r + 1))) *
        ∫⁻ u in Set.Ioi (0 : ℝ),
          ENNReal.ofReal (u ^ (r + 1) * ‖deningerLogPullDeriv h u‖) := hstep3

end

end RHTower
