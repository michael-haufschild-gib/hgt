import GaloisForLFunctions.HTGeometry.IntervalMeanSquareMoment

/-!
# The mixed first moment against the Perron kernel

Steps 3 and 5 of Matomäki–Teräväinen §7 (`../../../docs/drafts/pipeline/1-in-progress/matomaki-teravainen-e3-lean-programme.md`):
Cauchy–Schwarz pairs the two factors, and the dyadic split pays each block by the two affine mean
squares.  Both halves are already corpus theorems
(`HTGeometry.IntervalMeanSquareMoment.integral_norm_mul_norm_mul_kernel_le`); what is added here is
the Perron kernel `min(x/t, h)` in a globally continuous form and the specialisation to a *linear*
majorant for the first factor — the shape `(5.2)` supplies, since its right-hand side is
`(T/(x/h))·(log x)^{-2-2ε}`, proportional to the height with no constant term.

The output is an explicit inequality: a `√height` term and a term linear in the number of dyadic
blocks.  Nothing here is asymptotic and nothing is assumed beyond the two mean-square majorants.
-/

namespace RHTower.Sieve

open MeasureTheory

noncomputable section

/-- The Perron kernel `min(x/t, h)`, extended below the cutoff so as to be globally continuous.
On `[t₀, ∞)` it agrees with `min(x/t, h)`. -/
def perronKernel (x h t₀ : ℝ) : ℝ → ℝ := fun t => min (x / max t t₀) h

theorem continuous_perronKernel {x h t₀ : ℝ} (ht₀ : 0 < t₀) :
    Continuous (perronKernel x h t₀) := by
  have hden : Continuous fun t : ℝ => max t t₀ := continuous_id.max continuous_const
  have hne : ∀ t : ℝ, max t t₀ ≠ 0 := by
    intro t
    exact ne_of_gt (lt_of_lt_of_le ht₀ (le_max_right t t₀))
  exact (continuous_const.div hden hne).min continuous_const

theorem perronKernel_le_div {x h t₀ t : ℝ} (ht : t₀ ≤ t) :
    perronKernel x h t₀ t ≤ x / t := by
  have hmax : max t t₀ = t := max_eq_left ht
  rw [perronKernel, hmax]
  exact min_le_left _ _

theorem perronKernel_nonneg {x h t₀ t : ℝ} (hx : 0 ≤ x) (hh : 0 ≤ h) (ht₀ : 0 < t₀) :
    0 ≤ perronKernel x h t₀ t := by
  have hpos : 0 < max t t₀ := lt_of_lt_of_le ht₀ (le_max_right t t₀)
  rw [perronKernel]
  exact le_min (by positivity) hh

/-- **The mixed first moment against the Perron kernel.**  `A` carries a linear mean-square
majorant (the shape of `(5.2)`), `B` an affine one (the shape of `(FS7)`). -/
theorem integral_mixed_moment_perron_le {A B : ℝ → ℂ} (hA : Continuous A) (hB : Continuous B)
    {κA QB κB x h t₀ : ℝ} (hκA : 0 ≤ κA) (hQB : 0 ≤ QB) (hκB : 0 ≤ κB)
    (hx : 0 ≤ x) (ht₀ : 0 < t₀)
    (hmsA : ∀ U : ℝ, t₀ ≤ U → (∫ t in Set.Icc (-U) U, ‖A t‖ ^ 2) ≤ κA * U)
    (hmsB : ∀ U : ℝ, t₀ ≤ U → (∫ t in Set.Icc (-U) U, ‖B t‖ ^ 2) ≤ QB + κB * U) (M : ℕ) :
    (∫ t in t₀..(t₀ * 2 ^ M), (‖A t‖ * ‖B t‖) * perronKernel x h t₀ t)
      ≤ (x * (Real.sqrt κA * Real.sqrt QB) * Real.sqrt 2 / Real.sqrt t₀)
            * (1 - Real.sqrt 2 / 2)⁻¹
        + 2 * x * (Real.sqrt κA * Real.sqrt κB) * M := by
  have hmsA' : ∀ U : ℝ, t₀ ≤ U → (∫ t in Set.Icc (-U) U, ‖A t‖ ^ 2) ≤ 0 + κA * U := by
    intro U hU
    simpa using hmsA U hU
  have hmain := GaloisForLFunctions.HTGeometry.integral_norm_mul_norm_mul_kernel_le
    (A := A) (B := B) hA hB
    (G := perronKernel x h t₀) (continuous_perronKernel ht₀)
    (QA := 0) (κA := κA) (QB := QB) (κB := κB) (C := x) (t₀ := t₀)
    le_rfl hκA hQB hκB hx ht₀ hmsA' hmsB M
    (fun t ht _ => perronKernel_le_div ht)
  refine le_trans hmain (le_of_eq ?_)
  rw [Real.sqrt_zero]
  ring

end

end RHTower.Sieve
