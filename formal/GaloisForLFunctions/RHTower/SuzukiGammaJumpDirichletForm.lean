import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.MeasureTheory.Group.Integral

/-!
# The Gamma jump is a Dirichlet form

The second difference that defines the Gamma jump,

`(R v)(L) = ∫₀^∞ [2 v(L) - v(L+s) - v(L-s)] / (e^s - 1) ds`,

pairs with `v` into a positive quadratic form.  The mechanism is entirely elementary and needs no
Fourier transform: at each shift `s` the translation invariance of Lebesgue measure turns the
symmetrized pairing into the square of a difference,

`2‖v‖² - 2 Re ⟪v, v(·+s)⟫ = ‖v - v(·+s)‖²  ≥ 0`,

so integrating against the positive weight `1/(e^s-1)` keeps the sign.  This is the positivity that
the terminal coercive estimate of the flat-flux system uses for `R`.
-/

open MeasureTheory Filter

namespace RHTower

noncomputable section

/-- **The shift Dirichlet identity.**  The squared difference of a profile and its translate is
the symmetrized pairing. -/
theorem integral_normSq_sub_shift {v : ℝ → ℂ} (hmeas : AEStronglyMeasurable v volume)
    (hint : Integrable (fun L => ‖v L‖ ^ 2) volume) (s : ℝ) :
    (∫ L : ℝ, ‖v L - v (L + s)‖ ^ 2)
      = 2 * (∫ L : ℝ, ‖v L‖ ^ 2)
        - 2 * ∫ L : ℝ, (v L * (starRingEnd ℂ) (v (L + s))).re := by
  have hshiftMeas : AEStronglyMeasurable (fun L : ℝ => v (L + s)) volume :=
    hmeas.comp_measurePreserving (measurePreserving_add_right volume s)
  have hshift : Integrable (fun L : ℝ => ‖v (L + s)‖ ^ 2) volume := by
    have h := hint.comp_add_right s
    exact h
  have hcross : Integrable (fun L : ℝ => (v L * (starRingEnd ℂ) (v (L + s))).re) volume := by
    have hbound : ∀ L : ℝ, ‖(v L * (starRingEnd ℂ) (v (L + s))).re‖
        ≤ (‖v L‖ ^ 2 + ‖v (L + s)‖ ^ 2) / 2 := by
      intro L
      have h1 : ‖(v L * (starRingEnd ℂ) (v (L + s))).re‖
          ≤ ‖v L * (starRingEnd ℂ) (v (L + s))‖ := by
        simpa using Complex.abs_re_le_norm (v L * (starRingEnd ℂ) (v (L + s)))
      have h2 : ‖v L * (starRingEnd ℂ) (v (L + s))‖ = ‖v L‖ * ‖v (L + s)‖ := by
        rw [norm_mul, RCLike.norm_conj]
      have h3 : ‖v L‖ * ‖v (L + s)‖ ≤ (‖v L‖ ^ 2 + ‖v (L + s)‖ ^ 2) / 2 := by
        nlinarith [sq_nonneg (‖v L‖ - ‖v (L + s)‖)]
      rw [h2] at h1
      linarith
    refine Integrable.mono' (g := fun L : ℝ => (‖v L‖ ^ 2 + ‖v (L + s)‖ ^ 2) / 2)
      ((hint.add hshift).div_const 2) ?_ (Filter.Eventually.of_forall hbound)
    have hprod : AEStronglyMeasurable
        (fun L : ℝ => v L * (starRingEnd ℂ) (v (L + s))) volume :=
      hmeas.mul (Complex.continuous_conj.comp_aestronglyMeasurable hshiftMeas)
    exact Complex.reCLM.continuous.comp_aestronglyMeasurable hprod
  have hexpand : ∀ L : ℝ, ‖v L - v (L + s)‖ ^ 2
      = ‖v L‖ ^ 2 + ‖v (L + s)‖ ^ 2 - 2 * (v L * (starRingEnd ℂ) (v (L + s))).re := by
    intro L
    simp [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.mul_re]
    ring
  have hshiftEq : (∫ L : ℝ, ‖v (L + s)‖ ^ 2) = ∫ L : ℝ, ‖v L‖ ^ 2 :=
    integral_add_right_eq_self (fun L => ‖v L‖ ^ 2) s
  calc (∫ L : ℝ, ‖v L - v (L + s)‖ ^ 2)
      = ∫ L : ℝ, (‖v L‖ ^ 2 + ‖v (L + s)‖ ^ 2
          - 2 * (v L * (starRingEnd ℂ) (v (L + s))).re) :=
        integral_congr_ae (Filter.Eventually.of_forall hexpand)
    _ = (∫ L : ℝ, ‖v L‖ ^ 2) + (∫ L : ℝ, ‖v (L + s)‖ ^ 2)
          - 2 * ∫ L : ℝ, (v L * (starRingEnd ℂ) (v (L + s))).re := by
        rw [show (fun L : ℝ => ‖v L‖ ^ 2 + ‖v (L + s)‖ ^ 2
            - 2 * (v L * (starRingEnd ℂ) (v (L + s))).re)
            = fun L : ℝ => ((fun L => ‖v L‖ ^ 2) + fun L => ‖v (L + s)‖ ^ 2) L
              - (fun L => 2 * (v L * (starRingEnd ℂ) (v (L + s))).re) L from rfl,
          integral_sub (hint.add hshift) (hcross.const_mul 2)]
        simp only [Pi.add_apply]
        rw [integral_add hint hshift, MeasureTheory.integral_const_mul]
    _ = 2 * (∫ L : ℝ, ‖v L‖ ^ 2)
          - 2 * ∫ L : ℝ, (v L * (starRingEnd ℂ) (v (L + s))).re := by
        rw [hshiftEq]
        ring

/-- **The Gamma jump form is positive at every shift.** -/
theorem gammaJump_shift_form_nonneg {v : ℝ → ℂ} (hmeas : AEStronglyMeasurable v volume)
    (hint : Integrable (fun L => ‖v L‖ ^ 2) volume) (s : ℝ) :
    0 ≤ 2 * (∫ L : ℝ, ‖v L‖ ^ 2)
      - 2 * ∫ L : ℝ, (v L * (starRingEnd ℂ) (v (L + s))).re := by
  rw [← integral_normSq_sub_shift hmeas hint s]
  exact integral_nonneg fun L => by positivity

end

end RHTower
