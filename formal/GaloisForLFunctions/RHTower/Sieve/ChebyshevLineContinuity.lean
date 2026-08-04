import GaloisForLFunctions.RHTower.Sieve.ChebyshevRightLineBound
import GaloisForLFunctions.RHTower.Sieve.EdgeBoundsSharp

/-!
# Continuity of the Chebyshev integrand on the Perron line

The truncation-error estimate needs the integrand continuous along the line.  Right of the abscissa
`ζ` is analytic and nonvanishing, so `ζ'` is analytic there too and the quotient is continuous.

Analyticity of the derivative is what makes this immediate: `deriv` of an analytic function is
analytic, whereas differentiability alone would say nothing about `ζ'` being continuous.
-/

namespace RHTower.Sieve

open Complex MeasureTheory GaloisForLFunctions.HTGeometry

/-- `ζ` is analytic away from the pole. -/
theorem analyticAt_riemannZeta_of_ne_one {s : ℂ} (hs : s ≠ 1) :
    AnalyticAt ℂ riemannZeta s := by
  have hdiff : DifferentiableOn ℂ riemannZeta ({1}ᶜ : Set ℂ) :=
    differentiableOn_riemannZeta_of_ne_one (fun w hw => by simpa using hw)
  exact (hdiff.analyticOnNhd isOpen_compl_singleton) s (by simpa using hs)

/-- **The Chebyshev integrand is continuous on the Perron line.** -/
theorem continuous_neg_logDeriv_line {d : ℝ} (hd : 1 < d) :
    Continuous fun y : ℝ =>
      -(deriv riemannZeta ((d : ℂ) + (y : ℝ) * Complex.I))
        / riemannZeta ((d : ℂ) + (y : ℝ) * Complex.I) := by
  refine continuous_iff_continuousAt.2 fun y => ?_
  have hre : ((d : ℂ) + (y : ℝ) * Complex.I).re = d := by simp
  have hs : ((d : ℂ) + (y : ℝ) * Complex.I) ≠ 1 := by
    intro h
    rw [h] at hre
    simp at hre
    linarith
  have hz : riemannZeta ((d : ℂ) + (y : ℝ) * Complex.I) ≠ 0 :=
    riemannZeta_ne_zero_of_one_le_re (by rw [hre]; linarith)
  have hana := analyticAt_riemannZeta_of_ne_one hs
  have hin : Continuous fun u : ℝ => ((d : ℂ) + (u : ℝ) * Complex.I) := by fun_prop
  have hnum : ContinuousAt (fun z : ℂ => -(deriv riemannZeta z)) _ :=
    (hana.deriv.continuousAt).neg
  have hden : ContinuousAt riemannZeta _ := hana.continuousAt
  have hquot : ContinuousAt (fun z : ℂ => -(deriv riemannZeta z) / riemannZeta z)
      ((d : ℂ) + (y : ℝ) * Complex.I) := hnum.div hden hz
  exact ContinuousAt.comp
    (g := fun z : ℂ => -(deriv riemannZeta z) / riemannZeta z)
    (f := fun u : ℝ => ((d : ℂ) + (u : ℝ) * Complex.I)) hquot hin.continuousAt

/-- **The truncation error for the Chebyshev Perron integral.** -/
theorem norm_truncation_error_chebyshev {N H : ℝ} (hN : 0 < N) (hH : 0 < H) {d T C : ℝ}
    (hd : 1 < d) (hT : 1 ≤ T)
    (hbd : ∀ s : ℂ, 0 < s.re → s.re ≤ d →
      |s.im| ^ (1 + 1) * ‖mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) s‖ ≤ C) :
    ‖(∫ y : ℝ, (-(deriv riemannZeta ((d : ℂ) + (y : ℝ) * Complex.I))
            / riemannZeta ((d : ℂ) + (y : ℝ) * Complex.I))
          * mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) ((d : ℂ) + (y : ℝ) * Complex.I))
        - ∫ y : ℝ in (-T)..T, (-(deriv riemannZeta ((d : ℂ) + (y : ℝ) * Complex.I))
            / riemannZeta ((d : ℂ) + (y : ℝ) * Complex.I))
          * mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ))
              ((d : ℂ) + (y : ℝ) * Complex.I)‖
      ≤ 2 * ((∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-d)) * C) / T := by
  refine norm_truncation_error_le (N := N) (H := H) (d := d) (T := T) (C := C)
    (M := ∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-d))
    (F := fun s => -(deriv riemannZeta s) / riemannZeta s)
    hN hH (by linarith) hT tsum_vonMangoldt_rpow_nonneg hbd
    (continuous_neg_logDeriv_line hd) (fun y => norm_neg_logDeriv_le_line hd)

end RHTower.Sieve
