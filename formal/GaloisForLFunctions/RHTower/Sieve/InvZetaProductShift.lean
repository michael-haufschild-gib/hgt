import GaloisForLFunctions.RHTower.Sieve.MoebiusPerron
import GaloisForLFunctions.RHTower.Sieve.ZeroFreeRectangle
import GaloisForLFunctions.HTGeometry.SmoothWeightShift

/-!
# Shifting the Perron integrand

The contour identity proved for `invZeta` alone is not what the Perron argument needs: the object
integrated is the *product* `invZeta · W`, and Cauchy's theorem applies to the product.  The second
factor is holomorphic on every strip inside `Re s > 0`, so the product inherits holomorphy from
`invZeta` on a zero-free rectangle, and the truncated shift transfers verbatim.

Also recorded here is the identification of the Perron integrand: on `Re s > 1` the Dirichlet series
of `μ` is `1/ζ`, hence `invZeta`.  This is what lets the analytic estimates, all stated for
`invZeta`, act on the Perron formula.
-/

namespace RHTower.Sieve

open Complex MeasureTheory GaloisForLFunctions.HTGeometry

/-- **The Perron integrand is the regular reciprocal.**  On `Re s > 1` the Möbius Dirichlet series
is `1/ζ(s)`, which off the pole is `invZeta s`. -/
theorem tsum_moebius_cpow_eq_invZeta {s : ℂ} (hs : 1 < s.re) :
    (∑' n : ℕ, (ArithmeticFunction.moebius n : ℂ) * (n : ℂ) ^ (-s)) = invZeta s := by
  have hne : s ≠ 1 := by
    intro h
    rw [h] at hs
    simp at hs
  rw [tsum_cpow_neg_eq_LSeries (by simp) s, LSeries_moebius_eq_inv hs, invZeta_eq_inv hne]

/-- `invZeta` is continuous along a vertical line right of the abscissa. -/
theorem continuous_invZeta_line {c : ℝ} (hc : 1 < c) :
    Continuous fun y : ℝ => invZeta ((c : ℂ) + (y : ℝ) * Complex.I) := by
  refine continuous_iff_continuousAt.2 fun y => ?_
  have hre : ((c : ℂ) + (y : ℝ) * Complex.I).re = c := by simp
  have hne : ((c : ℂ) + (y : ℝ) * Complex.I) ≠ 1 := by
    intro h
    rw [h] at hre
    simp at hre
    linarith
  have hz : riemannZeta ((c : ℂ) + (y : ℝ) * Complex.I) ≠ 0 :=
    riemannZeta_ne_zero_of_one_le_re (by rw [hre]; linarith)
  have hin : Continuous fun u : ℝ => ((c : ℂ) + (u : ℝ) * Complex.I) := by fun_prop
  exact ContinuousAt.comp (g := invZeta) (f := fun u : ℝ => ((c : ℂ) + (u : ℝ) * Complex.I))
    ((differentiableAt_invZeta_of_zeta_ne_zero hne hz).continuousAt) hin.continuousAt

/-- **Holomorphy of the Perron integrand on a zero-free rectangle.** -/
theorem differentiableOn_invZetaW_rect {N H : ℝ} (hH : 0 < H) {c d T : ℝ} (hc : 0 < c)
    (hcd : c ≤ d)
    (h : ∀ s ∈ Set.uIcc c d ×ℂ Set.uIcc (-T) T, s ≠ 1 → riemannZeta s ≠ 0) :
    DifferentiableOn ℂ
      (fun s => invZeta s * mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) s)
      (Set.uIcc c d ×ℂ Set.uIcc (-T) T) :=
  (differentiableOn_invZeta_rect h).mul
    ((differentiableOn_mellin_smoothWeight_strip hH hc).mono (rect_subset_verticalStrip hcd T))

/-- **The truncated contour shift for the Perron integrand.**  The four-edge identity, with the only
hypothesis being that `ζ` has no zeros in the rectangle. -/
theorem integral_invZetaW_vertical_sub_eq_horizontal_rect {N H : ℝ} (hH : 0 < H) {c d T : ℝ}
    (hc : 0 < c) (hcd : c ≤ d)
    (h : ∀ s ∈ Set.uIcc c d ×ℂ Set.uIcc (-T) T, s ≠ 1 → riemannZeta s ≠ 0) :
    (Complex.I • (∫ y : ℝ in (-T)..T, invZeta ((d : ℂ) + (y : ℝ) * Complex.I)
          * mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) ((d : ℂ) + (y : ℝ) * Complex.I)))
        - Complex.I • (∫ y : ℝ in (-T)..T, invZeta ((c : ℂ) + (y : ℝ) * Complex.I)
          * mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) ((c : ℂ) + (y : ℝ) * Complex.I))
      = (∫ x : ℝ in c..d, invZeta ((x : ℂ) + ((T : ℝ) : ℂ) * Complex.I)
            * mellin (fun x' : ℝ => ((smoothWeight N H x' : ℝ) : ℂ))
                ((x : ℂ) + ((T : ℝ) : ℂ) * Complex.I))
        - ∫ x : ℝ in c..d, invZeta ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I)
            * mellin (fun x' : ℝ => ((smoothWeight N H x' : ℝ) : ℂ))
                ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I) :=
  integral_vertical_sub_eq_horizontal_rect T (differentiableOn_invZetaW_rect hH hc hcd h)

/-- **The shift, with the zero-free hypothesis discharged.**  At every height there is a genuine
rectangle crossing the abscissa on which the identity holds. -/
theorem exists_integral_invZetaW_shift {N H : ℝ} (hH : 0 < H) {T : ℝ} (hT : 0 ≤ T) :
    ∃ δ > 0, ∀ c d : ℝ, 1 - δ ≤ c → c ≤ 1 → 1 ≤ d → 0 < c →
      (Complex.I • (∫ y : ℝ in (-T)..T, invZeta ((d : ℂ) + (y : ℝ) * Complex.I)
            * mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) ((d : ℂ) + (y : ℝ) * Complex.I)))
          - Complex.I • (∫ y : ℝ in (-T)..T, invZeta ((c : ℂ) + (y : ℝ) * Complex.I)
            * mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) ((c : ℂ) + (y : ℝ) * Complex.I))
        = (∫ x : ℝ in c..d, invZeta ((x : ℂ) + ((T : ℝ) : ℂ) * Complex.I)
              * mellin (fun x' : ℝ => ((smoothWeight N H x' : ℝ) : ℂ))
                  ((x : ℂ) + ((T : ℝ) : ℂ) * Complex.I))
          - ∫ x : ℝ in c..d, invZeta ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I)
              * mellin (fun x' : ℝ => ((smoothWeight N H x' : ℝ) : ℂ))
                  ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I) := by
  obtain ⟨δ, hδ, hzf⟩ := exists_zero_free_rect hT
  exact ⟨δ, hδ, fun c d hc hc1 hd hc0 =>
    integral_invZetaW_vertical_sub_eq_horizontal_rect hH hc0 (le_trans hc1 hd)
      (hzf c d hc hc1 hd)⟩

end RHTower.Sieve
