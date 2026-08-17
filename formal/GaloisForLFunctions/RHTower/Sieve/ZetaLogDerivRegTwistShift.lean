import GaloisForLFunctions.RHTower.Sieve.ZetaLogDerivRegShift
import GaloisForLFunctions.RHTower.Sieve.InvZetaTwistShift

/-!
# The contour shift for the twisted regular Chebyshev integrand

The Perron integrand of the twisted von Mangoldt function is `-ζ'/ζ(s + iτ)·W(s)`.  Its whole pole
sits in the separated term `1/(s + iτ - 1)`; the remaining factor is the regular part
`zetaLogDerivReg = -G'/G` with `G(s) = (s-1)ζ(s)` entire and `G(1) = 1`, which is holomorphic
wherever `ζ` is nonvanishing, the abscissa included.

Holomorphy of `s ↦ zetaLogDerivReg(s + iτ)` on a rectangle `[c,d] × [-T,T]` is holomorphy of
`zetaLogDerivReg` on the translated rectangle, contained in the symmetric rectangle at the enlarged
height `|τ| + T`.  So the four-edge identity transfers with no new analysis and no residue: the
twist costs only the passage from height `T` to height `|τ| + T`, which is exactly what the
zero-free region charges for working further up the strip.
-/

namespace RHTower.Sieve

open Complex MeasureTheory GaloisForLFunctions.HTGeometry

/-- Holomorphy of the twisted regular part on a rectangle, from the zero-free hypothesis at the
enlarged height. -/
theorem differentiableOn_zetaLogDerivRegTwist_rect {c d T : ℝ} (τ : ℝ) (hT : 0 ≤ T)
    (h : ∀ s ∈ Set.uIcc c d ×ℂ Set.uIcc (-(|τ| + T)) (|τ| + T), s ≠ 1 → riemannZeta s ≠ 0) :
    DifferentiableOn ℂ (fun s => zetaLogDerivReg (s + (τ : ℂ) * Complex.I))
      (Set.uIcc c d ×ℂ Set.uIcc (-T) T) := by
  have hcomp : DifferentiableOn ℂ (zetaLogDerivReg ∘ fun s : ℂ => s + (τ : ℂ) * Complex.I)
      (Set.uIcc c d ×ℂ Set.uIcc (-T) T) :=
    DifferentiableOn.comp (differentiableOn_zetaLogDerivReg_rect h)
      ((differentiable_id.add_const ((τ : ℂ) * Complex.I)).differentiableOn)
      (mapsTo_add_mul_I τ hT)
  exact hcomp

/-- **Holomorphy of the twisted regular Chebyshev integrand on a rectangle.** -/
theorem differentiableOn_zetaLogDerivRegTwistW_rect {N H : ℝ} (hH : 0 < H) {c d T : ℝ} (τ : ℝ)
    (hc : 0 < c) (hcd : c ≤ d) (hT : 0 ≤ T)
    (h : ∀ s ∈ Set.uIcc c d ×ℂ Set.uIcc (-(|τ| + T)) (|τ| + T), s ≠ 1 → riemannZeta s ≠ 0) :
    DifferentiableOn ℂ
      (fun s => zetaLogDerivReg (s + (τ : ℂ) * Complex.I)
        * mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) s)
      (Set.uIcc c d ×ℂ Set.uIcc (-T) T) :=
  (differentiableOn_zetaLogDerivRegTwist_rect τ hT h).mul
    ((differentiableOn_mellin_smoothWeight_strip hH hc).mono (rect_subset_verticalStrip hcd T))

/-- **The truncated contour shift for the twisted regular Chebyshev integrand.**  No residue: the
whole pole of `-ζ'/ζ` sits in the separated term `1/(s-1)`, so the regular part crosses the abscissa
freely.  The twist costs only the passage from height `T` to height `|τ| + T`. -/
theorem integral_zetaLogDerivRegTwistW_vertical_sub_eq_horizontal_rect {N H : ℝ} (hH : 0 < H)
    {c d T : ℝ} (τ : ℝ) (hc : 0 < c) (hcd : c ≤ d) (hT : 0 ≤ T)
    (h : ∀ s ∈ Set.uIcc c d ×ℂ Set.uIcc (-(|τ| + T)) (|τ| + T), s ≠ 1 → riemannZeta s ≠ 0) :
    (Complex.I • (∫ y : ℝ in (-T)..T,
          zetaLogDerivReg ((d : ℂ) + (y : ℝ) * Complex.I + (τ : ℂ) * Complex.I)
            * mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ))
                ((d : ℂ) + (y : ℝ) * Complex.I)))
        - Complex.I • (∫ y : ℝ in (-T)..T,
          zetaLogDerivReg ((c : ℂ) + (y : ℝ) * Complex.I + (τ : ℂ) * Complex.I)
            * mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ))
                ((c : ℂ) + (y : ℝ) * Complex.I))
      = (∫ x : ℝ in c..d,
            zetaLogDerivReg ((x : ℂ) + ((T : ℝ) : ℂ) * Complex.I + (τ : ℂ) * Complex.I)
              * mellin (fun x' : ℝ => ((smoothWeight N H x' : ℝ) : ℂ))
                  ((x : ℂ) + ((T : ℝ) : ℂ) * Complex.I))
        - ∫ x : ℝ in c..d,
            zetaLogDerivReg ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I + (τ : ℂ) * Complex.I)
              * mellin (fun x' : ℝ => ((smoothWeight N H x' : ℝ) : ℂ))
                  ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I) :=
  integral_vertical_sub_eq_horizontal_rect T
    (differentiableOn_zetaLogDerivRegTwistW_rect hH τ hc hcd hT h)

end RHTower.Sieve
