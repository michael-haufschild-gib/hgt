import GaloisForLFunctions.RHTower.Sieve.ZetaLogDerivRegular
import GaloisForLFunctions.RHTower.Sieve.InvZetaProductShift

/-!
# Shifting the regular part of `-ζ'/ζ`

The regular part `zetaLogDerivReg = -G'/G` is holomorphic wherever the entire unit `G = (s-1)ζ(s)`
is nonvanishing — which off the pole means wherever `ζ` is, and *at* the pole holds automatically
since `G(1) = 1`.  So on a zero-free rectangle it satisfies the same Cauchy identity as `invZeta`,
and the contour may be shifted across the abscissa with no residue from this part.

The residue of `-ζ'/ζ` therefore comes entirely from the separated pole term `1/(s-1)`, which is the
statement that the prime number theorem's main term is the pole and nothing else.
-/

namespace RHTower.Sieve

open Complex MeasureTheory RHTower GaloisForLFunctions.HTGeometry

/-- The regular part is holomorphic on a zero-free rectangle. -/
theorem differentiableOn_zetaLogDerivReg_rect {c d T : ℝ}
    (h : ∀ s ∈ Set.uIcc c d ×ℂ Set.uIcc (-T) T, s ≠ 1 → riemannZeta s ≠ 0) :
    DifferentiableOn ℂ zetaLogDerivReg (Set.uIcc c d ×ℂ Set.uIcc (-T) T) := by
  intro s hs
  rcases eq_or_ne s 1 with rfl | hs1
  · exact differentiableAt_zetaLogDerivReg_one.differentiableWithinAt
  · exact (differentiableAt_zetaLogDerivReg
      ((zetaResidueUnit_ne_zero_iff hs1).2 (h s hs hs1))).differentiableWithinAt

/-- **Holomorphy of the regular Chebyshev integrand.** -/
theorem differentiableOn_zetaLogDerivRegW_rect {N H : ℝ} (hH : 0 < H) {c d T : ℝ} (hc : 0 < c)
    (hcd : c ≤ d)
    (h : ∀ s ∈ Set.uIcc c d ×ℂ Set.uIcc (-T) T, s ≠ 1 → riemannZeta s ≠ 0) :
    DifferentiableOn ℂ
      (fun s => zetaLogDerivReg s * mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) s)
      (Set.uIcc c d ×ℂ Set.uIcc (-T) T) :=
  (differentiableOn_zetaLogDerivReg_rect h).mul
    ((differentiableOn_mellin_smoothWeight_strip hH hc).mono (rect_subset_verticalStrip hcd T))

/-- **The truncated contour shift for the regular part.**  No residue: the regular part is
holomorphic across the abscissa, pole included. -/
theorem integral_zetaLogDerivRegW_vertical_sub_eq_horizontal_rect {N H : ℝ} (hH : 0 < H)
    {c d T : ℝ} (hc : 0 < c) (hcd : c ≤ d)
    (h : ∀ s ∈ Set.uIcc c d ×ℂ Set.uIcc (-T) T, s ≠ 1 → riemannZeta s ≠ 0) :
    (Complex.I • (∫ y : ℝ in (-T)..T, zetaLogDerivReg ((d : ℂ) + (y : ℝ) * Complex.I)
          * mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) ((d : ℂ) + (y : ℝ) * Complex.I)))
        - Complex.I • (∫ y : ℝ in (-T)..T, zetaLogDerivReg ((c : ℂ) + (y : ℝ) * Complex.I)
          * mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) ((c : ℂ) + (y : ℝ) * Complex.I))
      = (∫ x : ℝ in c..d, zetaLogDerivReg ((x : ℂ) + ((T : ℝ) : ℂ) * Complex.I)
            * mellin (fun x' : ℝ => ((smoothWeight N H x' : ℝ) : ℂ))
                ((x : ℂ) + ((T : ℝ) : ℂ) * Complex.I))
        - ∫ x : ℝ in c..d, zetaLogDerivReg ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I)
            * mellin (fun x' : ℝ => ((smoothWeight N H x' : ℝ) : ℂ))
                ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I) :=
  integral_vertical_sub_eq_horizontal_rect T (differentiableOn_zetaLogDerivRegW_rect hH hc hcd h)

/-- **The Chebyshev integrand splits.**  On a zero-free rectangle, away from the pole, the Perron
integrand is the pole term plus the regular part. -/
theorem chebyshev_integrand_split {N H : ℝ} {s : ℂ} (hs : s ≠ 1) (hz : riemannZeta s ≠ 0) :
    (-(deriv riemannZeta s) / riemannZeta s)
        * mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) s
      = (s - 1)⁻¹ * mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) s
        + zetaLogDerivReg s * mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) s := by
  have hsplit := neg_logDeriv_riemannZeta_eq_of_ne_zero hs hz
  rw [logDeriv_apply] at hsplit
  rw [show -(deriv riemannZeta s) / riemannZeta s = -(deriv riemannZeta s / riemannZeta s) by ring,
    hsplit]
  ring

end RHTower.Sieve
