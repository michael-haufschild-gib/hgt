import GaloisForLFunctions.RHTower.Sieve.PoleTermSplit
import GaloisForLFunctions.RHTower.Sieve.ZetaLogDerivRegBound

/-!
# The Chebyshev integrand in three pieces

Combining the two splittings — the pole of `-ζ'/ζ` and the pole of `W(s)/(s-1)` — writes the Perron
integrand as

    (-ζ'/ζ)(s)·W(s) = dslope W 1 s + W(1)·(s-1)⁻¹ + zetaLogDerivReg s · W(s),

valid off the pole and away from the zeros of `ζ`.  The first two summands involve no zeta at all
and the third is the only one carrying analytic content.  On the contour: the first shifts with no
residue, the second contributes `2πi·W(1)`, and the third shifts with no residue on a zero-free
rectangle.
-/

namespace RHTower.Sieve

open Complex GaloisForLFunctions.HTGeometry

/-- **The Chebyshev integrand, fully split.** -/
theorem chebyshev_integrand_split_full {N H : ℝ} {s : ℂ} (hs : s ≠ 1)
    (hz : riemannZeta s ≠ 0) :
    (-(deriv riemannZeta s) / riemannZeta s)
        * mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) s
      = dslope (mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ))) 1 s
        + mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) 1 * (s - 1)⁻¹
        + zetaLogDerivReg s * mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) s := by
  rw [chebyshev_integrand_split (N := N) (H := H) hs hz,
    mellin_div_sub_one_split (N := N) (H := H) hs]
  ring

/-- **The integrand on the Perron line.**  Right of the abscissa `ζ` has no zeros, so the splitting
holds on the whole line. -/
theorem chebyshev_integrand_split_line {N H : ℝ} {d y : ℝ} (hd : 1 < d) :
    (-(deriv riemannZeta ((d : ℂ) + (y : ℝ) * Complex.I))
          / riemannZeta ((d : ℂ) + (y : ℝ) * Complex.I))
        * mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ))
            ((d : ℂ) + (y : ℝ) * Complex.I)
      = dslope (mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ))) 1
            ((d : ℂ) + (y : ℝ) * Complex.I)
        + mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) 1
            * (((d : ℂ) + (y : ℝ) * Complex.I) - 1)⁻¹
        + zetaLogDerivReg ((d : ℂ) + (y : ℝ) * Complex.I)
            * mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ))
                ((d : ℂ) + (y : ℝ) * Complex.I) := by
  have hre : ((d : ℂ) + (y : ℝ) * Complex.I).re = d := by simp
  have hs : ((d : ℂ) + (y : ℝ) * Complex.I) ≠ 1 := by
    intro h
    rw [h] at hre
    simp at hre
    linarith
  have hz : riemannZeta ((d : ℂ) + (y : ℝ) * Complex.I) ≠ 0 :=
    riemannZeta_ne_zero_of_one_le_re (by rw [hre]; linarith)
  exact chebyshev_integrand_split_full hs hz

end RHTower.Sieve
