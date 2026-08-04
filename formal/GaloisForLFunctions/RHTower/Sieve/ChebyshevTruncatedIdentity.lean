import GaloisForLFunctions.RHTower.Sieve.ChebyshevMainTerm

/-!
# The truncated Chebyshev identity

Assembling the Perron identity, the truncation, the three-piece split and the explicit pole
integral:

    2π ∑ₙ Λ(n)w(n)
      = (tail beyond height T)
        + ∫_{-T}^{T} dslope W 1
        + W(1)·2·arctan(T/(d-1))
        + ∫_{-T}^{T} zetaLogDerivReg·W.

The third summand is the main term, explicit and estimate-free; the first is bounded by the
truncation lemma, and the second and fourth are what the contour shift moves to the left edge.
-/

namespace RHTower.Sieve

open Complex MeasureTheory ArithmeticFunction GaloisForLFunctions.HTGeometry

/-- **The truncated Chebyshev identity.** -/
theorem tsum_vonMangoldt_truncated_identity {N H : ℝ} (hN : 0 < N) (hH : 0 < H) {d T : ℝ}
    (hd : 1 < d) :
    (2 * Real.pi : ℝ) • (∑' n : ℕ,
        ((vonMangoldt n : ℝ) : ℂ) * ((smoothWeight N H (n : ℝ) : ℝ) : ℂ))
      = ((∫ y : ℝ, (-(deriv riemannZeta ((d : ℂ) + (y : ℝ) * Complex.I))
              / riemannZeta ((d : ℂ) + (y : ℝ) * Complex.I))
            * mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ))
                ((d : ℂ) + (y : ℝ) * Complex.I))
          - ∫ y : ℝ in (-T)..T, (-(deriv riemannZeta ((d : ℂ) + (y : ℝ) * Complex.I))
              / riemannZeta ((d : ℂ) + (y : ℝ) * Complex.I))
            * mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ))
                ((d : ℂ) + (y : ℝ) * Complex.I))
        + (∫ y : ℝ in (-T)..T,
            dslope (mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ))) 1
              ((d : ℂ) + (y : ℝ) * Complex.I))
        + mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) 1
            * ((2 * Real.arctan (T / (d - 1)) : ℝ) : ℂ)
        + (∫ y : ℝ in (-T)..T, zetaLogDerivReg ((d : ℂ) + (y : ℝ) * Complex.I)
            * mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ))
                ((d : ℂ) + (y : ℝ) * Complex.I)) := by
  have hperron := tsum_vonMangoldt_smoothWeight_eq_logDeriv_integral hN hH hd
  have hsplitline : (∫ y : ℝ in (-T)..T, (-(deriv riemannZeta ((d : ℂ) + (y : ℝ) * Complex.I))
        / riemannZeta ((d : ℂ) + (y : ℝ) * Complex.I))
      * mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ))
          ((d : ℂ) + (y : ℝ) * Complex.I))
      = ∫ y : ℝ in (-T)..T, (dslope (mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ))) 1
            ((d : ℂ) + (y : ℝ) * Complex.I)
          + mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) 1
              * (((d : ℂ) + (y : ℝ) * Complex.I) - 1)⁻¹
          + zetaLogDerivReg ((d : ℂ) + (y : ℝ) * Complex.I)
              * mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ))
                  ((d : ℂ) + (y : ℝ) * Complex.I)) :=
    intervalIntegral.integral_congr (fun y _ => chebyshev_integrand_split_line hd)
  rw [hperron, hsplitline, integral_truncated_chebyshev_split hH hd,
    integral_pole_term_line hd]
  ring

end RHTower.Sieve
