import GaloisForLFunctions.RHTower.Sieve.ChebyshevLineContinuity

/-!
# The Chebyshev Perron identity

Rewriting the Perron integrand as `-ζ'/ζ` gives the identity the contour argument consumes:

    2π · ∑ₙ Λ(n)·w(n)  =  ∫_ℝ (-ζ'/ζ)(d+iy) · W(d+iy) dy,     d > 1.

This is the exact analogue of `tsum_moebius_smoothWeight_eq_invZeta_integral`, with the difference
that the integrand has a pole inside the contour rather than a removable singularity.
-/

namespace RHTower.Sieve

open Complex MeasureTheory ArithmeticFunction GaloisForLFunctions.HTGeometry

/-- **The Chebyshev Perron identity.** -/
theorem tsum_vonMangoldt_smoothWeight_eq_logDeriv_integral {N H : ℝ} (hN : 0 < N) (hH : 0 < H)
    {d : ℝ} (hd : 1 < d) :
    (2 * Real.pi : ℝ) • (∑' n : ℕ,
        ((vonMangoldt n : ℝ) : ℂ) * ((smoothWeight N H (n : ℝ) : ℝ) : ℂ))
      = ∫ y : ℝ, (-(deriv riemannZeta ((d : ℂ) + (y : ℝ) * Complex.I))
            / riemannZeta ((d : ℂ) + (y : ℝ) * Complex.I))
          * mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ))
              ((d : ℂ) + (y : ℝ) * Complex.I) := by
  rw [tsum_vonMangoldt_smoothWeight_eq_integral hN hH hd]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  dsimp only
  have hre : ((d : ℂ) + (y : ℝ) * Complex.I).re = d := by simp
  rw [tsum_vonMangoldt_cpow_eq (by rw [hre]; exact hd)]

/-- **The Chebyshev Perron integrand, split.**  The identity with the integrand written as the pole
term plus two holomorphic pieces. -/
theorem tsum_vonMangoldt_smoothWeight_eq_split_integral {N H : ℝ} (hN : 0 < N) (hH : 0 < H)
    {d : ℝ} (hd : 1 < d) :
    (2 * Real.pi : ℝ) • (∑' n : ℕ,
        ((vonMangoldt n : ℝ) : ℂ) * ((smoothWeight N H (n : ℝ) : ℝ) : ℂ))
      = ∫ y : ℝ, (dslope (mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ))) 1
              ((d : ℂ) + (y : ℝ) * Complex.I)
            + mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) 1
                * (((d : ℂ) + (y : ℝ) * Complex.I) - 1)⁻¹
            + zetaLogDerivReg ((d : ℂ) + (y : ℝ) * Complex.I)
                * mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ))
                    ((d : ℂ) + (y : ℝ) * Complex.I)) := by
  rw [tsum_vonMangoldt_smoothWeight_eq_logDeriv_integral hN hH hd]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  dsimp only
  exact chebyshev_integrand_split_line hd

end RHTower.Sieve
