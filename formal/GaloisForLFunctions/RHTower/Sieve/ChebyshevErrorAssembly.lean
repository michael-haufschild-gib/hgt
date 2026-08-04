import GaloisForLFunctions.RHTower.Sieve.ChebyshevMainTermBound

/-!
# The Chebyshev error with the tail made explicit

Substituting the truncation estimate for the first error piece leaves only the two contour-shift
integrals:

    ‖ 2π ∑ₙ Λ(n)w(n) - W(1)·2·arctan(T/(d-1)) ‖ ≤ 2·M·C/T + E₂ + E₃,

with `M = ∑ₙ Λ(n)n^{-d}` the value of the Dirichlet series at the abscissa and `C` a decay constant
for the Mellin transform.  The tail is the only piece whose bound depends on the height alone; the
other two are what the shift moves to the left edge.
-/

namespace RHTower.Sieve

open Complex MeasureTheory ArithmeticFunction GaloisForLFunctions.HTGeometry

/-- **The Chebyshev error, with the truncation tail substituted.** -/
theorem norm_tsum_vonMangoldt_sub_main_le_tail {N H : ℝ} (hN : 0 < N) (hH : 0 < H)
    {d T C E₂ E₃ : ℝ} (hd : 1 < d) (hT : 1 ≤ T)
    (hbd : ∀ s : ℂ, 0 < s.re → s.re ≤ d →
      |s.im| ^ (1 + 1) * ‖mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) s‖ ≤ C)
    (hdslope : ‖∫ y : ℝ in (-T)..T,
        dslope (mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ))) 1
          ((d : ℂ) + (y : ℝ) * Complex.I)‖ ≤ E₂)
    (hreg : ‖∫ y : ℝ in (-T)..T, zetaLogDerivReg ((d : ℂ) + (y : ℝ) * Complex.I)
        * mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ))
            ((d : ℂ) + (y : ℝ) * Complex.I)‖ ≤ E₃) :
    ‖(2 * Real.pi : ℝ) • (∑' n : ℕ,
          ((vonMangoldt n : ℝ) : ℂ) * ((smoothWeight N H (n : ℝ) : ℝ) : ℂ))
        - mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) 1
            * ((2 * Real.arctan (T / (d - 1)) : ℝ) : ℂ)‖
      ≤ 2 * ((∑' n : ℕ, (vonMangoldt n : ℝ) * (n : ℝ) ^ (-d)) * C) / T + E₂ + E₃ :=
  norm_tsum_vonMangoldt_sub_main_le hN hH hd
    (norm_truncation_error_chebyshev hN hH hd hT hbd) hdslope hreg

end RHTower.Sieve
