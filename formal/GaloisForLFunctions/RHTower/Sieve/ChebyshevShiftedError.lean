import GaloisForLFunctions.RHTower.Sieve.ChebyshevErrorAssembly
import GaloisForLFunctions.RHTower.Sieve.ContourShiftNormBound

/-!
# The Chebyshev error on the shifted contour

Both residue-free pieces move to the left edge, so the whole error is a tail plus six edge integrals:

    ‖ 2π ∑ₙ Λ(n)w(n) - W(1)·2·arctan(T/(d-1)) ‖
      ≤ 2·M·C/T
        + (left + top + bottom for the divided difference)
        + (left + top + bottom for the regular part).

Every term on the right is an integral over an explicit contour edge of an explicit integrand.  The
main term on the left is `W(1)·2·arctan(T/(d-1))`, which is the mass of the cutoff in the limit — so
this inequality *is* the prime number theorem with the error still in contour form.
-/

namespace RHTower.Sieve

open Complex MeasureTheory ArithmeticFunction GaloisForLFunctions.HTGeometry

/-- **The Chebyshev error on the shifted contour.** -/
theorem norm_tsum_vonMangoldt_sub_main_le_shifted {N H : ℝ} (hN : 0 < N) (hH : 0 < H)
    {c d T C : ℝ} (hc0 : 0 < c) (hc : c < 1) (hd : 1 < d) (hT : 1 ≤ T)
    (hzf : ∀ s ∈ Set.uIcc c d ×ℂ Set.uIcc (-T) T, s ≠ 1 → riemannZeta s ≠ 0)
    (hbd : ∀ s : ℂ, 0 < s.re → s.re ≤ d →
      |s.im| ^ (1 + 1) * ‖mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) s‖ ≤ C) :
    ‖(2 * Real.pi : ℝ) • (∑' n : ℕ,
          ((vonMangoldt n : ℝ) : ℂ) * ((smoothWeight N H (n : ℝ) : ℝ) : ℂ))
        - mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) 1
            * ((2 * Real.arctan (T / (d - 1)) : ℝ) : ℂ)‖
      ≤ 2 * ((∑' n : ℕ, (vonMangoldt n : ℝ) * (n : ℝ) ^ (-d)) * C) / T
        + (‖∫ y : ℝ in (-T)..T, dslope (mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ))) 1
              ((c : ℂ) + (y : ℝ) * Complex.I)‖
          + ‖∫ x : ℝ in c..d, dslope (mellin (fun x' : ℝ => ((smoothWeight N H x' : ℝ) : ℂ))) 1
              ((x : ℂ) + ((T : ℝ) : ℂ) * Complex.I)‖
          + ‖∫ x : ℝ in c..d, dslope (mellin (fun x' : ℝ => ((smoothWeight N H x' : ℝ) : ℂ))) 1
              ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I)‖)
        + (‖∫ y : ℝ in (-T)..T, zetaLogDerivReg ((c : ℂ) + (y : ℝ) * Complex.I)
              * mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ))
                  ((c : ℂ) + (y : ℝ) * Complex.I)‖
          + ‖∫ x : ℝ in c..d, zetaLogDerivReg ((x : ℂ) + ((T : ℝ) : ℂ) * Complex.I)
              * mellin (fun x' : ℝ => ((smoothWeight N H x' : ℝ) : ℂ))
                  ((x : ℂ) + ((T : ℝ) : ℂ) * Complex.I)‖
          + ‖∫ x : ℝ in c..d, zetaLogDerivReg ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I)
              * mellin (fun x' : ℝ => ((smoothWeight N H x' : ℝ) : ℂ))
                  ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I)‖) :=
  norm_tsum_vonMangoldt_sub_main_le_tail hN hH hd hT hbd
    (norm_integral_dslope_mellin_right_le hH hc0 hc hd (by linarith))
    (norm_integral_zetaLogDerivRegW_right_le hH hc0 (by linarith) hzf)

end RHTower.Sieve
