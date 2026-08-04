import GaloisForLFunctions.RHTower.Sieve.ChebyshevTruncatedIdentity

/-!
# The smoothed Chebyshev sum against its main term

The truncated identity has four summands, one of which is the main term.  Bounding the other three
bounds the difference:

    ‖ 2π ∑ₙ Λ(n)w(n) - W(1)·2·arctan(T/(d-1)) ‖ ≤ E₁ + E₂ + E₃.

This is the shape the numerical assembly consumes: the main term is explicit and the error is a sum
of three quantities each already controlled.
-/

namespace RHTower.Sieve

open Complex MeasureTheory ArithmeticFunction GaloisForLFunctions.HTGeometry

/-- **The smoothed Chebyshev sum differs from the main term by the three error pieces.** -/
theorem norm_tsum_vonMangoldt_sub_main_le {N H : ℝ} (hN : 0 < N) (hH : 0 < H)
    {d T E₁ E₂ E₃ : ℝ} (hd : 1 < d)
    (htail : ‖(∫ y : ℝ, (-(deriv riemannZeta ((d : ℂ) + (y : ℝ) * Complex.I))
            / riemannZeta ((d : ℂ) + (y : ℝ) * Complex.I))
          * mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ))
              ((d : ℂ) + (y : ℝ) * Complex.I))
        - ∫ y : ℝ in (-T)..T, (-(deriv riemannZeta ((d : ℂ) + (y : ℝ) * Complex.I))
            / riemannZeta ((d : ℂ) + (y : ℝ) * Complex.I))
          * mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ))
              ((d : ℂ) + (y : ℝ) * Complex.I)‖ ≤ E₁)
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
      ≤ E₁ + E₂ + E₃ := by
  set A : ℂ := (∫ y : ℝ, (-(deriv riemannZeta ((d : ℂ) + (y : ℝ) * Complex.I))
          / riemannZeta ((d : ℂ) + (y : ℝ) * Complex.I))
        * mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ))
            ((d : ℂ) + (y : ℝ) * Complex.I))
      - ∫ y : ℝ in (-T)..T, (-(deriv riemannZeta ((d : ℂ) + (y : ℝ) * Complex.I))
          / riemannZeta ((d : ℂ) + (y : ℝ) * Complex.I))
        * mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ))
            ((d : ℂ) + (y : ℝ) * Complex.I) with hAdef
  set B : ℂ := ∫ y : ℝ in (-T)..T,
      dslope (mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ))) 1
        ((d : ℂ) + (y : ℝ) * Complex.I) with hBdef
  set C : ℂ := ∫ y : ℝ in (-T)..T, zetaLogDerivReg ((d : ℂ) + (y : ℝ) * Complex.I)
      * mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ))
          ((d : ℂ) + (y : ℝ) * Complex.I) with hCdef
  have hid := tsum_vonMangoldt_truncated_identity hN hH (d := d) (T := T) hd
  rw [← hAdef, ← hBdef, ← hCdef] at hid
  have hrw : (2 * Real.pi : ℝ) • (∑' n : ℕ,
        ((vonMangoldt n : ℝ) : ℂ) * ((smoothWeight N H (n : ℝ) : ℝ) : ℂ))
      - mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) 1
          * ((2 * Real.arctan (T / (d - 1)) : ℝ) : ℂ)
      = A + B + C := by
    rw [hid]
    ring
  rw [hrw]
  calc ‖A + B + C‖ ≤ ‖A + B‖ + ‖C‖ := norm_add_le _ _
    _ ≤ ‖A‖ + ‖B‖ + ‖C‖ := by
        have := norm_add_le A B
        linarith
    _ ≤ E₁ + E₂ + E₃ := by linarith

end RHTower.Sieve
