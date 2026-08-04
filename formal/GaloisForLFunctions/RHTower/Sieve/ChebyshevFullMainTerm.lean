import GaloisForLFunctions.RHTower.Sieve.ChebyshevLeftPoleTerm

/-!
# The full main term

Shifting the divided difference to the left edge and extracting the pole term there produces the
*whole* residue, not half of it:

    2π ∑ₙ Λ(n)w(n) - W(1)·(2·arctan(T/(d-1)) - 2·arctan(T/(c-1)))
      = tail + ∫ W(c+iy)/(c-1+iy) dy - I·(top - bottom) + ∫ regular,

and the bracket tends to `2π` as `T → ∞`.  With the Perron factor `2π` this says
`∑ₙ Λ(n)w(n) ≈ W(1)`, the mass of the cutoff.

The right line contributes `arctan(T/(d-1)) → π/2` and the left line `-arctan(T/(c-1)) → π/2`; both
halves are needed, which is why the divided difference cannot simply be discarded on the left edge.
-/

namespace RHTower.Sieve

open Complex MeasureTheory ArithmeticFunction GaloisForLFunctions.HTGeometry

/-- **A residue-free shift, solved for the right edge.** -/
theorem eq_of_shift_identity {Vd Vc Ht Hb : ℂ}
    (hshift : Complex.I • Vd - Complex.I • Vc = Ht - Hb) :
    Vd = Vc - Complex.I * (Ht - Hb) := by
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  have h : Complex.I * Vd - Complex.I * Vc = Ht - Hb := by
    simpa only [smul_eq_mul] using hshift
  linear_combination (-Complex.I) * h + (Vd - Vc) * hI

/-- **The truncated Chebyshev identity with the full main term.** -/
theorem tsum_vonMangoldt_full_main_identity {N H : ℝ} (hN : 0 < N) (hH : 0 < H) {c d T : ℝ}
    (hc0 : 0 < c) (hc : c < 1) (hd : 1 < d) (hT : 0 < T) :
    (2 * Real.pi : ℝ) • (∑' n : ℕ,
          ((vonMangoldt n : ℝ) : ℂ) * ((smoothWeight N H (n : ℝ) : ℝ) : ℂ))
        - mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) 1
            * (((2 * Real.arctan (T / (d - 1)) - 2 * Real.arctan (T / (c - 1)) : ℝ)) : ℂ)
      = ((∫ y : ℝ, (-(deriv riemannZeta ((d : ℂ) + (y : ℝ) * Complex.I))
              / riemannZeta ((d : ℂ) + (y : ℝ) * Complex.I))
            * mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ))
                ((d : ℂ) + (y : ℝ) * Complex.I))
          - ∫ y : ℝ in (-T)..T, (-(deriv riemannZeta ((d : ℂ) + (y : ℝ) * Complex.I))
              / riemannZeta ((d : ℂ) + (y : ℝ) * Complex.I))
            * mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ))
                ((d : ℂ) + (y : ℝ) * Complex.I))
        + ((∫ y : ℝ in (-T)..T, mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ))
                ((c : ℂ) + (y : ℝ) * Complex.I)
              * (((c : ℂ) + (y : ℝ) * Complex.I) - 1)⁻¹)
            - Complex.I * ((∫ x : ℝ in c..d,
                  dslope (mellin (fun x' : ℝ => ((smoothWeight N H x' : ℝ) : ℂ))) 1
                    ((x : ℂ) + ((T : ℝ) : ℂ) * Complex.I))
                - ∫ x : ℝ in c..d,
                  dslope (mellin (fun x' : ℝ => ((smoothWeight N H x' : ℝ) : ℂ))) 1
                    ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I)))
        + (∫ y : ℝ in (-T)..T, zetaLogDerivReg ((d : ℂ) + (y : ℝ) * Complex.I)
            * mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ))
                ((d : ℂ) + (y : ℝ) * Complex.I)) := by
  have hid := tsum_vonMangoldt_truncated_identity hN hH (d := d) (T := T) hd
  have hshift := eq_of_shift_identity
    (integral_dslope_mellin_vertical_sub_eq_horizontal_rect hH hc0 hc hd hT (N := N) (H := H))
  have hleft := integral_dslope_mellin_left_eq (N := N) (H := H) hH (c := c) (T := T) hc0 hc.ne
  rw [hid, hshift, hleft]
  push_cast
  ring

end RHTower.Sieve
