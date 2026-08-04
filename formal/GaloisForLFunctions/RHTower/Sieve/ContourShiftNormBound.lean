import GaloisForLFunctions.RHTower.Sieve.PoleTermSplit

/-!
# From a residue-free shift to a bound on the right edge

A Cauchy identity of the form

    I • V_d - I • V_c = H_top - H_bot

bounds the right vertical edge by the other three:  `‖V_d‖ ≤ ‖V_c‖ + ‖H_top‖ + ‖H_bot‖`.  The factor
`I` is a unit, so it costs nothing in norm.

Applying this to the two residue-free pieces of the Chebyshev integrand moves both of them to the
left edge, which is where the zero-free region makes them small.
-/

namespace RHTower.Sieve

open Complex MeasureTheory GaloisForLFunctions.HTGeometry

/-- **A residue-free shift bounds the right edge by the other three.** -/
theorem norm_le_of_shift_identity {Vd Vc Ht Hb : ℂ}
    (hshift : Complex.I • Vd - Complex.I • Vc = Ht - Hb) :
    ‖Vd‖ ≤ ‖Vc‖ + ‖Ht‖ + ‖Hb‖ := by
  have hsm : Complex.I • Vd - Complex.I • Vc = Complex.I * (Vd - Vc) := by
    simp only [smul_eq_mul]
    ring
  have hprod : Complex.I * (Vd - Vc) = Ht - Hb := by rw [← hsm, hshift]
  have hnorm : ‖Vd - Vc‖ = ‖Ht - Hb‖ := by
    have := congrArg norm hprod
    rwa [norm_mul, Complex.norm_I, one_mul] at this
  calc ‖Vd‖ = ‖(Vd - Vc) + Vc‖ := by ring_nf
    _ ≤ ‖Vd - Vc‖ + ‖Vc‖ := norm_add_le _ _
    _ = ‖Ht - Hb‖ + ‖Vc‖ := by rw [hnorm]
    _ ≤ (‖Ht‖ + ‖Hb‖) + ‖Vc‖ := by
        have := norm_sub_le Ht Hb
        linarith
    _ = ‖Vc‖ + ‖Ht‖ + ‖Hb‖ := by ring

/-- **The regular part of the Chebyshev integrand, moved to the left edge.** -/
theorem norm_integral_zetaLogDerivRegW_right_le {N H : ℝ} (hH : 0 < H) {c d T : ℝ} (hc : 0 < c)
    (hcd : c ≤ d)
    (h : ∀ s ∈ Set.uIcc c d ×ℂ Set.uIcc (-T) T, s ≠ 1 → riemannZeta s ≠ 0) :
    ‖∫ y : ℝ in (-T)..T, zetaLogDerivReg ((d : ℂ) + (y : ℝ) * Complex.I)
        * mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) ((d : ℂ) + (y : ℝ) * Complex.I)‖
      ≤ ‖∫ y : ℝ in (-T)..T, zetaLogDerivReg ((c : ℂ) + (y : ℝ) * Complex.I)
            * mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) ((c : ℂ) + (y : ℝ) * Complex.I)‖
        + ‖∫ x : ℝ in c..d, zetaLogDerivReg ((x : ℂ) + ((T : ℝ) : ℂ) * Complex.I)
            * mellin (fun x' : ℝ => ((smoothWeight N H x' : ℝ) : ℂ))
                ((x : ℂ) + ((T : ℝ) : ℂ) * Complex.I)‖
        + ‖∫ x : ℝ in c..d, zetaLogDerivReg ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I)
            * mellin (fun x' : ℝ => ((smoothWeight N H x' : ℝ) : ℂ))
                ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I)‖ :=
  norm_le_of_shift_identity
    (integral_zetaLogDerivRegW_vertical_sub_eq_horizontal_rect hH hc hcd h)

/-- **The divided difference, moved to the left edge.** -/
theorem norm_integral_dslope_mellin_right_le {N H : ℝ} (hH : 0 < H) {c d T : ℝ} (hc0 : 0 < c)
    (hc : c < 1) (hd : 1 < d) (hT : 0 < T) :
    ‖∫ y : ℝ in (-T)..T, dslope (mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ))) 1
        ((d : ℂ) + (y : ℝ) * Complex.I)‖
      ≤ ‖∫ y : ℝ in (-T)..T, dslope (mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ))) 1
            ((c : ℂ) + (y : ℝ) * Complex.I)‖
        + ‖∫ x : ℝ in c..d, dslope (mellin (fun x' : ℝ => ((smoothWeight N H x' : ℝ) : ℂ))) 1
            ((x : ℂ) + ((T : ℝ) : ℂ) * Complex.I)‖
        + ‖∫ x : ℝ in c..d, dslope (mellin (fun x' : ℝ => ((smoothWeight N H x' : ℝ) : ℂ))) 1
            ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I)‖ :=
  norm_le_of_shift_identity
    (integral_dslope_mellin_vertical_sub_eq_horizontal_rect hH hc0 hc hd hT)

end RHTower.Sieve
