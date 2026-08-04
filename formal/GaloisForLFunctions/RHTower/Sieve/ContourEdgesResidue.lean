import GaloisForLFunctions.RHTower.Sieve.ChebyshevIntegrandSplit
import GaloisForLFunctions.RHTower.Sieve.PerronEdgeAssembly

/-!
# The four-edge combination with a residue

`norm_le_of_contour_edges` bounds the Perron integral when the boundary functional vanishes.  When
it equals a residue instead, the same argument bounds the Perron integral *minus* the residue — the
main term — by the same four edge estimates.

The factor `-I` appears because the shift identity carries `I` on the vertical edges: solving for
`Vd - Vc` multiplies through by `I⁻¹ = -I`.
-/

namespace RHTower.Sieve

open Complex

/-- **The four-edge combination with a residue.**  The Perron integral differs from `-I·Res` by at
most the sum of the four edge bounds. -/
theorem norm_sub_le_of_contour_edges_residue {P Vd Vc Ht Hb Res : ℂ} {E₁ E₂ E₃ E₄ : ℝ}
    (hshift : Complex.I * Vd - Complex.I * Vc - (Ht - Hb) = Res)
    (htrunc : ‖P - Vd‖ ≤ E₁) (htop : ‖Ht‖ ≤ E₂) (hbot : ‖Hb‖ ≤ E₃) (hleft : ‖Vc‖ ≤ E₄) :
    ‖P - (-Complex.I) * Res‖ ≤ E₁ + E₂ + E₃ + E₄ := by
  have hI : Complex.I * (-Complex.I) = 1 := by
    rw [mul_neg, Complex.I_mul_I, neg_neg]
  have hmid : Vd - Vc = (-Complex.I) * (Res + (Ht - Hb)) := by
    have h : Complex.I * (Vd - Vc) = Res + (Ht - Hb) := by linear_combination hshift
    calc Vd - Vc = (Complex.I * (-Complex.I)) * (Vd - Vc) := by rw [hI]; ring
      _ = (-Complex.I) * (Complex.I * (Vd - Vc)) := by ring
      _ = (-Complex.I) * (Res + (Ht - Hb)) := by rw [h]
  have hdecomp : P - (-Complex.I) * Res
      = (P - Vd) + (-Complex.I) * (Ht - Hb) + Vc := by
    have := hmid
    linear_combination this
  rw [hdecomp]
  have hnormI : ‖(-Complex.I) * (Ht - Hb)‖ = ‖Ht - Hb‖ := by
    rw [norm_mul, norm_neg, Complex.norm_I, one_mul]
  have hmidbd : ‖(-Complex.I) * (Ht - Hb)‖ ≤ E₂ + E₃ := by
    rw [hnormI]
    exact le_trans (norm_sub_le _ _) (by linarith)
  calc ‖(P - Vd) + (-Complex.I) * (Ht - Hb) + Vc‖
      ≤ ‖(P - Vd) + (-Complex.I) * (Ht - Hb)‖ + ‖Vc‖ := norm_add_le _ _
    _ ≤ ‖P - Vd‖ + ‖(-Complex.I) * (Ht - Hb)‖ + ‖Vc‖ := by
        have := norm_add_le (P - Vd) ((-Complex.I) * (Ht - Hb))
        linarith
    _ ≤ E₁ + (E₂ + E₃) + E₄ := by linarith
    _ = E₁ + E₂ + E₃ + E₄ := by ring

end RHTower.Sieve
