import GaloisForLFunctions.RHTower.Sieve.InvZetaProductShift
import GaloisForLFunctions.RHTower.Sieve.TruncationError
import GaloisForLFunctions.RHTower.Sieve.HorizontalEdgeBound

/-!
# Combining the four edges

The contour argument produces five quantities: the Perron integral `P` on the full line `Re s = d`,
its truncation `Vd`, the shifted vertical integral `Vc` on `Re s = c`, and the two horizontal edges
`Ht`, `Hb`.  Cauchy's theorem relates the last four; the truncation error relates the first two.

The combination itself is pure triangle inequality, and is isolated here so that the analytic
estimates can be substituted one at a time.  Note that the shift is stated with a factor `I` on the
vertical integrals, which costs nothing: `‖I • z‖ = ‖z‖`.
-/

namespace RHTower.Sieve

open Complex MeasureTheory GaloisForLFunctions.HTGeometry

/-- **The four-edge combination.**  Given the Cauchy identity and a bound on each of the four
pieces, the Perron integral is bounded by their sum. -/
theorem norm_le_of_contour_edges {P Vd Vc Ht Hb : ℂ} {E₁ E₂ E₃ E₄ : ℝ}
    (hshift : Complex.I • Vd - Complex.I • Vc = Ht - Hb)
    (htrunc : ‖P - Vd‖ ≤ E₁) (htop : ‖Ht‖ ≤ E₂) (hbot : ‖Hb‖ ≤ E₃) (hleft : ‖Vc‖ ≤ E₄) :
    ‖P‖ ≤ E₁ + E₂ + E₃ + E₄ := by
  have hIsmul : Complex.I • (Vd - Vc) = Ht - Hb := by
    rw [smul_sub]
    exact hshift
  have hmid : ‖Vd - Vc‖ ≤ E₂ + E₃ := by
    have hnorm : ‖Vd - Vc‖ = ‖Ht - Hb‖ := by
      rw [← hIsmul, norm_smul, Complex.norm_I, one_mul]
    rw [hnorm]
    exact le_trans (norm_sub_le _ _) (by linarith)
  have hdecomp : P = (P - Vd) + (Vd - Vc) + Vc := by ring
  calc ‖P‖ = ‖(P - Vd) + (Vd - Vc) + Vc‖ := by rw [← hdecomp]
    _ ≤ ‖(P - Vd) + (Vd - Vc)‖ + ‖Vc‖ := norm_add_le _ _
    _ ≤ ‖P - Vd‖ + ‖Vd - Vc‖ + ‖Vc‖ := by
        have := norm_add_le (P - Vd) (Vd - Vc)
        linarith
    _ ≤ E₁ + (E₂ + E₃) + E₄ := by linarith
    _ = E₁ + E₂ + E₃ + E₄ := by ring

/-- **The Perron identity in terms of the regular reciprocal.**  The smoothed Möbius sum is the
vertical integral of `invZeta · W` on any line right of the abscissa. -/
theorem tsum_moebius_smoothWeight_eq_invZeta_integral {N H : ℝ} (hN : 0 < N) (hH : 0 < H)
    {d : ℝ} (hd : 1 < d) :
    (2 * Real.pi : ℝ) • (∑' n : ℕ,
        (ArithmeticFunction.moebius n : ℂ) * ((smoothWeight N H (n : ℝ) : ℝ) : ℂ))
      = ∫ y : ℝ, invZeta ((d : ℂ) + (y : ℝ) * Complex.I)
          * mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ))
              ((d : ℂ) + (y : ℝ) * Complex.I) := by
  have ha : ∀ n : ℕ, ‖(ArithmeticFunction.moebius n : ℂ)‖ ≤ 1 := by
    intro n
    rw [← Complex.ofReal_intCast, Complex.norm_real, Real.norm_eq_abs]
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one
  have ha0 : (ArithmeticFunction.moebius 0 : ℂ) = 0 := by simp
  have hperron := tsum_mul_smoothWeight_eq_integral
    (a := fun n => (ArithmeticFunction.moebius n : ℂ)) ha ha0 hN hH hd
  rw [hperron]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  dsimp only
  have hre : ((d : ℂ) + (y : ℝ) * Complex.I).re = d := by simp
  rw [tsum_moebius_cpow_eq_invZeta (by rw [hre]; exact hd)]

/-- **The Möbius sum bounded by the four edges.**  Every hypothesis is an estimate on one edge of
the truncated rectangle, together with the Cauchy identity relating them. -/
theorem norm_tsum_moebius_smoothWeight_le_edges {N H : ℝ} (hN : 0 < N) (hH : 0 < H)
    {c d T E₁ E₂ E₃ E₄ : ℝ} (hd : 1 < d) (hc : 0 < c) (hcd : c ≤ d)
    (hzf : ∀ s ∈ Set.uIcc c d ×ℂ Set.uIcc (-T) T, s ≠ 1 → riemannZeta s ≠ 0)
    (htrunc : ‖(∫ y : ℝ, invZeta ((d : ℂ) + (y : ℝ) * Complex.I)
          * mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) ((d : ℂ) + (y : ℝ) * Complex.I))
        - ∫ y : ℝ in (-T)..T, invZeta ((d : ℂ) + (y : ℝ) * Complex.I)
          * mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ))
              ((d : ℂ) + (y : ℝ) * Complex.I)‖ ≤ E₁)
    (htop : ‖∫ x : ℝ in c..d, invZeta ((x : ℂ) + ((T : ℝ) : ℂ) * Complex.I)
        * mellin (fun x' : ℝ => ((smoothWeight N H x' : ℝ) : ℂ))
            ((x : ℂ) + ((T : ℝ) : ℂ) * Complex.I)‖ ≤ E₂)
    (hbot : ‖∫ x : ℝ in c..d, invZeta ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I)
        * mellin (fun x' : ℝ => ((smoothWeight N H x' : ℝ) : ℂ))
            ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I)‖ ≤ E₃)
    (hleft : ‖∫ y : ℝ in (-T)..T, invZeta ((c : ℂ) + (y : ℝ) * Complex.I)
        * mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ))
            ((c : ℂ) + (y : ℝ) * Complex.I)‖ ≤ E₄) :
    ‖(2 * Real.pi : ℝ) • (∑' n : ℕ,
        (ArithmeticFunction.moebius n : ℂ) * ((smoothWeight N H (n : ℝ) : ℝ) : ℂ))‖
      ≤ E₁ + E₂ + E₃ + E₄ := by
  rw [tsum_moebius_smoothWeight_eq_invZeta_integral hN hH hd]
  exact norm_le_of_contour_edges
    (integral_invZetaW_vertical_sub_eq_horizontal_rect hH hc hcd hzf)
    htrunc htop hbot hleft

end RHTower.Sieve
