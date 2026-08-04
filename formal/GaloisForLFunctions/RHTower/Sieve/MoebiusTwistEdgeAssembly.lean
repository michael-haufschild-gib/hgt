import GaloisForLFunctions.RHTower.Sieve.InvZetaTwistShift
import GaloisForLFunctions.RHTower.Sieve.MoebiusTwistPerron
import GaloisForLFunctions.RHTower.Sieve.PerronEdgeAssembly

/-!
# The twisted Möbius sum bounded by the four edges

The Perron identity and the four-edge decomposition both transfer to the twist `μ(n) ↦ μ(n)n^{-iτ}`.
The integrand becomes `invZeta(s + iτ)·W(s)`: the Dirichlet series of the twisted coefficients is the
untwisted one shifted, and the contour identity for the shifted integrand is the contour identity for
`invZeta` on the translated rectangle.  So

`‖∑' μ(n)n^{-iτ}·w(n)‖ ≤ E₁ + E₂ + E₃ + E₄`

with the same four edges, the only change being that the zero-free hypothesis is taken at the
enlarged height `|τ| + T`.
-/

namespace RHTower.Sieve

open Complex MeasureTheory GaloisForLFunctions.HTGeometry

/-- **The twisted Perron identity in terms of the regular reciprocal.**  On any line right of the
abscissa the twisted smoothed sum is the vertical integral of `invZeta(· + iτ)·W`. -/
theorem tsum_moebiusTwist_smoothWeight_eq_invZeta_integral {N H : ℝ} (hN : 0 < N) (hH : 0 < H)
    {d : ℝ} (hd : 1 < d) (τ : ℝ) :
    (2 * Real.pi : ℝ) • (∑' n : ℕ,
        moebiusTwist τ n * ((smoothWeight N H (n : ℝ) : ℝ) : ℂ))
      = ∫ y : ℝ, invZeta ((d : ℂ) + (y : ℝ) * Complex.I + (τ : ℂ) * Complex.I)
          * mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ))
              ((d : ℂ) + (y : ℝ) * Complex.I) := by
  rw [tsum_mul_smoothWeight_eq_integral (a := moebiusTwist τ)
    (norm_moebiusTwist_le_one τ) (moebiusTwist_zero τ) hN hH hd]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  dsimp only
  have hre : ((d : ℂ) + (y : ℝ) * Complex.I + (τ : ℂ) * Complex.I).re = d := by simp
  rw [tsum_moebiusTwist_cpow, ← tsum_cpow_neg_eq_LSeries
      (a := fun n => (ArithmeticFunction.moebius n : ℂ)) (by simp),
    tsum_moebius_cpow_eq_invZeta (by rw [hre]; exact hd)]

/-- **The twisted Möbius sum bounded by the four edges.**  Every hypothesis is an estimate on one
edge of the rectangle; the zero-free input is taken at the enlarged height `|τ| + T`. -/
theorem norm_tsum_moebiusTwist_smoothWeight_le_edges {N H : ℝ} (hN : 0 < N) (hH : 0 < H)
    {c d T E₁ E₂ E₃ E₄ : ℝ} (τ : ℝ) (hd : 1 < d) (hc : 0 < c) (hcd : c ≤ d) (hT : 0 ≤ T)
    (hzf : ∀ s ∈ Set.uIcc c d ×ℂ Set.uIcc (-(|τ| + T)) (|τ| + T), s ≠ 1 → riemannZeta s ≠ 0)
    (htrunc : ‖(∫ y : ℝ, invZeta ((d : ℂ) + (y : ℝ) * Complex.I + (τ : ℂ) * Complex.I)
          * mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) ((d : ℂ) + (y : ℝ) * Complex.I))
        - ∫ y : ℝ in (-T)..T, invZeta ((d : ℂ) + (y : ℝ) * Complex.I + (τ : ℂ) * Complex.I)
          * mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ))
              ((d : ℂ) + (y : ℝ) * Complex.I)‖ ≤ E₁)
    (htop : ‖∫ x : ℝ in c..d, invZeta ((x : ℂ) + ((T : ℝ) : ℂ) * Complex.I + (τ : ℂ) * Complex.I)
        * mellin (fun x' : ℝ => ((smoothWeight N H x' : ℝ) : ℂ))
            ((x : ℂ) + ((T : ℝ) : ℂ) * Complex.I)‖ ≤ E₂)
    (hbot : ‖∫ x : ℝ in c..d, invZeta ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I + (τ : ℂ) * Complex.I)
        * mellin (fun x' : ℝ => ((smoothWeight N H x' : ℝ) : ℂ))
            ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I)‖ ≤ E₃)
    (hleft : ‖∫ y : ℝ in (-T)..T, invZeta ((c : ℂ) + (y : ℝ) * Complex.I + (τ : ℂ) * Complex.I)
        * mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ))
            ((c : ℂ) + (y : ℝ) * Complex.I)‖ ≤ E₄) :
    ‖(2 * Real.pi : ℝ) • (∑' n : ℕ,
        moebiusTwist τ n * ((smoothWeight N H (n : ℝ) : ℝ) : ℂ))‖
      ≤ E₁ + E₂ + E₃ + E₄ := by
  rw [tsum_moebiusTwist_smoothWeight_eq_invZeta_integral hN hH hd τ]
  exact norm_le_of_contour_edges
    (integral_vertical_sub_eq_horizontal_rect T
      (differentiableOn_invZetaTwistW_rect hH τ hc hcd hT hzf))
    htrunc htop hbot hleft

end RHTower.Sieve
