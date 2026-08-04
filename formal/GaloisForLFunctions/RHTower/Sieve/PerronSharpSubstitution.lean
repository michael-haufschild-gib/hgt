import GaloisForLFunctions.RHTower.Sieve.EdgeBoundsSharp
import GaloisForLFunctions.RHTower.Sieve.PerronEdgeAssembly

/-!
# The four-edge inequality with constants where they are used

The substituted form of the contour bound, with the three decay constants of the cutoff's transform
supplied as hypotheses rather than fixed in advance.  Two of them are taken at the right abscissa
`d`, which both the truncation error and the horizontal edges reach; the third at the left abscissa
`c`, which is the only one the left edge meets.

This is the form the assembly needs, because the abscissae depend on the contour parameter and so
the constants cannot be chosen before it.
-/

namespace RHTower.Sieve

open Complex MeasureTheory GaloisForLFunctions.HTGeometry

/-- **The four-edge inequality, sharp form.** -/
theorem norm_tsum_moebius_smoothWeight_le_sharp {N H : ℝ} (hN : 0 < N) (hH : 0 < H) (j : ℕ)
    {c d T Md Mh Mc C₁ C₂ C₃ : ℝ}
    (hd : 1 < d) (hc : 0 < c) (hcd : c ≤ d) (hT : 1 ≤ T)
    (hMd : 0 ≤ Md) (hMh : 0 ≤ Mh) (hMc : 0 ≤ Mc)
    (hzf : ∀ s ∈ Set.uIcc c d ×ℂ Set.uIcc (-T) T, s ≠ 1 → riemannZeta s ≠ 0)
    (hFd : ∀ y : ℝ, ‖invZeta ((d : ℂ) + (y : ℝ) * Complex.I)‖ ≤ Md)
    (hFt : ∀ x ∈ Set.Ioc c d, ‖invZeta ((x : ℂ) + ((T : ℝ) : ℂ) * Complex.I)‖ ≤ Mh)
    (hFb : ∀ x ∈ Set.Ioc c d, ‖invZeta ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I)‖ ≤ Mh)
    (hFc : ∀ y ∈ Set.Icc (-T) T, ‖invZeta ((c : ℂ) + (y : ℝ) * Complex.I)‖ ≤ Mc)
    (hFccont : ContinuousOn (fun y : ℝ => invZeta ((c : ℂ) + (y : ℝ) * Complex.I))
      (Set.uIcc (-T) T))
    (hbd1 : ∀ s : ℂ, 0 < s.re → s.re ≤ d →
      |s.im| ^ (1 + 1) * ‖mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) s‖ ≤ C₁)
    (hbd2 : ∀ s : ℂ, 0 < s.re → s.re ≤ d →
      |s.im| ^ (j + 1) * ‖mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) s‖ ≤ C₂)
    (hbd3 : ∀ s : ℂ, 0 < s.re → s.re ≤ c →
      |s.im| ^ (1 + 1) * ‖mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) s‖ ≤ C₃) :
    ‖(2 * Real.pi : ℝ) • (∑' n : ℕ,
        (ArithmeticFunction.moebius n : ℂ) * ((smoothWeight N H (n : ℝ) : ℝ) : ℂ))‖
      ≤ 2 * (Md * C₁) / T
          + Mh * C₂ / T ^ (j + 1) * (d - c)
          + Mh * C₂ / T ^ (j + 1) * (d - c)
          + Mc * (2 * ((N + H) ^ c / c) + 2 * C₃) := by
  have hT0 : (0 : ℝ) < T := by linarith
  have hTabs : |T| = T := abs_of_pos hT0
  have hTnabs : |(-T)| = T := by rw [abs_neg, hTabs]
  have hd0 : (0 : ℝ) < d := by linarith
  have h₁ := norm_truncation_error_le hN hH hd0 hT hMd hbd1 (continuous_invZeta_line hd) hFd
  have h₂ := norm_horizontal_edge_le (N := N) (H := H) j hc hcd (ne_of_gt hT0) hMh hbd2 hFt
  have h₃ := norm_horizontal_edge_le (N := N) (H := H) j hc hcd (by linarith : (-T : ℝ) ≠ 0)
    hMh hbd2 hFb
  have h₄ := norm_integral_vertical_edge_le hN hH hc hT hMc hbd3 hFccont hFc
  rw [hTabs] at h₂
  rw [hTnabs] at h₃
  exact norm_tsum_moebius_smoothWeight_le_edges hN hH hd hc hcd hzf h₁ h₂ h₃ h₄

end RHTower.Sieve
