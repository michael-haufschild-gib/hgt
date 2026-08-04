import GaloisForLFunctions.RHTower.Sieve.MoebiusTwistEdgeSubstitution
import GaloisForLFunctions.RHTower.Sieve.PerronSharpSubstitution

/-!
# The twisted contour bound with the decay constants taken where they are used

The three sharp edge estimates carry the cutoff's decay constant as a hypothesis, so the caller fixes
it at the abscissa actually met on that edge.  They are stated for an arbitrary integrand, so they
apply to `invZeta(· + iτ)` unchanged, and substituting them into the twisted four-edge inequality
gives the twisted bound at an arbitrary smoothing width.
-/

namespace RHTower.Sieve

open Complex MeasureTheory GaloisForLFunctions.HTGeometry

/-- **The twisted contour bound, with the three decay constants as hypotheses.** -/
theorem norm_tsum_moebiusTwist_smoothWeight_le_sharp {N H : ℝ} (hN : 0 < N) (hH : 0 < H) (j : ℕ)
    {c d T Md Mh Mc C₁ C₂ C₃ : ℝ} (τ : ℝ)
    (hd : 1 < d) (hc : 0 < c) (hcd : c ≤ d) (hT : 1 ≤ T)
    (hMd : 0 ≤ Md) (hMh : 0 ≤ Mh) (hMc : 0 ≤ Mc)
    (hzf : ∀ s ∈ Set.uIcc c d ×ℂ Set.uIcc (-(|τ| + T)) (|τ| + T), s ≠ 1 → riemannZeta s ≠ 0)
    (hFd : ∀ y : ℝ, ‖invZeta ((d : ℂ) + (y : ℝ) * Complex.I + (τ : ℂ) * Complex.I)‖ ≤ Md)
    (hFt : ∀ x ∈ Set.Ioc c d,
      ‖invZeta ((x : ℂ) + ((T : ℝ) : ℂ) * Complex.I + (τ : ℂ) * Complex.I)‖ ≤ Mh)
    (hFb : ∀ x ∈ Set.Ioc c d,
      ‖invZeta ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I + (τ : ℂ) * Complex.I)‖ ≤ Mh)
    (hFc : ∀ y ∈ Set.Icc (-T) T,
      ‖invZeta ((c : ℂ) + (y : ℝ) * Complex.I + (τ : ℂ) * Complex.I)‖ ≤ Mc)
    (hFccont : ContinuousOn
      (fun y : ℝ => invZeta ((c : ℂ) + (y : ℝ) * Complex.I + (τ : ℂ) * Complex.I))
      (Set.uIcc (-T) T))
    (hbd1 : ∀ s : ℂ, 0 < s.re → s.re ≤ d →
      |s.im| ^ (1 + 1) * ‖mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) s‖ ≤ C₁)
    (hbd2 : ∀ s : ℂ, 0 < s.re → s.re ≤ d →
      |s.im| ^ (j + 1) * ‖mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) s‖ ≤ C₂)
    (hbd3 : ∀ s : ℂ, 0 < s.re → s.re ≤ c →
      |s.im| ^ (1 + 1) * ‖mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) s‖ ≤ C₃) :
    ‖(2 * Real.pi : ℝ) • (∑' n : ℕ,
        moebiusTwist τ n * ((smoothWeight N H (n : ℝ) : ℝ) : ℂ))‖
      ≤ 2 * (Md * C₁) / T
          + Mh * C₂ / T ^ (j + 1) * (d - c)
          + Mh * C₂ / T ^ (j + 1) * (d - c)
          + Mc * (2 * ((N + H) ^ c / c) + 2 * C₃) := by
  have hT0 : (0 : ℝ) < T := by linarith
  have hTabs : |T| = T := abs_of_pos hT0
  have hTnabs : |(-T)| = T := by rw [abs_neg, hTabs]
  have hd0 : (0 : ℝ) < d := by linarith
  have h₁ := norm_truncation_error_le hN hH hd0 hT hMd hbd1
    (F := fun s => invZeta (s + (τ : ℂ) * Complex.I)) (continuous_invZetaTwist_line τ hd) hFd
  have h₂ := norm_horizontal_edge_le (N := N) (H := H) j hc hcd (ne_of_gt hT0) hMh hbd2
    (F := fun s => invZeta (s + (τ : ℂ) * Complex.I)) hFt
  have h₃ := norm_horizontal_edge_le (N := N) (H := H) j hc hcd (by linarith : (-T : ℝ) ≠ 0)
    hMh hbd2 (F := fun s => invZeta (s + (τ : ℂ) * Complex.I)) hFb
  have h₄ := norm_integral_vertical_edge_le hN hH hc hT hMc hbd3
    (F := fun s => invZeta (s + (τ : ℂ) * Complex.I)) hFccont hFc
  rw [hTabs] at h₂
  rw [hTnabs] at h₃
  exact norm_tsum_moebiusTwist_smoothWeight_le_edges hN hH τ hd hc hcd (le_of_lt hT0) hzf
    h₁ h₂ h₃ h₄

end RHTower.Sieve
