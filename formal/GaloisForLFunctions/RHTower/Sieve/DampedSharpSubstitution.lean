import GaloisForLFunctions.RHTower.Sieve.DampedPerron
import GaloisForLFunctions.RHTower.Sieve.EdgeBoundsSharp

/-!
# The four-edge inequality, sharp form, for the damped series

The damped analogue of `Sieve/PerronSharpSubstitution`.  The three sharp edge estimates of
`Sieve/EdgeBoundsSharp` are generic in the Dirichlet series, so only the continuity input and the
final assembly change.
-/

namespace RHTower.Sieve

open Complex MeasureTheory GaloisForLFunctions.HTGeometry

noncomputable section

/-- **The four-edge inequality, sharp form, damped.** -/
theorem norm_tsum_damped_smoothWeight_le_sharp {P : Finset ℕ} (hPprime : ∀ q ∈ P, q.Prime)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) {N H : ℝ} (hN : 0 < N) (hH : 0 < H) (j : ℕ)
    {c d T Md Mh Mc C₁ C₂ C₃ : ℝ}
    (hd : 1 < d) (hc : 0 < c) (hcd : c ≤ d) (hT : 1 ≤ T)
    (hMd : 0 ≤ Md) (hMh : 0 ≤ Mh) (hMc : 0 ≤ Mc)
    (hzf : ∀ s ∈ Set.uIcc c d ×ℂ Set.uIcc (-T) T, s ≠ 1 → riemannZeta s ≠ 0)
    (hFd : ∀ y : ℝ, ‖dampedInvZeta P t ((d : ℂ) + (y : ℝ) * Complex.I)‖ ≤ Md)
    (hFt : ∀ x ∈ Set.Ioc c d,
      ‖dampedInvZeta P t ((x : ℂ) + ((T : ℝ) : ℂ) * Complex.I)‖ ≤ Mh)
    (hFb : ∀ x ∈ Set.Ioc c d,
      ‖dampedInvZeta P t ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I)‖ ≤ Mh)
    (hFc : ∀ y ∈ Set.Icc (-T) T,
      ‖dampedInvZeta P t ((c : ℂ) + (y : ℝ) * Complex.I)‖ ≤ Mc)
    (hFccont : ContinuousOn (fun y : ℝ => dampedInvZeta P t ((c : ℂ) + (y : ℝ) * Complex.I))
      (Set.uIcc (-T) T))
    (hbd1 : ∀ s : ℂ, 0 < s.re → s.re ≤ d →
      |s.im| ^ (1 + 1) * ‖mellin (fun x : ℝ =>
        ((GaloisForLFunctions.HTGeometry.smoothWeight N H x : ℝ) : ℂ)) s‖ ≤ C₁)
    (hbd2 : ∀ s : ℂ, 0 < s.re → s.re ≤ d →
      |s.im| ^ (j + 1) * ‖mellin (fun x : ℝ =>
        ((GaloisForLFunctions.HTGeometry.smoothWeight N H x : ℝ) : ℂ)) s‖ ≤ C₂)
    (hbd3 : ∀ s : ℂ, 0 < s.re → s.re ≤ c →
      |s.im| ^ (1 + 1) * ‖mellin (fun x : ℝ =>
        ((GaloisForLFunctions.HTGeometry.smoothWeight N H x : ℝ) : ℂ)) s‖ ≤ C₃) :
    ‖(2 * Real.pi : ℝ) • (∑' n : ℕ, dampedOmegaMoebius P t n
        * ((GaloisForLFunctions.HTGeometry.smoothWeight N H (n : ℝ) : ℝ) : ℂ))‖
      ≤ 2 * (Md * C₁) / T
          + Mh * C₂ / T ^ (j + 1) * (d - c)
          + Mh * C₂ / T ^ (j + 1) * (d - c)
          + Mc * (2 * ((N + H) ^ c / c) + 2 * C₃) := by
  have hP2 : ∀ q ∈ P, 2 ≤ q := fun q hq => (hPprime q hq).two_le
  have hT0 : (0 : ℝ) < T := by linarith
  have hTabs : |T| = T := abs_of_pos hT0
  have hTnabs : |(-T)| = T := by rw [abs_neg, hTabs]
  have hd0 : (0 : ℝ) < d := by linarith
  have h₁ := norm_truncation_error_le hN hH hd0 hT hMd hbd1
    (continuous_dampedInvZeta_line hP2 t hd) hFd
  have h₂ := norm_horizontal_edge_le (N := N) (H := H) j hc hcd (ne_of_gt hT0) hMh hbd2 hFt
  have h₃ := norm_horizontal_edge_le (N := N) (H := H) j hc hcd (by linarith : (-T : ℝ) ≠ 0)
    hMh hbd2 hFb
  have h₄ := norm_integral_vertical_edge_le hN hH hc hT hMc hbd3 hFccont hFc
  rw [hTabs] at h₂
  rw [hTnabs] at h₃
  exact norm_tsum_damped_smoothWeight_le_edges hPprime ht0 ht1 hN hH hd hc hcd hzf h₁ h₂ h₃ h₄

end

end RHTower.Sieve
