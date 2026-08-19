import GaloisForLFunctions.RHTower.Sieve.DampedTwistEdgeSubstitution
import GaloisForLFunctions.RHTower.Sieve.EdgeBoundsSharp

/-!
# The four-edge inequality, sharp form, for the twisted damped series

The three sharp edge estimates of `Sieve/EdgeBoundsSharp` are generic in the Dirichlet series, so
they apply to `dampedInvZeta P t (· + iτ)` unchanged; only the continuity input along the right line
and the final assembly are specific to the twisted damped series.
-/

namespace RHTower.Sieve

open Complex MeasureTheory GaloisForLFunctions.HTGeometry

noncomputable section

/-- **The four-edge inequality, sharp form, twisted damped.** -/
theorem norm_tsum_dampedTwist_smoothWeight_le_sharp {P : Finset ℕ} (hPprime : ∀ q ∈ P, q.Prime)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) {N H : ℝ} (hN : 0 < N) (hH : 0 < H) (j : ℕ)
    {c d T Md Mh Mc C₁ C₂ C₃ : ℝ} (τ : ℝ)
    (hd : 1 < d) (hc : 0 < c) (hcd : c ≤ d) (hT : 1 ≤ T)
    (hMd : 0 ≤ Md) (hMh : 0 ≤ Mh) (hMc : 0 ≤ Mc)
    (hzf : ∀ s ∈ Set.uIcc c d ×ℂ Set.uIcc (-(|τ| + T)) (|τ| + T), s ≠ 1 → riemannZeta s ≠ 0)
    (hFd : ∀ y : ℝ,
      ‖dampedInvZeta P t ((d : ℂ) + (y : ℝ) * Complex.I + (τ : ℂ) * Complex.I)‖ ≤ Md)
    (hFt : ∀ x ∈ Set.Ioc c d,
      ‖dampedInvZeta P t ((x : ℂ) + ((T : ℝ) : ℂ) * Complex.I + (τ : ℂ) * Complex.I)‖ ≤ Mh)
    (hFb : ∀ x ∈ Set.Ioc c d,
      ‖dampedInvZeta P t ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I + (τ : ℂ) * Complex.I)‖ ≤ Mh)
    (hFc : ∀ y ∈ Set.Icc (-T) T,
      ‖dampedInvZeta P t ((c : ℂ) + (y : ℝ) * Complex.I + (τ : ℂ) * Complex.I)‖ ≤ Mc)
    (hFccont : ContinuousOn
      (fun y : ℝ => dampedInvZeta P t ((c : ℂ) + (y : ℝ) * Complex.I + (τ : ℂ) * Complex.I))
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
    ‖(2 * Real.pi : ℝ) • (∑' n : ℕ, dampedTwist P t τ n
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
    (F := fun s => dampedInvZeta P t (s + (τ : ℂ) * Complex.I))
    (continuous_dampedInvZetaTwist_line hP2 t τ hd) hFd
  have h₂ := norm_horizontal_edge_le (N := N) (H := H) j hc hcd (ne_of_gt hT0) hMh hbd2
    (F := fun s => dampedInvZeta P t (s + (τ : ℂ) * Complex.I)) hFt
  have h₃ := norm_horizontal_edge_le (N := N) (H := H) j hc hcd (by linarith : (-T : ℝ) ≠ 0)
    hMh hbd2 (F := fun s => dampedInvZeta P t (s + (τ : ℂ) * Complex.I)) hFb
  have h₄ := norm_integral_vertical_edge_le hN hH hc hT hMc hbd3
    (F := fun s => dampedInvZeta P t (s + (τ : ℂ) * Complex.I)) hFccont hFc
  rw [hTabs] at h₂
  rw [hTnabs] at h₃
  exact norm_tsum_dampedTwist_smoothWeight_le_edges hPprime ht0 ht1 hN hH τ hd hc hcd
    (le_of_lt hT0) hzf h₁ h₂ h₃ h₄

end

end RHTower.Sieve
