import GaloisForLFunctions.RHTower.Sieve.DampedTwistEdges
import GaloisForLFunctions.RHTower.Sieve.MoebiusTwistEdgeSubstitution

/-!
# The twisted damped contour bound with the edges substituted

The damped analogue of `Sieve/MoebiusTwistEdgeSubstitution`.  The three generic edge estimates are
applied to `F s = dampedInvZeta P t (s + iτ)`; the only new input is continuity of that function
along the right line, which is the untwisted continuity composed with a translation.
-/

namespace RHTower.Sieve

open Complex MeasureTheory GaloisForLFunctions.HTGeometry

noncomputable section

/-- The shifted damped integrand is continuous along the right line. -/
theorem continuous_dampedInvZetaTwist_line {P : Finset ℕ} (hP : ∀ q ∈ P, 2 ≤ q) (t : ℝ)
    {d : ℝ} (τ : ℝ) (hd : 1 < d) :
    Continuous fun y : ℝ =>
      dampedInvZeta P t ((d : ℂ) + (y : ℝ) * Complex.I + (τ : ℂ) * Complex.I) := by
  have hfun : (fun y : ℝ =>
        dampedInvZeta P t ((d : ℂ) + (y : ℝ) * Complex.I + (τ : ℂ) * Complex.I))
      = (fun y : ℝ => dampedInvZeta P t ((d : ℂ) + (y : ℝ) * Complex.I))
        ∘ fun y : ℝ => y + τ := by
    funext y
    simp only [Function.comp_apply]
    congr 1
    push_cast
    ring
  rw [hfun]
  exact (continuous_dampedInvZeta_line hP t hd).comp (continuous_id.add continuous_const)

/-- **The twisted damped contour bound with the edges substituted.** -/
theorem exists_norm_tsum_dampedTwist_smoothWeight_le {P : Finset ℕ}
    (hPprime : ∀ q ∈ P, q.Prime) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) {N H : ℝ}
    (hN : 0 < N) (hH : 0 < H) (j : ℕ) (σmax : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ τ c d T Md Mh Mc : ℝ,
      1 < d → d ≤ σmax → 0 < c → c ≤ d → 1 ≤ T → 0 ≤ Md → 0 ≤ Mh → 0 ≤ Mc →
      (∀ s ∈ Set.uIcc c d ×ℂ Set.uIcc (-(|τ| + T)) (|τ| + T), s ≠ 1 → riemannZeta s ≠ 0) →
      (∀ y : ℝ,
        ‖dampedInvZeta P t ((d : ℂ) + (y : ℝ) * Complex.I + (τ : ℂ) * Complex.I)‖ ≤ Md) →
      (∀ x ∈ Set.Ioc c d,
        ‖dampedInvZeta P t ((x : ℂ) + ((T : ℝ) : ℂ) * Complex.I + (τ : ℂ) * Complex.I)‖ ≤ Mh) →
      (∀ x ∈ Set.Ioc c d,
        ‖dampedInvZeta P t ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I + (τ : ℂ) * Complex.I)‖ ≤ Mh) →
      (∀ y ∈ Set.Icc (-T) T,
        ‖dampedInvZeta P t ((c : ℂ) + (y : ℝ) * Complex.I + (τ : ℂ) * Complex.I)‖ ≤ Mc) →
      ContinuousOn (fun y : ℝ =>
          dampedInvZeta P t ((c : ℂ) + (y : ℝ) * Complex.I + (τ : ℂ) * Complex.I))
        (Set.uIcc (-T) T) →
      ‖(2 * Real.pi : ℝ) • (∑' n : ℕ, dampedTwist P t τ n
          * ((GaloisForLFunctions.HTGeometry.smoothWeight N H (n : ℝ) : ℝ) : ℂ))‖
        ≤ 2 * (Md * C) / T
            + Mh * C / T ^ (j + 1) * (d - c)
            + Mh * C / T ^ (j + 1) * (d - c)
            + Mc * (2 * ((N + H) ^ c / c) + 2 * C) := by
  have hP2 : ∀ q ∈ P, 2 ≤ q := fun q hq => (hPprime q hq).two_le
  obtain ⟨C₁, hC₁, htr⟩ := exists_bound_truncation_error hN hH σmax
  obtain ⟨C₂, hC₂, hhor⟩ := exists_horizontal_edge_bound hN hH j σmax
  obtain ⟨C₃, hC₃, hver⟩ := exists_vertical_edge_bound hN hH σmax
  refine ⟨max (max C₁ C₂) C₃, le_trans hC₁ (le_trans (le_max_left _ _) (le_max_left _ _)),
    fun τ c d T Md Mh Mc hd hdmax hc hcd hT hMd hMh hMc hzf hFd hFt hFb hFc hFccont => ?_⟩
  set F : ℂ → ℂ := fun s => dampedInvZeta P t (s + (τ : ℂ) * Complex.I) with hFdef
  set C : ℝ := max (max C₁ C₂) C₃ with hCdef
  have hCC₁ : C₁ ≤ C := le_trans (le_max_left _ _) (le_max_left _ _)
  have hCC₂ : C₂ ≤ C := le_trans (le_max_right _ _) (le_max_left _ _)
  have hCC₃ : C₃ ≤ C := le_max_right _ _
  have hT0 : (0 : ℝ) < T := by linarith
  have hTabs : |T| = T := abs_of_pos hT0
  have hTnabs : |(-T)| = T := by rw [abs_neg, hTabs]
  have hd0 : (0 : ℝ) < d := by linarith
  have hdc : (0 : ℝ) ≤ d - c := by linarith
  have h₁ := htr F d T Md hd0 hdmax hT hMd (continuous_dampedInvZetaTwist_line hP2 t τ hd) hFd
  have h₁' : ‖(∫ y : ℝ,
        dampedInvZeta P t ((d : ℂ) + (y : ℝ) * Complex.I + (τ : ℂ) * Complex.I)
        * mellin (fun x : ℝ =>
            ((GaloisForLFunctions.HTGeometry.smoothWeight N H x : ℝ) : ℂ))
          ((d : ℂ) + (y : ℝ) * Complex.I))
      - ∫ y : ℝ in (-T)..T,
        dampedInvZeta P t ((d : ℂ) + (y : ℝ) * Complex.I + (τ : ℂ) * Complex.I)
        * mellin (fun x : ℝ =>
            ((GaloisForLFunctions.HTGeometry.smoothWeight N H x : ℝ) : ℂ))
          ((d : ℂ) + (y : ℝ) * Complex.I)‖ ≤ 2 * (Md * C) / T := by
    refine le_trans h₁ ?_
    have : Md * C₁ ≤ Md * C := mul_le_mul_of_nonneg_left hCC₁ hMd
    gcongr
  have h₂ := hhor F c d T Mh hc hcd hdmax (ne_of_gt hT0) hMh hFt
  have h₂' : ‖∫ x : ℝ in c..d,
      dampedInvZeta P t ((x : ℂ) + ((T : ℝ) : ℂ) * Complex.I + (τ : ℂ) * Complex.I)
      * mellin (fun x' : ℝ =>
          ((GaloisForLFunctions.HTGeometry.smoothWeight N H x' : ℝ) : ℂ))
        ((x : ℂ) + ((T : ℝ) : ℂ) * Complex.I)‖ ≤ Mh * C / T ^ (j + 1) * (d - c) := by
    rw [hTabs] at h₂
    refine le_trans h₂ ?_
    have hstep : Mh * C₂ ≤ Mh * C := mul_le_mul_of_nonneg_left hCC₂ hMh
    gcongr
  have h₃ := hhor F c d (-T) Mh hc hcd hdmax (by linarith) hMh hFb
  have h₃' : ‖∫ x : ℝ in c..d,
      dampedInvZeta P t ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I + (τ : ℂ) * Complex.I)
      * mellin (fun x' : ℝ =>
          ((GaloisForLFunctions.HTGeometry.smoothWeight N H x' : ℝ) : ℂ))
        ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I)‖ ≤ Mh * C / T ^ (j + 1) * (d - c) := by
    rw [hTnabs] at h₃
    refine le_trans h₃ ?_
    have hstep : Mh * C₂ ≤ Mh * C := mul_le_mul_of_nonneg_left hCC₂ hMh
    gcongr
  have h₄ := hver F c T Mc hc (le_trans hcd hdmax) hT hMc hFccont hFc
  have h₄' : ‖∫ y : ℝ in (-T)..T,
      dampedInvZeta P t ((c : ℂ) + (y : ℝ) * Complex.I + (τ : ℂ) * Complex.I)
      * mellin (fun x : ℝ =>
          ((GaloisForLFunctions.HTGeometry.smoothWeight N H x : ℝ) : ℂ))
        ((c : ℂ) + (y : ℝ) * Complex.I)‖
      ≤ Mc * (2 * ((N + H) ^ c / c) + 2 * C) := by
    refine le_trans h₄ ?_
    gcongr
  exact norm_tsum_dampedTwist_smoothWeight_le_edges hPprime ht0 ht1 hN hH τ hd hc hcd
    (le_of_lt hT0) hzf h₁' h₂' h₃' h₄'

end

end RHTower.Sieve
