import GaloisForLFunctions.RHTower.Sieve.PerronEdgeAssembly
import GaloisForLFunctions.RHTower.Sieve.VerticalEdgeBound

/-!
# The four edges, substituted

Each of the four edge estimates is proved with its own constant.  Substituting them into the
combination gives a single inequality for the smoothed Möbius sum in which the only remaining data
are the geometry `c, d, T` of the rectangle and three bounds `Md, Mh, Mc` for `invZeta` on the
right line, the horizontal edges and the left line.

The three constants are merged into one by taking the largest: every bound depends on its constant
monotonically, because the coefficient multiplying it is a norm bound and hence nonnegative.
-/

namespace RHTower.Sieve

open Complex MeasureTheory GaloisForLFunctions.HTGeometry

/-- **The smoothed Möbius sum, bounded by the rectangle data.**  A single unconditional inequality:
the only inputs are the size of `invZeta` on the three edges and the geometry of the rectangle. -/
theorem exists_norm_tsum_moebius_smoothWeight_le {N H : ℝ} (hN : 0 < N) (hH : 0 < H) (j : ℕ)
    (σmax : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ c d T Md Mh Mc : ℝ,
      1 < d → d ≤ σmax → 0 < c → c ≤ d → 1 ≤ T → 0 ≤ Md → 0 ≤ Mh → 0 ≤ Mc →
      (∀ s ∈ Set.uIcc c d ×ℂ Set.uIcc (-T) T, s ≠ 1 → riemannZeta s ≠ 0) →
      (∀ y : ℝ, ‖invZeta ((d : ℂ) + (y : ℝ) * Complex.I)‖ ≤ Md) →
      (∀ x ∈ Set.Ioc c d, ‖invZeta ((x : ℂ) + ((T : ℝ) : ℂ) * Complex.I)‖ ≤ Mh) →
      (∀ x ∈ Set.Ioc c d, ‖invZeta ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I)‖ ≤ Mh) →
      (∀ y ∈ Set.Icc (-T) T, ‖invZeta ((c : ℂ) + (y : ℝ) * Complex.I)‖ ≤ Mc) →
      ContinuousOn (fun y : ℝ => invZeta ((c : ℂ) + (y : ℝ) * Complex.I)) (Set.uIcc (-T) T) →
      ‖(2 * Real.pi : ℝ) • (∑' n : ℕ,
          (ArithmeticFunction.moebius n : ℂ) * ((smoothWeight N H (n : ℝ) : ℝ) : ℂ))‖
        ≤ 2 * (Md * C) / T
            + Mh * C / T ^ (j + 1) * (d - c)
            + Mh * C / T ^ (j + 1) * (d - c)
            + Mc * (2 * ((N + H) ^ c / c) + 2 * C) := by
  obtain ⟨C₁, hC₁, htr⟩ := exists_bound_truncation_error hN hH σmax
  obtain ⟨C₂, hC₂, hhor⟩ := exists_horizontal_edge_bound hN hH j σmax
  obtain ⟨C₃, hC₃, hver⟩ := exists_vertical_edge_bound hN hH σmax
  refine ⟨max (max C₁ C₂) C₃, le_trans hC₁ (le_trans (le_max_left _ _) (le_max_left _ _)),
    fun c d T Md Mh Mc hd hdmax hc hcd hT hMd hMh hMc hzf hFd hFt hFb hFc hFccont => ?_⟩
  set C : ℝ := max (max C₁ C₂) C₃ with hCdef
  have hCC₁ : C₁ ≤ C := le_trans (le_max_left _ _) (le_max_left _ _)
  have hCC₂ : C₂ ≤ C := le_trans (le_max_right _ _) (le_max_left _ _)
  have hCC₃ : C₃ ≤ C := le_max_right _ _
  have hT0 : (0 : ℝ) < T := by linarith
  have hTabs : |T| = T := abs_of_pos hT0
  have hTnabs : |(-T)| = T := by rw [abs_neg, hTabs]
  have hd0 : (0 : ℝ) < d := by linarith
  have hdc : (0 : ℝ) ≤ d - c := by linarith
  -- the truncation error
  have h₁ := htr invZeta d T Md hd0 hdmax hT hMd (continuous_invZeta_line hd) hFd
  have h₁' : ‖(∫ y : ℝ, invZeta ((d : ℂ) + (y : ℝ) * Complex.I)
        * mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) ((d : ℂ) + (y : ℝ) * Complex.I))
      - ∫ y : ℝ in (-T)..T, invZeta ((d : ℂ) + (y : ℝ) * Complex.I)
        * mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ))
            ((d : ℂ) + (y : ℝ) * Complex.I)‖ ≤ 2 * (Md * C) / T := by
    refine le_trans h₁ ?_
    have : Md * C₁ ≤ Md * C := mul_le_mul_of_nonneg_left hCC₁ hMd
    gcongr
  -- the horizontal edges
  have h₂ := hhor invZeta c d T Mh hc hcd hdmax (ne_of_gt hT0) hMh hFt
  have h₂' : ‖∫ x : ℝ in c..d, invZeta ((x : ℂ) + ((T : ℝ) : ℂ) * Complex.I)
      * mellin (fun x' : ℝ => ((smoothWeight N H x' : ℝ) : ℂ))
          ((x : ℂ) + ((T : ℝ) : ℂ) * Complex.I)‖ ≤ Mh * C / T ^ (j + 1) * (d - c) := by
    rw [hTabs] at h₂
    refine le_trans h₂ ?_
    have hstep : Mh * C₂ ≤ Mh * C := mul_le_mul_of_nonneg_left hCC₂ hMh
    gcongr
  have h₃ := hhor invZeta c d (-T) Mh hc hcd hdmax (by linarith) hMh hFb
  have h₃' : ‖∫ x : ℝ in c..d, invZeta ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I)
      * mellin (fun x' : ℝ => ((smoothWeight N H x' : ℝ) : ℂ))
          ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I)‖ ≤ Mh * C / T ^ (j + 1) * (d - c) := by
    rw [hTnabs] at h₃
    refine le_trans h₃ ?_
    have hstep : Mh * C₂ ≤ Mh * C := mul_le_mul_of_nonneg_left hCC₂ hMh
    gcongr
  -- the left edge
  have h₄ := hver invZeta c T Mc hc (le_trans hcd hdmax) hT hMc hFccont hFc
  have h₄' : ‖∫ y : ℝ in (-T)..T, invZeta ((c : ℂ) + (y : ℝ) * Complex.I)
      * mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ))
          ((c : ℂ) + (y : ℝ) * Complex.I)‖
      ≤ Mc * (2 * ((N + H) ^ c / c) + 2 * C) := by
    refine le_trans h₄ ?_
    gcongr
  exact norm_tsum_moebius_smoothWeight_le_edges hN hH hd hc hcd hzf h₁' h₂' h₃' h₄'

end RHTower.Sieve
