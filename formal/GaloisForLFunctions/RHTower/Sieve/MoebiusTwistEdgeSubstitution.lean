import GaloisForLFunctions.RHTower.Sieve.MoebiusTwistEdgeAssembly
import GaloisForLFunctions.RHTower.Sieve.PerronEdgeSubstitution
import GaloisForLFunctions.RHTower.Sieve.InvZetaEdgeBounds

/-!
# The four edges of the twisted contour, substituted

The three edge estimates of the Perron argument — the truncation error, the horizontal edges and the
left vertical edge — are stated for an arbitrary integrand, so they apply verbatim to
`invZeta(· + iτ)`.  Substituting them into the four-edge inequality gives the twisted analogue of the
contour bound:

`‖∑' μ(n)n^{-iτ}·w(n)‖ ≤ 2M_d C/T + 2 M_h C (d-c)/T^{j+1} + M_c(2(N+H)^c/c + 2C)`

with the same absolute constant `C` for every twist.  Only the zero-free hypothesis moves: it is
taken at the enlarged height `|τ| + T`.
-/

namespace RHTower.Sieve

open Complex MeasureTheory GaloisForLFunctions.HTGeometry

/-- The shift by `τ` maps `[-T, T]` into `[-(|τ|+T), |τ|+T]`. -/
theorem mapsTo_add_const_uIcc {T : ℝ} (τ : ℝ) (hT : 0 ≤ T) :
    Set.MapsTo (fun y : ℝ => y + τ) (Set.uIcc (-T) T) (Set.uIcc (-(|τ| + T)) (|τ| + T)) := by
  intro y hy
  have habs : (0 : ℝ) ≤ |τ| := abs_nonneg τ
  have h1 : -|τ| ≤ τ := neg_abs_le τ
  have h2 : τ ≤ |τ| := le_abs_self τ
  rw [Set.uIcc_of_le (by linarith : (-T : ℝ) ≤ T), Set.mem_Icc] at hy
  rw [Set.uIcc_of_le (by linarith : -(|τ| + T) ≤ |τ| + T), Set.mem_Icc]
  exact ⟨by linarith [hy.1], by linarith [hy.2]⟩

/-- The twisted integrand is continuous on a line right of the abscissa. -/
theorem continuous_invZetaTwist_line {d : ℝ} (τ : ℝ) (hd : 1 < d) :
    Continuous fun y : ℝ =>
      invZeta ((d : ℂ) + (y : ℝ) * Complex.I + (τ : ℂ) * Complex.I) := by
  have hfun : (fun y : ℝ => invZeta ((d : ℂ) + (y : ℝ) * Complex.I + (τ : ℂ) * Complex.I))
      = (fun y : ℝ => invZeta ((d : ℂ) + (y : ℝ) * Complex.I)) ∘ fun y : ℝ => y + τ := by
    funext y
    simp only [Function.comp_apply]
    congr 1
    push_cast
    ring
  rw [hfun]
  exact (continuous_invZeta_line hd).comp (continuous_id.add continuous_const)

/-- The twisted integrand is continuous on the truncated left edge. -/
theorem continuousOn_invZetaTwist_left_line {c d T : ℝ} (τ : ℝ) (hT : 0 ≤ T) (hcd : c ≤ 1)
    (hd1 : 1 ≤ d)
    (hzf : ∀ s ∈ Set.uIcc c d ×ℂ Set.uIcc (-(|τ| + T)) (|τ| + T), s ≠ 1 → riemannZeta s ≠ 0) :
    ContinuousOn (fun y : ℝ => invZeta ((c : ℂ) + (y : ℝ) * Complex.I + (τ : ℂ) * Complex.I))
      (Set.uIcc (-T) T) := by
  have hfun : (fun y : ℝ => invZeta ((c : ℂ) + (y : ℝ) * Complex.I + (τ : ℂ) * Complex.I))
      = (fun y : ℝ => invZeta ((c : ℂ) + (y : ℝ) * Complex.I)) ∘ fun y : ℝ => y + τ := by
    funext y
    simp only [Function.comp_apply]
    congr 1
    push_cast
    ring
  rw [hfun]
  exact (continuousOn_invZeta_left_line hcd hd1 hzf).comp
    (continuous_id.add continuous_const).continuousOn (mapsTo_add_const_uIcc τ hT)

/-- **The twisted contour bound with the edges substituted.**  One absolute constant `C`, uniform in
the twist; the zero-free input is taken at height `|τ| + T`. -/
theorem exists_norm_tsum_moebiusTwist_smoothWeight_le {N H : ℝ} (hN : 0 < N) (hH : 0 < H) (j : ℕ)
    (σmax : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ τ c d T Md Mh Mc : ℝ,
      1 < d → d ≤ σmax → 0 < c → c ≤ d → 1 ≤ T → 0 ≤ Md → 0 ≤ Mh → 0 ≤ Mc →
      (∀ s ∈ Set.uIcc c d ×ℂ Set.uIcc (-(|τ| + T)) (|τ| + T), s ≠ 1 → riemannZeta s ≠ 0) →
      (∀ y : ℝ, ‖invZeta ((d : ℂ) + (y : ℝ) * Complex.I + (τ : ℂ) * Complex.I)‖ ≤ Md) →
      (∀ x ∈ Set.Ioc c d,
        ‖invZeta ((x : ℂ) + ((T : ℝ) : ℂ) * Complex.I + (τ : ℂ) * Complex.I)‖ ≤ Mh) →
      (∀ x ∈ Set.Ioc c d,
        ‖invZeta ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I + (τ : ℂ) * Complex.I)‖ ≤ Mh) →
      (∀ y ∈ Set.Icc (-T) T,
        ‖invZeta ((c : ℂ) + (y : ℝ) * Complex.I + (τ : ℂ) * Complex.I)‖ ≤ Mc) →
      ContinuousOn (fun y : ℝ => invZeta ((c : ℂ) + (y : ℝ) * Complex.I + (τ : ℂ) * Complex.I))
        (Set.uIcc (-T) T) →
      ‖(2 * Real.pi : ℝ) • (∑' n : ℕ,
          moebiusTwist τ n * ((smoothWeight N H (n : ℝ) : ℝ) : ℂ))‖
        ≤ 2 * (Md * C) / T
            + Mh * C / T ^ (j + 1) * (d - c)
            + Mh * C / T ^ (j + 1) * (d - c)
            + Mc * (2 * ((N + H) ^ c / c) + 2 * C) := by
  obtain ⟨C₁, hC₁, htr⟩ := exists_bound_truncation_error hN hH σmax
  obtain ⟨C₂, hC₂, hhor⟩ := exists_horizontal_edge_bound hN hH j σmax
  obtain ⟨C₃, hC₃, hver⟩ := exists_vertical_edge_bound hN hH σmax
  refine ⟨max (max C₁ C₂) C₃, le_trans hC₁ (le_trans (le_max_left _ _) (le_max_left _ _)),
    fun τ c d T Md Mh Mc hd hdmax hc hcd hT hMd hMh hMc hzf hFd hFt hFb hFc hFccont => ?_⟩
  set F : ℂ → ℂ := fun s => invZeta (s + (τ : ℂ) * Complex.I) with hFdef
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
  have h₁ := htr F d T Md hd0 hdmax hT hMd (continuous_invZetaTwist_line τ hd) hFd
  have h₁' : ‖(∫ y : ℝ, invZeta ((d : ℂ) + (y : ℝ) * Complex.I + (τ : ℂ) * Complex.I)
        * mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) ((d : ℂ) + (y : ℝ) * Complex.I))
      - ∫ y : ℝ in (-T)..T, invZeta ((d : ℂ) + (y : ℝ) * Complex.I + (τ : ℂ) * Complex.I)
        * mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ))
            ((d : ℂ) + (y : ℝ) * Complex.I)‖ ≤ 2 * (Md * C) / T := by
    refine le_trans h₁ ?_
    have : Md * C₁ ≤ Md * C := mul_le_mul_of_nonneg_left hCC₁ hMd
    gcongr
  -- the horizontal edges
  have h₂ := hhor F c d T Mh hc hcd hdmax (ne_of_gt hT0) hMh hFt
  have h₂' : ‖∫ x : ℝ in c..d,
      invZeta ((x : ℂ) + ((T : ℝ) : ℂ) * Complex.I + (τ : ℂ) * Complex.I)
      * mellin (fun x' : ℝ => ((smoothWeight N H x' : ℝ) : ℂ))
          ((x : ℂ) + ((T : ℝ) : ℂ) * Complex.I)‖ ≤ Mh * C / T ^ (j + 1) * (d - c) := by
    rw [hTabs] at h₂
    refine le_trans h₂ ?_
    have hstep : Mh * C₂ ≤ Mh * C := mul_le_mul_of_nonneg_left hCC₂ hMh
    gcongr
  have h₃ := hhor F c d (-T) Mh hc hcd hdmax (by linarith) hMh hFb
  have h₃' : ‖∫ x : ℝ in c..d,
      invZeta ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I + (τ : ℂ) * Complex.I)
      * mellin (fun x' : ℝ => ((smoothWeight N H x' : ℝ) : ℂ))
          ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I)‖ ≤ Mh * C / T ^ (j + 1) * (d - c) := by
    rw [hTnabs] at h₃
    refine le_trans h₃ ?_
    have hstep : Mh * C₂ ≤ Mh * C := mul_le_mul_of_nonneg_left hCC₂ hMh
    gcongr
  -- the left edge
  have h₄ := hver F c T Mc hc (le_trans hcd hdmax) hT hMc hFccont hFc
  have h₄' : ‖∫ y : ℝ in (-T)..T,
      invZeta ((c : ℂ) + (y : ℝ) * Complex.I + (τ : ℂ) * Complex.I)
      * mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ))
          ((c : ℂ) + (y : ℝ) * Complex.I)‖
      ≤ Mc * (2 * ((N + H) ^ c / c) + 2 * C) := by
    refine le_trans h₄ ?_
    gcongr
  exact norm_tsum_moebiusTwist_smoothWeight_le_edges hN hH τ hd hc hcd (le_of_lt hT0) hzf
    h₁' h₂' h₃' h₄'

end RHTower.Sieve
