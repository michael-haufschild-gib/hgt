import GaloisForLFunctions.RHTower.Sieve.ZetaLogDerivRegTwistShift
import GaloisForLFunctions.RHTower.Sieve.PerronEdgeSubstitution

/-!
# The four edges of the twisted regular Chebyshev integral

The corpus's three edge estimates — truncation error, horizontal edge, vertical edge — are stated
for an arbitrary integrand `F(s)·W(s)`, so they apply verbatim to the twisted regular part
`F = zetaLogDerivReg(· + iτ)`.  Substituting them into the four-edge combination, and taking the
largest of the three constants, leaves a single unconditional inequality whose only inputs are sup
bounds for the twisted regular part on the three edges and the geometry of the rectangle.

No residue appears: the whole pole of `-ζ'/ζ` was separated in `ChebyshevTwistPerronIdentity`, so
the regular part crosses the abscissa freely.  The zero-free hypothesis is taken at the enlarged
height `|τ| + T`, which is exactly what the twist costs.

Also recorded is the elementary bound `‖zetaLogDerivReg s‖ ≤ ‖ζ'/ζ(s)‖ + ‖(s-1)⁻¹‖`, which is how
the Route-T logarithmic-derivative estimate feeds the left edge.
-/

namespace RHTower.Sieve

open Complex MeasureTheory GaloisForLFunctions.HTGeometry

/-- The regular part is the logarithmic derivative with the pole removed, so it is bounded by the
logarithmic derivative plus the pole. -/
theorem norm_zetaLogDerivReg_le_logDeriv {s : ℂ} (hs : s ≠ 1) (hz : riemannZeta s ≠ 0) :
    ‖zetaLogDerivReg s‖ ≤ ‖logDeriv riemannZeta s‖ + ‖(s - 1)⁻¹‖ := by
  have hsplit := neg_logDeriv_riemannZeta_eq_of_ne_zero hs hz
  have hreg : zetaLogDerivReg s = -logDeriv riemannZeta s - (s - 1)⁻¹ := by
    linear_combination -hsplit
  rw [hreg]
  refine le_trans (norm_sub_le _ _) ?_
  rw [norm_neg]

/-- The twisted regular part is continuous on a line right of the abscissa. -/
theorem continuous_zetaLogDerivRegTwist_line {d τ : ℝ} (hd : 1 < d) :
    Continuous fun y : ℝ =>
      zetaLogDerivReg ((d : ℂ) + (y : ℝ) * Complex.I + (τ : ℂ) * Complex.I) := by
  refine continuous_iff_continuousAt.2 fun y => ?_
  have hre : ((d : ℂ) + (y : ℝ) * Complex.I + (τ : ℂ) * Complex.I).re = d := by simp
  have hne : ((d : ℂ) + (y : ℝ) * Complex.I + (τ : ℂ) * Complex.I) ≠ 1 := by
    intro h
    rw [h] at hre
    simp at hre
    linarith
  have hz : riemannZeta ((d : ℂ) + (y : ℝ) * Complex.I + (τ : ℂ) * Complex.I) ≠ 0 :=
    riemannZeta_ne_zero_of_one_le_re (by rw [hre]; linarith)
  have hin : Continuous fun u : ℝ =>
      ((d : ℂ) + (u : ℝ) * Complex.I + (τ : ℂ) * Complex.I) := by fun_prop
  exact ContinuousAt.comp (g := zetaLogDerivReg)
    (f := fun u : ℝ => ((d : ℂ) + (u : ℝ) * Complex.I + (τ : ℂ) * Complex.I))
    ((differentiableAt_zetaLogDerivReg
      ((zetaResidueUnit_ne_zero_iff hne).2 hz)).continuousAt) hin.continuousAt

/-- **The twisted regular Perron integral, bounded by the four edges.** -/
theorem norm_integral_zetaLogDerivRegTwist_le_edges {N H : ℝ} (hH : 0 < H)
    {c d T E₁ E₂ E₃ E₄ : ℝ} (τ : ℝ) (hc : 0 < c) (hcd : c ≤ d) (hT : 0 ≤ T)
    (hzf : ∀ s ∈ Set.uIcc c d ×ℂ Set.uIcc (-(|τ| + T)) (|τ| + T), s ≠ 1 → riemannZeta s ≠ 0)
    (htrunc : ‖(∫ y : ℝ, zetaLogDerivReg ((d : ℂ) + (y : ℝ) * Complex.I + (τ : ℂ) * Complex.I)
            * mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) ((d : ℂ) + (y : ℝ) * Complex.I))
          - ∫ y : ℝ in (-T)..T,
            zetaLogDerivReg ((d : ℂ) + (y : ℝ) * Complex.I + (τ : ℂ) * Complex.I)
              * mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ))
                  ((d : ℂ) + (y : ℝ) * Complex.I)‖ ≤ E₁)
    (htop : ‖∫ x : ℝ in c..d,
        zetaLogDerivReg ((x : ℂ) + ((T : ℝ) : ℂ) * Complex.I + (τ : ℂ) * Complex.I)
          * mellin (fun x' : ℝ => ((smoothWeight N H x' : ℝ) : ℂ))
              ((x : ℂ) + ((T : ℝ) : ℂ) * Complex.I)‖ ≤ E₂)
    (hbot : ‖∫ x : ℝ in c..d,
        zetaLogDerivReg ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I + (τ : ℂ) * Complex.I)
          * mellin (fun x' : ℝ => ((smoothWeight N H x' : ℝ) : ℂ))
              ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I)‖ ≤ E₃)
    (hleft : ‖∫ y : ℝ in (-T)..T,
        zetaLogDerivReg ((c : ℂ) + (y : ℝ) * Complex.I + (τ : ℂ) * Complex.I)
          * mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ))
              ((c : ℂ) + (y : ℝ) * Complex.I)‖ ≤ E₄) :
    ‖∫ y : ℝ, zetaLogDerivReg ((d : ℂ) + (y : ℝ) * Complex.I + (τ : ℂ) * Complex.I)
        * mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) ((d : ℂ) + (y : ℝ) * Complex.I)‖
      ≤ E₁ + E₂ + E₃ + E₄ :=
  norm_le_of_contour_edges
    (integral_zetaLogDerivRegTwistW_vertical_sub_eq_horizontal_rect hH τ hc hcd hT hzf)
    htrunc htop hbot hleft

/-- **The twisted regular Perron integral, bounded by the rectangle data.**  A single unconditional
inequality: the only inputs are sup bounds for the twisted regular part on the three edges and the
geometry of the rectangle. -/
theorem exists_norm_integral_zetaLogDerivRegTwist_le {N H : ℝ} (hN : 0 < N) (hH : 0 < H) (j : ℕ)
    (σmax : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ τ c d T Md Mh Mc : ℝ,
      1 < d → d ≤ σmax → 0 < c → c ≤ d → 1 ≤ T → 0 ≤ Md → 0 ≤ Mh → 0 ≤ Mc →
      (∀ s ∈ Set.uIcc c d ×ℂ Set.uIcc (-(|τ| + T)) (|τ| + T), s ≠ 1 → riemannZeta s ≠ 0) →
      (∀ y : ℝ, ‖zetaLogDerivReg ((d : ℂ) + (y : ℝ) * Complex.I + (τ : ℂ) * Complex.I)‖ ≤ Md) →
      (∀ x ∈ Set.Ioc c d,
        ‖zetaLogDerivReg ((x : ℂ) + ((T : ℝ) : ℂ) * Complex.I + (τ : ℂ) * Complex.I)‖ ≤ Mh) →
      (∀ x ∈ Set.Ioc c d,
        ‖zetaLogDerivReg ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I + (τ : ℂ) * Complex.I)‖ ≤ Mh) →
      (∀ y ∈ Set.Icc (-T) T,
        ‖zetaLogDerivReg ((c : ℂ) + (y : ℝ) * Complex.I + (τ : ℂ) * Complex.I)‖ ≤ Mc) →
      ContinuousOn (fun y : ℝ =>
          zetaLogDerivReg ((c : ℂ) + (y : ℝ) * Complex.I + (τ : ℂ) * Complex.I))
        (Set.uIcc (-T) T) →
      ‖∫ y : ℝ, zetaLogDerivReg ((d : ℂ) + (y : ℝ) * Complex.I + (τ : ℂ) * Complex.I)
          * mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) ((d : ℂ) + (y : ℝ) * Complex.I)‖
        ≤ 2 * (Md * C) / T
            + Mh * C / T ^ (j + 1) * (d - c)
            + Mh * C / T ^ (j + 1) * (d - c)
            + Mc * (2 * ((N + H) ^ c / c) + 2 * C) := by
  obtain ⟨C₁, hC₁, htr⟩ := exists_bound_truncation_error hN hH σmax
  obtain ⟨C₂, hC₂, hhor⟩ := exists_horizontal_edge_bound hN hH j σmax
  obtain ⟨C₃, hC₃, hver⟩ := exists_vertical_edge_bound hN hH σmax
  refine ⟨max (max C₁ C₂) C₃, le_trans hC₁ (le_trans (le_max_left _ _) (le_max_left _ _)),
    fun τ c d T Md Mh Mc hd hdmax hc hcd hT hMd hMh hMc hzf hFd hFt hFb hFc hFccont => ?_⟩
  set C : ℝ := max (max C₁ C₂) C₃ with hCdef
  have hCC₁ : C₁ ≤ C := le_trans (le_max_left _ _) (le_max_left _ _)
  have hCC₂ : C₂ ≤ C := le_trans (le_max_right _ _) (le_max_left _ _)
  have hCC₃ : C₃ ≤ C := le_max_right _ _
  have hT0 : (0 : ℝ) < T := by linarith
  have hTabs : |T| = T := abs_of_pos hT0
  have hTnabs : |(-T)| = T := by rw [abs_neg, hTabs]
  have hd0 : (0 : ℝ) < d := by linarith
  have hdc : (0 : ℝ) ≤ d - c := by linarith
  have h₁ := htr (fun s => zetaLogDerivReg (s + (τ : ℂ) * Complex.I)) d T Md hd0 hdmax hT hMd
    (continuous_zetaLogDerivRegTwist_line hd) hFd
  have h₁' : ‖(∫ y : ℝ, zetaLogDerivReg ((d : ℂ) + (y : ℝ) * Complex.I + (τ : ℂ) * Complex.I)
        * mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) ((d : ℂ) + (y : ℝ) * Complex.I))
      - ∫ y : ℝ in (-T)..T,
        zetaLogDerivReg ((d : ℂ) + (y : ℝ) * Complex.I + (τ : ℂ) * Complex.I)
          * mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ))
              ((d : ℂ) + (y : ℝ) * Complex.I)‖ ≤ 2 * (Md * C) / T := by
    refine le_trans h₁ ?_
    have : Md * C₁ ≤ Md * C := mul_le_mul_of_nonneg_left hCC₁ hMd
    gcongr
  have h₂ := hhor (fun s => zetaLogDerivReg (s + (τ : ℂ) * Complex.I)) c d T Mh hc hcd hdmax
    (ne_of_gt hT0) hMh hFt
  have h₂' : ‖∫ x : ℝ in c..d,
      zetaLogDerivReg ((x : ℂ) + ((T : ℝ) : ℂ) * Complex.I + (τ : ℂ) * Complex.I)
        * mellin (fun x' : ℝ => ((smoothWeight N H x' : ℝ) : ℂ))
            ((x : ℂ) + ((T : ℝ) : ℂ) * Complex.I)‖ ≤ Mh * C / T ^ (j + 1) * (d - c) := by
    rw [hTabs] at h₂
    refine le_trans h₂ ?_
    have hstep : Mh * C₂ ≤ Mh * C := mul_le_mul_of_nonneg_left hCC₂ hMh
    gcongr
  have h₃ := hhor (fun s => zetaLogDerivReg (s + (τ : ℂ) * Complex.I)) c d (-T) Mh hc hcd hdmax
    (by linarith) hMh hFb
  have h₃' : ‖∫ x : ℝ in c..d,
      zetaLogDerivReg ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I + (τ : ℂ) * Complex.I)
        * mellin (fun x' : ℝ => ((smoothWeight N H x' : ℝ) : ℂ))
            ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I)‖ ≤ Mh * C / T ^ (j + 1) * (d - c) := by
    rw [hTnabs] at h₃
    refine le_trans h₃ ?_
    have hstep : Mh * C₂ ≤ Mh * C := mul_le_mul_of_nonneg_left hCC₂ hMh
    gcongr
  have h₄ := hver (fun s => zetaLogDerivReg (s + (τ : ℂ) * Complex.I)) c T Mc hc
    (le_trans hcd hdmax) hT hMc hFccont hFc
  have h₄' : ‖∫ y : ℝ in (-T)..T,
      zetaLogDerivReg ((c : ℂ) + (y : ℝ) * Complex.I + (τ : ℂ) * Complex.I)
        * mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ))
            ((c : ℂ) + (y : ℝ) * Complex.I)‖
      ≤ Mc * (2 * ((N + H) ^ c / c) + 2 * C) := by
    refine le_trans h₄ ?_
    gcongr
  exact norm_integral_zetaLogDerivRegTwist_le_edges hH τ hc hcd (by linarith : (0:ℝ) ≤ T) hzf h₁' h₂' h₃' h₄'

end RHTower.Sieve
