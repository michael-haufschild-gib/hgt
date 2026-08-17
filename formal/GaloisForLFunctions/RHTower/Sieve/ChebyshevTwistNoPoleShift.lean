import GaloisForLFunctions.RHTower.Sieve.ChebyshevTwistLeftEdge
import GaloisForLFunctions.RHTower.Sieve.ChebyshevTwistEdgeBound

/-!
# The twisted contour above the truncation height

When the twist exceeds the truncation height the pole `1 - iτ` lies *outside* the rectangle, the
residue is not collected at all, and the twisted Chebyshev sum has no main term: the whole of

    2π ∑ₙ Λ(n) n^{-iτ} w(n)

is an error, bounded by the truncation tail plus the six edges of the rectangle.  This is the regime
in which a twisted prime sum exhibits genuine cancellation, and it is the one the
Matomäki--Radziwiłł ladder consumes.

There is no divided difference here.  The pole factor `(s + iτ - 1)⁻¹` is itself holomorphic on the
rectangle, and its size there is `(|τ| - T)⁻¹` *uniformly* — so the pole contributes nothing beyond
a factor that improves as the twist grows.  What replaces the residue bookkeeping is the single
inequality `|τ| - T ≤ |Im(s + iτ - 1)|` on the rectangle.
-/

namespace RHTower.Sieve

open Complex MeasureTheory GaloisForLFunctions.HTGeometry

/-- Below the twist the whole rectangle stays a fixed distance from the twisted pole, measured in
the imaginary direction alone. -/
theorem abs_im_shift_rect_ge {c d T τ : ℝ} (hT : 0 ≤ T) {s : ℂ}
    (hs : s ∈ Set.uIcc c d ×ℂ Set.uIcc (-T) T) :
    |τ| - T ≤ |(s + (τ : ℂ) * Complex.I - 1).im| := by
  have him : (s + (τ : ℂ) * Complex.I - 1).im = s.im + τ := by simp
  have hsim : |s.im| ≤ T := by
    rw [Complex.mem_reProdIm, Set.uIcc_of_le (by linarith : (-T : ℝ) ≤ T)] at hs
    exact abs_le.2 ⟨hs.2.1, hs.2.2⟩
  have h : |(s.im + τ) - s.im| ≤ |s.im + τ| + |s.im| := abs_sub _ _
  have he : (s.im + τ) - s.im = τ := by ring
  rw [he] at h
  rw [him]
  linarith

/-- The rectangle misses the twisted pole entirely. -/
theorem shift_ne_zero_rect {c d T τ : ℝ} (hT : 0 ≤ T) (hτ : T < |τ|) {s : ℂ}
    (hs : s ∈ Set.uIcc c d ×ℂ Set.uIcc (-T) T) :
    s + (τ : ℂ) * Complex.I - 1 ≠ 0 := by
  intro h
  have hge := abs_im_shift_rect_ge (c := c) (d := d) (τ := τ) hT hs
  rw [h] at hge
  simp only [Complex.zero_im, abs_zero] at hge
  linarith

/-- **The pole factor is uniformly small on the whole rectangle**, and it improves as the twist
grows past the truncation height. -/
theorem norm_inv_shift_rect_le {c d T τ : ℝ} (hT : 0 ≤ T) (hτ : T < |τ|) {s : ℂ}
    (hs : s ∈ Set.uIcc c d ×ℂ Set.uIcc (-T) T) :
    ‖(s + (τ : ℂ) * Complex.I - 1)⁻¹‖ ≤ (|τ| - T)⁻¹ := by
  have hge : |τ| - T ≤ ‖s + (τ : ℂ) * Complex.I - 1‖ :=
    le_trans (abs_im_shift_rect_ge (c := c) (d := d) (τ := τ) hT hs)
      (Complex.abs_im_le_norm _)
  rw [norm_inv]
  exact inv_anti₀ (by linarith) hge

/-- **The pole term of the twisted integrand is holomorphic on the rectangle** once the twist beats
the truncation height. -/
theorem differentiableOn_twistPoleInvW_rect {N H : ℝ} (hH : 0 < H) {c d T τ : ℝ}
    (hc0 : 0 < c) (hcd : c ≤ d) (hT : 0 ≤ T) (hτ : T < |τ|) :
    DifferentiableOn ℂ
      (fun s : ℂ => (s + (τ : ℂ) * Complex.I - 1)⁻¹
        * mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) s)
      (Set.uIcc c d ×ℂ Set.uIcc (-T) T) := by
  have hW : DifferentiableOn ℂ (mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)))
      (Set.uIcc c d ×ℂ Set.uIcc (-T) T) :=
    (differentiableOn_mellin_smoothWeight_strip hH hc0).mono (rect_subset_verticalStrip hcd T)
  have hlin : DifferentiableOn ℂ (fun s : ℂ => s + (τ : ℂ) * Complex.I - 1)
      (Set.uIcc c d ×ℂ Set.uIcc (-T) T) := by
    fun_prop
  exact (hlin.inv (fun s hs => shift_ne_zero_rect hT hτ hs)).mul hW

/-- **The truncated contour shift for the pole term of the twisted integrand.**  No residue: above
the truncation height the pole is outside the rectangle. -/
theorem integral_twistPoleInvW_vertical_sub_eq_horizontal_rect {N H : ℝ} (hH : 0 < H)
    {c d T τ : ℝ} (hc0 : 0 < c) (hcd : c ≤ d) (hT : 0 ≤ T) (hτ : T < |τ|) :
    (Complex.I • (∫ y : ℝ in (-T)..T,
          ((d : ℂ) + (y : ℝ) * Complex.I + (τ : ℂ) * Complex.I - 1)⁻¹
            * mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ))
                ((d : ℂ) + (y : ℝ) * Complex.I)))
        - Complex.I • (∫ y : ℝ in (-T)..T,
          ((c : ℂ) + (y : ℝ) * Complex.I + (τ : ℂ) * Complex.I - 1)⁻¹
            * mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ))
                ((c : ℂ) + (y : ℝ) * Complex.I))
      = (∫ x : ℝ in c..d,
            ((x : ℂ) + ((T : ℝ) : ℂ) * Complex.I + (τ : ℂ) * Complex.I - 1)⁻¹
              * mellin (fun x' : ℝ => ((smoothWeight N H x' : ℝ) : ℂ))
                  ((x : ℂ) + ((T : ℝ) : ℂ) * Complex.I))
        - ∫ x : ℝ in c..d,
            ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I + (τ : ℂ) * Complex.I - 1)⁻¹
              * mellin (fun x' : ℝ => ((smoothWeight N H x' : ℝ) : ℂ))
                  ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I) :=
  integral_vertical_sub_eq_horizontal_rect T
    (differentiableOn_twistPoleInvW_rect hH hc0 hcd hT hτ)

/-- **The twisted integrand on the Perron line, split in two.**  With no residue to isolate the
divided difference is unnecessary: the pole factor and the regular part suffice. -/
theorem chebyshev_twist_integrand_split_two {N H : ℝ} (τ : ℝ) {d y : ℝ} (hd : 1 < d) :
    (-logDeriv riemannZeta ((d : ℂ) + (y : ℝ) * Complex.I + (τ : ℂ) * Complex.I))
        * mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) ((d : ℂ) + (y : ℝ) * Complex.I)
      = ((d : ℂ) + (y : ℝ) * Complex.I + (τ : ℂ) * Complex.I - 1)⁻¹
          * mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) ((d : ℂ) + (y : ℝ) * Complex.I)
        + zetaLogDerivReg ((d : ℂ) + (y : ℝ) * Complex.I + (τ : ℂ) * Complex.I)
            * mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ))
                ((d : ℂ) + (y : ℝ) * Complex.I) := by
  have hne := sub_twistPole_ne_zero_line (d := d) (y := y) (τ := τ) hd
  rw [chebyshev_twist_integrand_split_line (N := N) (H := H) τ (d := d) (y := y) hd,
    dslope_mellin_twist_line (N := N) (H := H) (d := d) (y := y) (τ := τ) hd]
  field_simp
  ring

/-- **The truncated twisted Chebyshev identity above the truncation height.**  Three summands only:
the tail, the pole factor on the truncated line, and the regular part.  No main term. -/
theorem tsum_vonMangoldtTwist_truncated_two_identity (τ : ℝ) {N H : ℝ} (hN : 0 < N) (hH : 0 < H)
    {d T : ℝ} (hd : 1 < d) :
    (2 * Real.pi : ℝ) • (∑' n : ℕ,
        vonMangoldtTwist τ n * ((smoothWeight N H (n : ℝ) : ℝ) : ℂ))
      = ((∫ y : ℝ, (-logDeriv riemannZeta ((d : ℂ) + ((y + τ : ℝ)) * Complex.I))
              * mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ))
                  ((d : ℂ) + (y : ℝ) * Complex.I))
            - ∫ y : ℝ in (-T)..T, (-logDeriv riemannZeta ((d : ℂ) + ((y + τ : ℝ)) * Complex.I))
              * mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ))
                  ((d : ℂ) + (y : ℝ) * Complex.I))
        + (∫ y : ℝ in (-T)..T,
            ((d : ℂ) + (y : ℝ) * Complex.I + (τ : ℂ) * Complex.I - 1)⁻¹
              * mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ))
                  ((d : ℂ) + (y : ℝ) * Complex.I))
        + (∫ y : ℝ in (-T)..T,
            zetaLogDerivReg ((d : ℂ) + (y : ℝ) * Complex.I + (τ : ℂ) * Complex.I)
              * mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ))
                  ((d : ℂ) + (y : ℝ) * Complex.I)) := by
  have hd0 : (0 : ℝ) < d := by linarith
  have hperron := tsum_vonMangoldtTwist_smoothWeight_eq_logDeriv_integral τ hN hH hd
  have hshift : ∀ y : ℝ, (d : ℂ) + ((y + τ : ℝ)) * Complex.I
      = (d : ℂ) + (y : ℝ) * Complex.I + (τ : ℂ) * Complex.I := by
    intro y
    push_cast
    ring
  have hWcont : Continuous fun y : ℝ =>
      mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) ((d : ℂ) + (y : ℝ) * Complex.I) :=
    continuous_mellin_smoothWeight_line hH hd0
  have hlin : Continuous fun y : ℝ =>
      (d : ℂ) + (y : ℝ) * Complex.I + (τ : ℂ) * Complex.I - 1 := by fun_prop
  have hinv : Continuous fun y : ℝ =>
      ((d : ℂ) + (y : ℝ) * Complex.I + (τ : ℂ) * Complex.I - 1)⁻¹ :=
    hlin.inv₀ fun y => sub_twistPole_ne_zero_line hd
  have h1 : Continuous fun y : ℝ =>
      ((d : ℂ) + (y : ℝ) * Complex.I + (τ : ℂ) * Complex.I - 1)⁻¹
        * mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ))
            ((d : ℂ) + (y : ℝ) * Complex.I) := hinv.mul hWcont
  have h2 : Continuous fun y : ℝ =>
      zetaLogDerivReg ((d : ℂ) + (y : ℝ) * Complex.I + (τ : ℂ) * Complex.I)
        * mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ))
            ((d : ℂ) + (y : ℝ) * Complex.I) :=
    (continuous_zetaLogDerivRegTwist_line hd).mul hWcont
  have hsplitline : (∫ y : ℝ in (-T)..T,
        (-logDeriv riemannZeta ((d : ℂ) + ((y + τ : ℝ)) * Complex.I))
          * mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ))
              ((d : ℂ) + (y : ℝ) * Complex.I))
      = ∫ y : ℝ in (-T)..T,
          (((d : ℂ) + (y : ℝ) * Complex.I + (τ : ℂ) * Complex.I - 1)⁻¹
              * mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ))
                  ((d : ℂ) + (y : ℝ) * Complex.I)
            + zetaLogDerivReg ((d : ℂ) + (y : ℝ) * Complex.I + (τ : ℂ) * Complex.I)
                * mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ))
                    ((d : ℂ) + (y : ℝ) * Complex.I)) := by
    refine intervalIntegral.integral_congr fun y _ => ?_
    rw [hshift y]
    exact chebyshev_twist_integrand_split_two τ hd
  rw [hperron, hsplitline,
    intervalIntegral.integral_add (h1.intervalIntegrable _ _) (h2.intervalIntegrable _ _)]
  ring

/-- The pole term on the truncated right edge, moved to the left edge. -/
theorem norm_integral_twistPoleInvW_truncated_le {N H : ℝ} (hH : 0 < H) {c d T τ : ℝ}
    {E₂ E₃ E₄ : ℝ} (hc0 : 0 < c) (hcd : c ≤ d) (hT : 0 ≤ T) (hτ : T < |τ|)
    (htop : ‖∫ x : ℝ in c..d,
        ((x : ℂ) + ((T : ℝ) : ℂ) * Complex.I + (τ : ℂ) * Complex.I - 1)⁻¹
          * mellin (fun x' : ℝ => ((smoothWeight N H x' : ℝ) : ℂ))
              ((x : ℂ) + ((T : ℝ) : ℂ) * Complex.I)‖ ≤ E₂)
    (hbot : ‖∫ x : ℝ in c..d,
        ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I + (τ : ℂ) * Complex.I - 1)⁻¹
          * mellin (fun x' : ℝ => ((smoothWeight N H x' : ℝ) : ℂ))
              ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I)‖ ≤ E₃)
    (hleft : ‖∫ y : ℝ in (-T)..T,
        ((c : ℂ) + (y : ℝ) * Complex.I + (τ : ℂ) * Complex.I - 1)⁻¹
          * mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ))
              ((c : ℂ) + (y : ℝ) * Complex.I)‖ ≤ E₄) :
    ‖∫ y : ℝ in (-T)..T,
        ((d : ℂ) + (y : ℝ) * Complex.I + (τ : ℂ) * Complex.I - 1)⁻¹
          * mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ))
              ((d : ℂ) + (y : ℝ) * Complex.I)‖ ≤ E₂ + E₃ + E₄ :=
  norm_truncated_le_of_shift
    (integral_twistPoleInvW_vertical_sub_eq_horizontal_rect hH hc0 hcd hT hτ)
    htop hbot hleft

/-- **The twisted smoothed Chebyshev sum above the truncation height, with no main term.**  Seven
explicit pieces: the truncation tail, and the three edges of each of the two holomorphic halves of
the integrand. -/
theorem norm_tsum_vonMangoldtTwist_le_of_split_two (τ : ℝ) {N H : ℝ} (hN : 0 < N) (hH : 0 < H)
    {d T E₀ E₁ E₂ : ℝ} (hd : 1 < d)
    (htail : ‖(∫ y : ℝ, (-logDeriv riemannZeta ((d : ℂ) + ((y + τ : ℝ)) * Complex.I))
            * mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ))
                ((d : ℂ) + (y : ℝ) * Complex.I))
          - ∫ y : ℝ in (-T)..T, (-logDeriv riemannZeta ((d : ℂ) + ((y + τ : ℝ)) * Complex.I))
            * mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ))
                ((d : ℂ) + (y : ℝ) * Complex.I)‖ ≤ E₀)
    (hpole : ‖∫ y : ℝ in (-T)..T,
        ((d : ℂ) + (y : ℝ) * Complex.I + (τ : ℂ) * Complex.I - 1)⁻¹
          * mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ))
              ((d : ℂ) + (y : ℝ) * Complex.I)‖ ≤ E₁)
    (hreg : ‖∫ y : ℝ in (-T)..T,
        zetaLogDerivReg ((d : ℂ) + (y : ℝ) * Complex.I + (τ : ℂ) * Complex.I)
          * mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ))
              ((d : ℂ) + (y : ℝ) * Complex.I)‖ ≤ E₂) :
    ‖(2 * Real.pi : ℝ) • (∑' n : ℕ,
        vonMangoldtTwist τ n * ((smoothWeight N H (n : ℝ) : ℝ) : ℂ))‖ ≤ E₀ + E₁ + E₂ := by
  rw [tsum_vonMangoldtTwist_truncated_two_identity τ hN hH hd (T := T)]
  set A : ℂ := (∫ y : ℝ, (-logDeriv riemannZeta ((d : ℂ) + ((y + τ : ℝ)) * Complex.I))
        * mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) ((d : ℂ) + (y : ℝ) * Complex.I))
      - ∫ y : ℝ in (-T)..T, (-logDeriv riemannZeta ((d : ℂ) + ((y + τ : ℝ)) * Complex.I))
        * mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ))
            ((d : ℂ) + (y : ℝ) * Complex.I) with hA
  set B : ℂ := ∫ y : ℝ in (-T)..T,
      ((d : ℂ) + (y : ℝ) * Complex.I + (τ : ℂ) * Complex.I - 1)⁻¹
        * mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ))
            ((d : ℂ) + (y : ℝ) * Complex.I) with hB
  set D : ℂ := ∫ y : ℝ in (-T)..T,
      zetaLogDerivReg ((d : ℂ) + (y : ℝ) * Complex.I + (τ : ℂ) * Complex.I)
        * mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ))
            ((d : ℂ) + (y : ℝ) * Complex.I) with hD
  calc ‖A + B + D‖ ≤ ‖A + B‖ + ‖D‖ := norm_add_le _ _
    _ ≤ ‖A‖ + ‖B‖ + ‖D‖ := by linarith [norm_add_le A B]
    _ ≤ E₀ + E₁ + E₂ := by linarith


/-- On any horizontal slice below the twist the pole factor is uniformly small. -/
theorem norm_inv_shift_height_le {x u S τ : ℝ} (hτ : S < |τ|) (hu : |u| ≤ S) :
    ‖((x : ℂ) + (u : ℝ) * Complex.I + (τ : ℂ) * Complex.I - 1)⁻¹‖ ≤ (|τ| - S)⁻¹ := by
  have him : ((x : ℂ) + (u : ℝ) * Complex.I + (τ : ℂ) * Complex.I - 1).im = u + τ := by simp
  have h : |(u + τ) - u| ≤ |u + τ| + |u| := abs_sub _ _
  have he : (u + τ) - u = τ := by ring
  rw [he] at h
  have hge : |τ| - S ≤ ‖(x : ℂ) + (u : ℝ) * Complex.I + (τ : ℂ) * Complex.I - 1‖ := by
    have hnorm :=
      Complex.abs_im_le_norm ((x : ℂ) + (u : ℝ) * Complex.I + (τ : ℂ) * Complex.I - 1)
    rw [him] at hnorm
    linarith
  rw [norm_inv]
  exact inv_anti₀ (by linarith) hge

/-- The same slice misses the twisted pole. -/
theorem shift_ne_zero_height {x u S τ : ℝ} (hτ : S < |τ|) (hu : |u| ≤ S) :
    (x : ℂ) + (u : ℝ) * Complex.I + (τ : ℂ) * Complex.I - 1 ≠ 0 := by
  intro h
  have him : ((x : ℂ) + (u : ℝ) * Complex.I + (τ : ℂ) * Complex.I - 1).im = u + τ := by simp
  have hab : |(u + τ) - u| ≤ |u + τ| + |u| := abs_sub _ _
  have he : (u + τ) - u = τ := by ring
  rw [he] at hab
  rw [h] at him
  simp only [Complex.zero_im] at him
  rw [← him] at hab
  simp only [abs_zero] at hab
  linarith

/-- **The left edge of the pole term above the truncation height.**  The whole cost is the vertical
mass of the cutoff's transform against the twist-improved factor `(|τ| - T)⁻¹`. -/
theorem norm_integral_left_vertical_twistPoleInv_le {N H c T C τ : ℝ} (hN : 0 < N) (hH : 0 < H)
    (hc0 : 0 < c) (hT : 1 ≤ T) (hτ : T < |τ|)
    (hbd : ∀ s : ℂ, 0 < s.re → s.re ≤ c →
      |s.im| ^ (1 + 1) * ‖mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) s‖ ≤ C) :
    ‖∫ y : ℝ in (-T)..T,
        ((c : ℂ) + (y : ℝ) * Complex.I + (τ : ℂ) * Complex.I - 1)⁻¹
          * mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ))
              ((c : ℂ) + (y : ℝ) * Complex.I)‖
      ≤ (|τ| - T)⁻¹ * (2 * ((N + H) ^ c / c) + 2 * C) := by
  have hTT : (-T : ℝ) ≤ T := by linarith
  refine norm_integral_vertical_edge_le hN hH hc0 hT (inv_nonneg.2 (by linarith)) hbd
    (F := fun s : ℂ => (s + (τ : ℂ) * Complex.I - 1)⁻¹) ?_ ?_
  · refine ContinuousOn.inv₀ (by fun_prop) (fun y hy => ?_)
    rw [Set.uIcc_of_le hTT] at hy
    exact shift_ne_zero_height hτ (abs_le.2 ⟨hy.1, hy.2⟩)
  · intro y hy
    exact norm_inv_shift_height_le hτ (abs_le.2 ⟨hy.1, hy.2⟩)

/-- **The horizontal edges of the pole term above the truncation height.** -/
theorem exists_bound_horizontal_twistPoleInv {N H : ℝ} (hN : 0 < N) (hH : 0 < H) (j : ℕ)
    (σmax : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ c d T τ : ℝ, 0 < c → c ≤ d → d ≤ σmax → T ≠ 0 → |T| < |τ| →
      ‖∫ x : ℝ in c..d,
          ((x : ℂ) + ((T : ℝ) : ℂ) * Complex.I + (τ : ℂ) * Complex.I - 1)⁻¹
            * mellin (fun x' : ℝ => ((smoothWeight N H x' : ℝ) : ℂ))
                ((x : ℂ) + ((T : ℝ) : ℂ) * Complex.I)‖
        ≤ (|τ| - |T|)⁻¹ * C / |T| ^ (j + 1) * (d - c) := by
  obtain ⟨C, hC, hbd⟩ := exists_horizontal_edge_bound hN hH j σmax
  refine ⟨C, hC, fun c d T τ hc hcd hdmax hT hτ => ?_⟩
  exact hbd (fun s : ℂ => (s + (τ : ℂ) * Complex.I - 1)⁻¹) c d T ((|τ| - |T|)⁻¹) hc hcd hdmax hT
    (inv_nonneg.2 (by linarith)) (fun x _ => norm_inv_shift_height_le hτ (le_refl |T|))

end RHTower.Sieve
