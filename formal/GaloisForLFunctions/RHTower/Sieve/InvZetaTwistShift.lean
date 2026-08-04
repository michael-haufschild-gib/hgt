import GaloisForLFunctions.RHTower.Sieve.InvZetaProductShift

/-!
# The contour shift for the twisted Perron integrand

The Perron integrand of the twisted Möbius function is `invZeta(s + iτ)·W(s)`.  Holomorphy of the
first factor on a rectangle `[c,d] × [-T,T]` is holomorphy of `invZeta` on the *translated*
rectangle `[c,d] × [τ-T, τ+T]`, and that is contained in the corpus's symmetric rectangle at the
enlarged height `|τ| + T`.  So the whole four-edge identity transfers with no new analysis: the twist
costs only the passage from height `T` to height `|τ| + T`, which is exactly the loss the zero-free
region charges for working further up the critical strip.
-/

namespace RHTower.Sieve

open Complex MeasureTheory GaloisForLFunctions.HTGeometry

/-- The vertical shift by `τ` maps the rectangle `[c,d] × [-T,T]` into the symmetric rectangle at
height `|τ| + T`. -/
theorem mapsTo_add_mul_I {c d T : ℝ} (τ : ℝ) (hT : 0 ≤ T) :
    Set.MapsTo (fun s : ℂ => s + (τ : ℂ) * Complex.I)
      (Set.uIcc c d ×ℂ Set.uIcc (-T) T)
      (Set.uIcc c d ×ℂ Set.uIcc (-(|τ| + T)) (|τ| + T)) := by
  intro s hs
  rw [Complex.mem_reProdIm] at hs
  obtain ⟨hre, him⟩ := hs
  rw [Set.uIcc_of_le (by linarith : (-T : ℝ) ≤ T), Set.mem_Icc] at him
  have habs : (0 : ℝ) ≤ |τ| := abs_nonneg τ
  have h1 : -|τ| ≤ τ := neg_abs_le τ
  have h2 : τ ≤ |τ| := le_abs_self τ
  rw [Complex.mem_reProdIm]
  refine ⟨by simpa using hre, ?_⟩
  rw [Set.uIcc_of_le (by linarith : -(|τ| + T) ≤ |τ| + T), Set.mem_Icc,
    show (s + (τ : ℂ) * Complex.I).im = s.im + τ by simp]
  exact ⟨by linarith [him.1], by linarith [him.2]⟩

/-- Holomorphy of the twisted reciprocal of zeta on a rectangle, from the zero-free hypothesis at the
enlarged height. -/
theorem differentiableOn_invZetaTwist_rect {c d T : ℝ} (τ : ℝ) (hT : 0 ≤ T)
    (h : ∀ s ∈ Set.uIcc c d ×ℂ Set.uIcc (-(|τ| + T)) (|τ| + T), s ≠ 1 → riemannZeta s ≠ 0) :
    DifferentiableOn ℂ (fun s => invZeta (s + (τ : ℂ) * Complex.I))
      (Set.uIcc c d ×ℂ Set.uIcc (-T) T) :=
  DifferentiableOn.comp (differentiableOn_invZeta_rect h)
    ((differentiable_id.add_const ((τ : ℂ) * Complex.I)).differentiableOn)
    (mapsTo_add_mul_I τ hT)

/-- **Holomorphy of the twisted Perron integrand on a rectangle.** -/
theorem differentiableOn_invZetaTwistW_rect {N H : ℝ} (hH : 0 < H) {c d T : ℝ} (τ : ℝ)
    (hc : 0 < c) (hcd : c ≤ d) (hT : 0 ≤ T)
    (h : ∀ s ∈ Set.uIcc c d ×ℂ Set.uIcc (-(|τ| + T)) (|τ| + T), s ≠ 1 → riemannZeta s ≠ 0) :
    DifferentiableOn ℂ
      (fun s => invZeta (s + (τ : ℂ) * Complex.I)
        * mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) s)
      (Set.uIcc c d ×ℂ Set.uIcc (-T) T) :=
  (differentiableOn_invZetaTwist_rect τ hT h).mul
    ((differentiableOn_mellin_smoothWeight_strip hH hc).mono (rect_subset_verticalStrip hcd T))

/-- **The truncated contour shift for the twisted Perron integrand, unconditionally.**  For every
twist `τ` and every height `T` the four-edge identity holds across some rectangle crossing the
abscissa `re s = 1`; the zero-free input is taken at height `|τ| + T`. -/
theorem exists_integral_invZetaTwistW_shift {N H : ℝ} (hH : 0 < H) {T : ℝ} (hT : 0 ≤ T) (τ : ℝ) :
    ∃ δ > 0, ∀ c d : ℝ, 1 - δ ≤ c → c ≤ 1 → 1 ≤ d → 0 < c →
      (Complex.I • (∫ y : ℝ in (-T)..T,
            invZeta ((d : ℂ) + (y : ℝ) * Complex.I + (τ : ℂ) * Complex.I)
              * mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ))
                  ((d : ℂ) + (y : ℝ) * Complex.I)))
          - Complex.I • (∫ y : ℝ in (-T)..T,
            invZeta ((c : ℂ) + (y : ℝ) * Complex.I + (τ : ℂ) * Complex.I)
              * mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ))
                  ((c : ℂ) + (y : ℝ) * Complex.I))
        = (∫ x : ℝ in c..d,
              invZeta ((x : ℂ) + ((T : ℝ) : ℂ) * Complex.I + (τ : ℂ) * Complex.I)
                * mellin (fun x' : ℝ => ((smoothWeight N H x' : ℝ) : ℂ))
                    ((x : ℂ) + ((T : ℝ) : ℂ) * Complex.I))
          - ∫ x : ℝ in c..d,
              invZeta ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I + (τ : ℂ) * Complex.I)
                * mellin (fun x' : ℝ => ((smoothWeight N H x' : ℝ) : ℂ))
                    ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I) := by
  obtain ⟨δ, hδ, hzf⟩ := exists_zero_free_rect (T := |τ| + T) (by linarith [abs_nonneg τ])
  exact ⟨δ, hδ, fun c d hc hc1 hd hc0 =>
    integral_vertical_sub_eq_horizontal_rect T
      (differentiableOn_invZetaTwistW_rect hH τ hc0 (le_trans hc1 hd) hT (hzf c d hc hc1 hd))⟩

end RHTower.Sieve
