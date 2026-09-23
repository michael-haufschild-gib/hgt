import GaloisForLFunctions.RHTower.Sieve.ChebyshevTwistTruncatedIdentity
import GaloisForLFunctions.RHTower.Sieve.ChebyshevTwistEdgeBound

/-!
# The twisted Chebyshev sum minus its main term

The truncated twisted identity has four summands: the tail beyond height `T`, the divided
difference on the truncated line, the explicit main term, and the regular part.  Both the divided
difference and the regular part satisfy a four-edge identity with vanishing boundary functional, so
each of them, taken on the *right* edge, is bounded by its two horizontal edges plus its left edge.
Subtracting the main term and adding the three bounds gives

```text
‖ 2π ∑ₙ Λ(n) n^{-iτ} w(n)  -  W(1-iτ)·(arctan difference - i·log difference/2) ‖
    ≤  (tail)  +  (dslope edges)  +  (regular edges).
```

Nothing analytic is used here beyond the two shifts: this is the shape into which the Route-T
zero-free region and the logarithmic-derivative bound on that abscissa are substituted.
-/

namespace RHTower.Sieve

open Complex MeasureTheory GaloisForLFunctions.HTGeometry

/-- **Shifting a truncated vertical integral.**  When the boundary functional vanishes, the right
edge is bounded by the two horizontal edges and the left edge. -/
theorem norm_truncated_le_of_shift {Vd Vc Ht Hb : ℂ} {E₂ E₃ E₄ : ℝ}
    (hshift : Complex.I • Vd - Complex.I • Vc = Ht - Hb)
    (htop : ‖Ht‖ ≤ E₂) (hbot : ‖Hb‖ ≤ E₃) (hleft : ‖Vc‖ ≤ E₄) :
    ‖Vd‖ ≤ E₂ + E₃ + E₄ := by
  have h := norm_le_of_contour_edges (P := Vd) (E₁ := 0) hshift (by simp) htop hbot hleft
  linarith

/-- The divided-difference term on the truncated right edge, moved to the left edge. -/
theorem norm_integral_dslope_twist_truncated_le {N H : ℝ} (hH : 0 < H) {c d T τ : ℝ}
    {E₂ E₃ E₄ : ℝ} (hc0 : 0 < c) (hc : c < 1) (hd : 1 < d) (hτ : |τ| < T)
    (htop : ‖∫ x : ℝ in c..d,
        dslope (mellin (fun x' : ℝ => ((smoothWeight N H x' : ℝ) : ℂ))) (twistPole τ)
          ((x : ℂ) + ((T : ℝ) : ℂ) * Complex.I)‖ ≤ E₂)
    (hbot : ‖∫ x : ℝ in c..d,
        dslope (mellin (fun x' : ℝ => ((smoothWeight N H x' : ℝ) : ℂ))) (twistPole τ)
          ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I)‖ ≤ E₃)
    (hleft : ‖∫ y : ℝ in (-T)..T,
        dslope (mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ))) (twistPole τ)
          ((c : ℂ) + (y : ℝ) * Complex.I)‖ ≤ E₄) :
    ‖∫ y : ℝ in (-T)..T,
        dslope (mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ))) (twistPole τ)
          ((d : ℂ) + (y : ℝ) * Complex.I)‖ ≤ E₂ + E₃ + E₄ :=
  norm_truncated_le_of_shift
    (integral_dslope_mellin_twist_vertical_sub_eq_horizontal_rect hH hc0 hc hd hτ)
    htop hbot hleft

/-- The regular term on the truncated right edge, moved to the left edge. -/
theorem norm_integral_zetaLogDerivRegTwist_truncated_le {N H : ℝ} (hH : 0 < H) {c d T : ℝ}
    (τ : ℝ) {E₂ E₃ E₄ : ℝ} (hc : 0 < c) (hcd : c ≤ d) (hT : 0 ≤ T)
    (hzf : ∀ s ∈ Set.uIcc c d ×ℂ Set.uIcc (-(|τ| + T)) (|τ| + T), s ≠ 1 → riemannZeta s ≠ 0)
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
    ‖∫ y : ℝ in (-T)..T,
        zetaLogDerivReg ((d : ℂ) + (y : ℝ) * Complex.I + (τ : ℂ) * Complex.I)
          * mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ))
              ((d : ℂ) + (y : ℝ) * Complex.I)‖ ≤ E₂ + E₃ + E₄ :=
  norm_truncated_le_of_shift
    (integral_zetaLogDerivRegTwistW_vertical_sub_eq_horizontal_rect hH τ hc hcd hT hzf)
    htop hbot hleft

/-- The explicit factor of the twisted main term. -/
noncomputable def twistMainFactor (d T τ : ℝ) : ℂ :=
  (((Real.arctan ((T + τ) / (d - 1)) - Real.arctan ((-T + τ) / (d - 1)) : ℝ)) : ℂ)
    - ((((Real.log ((d - 1) ^ (2 : ℕ) + (T + τ) ^ (2 : ℕ))
          - Real.log ((d - 1) ^ (2 : ℕ) + (-T + τ) ^ (2 : ℕ))) / 2 : ℝ)) : ℂ) * Complex.I

/-- **The twisted smoothed Chebyshev sum, minus its main term, bounded by three pieces.**  The tail
beyond height `T`, the divided difference on the truncated line, and the regular part there — the
last two of which the shifts above move to the left edge. -/
theorem norm_tsum_vonMangoldtTwist_sub_mainTerm_le (τ : ℝ) {N H : ℝ} (hN : 0 < N) (hH : 0 < H)
    {d T : ℝ} (hd : 1 < d) {E₀ E₁ E₂ : ℝ}
    (htail : ‖(∫ y : ℝ, (-logDeriv riemannZeta ((d : ℂ) + ((y + τ : ℝ)) * Complex.I))
          * mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) ((d : ℂ) + (y : ℝ) * Complex.I))
        - ∫ y : ℝ in (-T)..T, (-logDeriv riemannZeta ((d : ℂ) + ((y + τ : ℝ)) * Complex.I))
          * mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ))
              ((d : ℂ) + (y : ℝ) * Complex.I)‖ ≤ E₀)
    (hdslope : ‖∫ y : ℝ in (-T)..T,
        dslope (mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ))) (twistPole τ)
          ((d : ℂ) + (y : ℝ) * Complex.I)‖ ≤ E₁)
    (hreg : ‖∫ y : ℝ in (-T)..T,
        zetaLogDerivReg ((d : ℂ) + (y : ℝ) * Complex.I + (τ : ℂ) * Complex.I)
          * mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ))
              ((d : ℂ) + (y : ℝ) * Complex.I)‖ ≤ E₂) :
    ‖(2 * Real.pi : ℝ) • (∑' n : ℕ,
          vonMangoldtTwist τ n * ((smoothWeight N H (n : ℝ) : ℝ) : ℂ))
        - mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) (twistPole τ)
            * twistMainFactor d T τ‖
      ≤ E₀ + E₁ + E₂ := by
  have hid := tsum_vonMangoldtTwist_truncated_identity τ hN hH hd (d := d) (T := T)
  set A : ℂ := (∫ y : ℝ, (-logDeriv riemannZeta ((d : ℂ) + ((y + τ : ℝ)) * Complex.I))
        * mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) ((d : ℂ) + (y : ℝ) * Complex.I))
      - ∫ y : ℝ in (-T)..T, (-logDeriv riemannZeta ((d : ℂ) + ((y + τ : ℝ)) * Complex.I))
        * mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ))
            ((d : ℂ) + (y : ℝ) * Complex.I) with hA
  set B : ℂ := ∫ y : ℝ in (-T)..T,
      dslope (mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ))) (twistPole τ)
        ((d : ℂ) + (y : ℝ) * Complex.I) with hB
  set D : ℂ := ∫ y : ℝ in (-T)..T,
      zetaLogDerivReg ((d : ℂ) + (y : ℝ) * Complex.I + (τ : ℂ) * Complex.I)
        * mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ))
            ((d : ℂ) + (y : ℝ) * Complex.I) with hD
  have hsub : (2 * Real.pi : ℝ) • (∑' n : ℕ,
        vonMangoldtTwist τ n * ((smoothWeight N H (n : ℝ) : ℝ) : ℂ))
      - mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) (twistPole τ)
          * twistMainFactor d T τ
      = A + B + D := by
    rw [hid, twistMainFactor]
    ring
  rw [hsub]
  calc ‖A + B + D‖ ≤ ‖A + B‖ + ‖D‖ := norm_add_le _ _
    _ ≤ ‖A‖ + ‖B‖ + ‖D‖ := by linarith [norm_add_le A B]
    _ ≤ E₀ + E₁ + E₂ := by linarith [htail, hdslope, hreg]

end RHTower.Sieve
