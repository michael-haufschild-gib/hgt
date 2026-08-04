import GaloisForLFunctions.RHTower.Sieve.ChebyshevFullMainTerm

/-!
# The Chebyshev estimate with the full main term

Bounding every piece of the full-main-term identity:

    ‖ 2π ∑ₙ Λ(n)w(n) - W(1)·(2·arctan(T/(d-1)) - 2·arctan(T/(c-1))) ‖
      ≤ 2·M·C/T
        + (left + top + bottom, divided difference)
        + (left + top + bottom, regular part),

where the divided difference's left edge is now the *pole-free* integral `∫ W(c+iy)/(c-1+iy) dy`.

The bracket tends to `2π`, so dividing by `2π` this is `∑ₙ Λ(n)w(n) = W(1) + error`, with `W(1)` the
mass of the cutoff.
-/

namespace RHTower.Sieve

open Complex MeasureTheory ArithmeticFunction GaloisForLFunctions.HTGeometry

/-- On a line left of `1`, the truncated pole integral tends to `-π`. -/
theorem tendsto_two_arctan_neg {α : ℝ} (hα : α < 0) :
    Filter.Tendsto (fun T : ℝ => 2 * Real.arctan (T / α)) Filter.atTop (nhds (-Real.pi)) := by
  have hpos : (0 : ℝ) < -α := by linarith
  have hrw : ∀ T : ℝ, 2 * Real.arctan (T / α) = -(2 * Real.arctan (T / (-α))) := by
    intro T
    rw [show T / α = -(T / (-α)) by field_simp, Real.arctan_neg]
    ring
  exact ((tendsto_two_arctan hpos).neg).congr fun T => (hrw T).symm

/-- **The main bracket tends to `2π`.** -/
theorem tendsto_main_bracket {c d : ℝ} (hc : c < 1) (hd : 1 < d) :
    Filter.Tendsto
      (fun T : ℝ => 2 * Real.arctan (T / (d - 1)) - 2 * Real.arctan (T / (c - 1)))
      Filter.atTop (nhds (2 * Real.pi)) := by
  have h1 : Filter.Tendsto (fun T : ℝ => 2 * Real.arctan (T / (d - 1))) Filter.atTop
      (nhds Real.pi) := tendsto_two_arctan (by linarith)
  have h2 : Filter.Tendsto (fun T : ℝ => 2 * Real.arctan (T / (c - 1))) Filter.atTop
      (nhds (-Real.pi)) := tendsto_two_arctan_neg (by linarith)
  have := h1.sub h2
  simpa only [sub_neg_eq_add, ← two_mul] using this

/-- **The Chebyshev estimate with the full main term.** -/
theorem norm_tsum_vonMangoldt_sub_full_main_le {N H : ℝ} (hN : 0 < N) (hH : 0 < H)
    {c d T C : ℝ} (hc0 : 0 < c) (hc : c < 1) (hd : 1 < d) (hT : 1 ≤ T)
    (hzf : ∀ s ∈ Set.uIcc c d ×ℂ Set.uIcc (-T) T, s ≠ 1 → riemannZeta s ≠ 0)
    (hbd : ∀ s : ℂ, 0 < s.re → s.re ≤ d →
      |s.im| ^ (1 + 1) * ‖mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) s‖ ≤ C) :
    ‖(2 * Real.pi : ℝ) • (∑' n : ℕ,
          ((vonMangoldt n : ℝ) : ℂ) * ((smoothWeight N H (n : ℝ) : ℝ) : ℂ))
        - mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) 1
            * (((2 * Real.arctan (T / (d - 1)) - 2 * Real.arctan (T / (c - 1)) : ℝ)) : ℂ)‖
      ≤ 2 * ((∑' n : ℕ, (vonMangoldt n : ℝ) * (n : ℝ) ^ (-d)) * C) / T
        + (‖∫ y : ℝ in (-T)..T, mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ))
                ((c : ℂ) + (y : ℝ) * Complex.I)
              * (((c : ℂ) + (y : ℝ) * Complex.I) - 1)⁻¹‖
          + ‖∫ x : ℝ in c..d, dslope (mellin (fun x' : ℝ => ((smoothWeight N H x' : ℝ) : ℂ))) 1
              ((x : ℂ) + ((T : ℝ) : ℂ) * Complex.I)‖
          + ‖∫ x : ℝ in c..d, dslope (mellin (fun x' : ℝ => ((smoothWeight N H x' : ℝ) : ℂ))) 1
              ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I)‖)
        + (‖∫ y : ℝ in (-T)..T, zetaLogDerivReg ((c : ℂ) + (y : ℝ) * Complex.I)
              * mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ))
                  ((c : ℂ) + (y : ℝ) * Complex.I)‖
          + ‖∫ x : ℝ in c..d, zetaLogDerivReg ((x : ℂ) + ((T : ℝ) : ℂ) * Complex.I)
              * mellin (fun x' : ℝ => ((smoothWeight N H x' : ℝ) : ℂ))
                  ((x : ℂ) + ((T : ℝ) : ℂ) * Complex.I)‖
          + ‖∫ x : ℝ in c..d, zetaLogDerivReg ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I)
              * mellin (fun x' : ℝ => ((smoothWeight N H x' : ℝ) : ℂ))
                  ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I)‖) := by
  have hTpos : (0 : ℝ) < T := by linarith
  rw [tsum_vonMangoldt_full_main_identity hN hH hc0 hc hd hTpos]
  set A : ℂ := (∫ y : ℝ, (-(deriv riemannZeta ((d : ℂ) + (y : ℝ) * Complex.I))
          / riemannZeta ((d : ℂ) + (y : ℝ) * Complex.I))
        * mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ))
            ((d : ℂ) + (y : ℝ) * Complex.I))
      - ∫ y : ℝ in (-T)..T, (-(deriv riemannZeta ((d : ℂ) + (y : ℝ) * Complex.I))
          / riemannZeta ((d : ℂ) + (y : ℝ) * Complex.I))
        * mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ))
            ((d : ℂ) + (y : ℝ) * Complex.I) with hA
  set Vc : ℂ := ∫ y : ℝ in (-T)..T, mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ))
        ((c : ℂ) + (y : ℝ) * Complex.I)
      * (((c : ℂ) + (y : ℝ) * Complex.I) - 1)⁻¹ with hVc
  set Ht : ℂ := ∫ x : ℝ in c..d, dslope (mellin (fun x' : ℝ => ((smoothWeight N H x' : ℝ) : ℂ))) 1
      ((x : ℂ) + ((T : ℝ) : ℂ) * Complex.I) with hHt
  set Hb : ℂ := ∫ x : ℝ in c..d, dslope (mellin (fun x' : ℝ => ((smoothWeight N H x' : ℝ) : ℂ))) 1
      ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I) with hHb
  set Rd : ℂ := ∫ y : ℝ in (-T)..T, zetaLogDerivReg ((d : ℂ) + (y : ℝ) * Complex.I)
      * mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ))
          ((d : ℂ) + (y : ℝ) * Complex.I) with hRd
  have htail : ‖A‖ ≤ 2 * ((∑' n : ℕ, (vonMangoldt n : ℝ) * (n : ℝ) ^ (-d)) * C) / T :=
    norm_truncation_error_chebyshev hN hH hd hT hbd
  have hreg := norm_integral_zetaLogDerivRegW_right_le (N := N) (H := H) hH hc0 (by linarith) hzf
  rw [← hRd] at hreg
  have hmid : ‖Vc - Complex.I * (Ht - Hb)‖ ≤ ‖Vc‖ + ‖Ht‖ + ‖Hb‖ := by
    have h1 : ‖Complex.I * (Ht - Hb)‖ = ‖Ht - Hb‖ := by
      rw [norm_mul, Complex.norm_I, one_mul]
    have h2 : ‖Ht - Hb‖ ≤ ‖Ht‖ + ‖Hb‖ := norm_sub_le _ _
    have h3 : ‖Vc - Complex.I * (Ht - Hb)‖ ≤ ‖Vc‖ + ‖Complex.I * (Ht - Hb)‖ := norm_sub_le _ _
    rw [h1] at h3
    linarith
  have htri : ‖A + (Vc - Complex.I * (Ht - Hb)) + Rd‖
      ≤ ‖A‖ + ‖Vc - Complex.I * (Ht - Hb)‖ + ‖Rd‖ := by
    have h1 := norm_add_le (A + (Vc - Complex.I * (Ht - Hb))) Rd
    have h2 := norm_add_le A (Vc - Complex.I * (Ht - Hb))
    linarith
  linarith

end RHTower.Sieve
