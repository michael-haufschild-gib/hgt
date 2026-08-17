import GaloisForLFunctions.RHTower.Sieve.ChebyshevTwistHorizontalDslope
import GaloisForLFunctions.RHTower.Sieve.ChebyshevFullMainTerm

/-!
# The full twisted main term

Shifting the twisted divided difference to the left edge and extracting the pole term there produces
the *whole* residue at `1 - iτ`, not half of it:

```text
2π ∑ₙ Λ(n) n^{-iτ} w(n) - W(1-iτ)·( twistMainFactor d T τ - twistMainFactor c T τ )
  = tail  +  ( ∫ W(c+iy)/(c-1+i(y+τ)) dy - i·(top - bottom) )  +  ∫ regular ,
```

and the bracket tends to `2π` as `T → ∞` — the right line contributing the half whose real part is
`+π` and the left line the half whose real part is `-π`, subtracted.

The twist changes none of this structurally.  What it changes is the geometry: both halves are now
computed about the point `1 - iτ`, the pole must lie inside the truncated rectangle for the shift to
produce the residue at all, and the symmetric truncation is no longer symmetric about the pole — so
each half acquires a logarithmic imaginary part alongside its arctangent, and the two logarithms
cancel only in the limit.
-/

namespace RHTower.Sieve

open Complex MeasureTheory ArithmeticFunction GaloisForLFunctions.HTGeometry

/-- **The truncated twisted Chebyshev identity with the full main term.** -/
theorem tsum_vonMangoldtTwist_full_main_identity (τ : ℝ) {N H : ℝ} (hN : 0 < N) (hH : 0 < H)
    {c d T : ℝ} (hc0 : 0 < c) (hc : c < 1) (hd : 1 < d) (hτ : |τ| < T) :
    (2 * Real.pi : ℝ) • (∑' n : ℕ,
          vonMangoldtTwist τ n * ((smoothWeight N H (n : ℝ) : ℝ) : ℂ))
        - mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) (twistPole τ)
            * (twistMainFactor d T τ - twistMainFactor c T τ)
      = ((∫ y : ℝ, (-logDeriv riemannZeta ((d : ℂ) + ((y + τ : ℝ)) * Complex.I))
              * mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ))
                  ((d : ℂ) + (y : ℝ) * Complex.I))
            - ∫ y : ℝ in (-T)..T, (-logDeriv riemannZeta ((d : ℂ) + ((y + τ : ℝ)) * Complex.I))
              * mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ))
                  ((d : ℂ) + (y : ℝ) * Complex.I))
        + ((∫ y : ℝ in (-T)..T,
                mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ))
                    ((c : ℂ) + (y : ℝ) * Complex.I)
                  * ((c : ℂ) + (y : ℝ) * Complex.I + (τ : ℂ) * Complex.I - 1)⁻¹)
            - Complex.I * ((∫ x : ℝ in c..d,
                  dslope (mellin (fun x' : ℝ => ((smoothWeight N H x' : ℝ) : ℂ))) (twistPole τ)
                    ((x : ℂ) + ((T : ℝ) : ℂ) * Complex.I))
                - ∫ x : ℝ in c..d,
                  dslope (mellin (fun x' : ℝ => ((smoothWeight N H x' : ℝ) : ℂ))) (twistPole τ)
                    ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I)))
        + (∫ y : ℝ in (-T)..T,
            zetaLogDerivReg ((d : ℂ) + (y : ℝ) * Complex.I + (τ : ℂ) * Complex.I)
              * mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ))
                  ((d : ℂ) + (y : ℝ) * Complex.I)) := by
  have hid := tsum_vonMangoldtTwist_truncated_identity τ hN hH hd (d := d) (T := T)
  have hshift := eq_of_shift_identity
    (integral_dslope_mellin_twist_vertical_sub_eq_horizontal_rect (N := N) (H := H)
      hH hc0 hc hd hτ)
  have hleft := integral_dslope_mellin_twist_left_eq (N := N) (H := H) (τ := τ)
    hH (c := c) (T := T) hc0 hc.ne
  rw [hid, hshift, hleft]
  simp only [twistMainFactor]
  ring

/-- **The twisted smoothed Chebyshev sum against its full main term.**  Five explicit pieces: the
truncation tail, the pole-free left edge, the two horizontal divided-difference edges, and the
regular part on the right line — which the contour shift then moves left in its turn. -/
theorem norm_tsum_vonMangoldtTwist_sub_full_main_le (τ : ℝ) {N H : ℝ} (hN : 0 < N) (hH : 0 < H)
    {c d T E₀ E₁ E₂ E₃ E₄ : ℝ} (hc0 : 0 < c) (hc : c < 1) (hd : 1 < d) (hτ : |τ| < T)
    (htail : ‖(∫ y : ℝ, (-logDeriv riemannZeta ((d : ℂ) + ((y + τ : ℝ)) * Complex.I))
            * mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ))
                ((d : ℂ) + (y : ℝ) * Complex.I))
          - ∫ y : ℝ in (-T)..T, (-logDeriv riemannZeta ((d : ℂ) + ((y + τ : ℝ)) * Complex.I))
            * mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ))
                ((d : ℂ) + (y : ℝ) * Complex.I)‖ ≤ E₀)
    (hleft : ‖∫ y : ℝ in (-T)..T,
        mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) ((c : ℂ) + (y : ℝ) * Complex.I)
          * ((c : ℂ) + (y : ℝ) * Complex.I + (τ : ℂ) * Complex.I - 1)⁻¹‖ ≤ E₁)
    (htop : ‖∫ x : ℝ in c..d,
        dslope (mellin (fun x' : ℝ => ((smoothWeight N H x' : ℝ) : ℂ))) (twistPole τ)
          ((x : ℂ) + ((T : ℝ) : ℂ) * Complex.I)‖ ≤ E₂)
    (hbot : ‖∫ x : ℝ in c..d,
        dslope (mellin (fun x' : ℝ => ((smoothWeight N H x' : ℝ) : ℂ))) (twistPole τ)
          ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I)‖ ≤ E₃)
    (hreg : ‖∫ y : ℝ in (-T)..T,
        zetaLogDerivReg ((d : ℂ) + (y : ℝ) * Complex.I + (τ : ℂ) * Complex.I)
          * mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ))
              ((d : ℂ) + (y : ℝ) * Complex.I)‖ ≤ E₄) :
    ‖(2 * Real.pi : ℝ) • (∑' n : ℕ,
          vonMangoldtTwist τ n * ((smoothWeight N H (n : ℝ) : ℝ) : ℂ))
        - mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) (twistPole τ)
            * (twistMainFactor d T τ - twistMainFactor c T τ)‖
      ≤ E₀ + E₁ + E₂ + E₃ + E₄ := by
  set A : ℂ := (∫ y : ℝ, (-logDeriv riemannZeta ((d : ℂ) + ((y + τ : ℝ)) * Complex.I))
        * mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) ((d : ℂ) + (y : ℝ) * Complex.I))
      - ∫ y : ℝ in (-T)..T, (-logDeriv riemannZeta ((d : ℂ) + ((y + τ : ℝ)) * Complex.I))
        * mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ))
            ((d : ℂ) + (y : ℝ) * Complex.I) with hA
  set B : ℂ := ∫ y : ℝ in (-T)..T,
      mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) ((c : ℂ) + (y : ℝ) * Complex.I)
        * ((c : ℂ) + (y : ℝ) * Complex.I + (τ : ℂ) * Complex.I - 1)⁻¹ with hB
  set P : ℂ := ∫ x : ℝ in c..d,
      dslope (mellin (fun x' : ℝ => ((smoothWeight N H x' : ℝ) : ℂ))) (twistPole τ)
        ((x : ℂ) + ((T : ℝ) : ℂ) * Complex.I) with hP
  set Q : ℂ := ∫ x : ℝ in c..d,
      dslope (mellin (fun x' : ℝ => ((smoothWeight N H x' : ℝ) : ℂ))) (twistPole τ)
        ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I) with hQ
  set R : ℂ := ∫ y : ℝ in (-T)..T,
      zetaLogDerivReg ((d : ℂ) + (y : ℝ) * Complex.I + (τ : ℂ) * Complex.I)
        * mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ))
            ((d : ℂ) + (y : ℝ) * Complex.I) with hR
  rw [tsum_vonMangoldtTwist_full_main_identity τ hN hH hc0 hc hd hτ]
  have hIP : ‖Complex.I * (P - Q)‖ ≤ E₂ + E₃ := by
    rw [norm_mul, Complex.norm_I, one_mul]
    exact le_trans (norm_sub_le P Q) (by linarith)
  calc ‖A + (B - Complex.I * (P - Q)) + R‖
      ≤ ‖A + (B - Complex.I * (P - Q))‖ + ‖R‖ := norm_add_le _ _
    _ ≤ ‖A‖ + ‖B - Complex.I * (P - Q)‖ + ‖R‖ := by linarith [norm_add_le A (B - Complex.I * (P - Q))]
    _ ≤ ‖A‖ + (‖B‖ + ‖Complex.I * (P - Q)‖) + ‖R‖ := by linarith [norm_sub_le B (Complex.I * (P - Q))]
    _ ≤ E₀ + E₁ + E₂ + E₃ + E₄ := by linarith

end RHTower.Sieve
