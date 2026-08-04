import GaloisForLFunctions.RHTower.Sieve.ChebyshevRegularEdges

/-!
# The Chebyshev estimate, fully explicit

Substituting all six edge bounds:

    ‖ 2π ∑ₙ Λ(n)w(n) - W(1)·(2·arctan(T/(d-1)) - 2·arctan(T/(c-1))) ‖
      ≤ 2·M·C_d/T
        + ( (1-c)⁻¹·(2(N+H)^c/c + 2C_c) + 2(d-c)·(C_d/T² + ‖W(1)‖)/T )
        + ( R₀·(2(N+H)^c/c + 2C_c) + 2(d-c)·R·C_d/T² ).

Two decay constants appear and must not be merged: `C_c` is taken on the line `Re s = c` and `C_d` on
the strip `0 < Re s ≤ d`.  A constant valid on the whole strip carries a factor `(N+H)^d`, which in
the application exceeds the saving the contour is bought with; the line constant is of size `(N+H)^c`
and is the one the left edge needs.

Every remaining quantity is a parameter of the contour or a bound on the regular part in the
zero-free region.
-/

namespace RHTower.Sieve

open Complex MeasureTheory ArithmeticFunction GaloisForLFunctions.HTGeometry

/-- **The Chebyshev estimate with every edge bounded explicitly.** -/
theorem norm_tsum_vonMangoldt_sub_full_main_le_explicit {N H : ℝ} (hN : 0 < N) (hH : 0 < H)
    {c d T Cc Cd R M : ℝ} (hc0 : 0 < c) (hc : c < 1) (hd : 1 < d) (hT : 1 ≤ T)
    (hR0 : 0 ≤ R) (hM : 0 ≤ M)
    (hzfrect : ∀ s ∈ Set.uIcc c d ×ℂ Set.uIcc (-T) T, s ≠ 1 → riemannZeta s ≠ 0)
    (hzfline : ∀ y ∈ Set.uIcc (-T) T, riemannZeta ((c : ℂ) + (y : ℝ) * Complex.I) ≠ 0)
    (hregline : ∀ y ∈ Set.Icc (-T) T, ‖zetaLogDerivReg ((c : ℂ) + (y : ℝ) * Complex.I)‖ ≤ M)
    (hregtop : ∀ x ∈ Set.uIoc c d,
      ‖zetaLogDerivReg ((x : ℂ) + ((T : ℝ) : ℂ) * Complex.I)‖ ≤ R)
    (hregbot : ∀ x ∈ Set.uIoc c d,
      ‖zetaLogDerivReg ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I)‖ ≤ R)
    (hbdc : ∀ s : ℂ, 0 < s.re → s.re ≤ c →
      |s.im| ^ (1 + 1) * ‖mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) s‖ ≤ Cc)
    (hbdd : ∀ s : ℂ, 0 < s.re → s.re ≤ d →
      |s.im| ^ (1 + 1) * ‖mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) s‖ ≤ Cd) :
    ‖(2 * Real.pi : ℝ) • (∑' n : ℕ,
          ((vonMangoldt n : ℝ) : ℂ) * ((smoothWeight N H (n : ℝ) : ℝ) : ℂ))
        - mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) 1
            * (((2 * Real.arctan (T / (d - 1)) - 2 * Real.arctan (T / (c - 1)) : ℝ)) : ℂ)‖
      ≤ 2 * ((∑' n : ℕ, (vonMangoldt n : ℝ) * (n : ℝ) ^ (-d)) * Cd) / T
        + ((1 - c)⁻¹ * (2 * ((N + H) ^ c / c) + 2 * Cc)
          + 2 * ((d - c) * ((Cd / T ^ (1 + 1)
              + ‖mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) 1‖) / T)))
        + (M * (2 * ((N + H) ^ c / c) + 2 * Cc)
          + 2 * ((d - c) * (R * (Cd / T ^ (1 + 1))))) := by
  have hTpos : (0 : ℝ) < T := by linarith
  have hTne : T ≠ 0 := ne_of_gt hTpos
  have habsT : |T| = T := abs_of_pos hTpos
  have habsnT : |(-T : ℝ)| = T := by rw [abs_neg, habsT]
  have hcd : c ≤ d := by linarith
  have hVc := norm_integral_left_vertical_pole_free_le hN hH hc0 hc hT hbdc
  have hHt := norm_integral_horizontal_dslope_le (N := N) (H := H) (C := Cd) hc0 hcd hTne hbdd
  have hHb := norm_integral_horizontal_dslope_le (N := N) (H := H) (C := Cd) (T := -T)
    hc0 hcd (by simpa using hTne) hbdd
  have hVreg := norm_integral_left_vertical_reg_le hN hH hc0 hc.ne hT hM hzfline hregline hbdc
  have hRt := norm_integral_horizontal_reg_le (N := N) (H := H) (C := Cd) hc0 hcd hTne hR0
    hregtop hbdd
  have hRb := norm_integral_horizontal_reg_le (N := N) (H := H) (C := Cd) (T := -T) hc0 hcd
    (by simpa using hTne) hR0 hregbot hbdd
  rw [habsT] at hHt hRt
  rw [habsnT] at hHb hRb
  refine le_trans (norm_tsum_vonMangoldt_sub_full_main_le hN hH hc0 hc hd hT hzfrect hbdd) ?_
  linarith

end RHTower.Sieve
