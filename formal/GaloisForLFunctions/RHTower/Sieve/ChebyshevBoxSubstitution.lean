import GaloisForLFunctions.RHTower.Sieve.ChebyshevExplicitBound
import GaloisForLFunctions.RHTower.Sieve.ZetaLogDerivRegBox

/-!
# The contour fixed at the zero-free box

Taking `c = 1 - A/log⁹T` and `d = 1 + A/log⁹T` discharges every zeta-analytic hypothesis of the
explicit estimate at once: the rectangle is the zero-free strip truncated at height `T`, and the
regular part is bounded on it by `max M₀ ((2240/A)log⁹T + 1/9)`.

What remains in the bound is the cutoff's transform and the contour parameters — no further
information about `ζ` is used.
-/

namespace RHTower.Sieve

open Complex MeasureTheory ArithmeticFunction RHTower GaloisForLFunctions.HTGeometry

/-- **The Chebyshev estimate on the zero-free box.** -/
theorem norm_tsum_vonMangoldt_sub_full_main_le_box {N H : ℝ} (hN : 0 < N) (hH : 0 < H)
    {T Cc Cd δ₀ M₀ : ℝ} (hT : 9 ≤ T) (hM₀ : 0 ≤ M₀)
    (hfit : zetaLowerA / Real.log T ^ 9 ≤ δ₀)
    (hlowzf : ∀ c d : ℝ, 1 - δ₀ ≤ c → c ≤ 1 → 1 ≤ d →
      ∀ s ∈ Set.uIcc c d ×ℂ Set.uIcc (-9 : ℝ) 9, s ≠ 1 → riemannZeta s ≠ 0)
    (hlowbox : ∀ s : ℂ, 1 - δ₀ ≤ s.re → s.re ≤ 2 → |s.im| ≤ 9 → ‖zetaLogDerivReg s‖ ≤ M₀)
    (hbdc : ∀ s : ℂ, 0 < s.re → s.re ≤ 1 - zetaLowerA / Real.log T ^ 9 →
      |s.im| ^ (1 + 1) * ‖mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) s‖ ≤ Cc)
    (hbdd : ∀ s : ℂ, 0 < s.re → s.re ≤ 1 + zetaLowerA / Real.log T ^ 9 →
      |s.im| ^ (1 + 1) * ‖mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) s‖ ≤ Cd) :
    ‖(2 * Real.pi : ℝ) • (∑' n : ℕ,
          ((vonMangoldt n : ℝ) : ℂ) * ((smoothWeight N H (n : ℝ) : ℝ) : ℂ))
        - mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) 1
            * (((2 * Real.arctan (T / (zetaLowerA / Real.log T ^ 9))
                - 2 * Real.arctan (T / (-(zetaLowerA / Real.log T ^ 9))) : ℝ)) : ℂ)‖
      ≤ 2 * ((∑' n : ℕ, (vonMangoldt n : ℝ)
              * (n : ℝ) ^ (-(1 + zetaLowerA / Real.log T ^ 9))) * Cd) / T
        + ((zetaLowerA / Real.log T ^ 9)⁻¹
            * (2 * ((N + H) ^ (1 - zetaLowerA / Real.log T ^ 9)
                / (1 - zetaLowerA / Real.log T ^ 9)) + 2 * Cc)
          + 2 * ((2 * (zetaLowerA / Real.log T ^ 9)) * ((Cd / T ^ (1 + 1)
              + ‖mellin (fun x : ℝ => ((smoothWeight N H x : ℝ) : ℂ)) 1‖) / T)))
        + (max M₀ (2240 / zetaLowerA * Real.log T ^ 9 + 1 / 9)
              * (2 * ((N + H) ^ (1 - zetaLowerA / Real.log T ^ 9)
                  / (1 - zetaLowerA / Real.log T ^ 9)) + 2 * Cc)
          + 2 * ((2 * (zetaLowerA / Real.log T ^ 9))
              * (max M₀ (2240 / zetaLowerA * Real.log T ^ 9 + 1 / 9) * (Cd / T ^ (1 + 1))))) := by
  have hA0 : (0 : ℝ) < zetaLowerA := zetaLowerA_pos
  have hA1 : zetaLowerA ≤ 1 := zetaLowerA_le_one
  have hlogT : 2 < Real.log T := by
    have hexp2 := exp_two_lt_eight
    have h1 : Real.log (Real.exp 2) < Real.log T :=
      Real.log_lt_log (Real.exp_pos 2) (by linarith)
    rwa [Real.log_exp] at h1
  have hLT0 : (0 : ℝ) < Real.log T := by linarith
  set w : ℝ := zetaLowerA / Real.log T ^ 9 with hw
  have hw0 : (0 : ℝ) < w := by rw [hw]; positivity
  have hw1 : w ≤ 1 / 2 := by
    rw [hw, div_le_div_iff₀ (by positivity) (by norm_num)]
    have h1 : (2 : ℝ) ^ 9 ≤ Real.log T ^ 9 := pow_le_pow_left₀ (by norm_num) hlogT.le 9
    nlinarith
  have hc0 : (0 : ℝ) < 1 - w := by linarith
  have hc : (1 : ℝ) - w < 1 := by linarith
  have hd : (1 : ℝ) < 1 + w := by linarith
  have hT1 : (1 : ℝ) ≤ T := by linarith
  have hTpos : (0 : ℝ) < T := by linarith
  set M : ℝ := max M₀ (2240 / zetaLowerA * Real.log T ^ 9 + 1 / 9) with hM
  have hM0 : 0 ≤ M := le_trans hM₀ (le_max_left _ _)
  have hbox : ∀ s : ℂ, 1 - w ≤ s.re → s.re ≤ 1 + w → |s.im| ≤ T →
      ‖zetaLogDerivReg s‖ ≤ M := fun s h1 h2 h3 =>
    norm_zetaLogDerivReg_box_le hT hfit hlowbox h1 h2 h3
  have hzfbox : ∀ s : ℂ, 1 - w ≤ s.re → s.re ≤ 1 + w → |s.im| ≤ T → s ≠ 1 →
      riemannZeta s ≠ 0 := fun s h1 h2 h3 h4 =>
    riemannZeta_ne_zero_box hT hfit hlowzf h1 h2 h3 h4
  have hzfrect : ∀ s ∈ Set.uIcc (1 - w) (1 + w) ×ℂ Set.uIcc (-T) T, s ≠ 1 →
      riemannZeta s ≠ 0 := by
    intro s hs hs1
    rw [Complex.mem_reProdIm, Set.uIcc_of_le (by linarith),
      Set.uIcc_of_le (by linarith : (-T : ℝ) ≤ T)] at hs
    exact hzfbox s hs.1.1 hs.1.2 (abs_le.2 ⟨hs.2.1, hs.2.2⟩) hs1
  have hre : ∀ y : ℝ, (((1 - w : ℝ) : ℂ) + (y : ℝ) * Complex.I).re = 1 - w := fun y => by simp
  have him : ∀ y : ℝ, (((1 - w : ℝ) : ℂ) + (y : ℝ) * Complex.I).im = y := fun y => by simp
  have hzfline : ∀ y ∈ Set.uIcc (-T) T,
      riemannZeta (((1 - w : ℝ) : ℂ) + (y : ℝ) * Complex.I) ≠ 0 := by
    intro y hy
    rw [Set.uIcc_of_le (by linarith : (-T : ℝ) ≤ T)] at hy
    refine hzfbox _ (by rw [hre]) (by rw [hre]; linarith) (by rw [him]; exact abs_le.2 hy) ?_
    intro h
    have := congrArg Complex.re h
    rw [hre] at this
    simp at this
    linarith
  have hregline : ∀ y ∈ Set.Icc (-T) T,
      ‖zetaLogDerivReg (((1 - w : ℝ) : ℂ) + (y : ℝ) * Complex.I)‖ ≤ M := by
    intro y hy
    exact hbox _ (by rw [hre]) (by rw [hre]; linarith) (by rw [him]; exact abs_le.2 ⟨hy.1, hy.2⟩)
  have hreH : ∀ (x t : ℝ), ((x : ℂ) + ((t : ℝ) : ℂ) * Complex.I).re = x := fun x t => by simp
  have himH : ∀ (x t : ℝ), ((x : ℂ) + ((t : ℝ) : ℂ) * Complex.I).im = t := fun x t => by simp
  have hregtop : ∀ x ∈ Set.uIoc (1 - w) (1 + w),
      ‖zetaLogDerivReg ((x : ℂ) + ((T : ℝ) : ℂ) * Complex.I)‖ ≤ M := by
    intro x hx
    rw [Set.uIoc_of_le (by linarith)] at hx
    exact hbox _ (by rw [hreH]; exact hx.1.le) (by rw [hreH]; exact hx.2)
      (by rw [himH]; rw [abs_of_pos hTpos])
  have hregbot : ∀ x ∈ Set.uIoc (1 - w) (1 + w),
      ‖zetaLogDerivReg ((x : ℂ) + ((-T : ℝ) : ℂ) * Complex.I)‖ ≤ M := by
    intro x hx
    rw [Set.uIoc_of_le (by linarith)] at hx
    exact hbox _ (by rw [hreH]; exact hx.1.le) (by rw [hreH]; exact hx.2)
      (by rw [himH]; rw [abs_neg, abs_of_pos hTpos])
  have hmain := norm_tsum_vonMangoldt_sub_full_main_le_explicit hN hH (c := 1 - w) (d := 1 + w)
    (T := T) (Cc := Cc) (Cd := Cd) (R := M) (M := M) hc0 hc hd hT1 hM0 hM0
    hzfrect hzfline hregline hregtop hregbot hbdc hbdd
  have harc1 : ((1 : ℝ) + w) - 1 = w := by ring
  have harc2 : ((1 : ℝ) - w) - 1 = -w := by ring
  have hwidth : ((1 : ℝ) + w) - (1 - w) = 2 * w := by ring
  have hone : (1 : ℝ) - (1 - w) = w := by ring
  rw [harc1, harc2, hwidth, hone] at hmain
  exact hmain

end RHTower.Sieve
