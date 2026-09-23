import GaloisForLFunctions.HTGeometry.GammaAffineStirlingSignature

/-!
# No flat cancellation in the archimedean residue field

The three scales `1`, `log s`, `1/s` are *independent modulo `O(|s|⁻²)`*: if

```text
‖a + b log t + c/t‖ ≤ K/t²      for all large real `t`,
```

then `a = b = c = 0`.  Reading `log t → ∞` kills `b`, then letting `t → ∞` kills `a`, then the
remaining `‖c‖ ≤ K/t` kills `c`.

This is exactly the "no flat cancellation in the archimedean residue field" step: a nonzero
Stirling signature cannot be hidden inside the remainder of the expansion.  Combined with
`exists_norm_digamma_affine_expansion_le` it separates the monomials of
`e^{αs} s^β ∏_j Γ(λ_j s + μ_j)^{n_j}` by their three signature data.
-/

namespace GaloisForLFunctions.HTGeometry

open Complex Filter Topology

noncomputable section

/-! ## Independence of the three archimedean scales -/

theorem three_term_expansion_eq_zero {a b c : ℂ} {K R : ℝ}
    (h : ∀ t : ℝ, R ≤ t → 1 ≤ t →
      ‖a + b * ((Real.log t : ℝ) : ℂ) + c / ((t : ℝ) : ℂ)‖ ≤ K / t ^ (2 : ℕ)) :
    a = 0 ∧ b = 0 ∧ c = 0 := by
  -- the constant is forced to be nonnegative
  have hK0 : 0 ≤ K := by
    set t0 : ℝ := max R 1 with ht0def
    have ht01 : (1 : ℝ) ≤ t0 := le_max_right _ _
    have hpos : (0 : ℝ) < t0 ^ (2 : ℕ) := by positivity
    have hb := h t0 (le_max_left _ _) ht01
    have hnn := norm_nonneg (a + b * ((Real.log t0 : ℝ) : ℂ) + c / ((t0 : ℝ) : ℂ))
    have : (0 : ℝ) ≤ K / t0 ^ (2 : ℕ) := le_trans hnn hb
    rw [le_div_iff₀ hpos] at this
    linarith
  set M : ℝ := K + ‖a‖ + ‖c‖ with hMdef
  have hlog : ∀ t : ℝ, R ≤ t → 1 ≤ t → ‖b‖ * Real.log t ≤ M := by
    intro t hR ht1
    have ht0 : (0 : ℝ) < t := by linarith
    have hbt : ‖b * ((Real.log t : ℝ) : ℂ)‖ = ‖b‖ * Real.log t := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.log_nonneg ht1)]
    have hct : ‖c / ((t : ℝ) : ℂ)‖ = ‖c‖ / t := by
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht0]
    have hid : b * ((Real.log t : ℝ) : ℂ)
        = (a + b * ((Real.log t : ℝ) : ℂ) + c / ((t : ℝ) : ℂ)) - a
          - c / ((t : ℝ) : ℂ) := by ring
    have hstep1 : ‖(a + b * ((Real.log t : ℝ) : ℂ) + c / ((t : ℝ) : ℂ)) - a
        - c / ((t : ℝ) : ℂ)‖
        ≤ ‖(a + b * ((Real.log t : ℝ) : ℂ) + c / ((t : ℝ) : ℂ)) - a‖
          + ‖c / ((t : ℝ) : ℂ)‖ :=
      norm_sub_le ((a + b * ((Real.log t : ℝ) : ℂ) + c / ((t : ℝ) : ℂ)) - a)
        (c / ((t : ℝ) : ℂ))
    have hstep2 : ‖(a + b * ((Real.log t : ℝ) : ℂ) + c / ((t : ℝ) : ℂ)) - a‖
        ≤ ‖a + b * ((Real.log t : ℝ) : ℂ) + c / ((t : ℝ) : ℂ)‖ + ‖a‖ :=
      norm_sub_le (a + b * ((Real.log t : ℝ) : ℂ) + c / ((t : ℝ) : ℂ)) a
    have hmain := h t hR ht1
    have ht2 : (1 : ℝ) ≤ t ^ (2 : ℕ) := by nlinarith [ht1]
    have hK : K / t ^ (2 : ℕ) ≤ K := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith [mul_nonneg hK0 (by linarith : (0 : ℝ) ≤ t ^ (2 : ℕ) - 1)]
    have hc : ‖c‖ / t ≤ ‖c‖ := by
      rw [div_le_iff₀ ht0]
      nlinarith [norm_nonneg c, ht1]
    rw [hMdef]
    rw [← hbt, hid]
    rw [hct] at hstep1
    linarith [hstep1, hstep2, hmain, hK, hc]
  have hb : b = 0 := by
    by_contra hbne
    have hbpos : (0 : ℝ) < ‖b‖ := norm_pos_iff.mpr hbne
    set T : ℝ := max (max R 1) (Real.exp (M / ‖b‖ + 1)) with hTdef
    have hTR : R ≤ T := le_trans (le_max_left R 1) (le_max_left _ _)
    have hT1 : 1 ≤ T := le_trans (le_max_right R 1) (le_max_left _ _)
    have hTexp : Real.exp (M / ‖b‖ + 1) ≤ T := le_max_right _ _
    have hlogT : M / ‖b‖ + 1 ≤ Real.log T := by
      have h1 := Real.log_le_log (Real.exp_pos _) hTexp
      rwa [Real.log_exp] at h1
    have hbound := hlog T hTR hT1
    have hstep : ‖b‖ * (M / ‖b‖ + 1) ≤ ‖b‖ * Real.log T :=
      mul_le_mul_of_nonneg_left hlogT hbpos.le
    have hval : ‖b‖ * (M / ‖b‖ + 1) = M + ‖b‖ := by field_simp
    rw [hval] at hstep
    linarith
  have ha : a = 0 := by
    by_contra hane
    have hapos : (0 : ℝ) < ‖a‖ := norm_pos_iff.mpr hane
    set T : ℝ := max (max R 1) ((K + ‖c‖) / ‖a‖ + 1) with hTdef
    have hTR : R ≤ T := le_trans (le_max_left R 1) (le_max_left _ _)
    have hT1 : 1 ≤ T := le_trans (le_max_right R 1) (le_max_left _ _)
    have hTbig : (K + ‖c‖) / ‖a‖ + 1 ≤ T := le_max_right _ _
    have hT0 : (0 : ℝ) < T := by linarith
    have hmain := h T hTR hT1
    rw [hb, zero_mul, add_zero] at hmain
    have hct : ‖c / ((T : ℝ) : ℂ)‖ = ‖c‖ / T := by
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hT0]
    have hid : a = (a + c / ((T : ℝ) : ℂ)) - c / ((T : ℝ) : ℂ) := by ring
    have hstep1 : ‖(a + c / ((T : ℝ) : ℂ)) - c / ((T : ℝ) : ℂ)‖
        ≤ ‖a + c / ((T : ℝ) : ℂ)‖ + ‖c / ((T : ℝ) : ℂ)‖ :=
      norm_sub_le (a + c / ((T : ℝ) : ℂ)) (c / ((T : ℝ) : ℂ))
    rw [hct] at hstep1
    have hKT : K / T ^ (2 : ℕ) ≤ K / T := by
      rw [div_le_div_iff₀ (by positivity) hT0]
      nlinarith [mul_nonneg (mul_nonneg hK0 hT0.le) (by nlinarith [hT1] : (0 : ℝ) ≤ T - 1)]
    have hfinal : ‖a‖ ≤ (K + ‖c‖) / T := by
      have hsum : ‖a‖ ≤ K / T + ‖c‖ / T := by
        rw [hid]
        linarith [hstep1, hmain, hKT]
      calc ‖a‖ ≤ K / T + ‖c‖ / T := hsum
        _ = (K + ‖c‖) / T := by ring
      
    rw [le_div_iff₀ hT0] at hfinal
    have hgt : (K + ‖c‖) / ‖a‖ < T := by linarith
    rw [div_lt_iff₀ hapos] at hgt
    nlinarith [hfinal, hgt]
  refine ⟨ha, hb, ?_⟩
  by_contra hcne
  have hcpos : (0 : ℝ) < ‖c‖ := norm_pos_iff.mpr hcne
  set T : ℝ := max (max R 1) (K / ‖c‖ + 1) with hTdef
  have hTR : R ≤ T := le_trans (le_max_left R 1) (le_max_left _ _)
  have hT1 : 1 ≤ T := le_trans (le_max_right R 1) (le_max_left _ _)
  have hTbig : K / ‖c‖ + 1 ≤ T := le_max_right _ _
  have hT0 : (0 : ℝ) < T := by linarith
  have hmain := h T hTR hT1
  rw [ha, hb, zero_mul, add_zero, zero_add] at hmain
  have hct : ‖c / ((T : ℝ) : ℂ)‖ = ‖c‖ / T := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hT0]
  rw [hct] at hmain
  rw [div_le_div_iff₀ hT0 (by positivity)] at hmain
  have hgt : K / ‖c‖ < T := by linarith
  rw [div_lt_iff₀ hcpos] at hgt
  nlinarith [hmain, hgt, hT0, hcpos]

end

end GaloisForLFunctions.HTGeometry
