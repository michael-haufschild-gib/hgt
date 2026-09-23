import GaloisForLFunctions.RHTower.ZetaLogDerivBound
import GaloisForLFunctions.RHTower.ZetaLogDerivLineBound
import GaloisForLFunctions.RHTower.ZetaVerticalLineBound

/-!
# Vertical bounds on the shifted line `Re s = 1 + 2ω`, uniform in the shift

For `|t| ≥ 9` and every shift `0 < 2ω ≤ 1` the reciprocal zeta and the logarithmic derivative
obey log-power bounds **independent of the shift**:

```text
‖1/ζ(1+2ω+it)‖   ≤ (26/A)·log⁷|t| ,
‖ζ′/ζ(1+2ω+it)‖  ≤ (2248/A²)·log¹⁸|t| ,
```

`A` the zero-free strip constant.  Inside the strip `2ω ≤ A/log⁹|t|` these are the zero-free
region bounds; outside it the shift itself is large, and the quartic lower bound right of the
one-line together with the Euler-region log-derivative bound take over.
-/

noncomputable section

namespace RHTower

open Complex

theorem two_lt_log_abs {t : ℝ} (ht : 9 ≤ |t|) : 2 < Real.log |t| := by
  have ht0 : (0 : ℝ) < |t| := by linarith
  have hexp2 := exp_two_lt_eight
  have h1 : Real.log (Real.exp 2) < Real.log |t| :=
    Real.log_lt_log (Real.exp_pos 2) (by linarith)
  rwa [Real.log_exp] at h1

theorem shift_line_cast (ω t : ℝ) :
    (1 : ℂ) + 2 * (ω : ℂ) + (t : ℂ) * Complex.I
      = ((1 + 2 * ω : ℝ) : ℂ) + (t : ℂ) * Complex.I := by
  push_cast
  ring

/-- **Uniform reciprocal bound on the shifted line.** -/
theorem norm_inv_riemannZeta_shift_le {ω t : ℝ} (hω : 0 < ω) (hω1 : 2 * ω ≤ 1) (ht : 9 ≤ |t|) :
    ‖(riemannZeta ((1 : ℂ) + 2 * (ω : ℂ) + (t : ℂ) * Complex.I))⁻¹‖
      ≤ 26 / zetaLowerA * Real.log |t| ^ (7 : ℕ) := by
  have hL2 : 2 < Real.log |t| := two_lt_log_abs ht
  have hL0 : (0 : ℝ) < Real.log |t| := by linarith
  have hA0 : (0 : ℝ) < zetaLowerA := zetaLowerA_pos
  have hA1 : zetaLowerA ≤ 1 := zetaLowerA_le_one
  have hL7 : (0 : ℝ) < Real.log |t| ^ (7 : ℕ) := by positivity
  rw [shift_line_cast]
  by_cases hcase : 2 * ω ≤ zetaLowerA / Real.log |t| ^ (9 : ℕ)
  · -- inside the zero-free strip
    have hL9 : (0 : ℝ) < Real.log |t| ^ (9 : ℕ) := by positivity
    have hσl : 1 - zetaLowerA / Real.log |t| ^ (9 : ℕ) ≤ 1 + 2 * ω := by
      have : (0 : ℝ) < zetaLowerA / Real.log |t| ^ (9 : ℕ) := by positivity
      linarith
    have hσu : 1 + 2 * ω ≤ 1 + zetaLowerA / Real.log |t| ^ (9 : ℕ) := by linarith
    have h := norm_inv_riemannZeta_le (σ := 1 + 2 * ω) ht hσl hσu
    have hmono : 20 / zetaLowerA * Real.log |t| ^ (7 : ℕ) ≤ 26 / zetaLowerA * Real.log |t| ^ (7 : ℕ) := by
      have h20 : 20 / zetaLowerA ≤ 26 / zetaLowerA := by
        rw [div_le_div_iff₀ hA0 hA0]
        nlinarith
      nlinarith [hL7]
    linarith
  · -- large shift: the quartic lower bound right of the one-line
    rw [not_le] at hcase
    have hL9 : (0 : ℝ) < Real.log |t| ^ (9 : ℕ) := by positivity
    have hq := pow_four_norm_riemannZeta_ge (x := 2 * ω) ht (by linarith) hω1
    have hcube : zetaLowerA ^ (3 : ℕ) / Real.log |t| ^ (27 : ℕ) ≤ (2 * ω) ^ (3 : ℕ) := by
      have h1 : zetaLowerA / Real.log |t| ^ (9 : ℕ) ≤ 2 * ω := le_of_lt hcase
      have h2 : (0 : ℝ) < zetaLowerA / Real.log |t| ^ (9 : ℕ) := by positivity
      have h3 : (zetaLowerA / Real.log |t| ^ (9 : ℕ)) ^ (3 : ℕ) ≤ (2 * ω) ^ (3 : ℕ) :=
        pow_le_pow_left₀ (le_of_lt h2) h1 3
      have h4 : (zetaLowerA / Real.log |t| ^ (9 : ℕ)) ^ (3 : ℕ)
          = zetaLowerA ^ (3 : ℕ) / Real.log |t| ^ (27 : ℕ) := by
        rw [div_pow, ← pow_mul]
      linarith [h4 ▸ h3]
    have hlow : zetaLowerA ^ (3 : ℕ) / (756 * Real.log |t| ^ (28 : ℕ))
        ≤ ‖riemannZeta (((1 + 2 * ω : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ ^ (4 : ℕ) := by
      refine le_trans ?_ hq
      have h27 : (0 : ℝ) < Real.log |t| ^ (27 : ℕ) := by positivity
      have hcube' : zetaLowerA ^ (3 : ℕ) ≤ (2 * ω) ^ (3 : ℕ) * Real.log |t| ^ (27 : ℕ) := by
        rw [div_le_iff₀ h27] at hcube
        linarith
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have hstep := mul_le_mul_of_nonneg_right hcube'
        (by positivity : (0 : ℝ) ≤ 756 * Real.log |t|)
      have hpow : ((2 * ω) ^ (3 : ℕ) * Real.log |t| ^ (27 : ℕ)) * (756 * Real.log |t|)
          = (2 * ω) ^ (3 : ℕ) * (756 * Real.log |t| ^ (28 : ℕ)) := by ring
      linarith [hpow ▸ hstep]
    have hζpos : (0 : ℝ) < ‖riemannZeta (((1 + 2 * ω : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ := by
      rcases eq_or_lt_of_le (norm_nonneg
        (riemannZeta (((1 + 2 * ω : ℝ) : ℂ) + (t : ℂ) * Complex.I))) with h | h
      · exfalso
        rw [← h] at hlow
        have : (0 : ℝ) ^ (4 : ℕ) = 0 := by norm_num
        rw [this] at hlow
        have : (0 : ℝ) < zetaLowerA ^ (3 : ℕ) / (756 * Real.log |t| ^ (28 : ℕ)) := by positivity
        linarith
      · exact h
    have hkey : 1 ≤ 6 / zetaLowerA * Real.log |t| ^ (7 : ℕ) *
        ‖riemannZeta (((1 + 2 * ω : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ := by
      refine le_of_pow_le_pow_left₀ (n := 4) (by norm_num) (by positivity) ?_
      have hexp : (6 / zetaLowerA * Real.log |t| ^ (7 : ℕ) *
          ‖riemannZeta (((1 + 2 * ω : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖) ^ (4 : ℕ)
          = (6 / zetaLowerA) ^ (4 : ℕ) * Real.log |t| ^ (28 : ℕ) *
            ‖riemannZeta (((1 + 2 * ω : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ ^ (4 : ℕ) := by
        rw [mul_pow, mul_pow, ← pow_mul]
      rw [hexp, one_pow]
      have h1 : (6 / zetaLowerA) ^ (4 : ℕ) * Real.log |t| ^ (28 : ℕ) *
          (zetaLowerA ^ (3 : ℕ) / (756 * Real.log |t| ^ (28 : ℕ)))
          ≤ (6 / zetaLowerA) ^ (4 : ℕ) * Real.log |t| ^ (28 : ℕ) *
            ‖riemannZeta (((1 + 2 * ω : ℝ) : ℂ) + (t : ℂ) * Complex.I)‖ ^ (4 : ℕ) := by
        have hpos : (0 : ℝ) ≤ (6 / zetaLowerA) ^ (4 : ℕ) * Real.log |t| ^ (28 : ℕ) := by positivity
        exact mul_le_mul_of_nonneg_left hlow hpos
      have h2 : (1 : ℝ) ≤ (6 / zetaLowerA) ^ (4 : ℕ) * Real.log |t| ^ (28 : ℕ) *
          (zetaLowerA ^ (3 : ℕ) / (756 * Real.log |t| ^ (28 : ℕ))) := by
        have hLpow : (0 : ℝ) < Real.log |t| ^ (28 : ℕ) := by positivity
        rw [div_pow]
        field_simp
        nlinarith [hA1, hA0]
      linarith
    rw [norm_inv]
    rw [inv_le_iff_one_le_mul₀ hζpos]
    have h6 : 6 / zetaLowerA * Real.log |t| ^ (7 : ℕ) ≤ 26 / zetaLowerA * Real.log |t| ^ (7 : ℕ) := by
      have hd : 6 / zetaLowerA ≤ 26 / zetaLowerA := by
        rw [div_le_div_iff₀ hA0 hA0]
        nlinarith
      nlinarith [hL7]
    have hmono := mul_le_mul_of_nonneg_right h6
      (norm_nonneg (riemannZeta (((1 + 2 * ω : ℝ) : ℂ) + (t : ℂ) * Complex.I)))
    linarith [hkey]

/-- **Uniform logarithmic-derivative bound on the shifted line.** -/
theorem norm_logDeriv_riemannZeta_shift_le {ω t : ℝ} (hω : 0 < ω) (hω1 : 2 * ω ≤ 1)
    (ht : 9 ≤ |t|) :
    ‖deriv riemannZeta ((1 : ℂ) + 2 * (ω : ℂ) + (t : ℂ) * Complex.I) /
        riemannZeta ((1 : ℂ) + 2 * (ω : ℂ) + (t : ℂ) * Complex.I)‖
      ≤ 2248 / zetaLowerA ^ (2 : ℕ) * Real.log |t| ^ (18 : ℕ) := by
  have hL2 : 2 < Real.log |t| := two_lt_log_abs ht
  have hL0 : (0 : ℝ) < Real.log |t| := by linarith
  have hA0 : (0 : ℝ) < zetaLowerA := zetaLowerA_pos
  have hA1 : zetaLowerA ≤ 1 := zetaLowerA_le_one
  rw [shift_line_cast]
  by_cases hcase : 2 * ω ≤ zetaLowerA / Real.log |t| ^ (9 : ℕ)
  · have hL9 : (0 : ℝ) < Real.log |t| ^ (9 : ℕ) := by positivity
    have hσl : 1 - zetaLowerA / Real.log |t| ^ (9 : ℕ) ≤ 1 + 2 * ω := by
      have : (0 : ℝ) < zetaLowerA / Real.log |t| ^ (9 : ℕ) := by positivity
      linarith
    have hσu : 1 + 2 * ω ≤ 1 + zetaLowerA / Real.log |t| ^ (9 : ℕ) := by linarith
    have h := norm_deriv_div_riemannZeta_le (σ := 1 + 2 * ω) ht hσl hσu
    have hstep : 2240 / zetaLowerA * Real.log |t| ^ (9 : ℕ)
        ≤ 2248 / zetaLowerA ^ (2 : ℕ) * Real.log |t| ^ (18 : ℕ) := by
      have h1 : Real.log |t| ^ (9 : ℕ) ≤ Real.log |t| ^ (18 : ℕ) := by
        apply pow_le_pow_right₀ (by linarith)
        norm_num
      have h2 : 2240 / zetaLowerA ≤ 2248 / zetaLowerA ^ (2 : ℕ) := by
        rw [div_le_div_iff₀ hA0 (by positivity)]
        nlinarith [pow_pos hA0 2]
      have h3 : (0 : ℝ) < Real.log |t| ^ (9 : ℕ) := by positivity
      have h4 := mul_le_mul_of_nonneg_right h2 (le_of_lt h3)
      have h5 := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ 2248 / zetaLowerA ^ (2 : ℕ))
      linarith
    linarith
  · rw [not_le] at hcase
    have hre : (((1 + 2 * ω : ℝ) : ℂ) + (t : ℂ) * Complex.I).re = 1 + 2 * ω := by
      simp [Complex.add_re, Complex.mul_re]
    have h := norm_zeta_logDeriv_le_line
      (s := ((1 + 2 * ω : ℝ) : ℂ) + (t : ℂ) * Complex.I) (by rw [hre]; linarith)
      (by rw [hre]; linarith)
    rw [hre] at h
    have hsimp : (1 : ℝ) + 2 * ω - 1 = 2 * ω := by ring
    rw [hsimp] at h
    have hlow : zetaLowerA ^ (2 : ℕ) / Real.log |t| ^ (18 : ℕ) ≤ (2 * ω) ^ (2 : ℕ) := by
      have h1 : zetaLowerA / Real.log |t| ^ (9 : ℕ) ≤ 2 * ω := le_of_lt hcase
      have h2 : (0 : ℝ) < zetaLowerA / Real.log |t| ^ (9 : ℕ) := by positivity
      have h3 : (zetaLowerA / Real.log |t| ^ (9 : ℕ)) ^ (2 : ℕ) ≤ (2 * ω) ^ (2 : ℕ) :=
        pow_le_pow_left₀ (le_of_lt h2) h1 2
      have h4 : (zetaLowerA / Real.log |t| ^ (9 : ℕ)) ^ (2 : ℕ)
          = zetaLowerA ^ (2 : ℕ) / Real.log |t| ^ (18 : ℕ) := by
        rw [div_pow, ← pow_mul]
      linarith [h4 ▸ h3]
    have hpos : (0 : ℝ) < (2 * ω) ^ (2 : ℕ) := by positivity
    have hstep : 8 / (2 * ω) ^ (2 : ℕ) ≤ 2248 / zetaLowerA ^ (2 : ℕ) * Real.log |t| ^ (18 : ℕ) := by
      have h5 : 8 / (2 * ω) ^ (2 : ℕ) ≤ 8 / (zetaLowerA ^ (2 : ℕ) / Real.log |t| ^ (18 : ℕ)) := by
        apply div_le_div_of_nonneg_left (by norm_num) (by positivity) hlow
      have h6 : (8 : ℝ) / (zetaLowerA ^ (2 : ℕ) / Real.log |t| ^ (18 : ℕ))
          = 8 * Real.log |t| ^ (18 : ℕ) / zetaLowerA ^ (2 : ℕ) := by
        field_simp
      have h7 : 8 * Real.log |t| ^ (18 : ℕ) / zetaLowerA ^ (2 : ℕ)
          ≤ 2248 / zetaLowerA ^ (2 : ℕ) * Real.log |t| ^ (18 : ℕ) := by
        rw [div_mul_eq_mul_div, mul_comm (2248 : ℝ)]
        apply div_le_div_of_nonneg_right ?_ (by positivity)
        nlinarith [pow_pos hL0 18]
      linarith [h6 ▸ h5]
    linarith

end RHTower
