import GaloisForLFunctions.RHTower.Sieve.ZetaLandauWide
import GaloisForLFunctions.RHTower.Sieve.ZetaZeroCount

/-!
# The zero count on the wide disc

Keeping the retained zeros in Landau's inequality at the centre, instead of discarding them, bounds
their number.  On the disc of radius `21/40` every zero `ρ` has `Re ρ ≤ 1`, so

```text
Re (9/8 + iγ - ρ)⁻¹ = (9/8 - Re ρ)/|9/8 + iγ - ρ|² ≥ (1/8)/(21/40)² = 200/441,
```

and the left side is at least `-(8 + A)` by the von Mangoldt series and the pole bound.  Hence the
count is `O(log|γ|)`.
-/

namespace RHTower.Sieve

open Complex

/-- The reciprocal at a zero of the wide disc. -/
theorem wide_re_inv_ge {γ : ℝ} {ρ : ℂ}
    (hd : ‖ρ - (((9 / 8 : ℝ) : ℂ) + (γ : ℂ) * Complex.I)‖ ≤ 21 / 40)
    (hz : riemannZeta ρ = 0) :
    (200 / 441 : ℝ) ≤ (((((9 / 8 : ℝ) : ℂ) + (γ : ℂ) * Complex.I) - ρ)⁻¹).re := by
  have hne : (((9 / 8 : ℝ) : ℂ) + (γ : ℂ) * Complex.I) ≠ ρ := by
    intro hcon
    exact zeta_wide_centre_ne_zero γ (by rw [hcon]; exact hz)
  have hrere : ρ.re ≤ 1 := by
    by_contra hcon
    exact riemannZeta_ne_zero_of_one_le_re (le_of_lt (not_le.mp hcon)) hz
  set w : ℂ := (((9 / 8 : ℝ) : ℂ) + (γ : ℂ) * Complex.I) - ρ with hwdef
  have hw0 : w ≠ 0 := sub_ne_zero.mpr hne
  have hwre : w.re = 9 / 8 - ρ.re := by rw [hwdef, Complex.sub_re, wide_centre_re]
  have hnorm : ‖w‖ ≤ 21 / 40 := by
    rw [hwdef, ← norm_neg]
    simpa using hd
  have hnormsq : Complex.normSq w = ‖w‖ ^ 2 := Complex.normSq_eq_norm_sq w
  have hnormpos : (0 : ℝ) < ‖w‖ := norm_pos_iff.mpr hw0
  have hsq : Complex.normSq w ≤ 441 / 1600 := by
    rw [hnormsq]; nlinarith [hnormpos, hnorm]
  have hsqpos : (0 : ℝ) < Complex.normSq w := by
    rw [hnormsq]; positivity
  rw [Complex.inv_re, hwre, le_div_iff₀ hsqpos]
  nlinarith [hsq, hrere]

/-- **The zero count on the wide disc.**  Any family of zeros in the disc, satisfying Landau's
inequality at the centre, has size `O(log|γ|)`. -/
theorem exists_wide_zero_count :
    ∃ E : ℝ, 0 < E ∧ ∀ γ : ℝ, 4 ≤ |γ| → ∀ (Z : Finset ℂ) (m : ℂ → ℕ),
      (∀ ρ ∈ Z, ‖ρ - (((9 / 8 : ℝ) : ℂ) + (γ : ℂ) * Complex.I)‖ ≤ 21 / 40) →
      (∀ ρ ∈ Z, riemannZeta ρ = 0) →
      ‖logDeriv riemannZeta (((9 / 8 : ℝ) : ℂ) + (γ : ℂ) * Complex.I)
          - ∑ ρ ∈ Z, (m ρ : ℂ) / ((((9 / 8 : ℝ) : ℂ) + (γ : ℂ) * Complex.I) - ρ)‖
        ≤ 320 / 21 * wideD * Real.log |γ| →
      ∑ ρ ∈ Z, (m ρ : ℝ) ≤ E * Real.log |γ| := by
  obtain ⟨A, hA⟩ := exists_pole_bound
  refine ⟨441 / 200 * (320 / 21 * wideD + 8 + max A 0),
    by nlinarith [wideD_pos, le_max_right A 0], ?_⟩
  intro γ hγ Z m hdist hzero hkey
  have hL1 := one_le_log_abs hγ
  have hγ0 : (0 : ℝ) < |γ| := by linarith
  have hAle : A ≤ max A 0 := le_max_left _ _
  have hA0 : (0 : ℝ) ≤ max A 0 := le_max_right _ _
  -- the real part of the retained sum
  have hreSum : (∑ ρ ∈ Z, (m ρ : ℂ) / ((((9 / 8 : ℝ) : ℂ) + (γ : ℂ) * Complex.I) - ρ)).re
      = ∑ ρ ∈ Z, (m ρ : ℝ)
          * (((((9 / 8 : ℝ) : ℂ) + (γ : ℂ) * Complex.I) - ρ)⁻¹).re := by
    rw [Complex.re_sum]
    exact Finset.sum_congr rfl fun ρ _ => re_natCast_div _ _
  have hsplit : -(logDeriv riemannZeta (((9 / 8 : ℝ) : ℂ) + (γ : ℂ) * Complex.I)).re
      ≤ 320 / 21 * wideD * Real.log |γ|
        - ∑ ρ ∈ Z, (m ρ : ℝ)
            * (((((9 / 8 : ℝ) : ℂ) + (γ : ℂ) * Complex.I) - ρ)⁻¹).re := by
    have hd : -(logDeriv riemannZeta (((9 / 8 : ℝ) : ℂ) + (γ : ℂ) * Complex.I)
          - ∑ ρ ∈ Z, (m ρ : ℂ) / ((((9 / 8 : ℝ) : ℂ) + (γ : ℂ) * Complex.I) - ρ)).re
        ≤ ‖logDeriv riemannZeta (((9 / 8 : ℝ) : ℂ) + (γ : ℂ) * Complex.I)
          - ∑ ρ ∈ Z, (m ρ : ℂ) / ((((9 / 8 : ℝ) : ℂ) + (γ : ℂ) * Complex.I) - ρ)‖ := by
      have h := Complex.abs_re_le_norm
        (logDeriv riemannZeta (((9 / 8 : ℝ) : ℂ) + (γ : ℂ) * Complex.I)
          - ∑ ρ ∈ Z, (m ρ : ℂ) / ((((9 / 8 : ℝ) : ℂ) + (γ : ℂ) * Complex.I) - ρ))
      have h2 := abs_le.mp h
      linarith [h2.1]
    rw [Complex.sub_re, hreSum] at hd
    linarith [hkey]
  -- the lower bound at the centre
  have hlow := neg_re_logDeriv_ge (σ := 9 / 8) (γ := γ) (by norm_num)
  have hpole := hA (9 / 8) (by norm_num) (by norm_num)
  rw [neg_div_re_eq_neg_logDeriv_re] at hpole
  have hpole' : -(logDeriv riemannZeta (((9 / 8 : ℝ) : ℂ))).re ≤ 8 + A := by
    have hd : (9 : ℝ) / 8 - 1 = 1 / 8 := by norm_num
    rw [hd] at hpole
    norm_num at hpole ⊢
    linarith
  -- each term is at least `200/441`
  have hterm : ∀ ρ ∈ Z, (200 / 441 : ℝ) * (m ρ : ℝ)
      ≤ (m ρ : ℝ) * (((((9 / 8 : ℝ) : ℂ) + (γ : ℂ) * Complex.I) - ρ)⁻¹).re := by
    intro ρ hρ
    have h := wide_re_inv_ge (hdist ρ hρ) (hzero ρ hρ)
    have hm0 : (0 : ℝ) ≤ (m ρ : ℝ) := Nat.cast_nonneg _
    nlinarith [h, hm0]
  have hsum200 : (200 / 441 : ℝ) * ∑ ρ ∈ Z, (m ρ : ℝ)
      ≤ ∑ ρ ∈ Z, (m ρ : ℝ)
          * (((((9 / 8 : ℝ) : ℂ) + (γ : ℂ) * Complex.I) - ρ)⁻¹).re := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum hterm
  have hstep : (200 / 441 : ℝ) * ∑ ρ ∈ Z, (m ρ : ℝ)
      ≤ 320 / 21 * wideD * Real.log |γ| + (8 + A) := by
    linarith [hsum200, hsplit, hlow, hpole']
  nlinarith [hstep, hL1, hAle, hA0, wideD_pos]

end RHTower.Sieve
