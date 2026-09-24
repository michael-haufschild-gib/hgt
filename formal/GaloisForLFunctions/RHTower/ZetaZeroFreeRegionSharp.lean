import GaloisForLFunctions.RHTower.HyperbolicZeroFreeClosed

/-!
# The zero-free region for `ζ` itself

`xiZeroCopy_zero_free_fiftyEight` is stated for the multiplicity copies of `ξ`.  Transporting it to
`ζ` needs only the zero correspondence `xi_eq_zero_iff` inside the strip and the conjugate copy for
negative ordinates:

```text
4 ≤ |γ|  →  1 − 1/(58 log |γ|) < β  →  ζ(β + iγ) ≠ 0 .
```

Against `Sieve.exists_zero_free_region`, whose width is `1/(10000 log |γ|)` and whose threshold is
`exp (u₀²)` with `u₀ ≥ 202`.
-/

open Complex

namespace RHTower

noncomputable section

/-- **The zero-free region for `ζ`, of width `1/(58 log |γ|)`, valid from `|γ| ≥ 4`.** -/
theorem riemannZeta_ne_zero_of_one_sub_lt_re {β γ : ℝ} (hγ : 4 ≤ |γ|)
    (hβ : 1 - 1 / 58 / Real.log |γ| < β) :
    riemannZeta ((β : ℂ) + (γ : ℂ) * Complex.I) ≠ 0 := by
  intro hzero
  set s : ℂ := (β : ℂ) + (γ : ℂ) * Complex.I with hsdef
  have hsre : s.re = β := by rw [hsdef]; simp
  have hsim : s.im = γ := by rw [hsdef]; simp
  have hγpos : (0 : ℝ) < |γ| := by linarith
  have hlog2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
    push_cast
    ring
  have hlog : (1 : ℝ) ≤ Real.log |γ| := by
    have h := Real.log_le_log (by norm_num : (0:ℝ) < 4) hγ
    rw [hlog4] at h
    linarith
  have hβ1 : β < 1 := by
    by_contra hc
    exact riemannZeta_ne_zero_of_one_le_re (by rw [hsre]; linarith [not_lt.mp hc]) hzero
  have hsmall : 1 / 58 / Real.log |γ| ≤ 1 / 58 := by
    rw [div_le_iff₀ (by linarith), div_mul_eq_mul_div, le_div_iff₀ (by norm_num)]
    nlinarith [hlog]
  have hβ0 : 0 < β := by linarith
  have hne1 : s ≠ 1 := by
    intro h
    have hg : γ = 0 := by rw [← hsim, h]; simp
    rw [hg] at hγ
    norm_num at hγ
  have hxi : xi s = 0 := (xi_eq_zero_iff (by rw [hsre]; exact hβ0) hne1).mpr hzero
  -- the multiplicity copy at `s`
  let ρ : XiDivisorSupport := ⟨s, mem_xi_divisor_support_of_eq_zero hxi⟩
  have hdpos := xi_divisor_pos_on_support ρ
  have hn : 0 < Int.toNat ((MeromorphicOn.divisor xi Set.univ) ((ρ : XiDivisorSupport) : ℂ)) := by
    omega
  let q : XiZeroCopy := ⟨ρ, ⟨0, hn⟩⟩
  have hqcoe : ((q.1 : XiDivisorSupport) : ℂ) = s := rfl
  rcases le_or_gt 0 γ with hg | hg
  · have hγ4 : (4 : ℝ) ≤ γ := by rwa [abs_of_nonneg hg] at hγ
    have hreg := xiZeroCopy_zero_free_fiftyEight (q := q)
      (by rw [hqcoe, hsim]; exact hγ4)
    rw [hqcoe, hsre, hsim] at hreg
    rw [abs_of_nonneg hg] at hβ
    linarith
  · have hγ4 : (4 : ℝ) ≤ -γ := by rwa [abs_of_neg hg] at hγ
    have hreg := xiZeroCopy_zero_free_fiftyEight (q := xiZeroCopyConjEquiv q)
      (by rw [coe_xiZeroCopyConj, hqcoe, Complex.conj_im, hsim]; exact hγ4)
    rw [coe_xiZeroCopyConj, hqcoe, Complex.conj_re, Complex.conj_im, hsre, hsim] at hreg
    rw [abs_of_neg hg] at hβ
    linarith

/-- Contrapositive form: every zero of `ζ` above ordinate `4` obeys the region. -/
theorem re_le_one_sub_of_riemannZeta_eq_zero {β γ : ℝ} (hγ : 4 ≤ |γ|)
    (hzero : riemannZeta ((β : ℂ) + (γ : ℂ) * Complex.I) = 0) :
    β ≤ 1 - 1 / 58 / Real.log |γ| := by
  by_contra hc
  exact riemannZeta_ne_zero_of_one_sub_lt_re hγ (not_le.mp hc) hzero

end

end RHTower
