import GaloisForLFunctions.RHTower.EMCarrier
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# The logarithmic vertical-line bound for zeta

Truncating the Euler--Maclaurin carrier at `N = ⌈|t|⌉` gives the classical uniform bound

```text
|ζ(σ + it)| ≤ log |t| + 5        (1 ≤ σ ≤ 2, |t| ≥ 2),
```

with all three pieces elementary: the Dirichlet polynomial is at most the harmonic number
`1 + log N`, the pole term is at most `1/|t| ≤ 1/2` because `N^(1-σ) ≤ 1`, and the Euler--Maclaurin
remainder is at most `‖s‖/N ≤ 1 + 2/|t| ≤ 2`.

The bound is uniform in `σ` down to the line `σ = 1`, which is what the critical scaling needs.
-/

namespace RHTower

noncomputable section

/-! ### Norms of natural powers -/

theorem norm_natCast_cpow_zetaVerticalLineBound {n : ℕ} (hn : 1 ≤ n) (z : ℂ) :
    ‖(n : ℂ) ^ z‖ = (n : ℝ) ^ z.re := by
  have hpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  rw [show ((n : ℕ) : ℂ) = (((n : ℕ) : ℝ) : ℂ) by push_cast; ring,
    Complex.norm_cpow_eq_rpow_re_of_pos hpos]

/-! ### The Dirichlet polynomial -/

/-- On the closed half plane `σ ≥ 1` the Dirichlet polynomial is at most the harmonic number. -/
theorem norm_dirichletPoly_le_one_add_log {N : ℕ} {s : ℂ} (hσ : 1 ≤ s.re) :
    ‖dirichletPoly N s‖ ≤ 1 + Real.log N := by
  have hterm : ∀ n ∈ Finset.Icc 1 N, ‖(n : ℂ) ^ (-s)‖ ≤ ((n : ℝ))⁻¹ := by
    intro n hn
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
    have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
    rw [norm_natCast_cpow_zetaVerticalLineBound hn1]
    have hle := Real.rpow_le_rpow_of_exponent_le hnR (by simp; linarith : (-s).re ≤ -1)
    rwa [Real.rpow_neg_one] at hle
  calc ‖dirichletPoly N s‖ ≤ ∑ n ∈ Finset.Icc 1 N, ‖(n : ℂ) ^ (-s)‖ := by
        rw [dirichletPoly]
        exact norm_sum_le _ _
    _ ≤ ∑ n ∈ Finset.Icc 1 N, ((n : ℝ))⁻¹ := Finset.sum_le_sum hterm
    _ = (harmonic N : ℝ) := by
        rw [harmonic_eq_sum_Icc]
        push_cast
        ring
    _ ≤ 1 + Real.log N := harmonic_le_one_add_log N

/-! ### The pole term -/

theorem norm_emPole_le {N : ℕ} (hN : 1 ≤ N) {s : ℂ} (hσ : 1 ≤ s.re) (ht : 2 ≤ |s.im|) :
    ‖emPole N s‖ ≤ 1 / 2 := by
  have hNR : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hnum : ‖(N : ℂ) ^ (1 - s)‖ ≤ 1 := by
    rw [norm_natCast_cpow_zetaVerticalLineBound hN]
    have hle := Real.rpow_le_rpow_of_exponent_le hNR (by simp; linarith : (1 - s).re ≤ 0)
    rwa [Real.rpow_zero] at hle
  have hden : (2 : ℝ) ≤ ‖s - 1‖ := by
    have habs : |(s - 1).im| ≤ ‖s - 1‖ := Complex.abs_im_le_norm _
    have him : (s - 1).im = s.im := by simp
    rw [him] at habs
    linarith
  rw [emPole, norm_div]
  rw [div_le_div_iff₀ (by linarith) (by norm_num : (0:ℝ) < 2)]
  nlinarith [norm_nonneg ((N : ℂ) ^ (1 - s))]

/-! ### The logarithmic bound -/

/-- **The logarithmic vertical-line bound.**  `|ζ(σ+it)| ≤ log|t| + 5` for `1 ≤ σ ≤ 2` and
`|t| ≥ 2`, uniformly in `σ`. -/
theorem norm_riemannZeta_le_log_add {s : ℂ}
    (hσ1 : 1 ≤ s.re) (hσ2 : s.re ≤ 2) (ht : 2 ≤ |s.im|) :
    ‖riemannZeta s‖ ≤ Real.log |s.im| + 5 := by
  have htpos : (0 : ℝ) < |s.im| := by linarith
  have hNge : |s.im| ≤ (⌈|s.im|⌉₊ : ℝ) := Nat.le_ceil _
  have hNlt : ((⌈|s.im|⌉₊ : ℕ) : ℝ) < |s.im| + 1 := Nat.ceil_lt_add_one htpos.le
  have hNR : (1 : ℝ) ≤ ((⌈|s.im|⌉₊ : ℕ) : ℝ) := by linarith
  have hN1 : 1 ≤ ⌈|s.im|⌉₊ := by exact_mod_cast hNR
  have hσ0 : 0 < s.re := by linarith
  have hs1 : s ≠ 1 := by
    intro h
    rw [h] at ht
    simp only [Complex.one_im, abs_zero] at ht
    linarith
  have hEM := zeta_sub_emCarrier_norm_le hN1 hσ0 hs1
  -- the remainder
  have hrem : ‖s‖ * ((⌈|s.im|⌉₊ : ℕ) : ℝ) ^ (-s.re) / s.re ≤ 2 := by
    have h1 : ((⌈|s.im|⌉₊ : ℕ) : ℝ) ^ (-s.re) ≤ (((⌈|s.im|⌉₊ : ℕ) : ℝ))⁻¹ := by
      have hle := Real.rpow_le_rpow_of_exponent_le hNR (by linarith : -s.re ≤ -1)
      rwa [Real.rpow_neg_one] at hle
    have h2 : ‖s‖ ≤ 2 + |s.im| := by
      have hb := Complex.norm_le_abs_re_add_abs_im s
      rw [abs_of_nonneg hσ0.le] at hb
      linarith
    have h3 : (((⌈|s.im|⌉₊ : ℕ) : ℝ))⁻¹ ≤ (|s.im|)⁻¹ := by
      exact inv_anti₀ htpos hNge
    have h4 : ‖s‖ * ((⌈|s.im|⌉₊ : ℕ) : ℝ) ^ (-s.re) ≤ (2 + |s.im|) * (|s.im|)⁻¹ := by
      refine mul_le_mul h2 (le_trans h1 h3) (Real.rpow_nonneg (by linarith) _) (by linarith)
    have h5 : (2 + |s.im|) * (|s.im|)⁻¹ ≤ 2 := by
      rw [← div_eq_mul_inv, div_le_iff₀ htpos]
      linarith
    have h6 : (0 : ℝ) ≤ ‖s‖ * ((⌈|s.im|⌉₊ : ℕ) : ℝ) ^ (-s.re) := by
      have := Real.rpow_nonneg (by linarith : (0:ℝ) ≤ ((⌈|s.im|⌉₊ : ℕ) : ℝ)) (-s.re)
      positivity
    calc ‖s‖ * ((⌈|s.im|⌉₊ : ℕ) : ℝ) ^ (-s.re) / s.re
        ≤ ‖s‖ * ((⌈|s.im|⌉₊ : ℕ) : ℝ) ^ (-s.re) / 1 := by
          refine div_le_div_of_nonneg_left h6 (by norm_num) hσ1
      _ = ‖s‖ * ((⌈|s.im|⌉₊ : ℕ) : ℝ) ^ (-s.re) := by ring
      _ ≤ 2 := le_trans h4 h5
  -- the logarithm of the truncation point
  have hlogN : Real.log ((⌈|s.im|⌉₊ : ℕ) : ℝ) ≤ Real.log |s.im| + 1 := by
    have he : (2 : ℝ) ≤ Real.exp 1 := by
      have := Real.add_one_le_exp (1 : ℝ)
      linarith
    have hle : ((⌈|s.im|⌉₊ : ℕ) : ℝ) ≤ Real.exp 1 * |s.im| := by
      nlinarith [hNlt, htpos, he]
    calc Real.log ((⌈|s.im|⌉₊ : ℕ) : ℝ)
        ≤ Real.log (Real.exp 1 * |s.im|) := Real.log_le_log (by linarith) hle
      _ = 1 + Real.log |s.im| := by
          rw [Real.log_mul (Real.exp_ne_zero 1) (ne_of_gt htpos), Real.log_exp]
      _ = Real.log |s.im| + 1 := by ring
  -- assemble
  have hcar : ‖emCarrier ⌈|s.im|⌉₊ s‖ ≤ Real.log |s.im| + 5 / 2 := by
    have hpoly := norm_dirichletPoly_le_one_add_log (N := ⌈|s.im|⌉₊) hσ1
    have hpole := norm_emPole_le hN1 hσ1 ht
    calc ‖emCarrier ⌈|s.im|⌉₊ s‖
        ≤ ‖dirichletPoly ⌈|s.im|⌉₊ s‖ + ‖emPole ⌈|s.im|⌉₊ s‖ := by
          rw [emCarrier]
          exact norm_add_le _ _
      _ ≤ (1 + Real.log ((⌈|s.im|⌉₊ : ℕ) : ℝ)) + 1 / 2 := by linarith
      _ ≤ Real.log |s.im| + 5 / 2 := by linarith
  have hfinal : ‖riemannZeta s‖ ≤ ‖riemannZeta s - emCarrier ⌈|s.im|⌉₊ s‖ +
      ‖emCarrier ⌈|s.im|⌉₊ s‖ := by
    have := norm_add_le (riemannZeta s - emCarrier ⌈|s.im|⌉₊ s) (emCarrier ⌈|s.im|⌉₊ s)
    simpa using this
  linarith

end

end RHTower
