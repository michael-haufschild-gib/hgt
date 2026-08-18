import Mathlib

/-!
# The Perron kernel on the one-line

Step 2 of Matomäki–Teräväinen §7 turns the short/long window comparison into an integral against

```text
K(s) = ((x+h)^s − x^s)/s ,      s = 1 + it ,
```

and the dyadic assembly of `Sieve/MixedMomentAssembly` consumes the branch `|K| ≤ C/|t|`.  That
branch is elementary: on the one-line the two powers have modulus `x+h` and `x`, and `|1+it| ≥ |t|`.
-/

namespace RHTower.Sieve

open Complex

noncomputable section

/-- **The Perron kernel decays like `1/|t|` on the one-line.** -/
theorem norm_perron_kernel_le_div {x h t : ℝ} (hx : 0 < x) (hh : 0 < h) (ht : t ≠ 0) :
    ‖(((x + h : ℝ) : ℂ) ^ ((1 : ℂ) + (t : ℝ) * Complex.I)
        - ((x : ℝ) : ℂ) ^ ((1 : ℂ) + (t : ℝ) * Complex.I))
      / ((1 : ℂ) + (t : ℝ) * Complex.I)‖
      ≤ 2 * (x + h) / |t| := by
  have hxh : (0 : ℝ) < x + h := by linarith
  have habs : (0 : ℝ) < |t| := abs_pos.2 ht
  have hre : ((1 : ℂ) + (t : ℝ) * Complex.I).re = 1 := by simp
  have hnum1 : ‖((x + h : ℝ) : ℂ) ^ ((1 : ℂ) + (t : ℝ) * Complex.I)‖ = x + h := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hxh, hre, Real.rpow_one]
  have hnum2 : ‖((x : ℝ) : ℂ) ^ ((1 : ℂ) + (t : ℝ) * Complex.I)‖ = x := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hx, hre, Real.rpow_one]
  have hden : |t| ≤ ‖(1 : ℂ) + (t : ℝ) * Complex.I‖ := by
    have him : ((1 : ℂ) + (t : ℝ) * Complex.I).im = t := by simp
    calc |t| = |((1 : ℂ) + (t : ℝ) * Complex.I).im| := by rw [him]
      _ ≤ ‖(1 : ℂ) + (t : ℝ) * Complex.I‖ := Complex.abs_im_le_norm _
  have hden0 : (0 : ℝ) < ‖(1 : ℂ) + (t : ℝ) * Complex.I‖ := lt_of_lt_of_le habs hden
  rw [norm_div]
  have hnum : ‖((x + h : ℝ) : ℂ) ^ ((1 : ℂ) + (t : ℝ) * Complex.I)
      - ((x : ℝ) : ℂ) ^ ((1 : ℂ) + (t : ℝ) * Complex.I)‖ ≤ 2 * (x + h) := by
    refine le_trans (norm_sub_le _ _) ?_
    rw [hnum1, hnum2]
    linarith
  calc ‖((x + h : ℝ) : ℂ) ^ ((1 : ℂ) + (t : ℝ) * Complex.I)
        - ((x : ℝ) : ℂ) ^ ((1 : ℂ) + (t : ℝ) * Complex.I)‖
        / ‖(1 : ℂ) + (t : ℝ) * Complex.I‖
      ≤ (2 * (x + h)) / ‖(1 : ℂ) + (t : ℝ) * Complex.I‖ :=
        div_le_div_of_nonneg_right hnum hden0.le
    _ ≤ 2 * (x + h) / |t| := by
        refine div_le_div_of_nonneg_left (by linarith) habs hden

/-- **The Perron kernel is bounded by the window length.**  The complementary branch, from the
integral representation `K = ∫_x^{x+h} u^{it} du`, whose integrand is unimodular. -/
theorem norm_perron_kernel_le_length {x h : ℝ} (hx : 0 < x) (hh : 0 < h) (t : ℝ) :
    ‖(((x + h : ℝ) : ℂ) ^ ((1 : ℂ) + (t : ℝ) * Complex.I)
        - ((x : ℝ) : ℂ) ^ ((1 : ℂ) + (t : ℝ) * Complex.I))
      / ((1 : ℂ) + (t : ℝ) * Complex.I)‖ ≤ h := by
  have hr : (((t : ℝ) : ℂ) * Complex.I).re = 0 := by simp
  have hcpow := integral_cpow (a := x) (b := x + h) (r := ((t : ℝ) : ℂ) * Complex.I)
    (Or.inl (by rw [hr]; norm_num))
  have hcomm : (((t : ℝ) : ℂ) * Complex.I) + 1 = (1 : ℂ) + ((t : ℝ) : ℂ) * Complex.I := by ring
  rw [hcomm] at hcpow
  rw [← hcpow]
  have hbd : ∀ u ∈ Set.uIoc x (x + h), ‖((u : ℝ) : ℂ) ^ (((t : ℝ) : ℂ) * Complex.I)‖ ≤ 1 := by
    intro u hu
    have hu0 : 0 < u := by
      rw [Set.uIoc_of_le (by linarith : x ≤ x + h), Set.mem_Ioc] at hu
      linarith [hu.1]
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hu0, hr, Real.rpow_zero]
  refine le_trans (intervalIntegral.norm_integral_le_of_norm_le_const hbd) ?_
  rw [show x + h - x = h by ring, abs_of_nonneg hh.le, one_mul]

/-- **The Perron kernel, both branches.**  This is the `min(h, x/|t|)` shape the §7 assembly uses. -/
theorem norm_perron_kernel_le_min {x h t : ℝ} (hx : 0 < x) (hh : 0 < h) (ht : t ≠ 0) :
    ‖(((x + h : ℝ) : ℂ) ^ ((1 : ℂ) + (t : ℝ) * Complex.I)
        - ((x : ℝ) : ℂ) ^ ((1 : ℂ) + (t : ℝ) * Complex.I))
      / ((1 : ℂ) + (t : ℝ) * Complex.I)‖
      ≤ min h (2 * (x + h) / |t|) :=
  le_min (norm_perron_kernel_le_length hx hh t) (norm_perron_kernel_le_div hx hh ht)

end

end RHTower.Sieve
