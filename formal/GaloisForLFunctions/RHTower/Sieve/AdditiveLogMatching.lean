import GaloisForLFunctions.RHTower.Sieve.DyadicBandBound

/-!
# The additive band is dominated by the logarithmic one

Gallagher's lemma is stated with the multiplicative kernel `(δ − |log m − log n|)₊`; the pair
expansion of the dyadic mean square produces the additive kernel `(ℓ − |m − n|)₊`.  On a range
`m, n ≥ A` the two are comparable, because `log` contracts:

```text
|log m − log n| ≤ |m − n| / A ,
```

by `log x ≤ x − 1` applied to `m/n`.  Hence, taking `δ = ℓ/A`,

```text
(ℓ − |m − n|)₊ ≤ A·(ℓ/A − |log m − log n|)₊ .
```

So every additive band is inside a logarithmic band of width `ℓ/A`, at the cost of the single
factor `A` — which is exactly the Jacobian of the change of variable and is what makes the two
formulations of Gallagher's lemma interchangeable on a dyadic range.
-/

noncomputable section

namespace RHTower.Sieve

open Finset

/-- One direction of the contraction. -/
theorem log_sub_le_div {A : ℕ} (hA : 1 ≤ A) {m n : ℕ} (hn : A ≤ n) (hnm : n ≤ m) :
    Real.log m - Real.log n ≤ ((m : ℝ) - n) / A := by
  have hA0 : (0 : ℝ) < A := by exact_mod_cast hA
  have hAn : (A : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := lt_of_lt_of_le hA0 hAn
  have hnmR : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast hnm
  have hm0 : (0 : ℝ) < m := lt_of_lt_of_le hn0 hnmR
  have hlog : Real.log ((m : ℝ) / n) ≤ (m : ℝ) / n - 1 :=
    Real.log_le_sub_one_of_pos (by positivity)
  rw [Real.log_div (ne_of_gt hm0) (ne_of_gt hn0)] at hlog
  have hstep : (m : ℝ) / n - 1 = ((m : ℝ) - n) / n := by field_simp
  rw [hstep] at hlog
  have hmn : (0 : ℝ) ≤ (m : ℝ) - n := by linarith
  have hdiv : ((m : ℝ) - n) / n ≤ ((m : ℝ) - n) / A :=
    div_le_div_of_nonneg_left hmn hA0 hAn
  linarith

/-- **The logarithm contracts on a range bounded below.** -/
theorem abs_log_sub_le {A : ℕ} (hA : 1 ≤ A) {m n : ℕ} (hm : A ≤ m) (hn : A ≤ n) :
    |Real.log m - Real.log n| ≤ |(m : ℝ) - (n : ℝ)| / A := by
  have hA0 : (0 : ℝ) < A := by exact_mod_cast hA
  rcases le_total n m with h | h
  · have hle := log_sub_le_div hA hn h
    have hmn : (n : ℝ) ≤ (m : ℝ) := by exact_mod_cast h
    have hlow : 0 ≤ Real.log m - Real.log n := by
      have hn0 : (0 : ℝ) < n := lt_of_lt_of_le hA0 (by exact_mod_cast hn)
      linarith [Real.log_le_log hn0 hmn]
    rw [abs_of_nonneg hlow, abs_of_nonneg (by linarith : (0 : ℝ) ≤ (m : ℝ) - n)]
    exact hle
  · have hle := log_sub_le_div hA hm h
    have hmn : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast h
    have hlow : 0 ≤ Real.log n - Real.log m := by
      have hm0 : (0 : ℝ) < m := lt_of_lt_of_le hA0 (by exact_mod_cast hm)
      linarith [Real.log_le_log hm0 hmn]
    rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith : (m : ℝ) - n ≤ 0)]
    have heq : -((m : ℝ) - (n : ℝ)) / (A : ℝ) = ((n : ℝ) - (m : ℝ)) / (A : ℝ) := by ring
    rw [heq]
    linarith [hle]

/-- **The additive band is inside the logarithmic band.** -/
theorem band_kernel_le_log_kernel {ℓ A m n : ℕ} (hA : 1 ≤ A) (hm : A ≤ m) (hn : A ≤ n) :
    max ((ℓ : ℝ) - |(m : ℝ) - (n : ℝ)|) 0
      ≤ (A : ℝ) * max ((ℓ : ℝ) / A - |Real.log m - Real.log n|) 0 := by
  have hA0 : (0 : ℝ) < A := by exact_mod_cast hA
  have hcontract := abs_log_sub_le hA hm hn
  rcases le_or_gt ((ℓ : ℝ)) (|(m : ℝ) - (n : ℝ)|) with h | h
  · rw [max_eq_right (by linarith)]
    have : (0 : ℝ) ≤ max ((ℓ : ℝ) / A - |Real.log m - Real.log n|) 0 := le_max_right _ _
    positivity
  · rw [max_eq_left (by linarith)]
    have hpos : ((ℓ : ℝ) - |(m : ℝ) - (n : ℝ)|) / A
        ≤ (ℓ : ℝ) / A - |Real.log m - Real.log n| := by
      rw [sub_div]
      linarith [hcontract]
    have hle : ((ℓ : ℝ) - |(m : ℝ) - (n : ℝ)|) / A
        ≤ max ((ℓ : ℝ) / A - |Real.log m - Real.log n|) 0 :=
      le_trans hpos (le_max_left _ _)
    have hmul := mul_le_mul_of_nonneg_left hle hA0.le
    rw [mul_div_cancel₀ _ (ne_of_gt hA0)] at hmul
    exact hmul

end RHTower.Sieve

end
