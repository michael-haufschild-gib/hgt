import GaloisForLFunctions.RHTower.Sieve.ZetaPartialSumTruncation

/-!
# A crude polynomial growth bound for `ζ`

Taking the truncation at `N = 1` collapses the head to `1` and leaves the two tail terms, so on the
half-plane `Re s ≥ 1/2`, away from the pole,

```text
‖ζ(s)‖ ≤ 2 + 2‖s‖.
```

That is far weaker than the logarithmic bound near the abscissa, but it is exactly what Landau's
lemma consumes: the bound enters only through `log M`, so a linear bound costs `O(log t)` — which is
the classical de la Vallée Poussin input.
-/

namespace RHTower.Sieve

open Complex

/-- The truncation at `N = 1` has head `1`. -/
theorem sum_Icc_one_one_cpow (w : ℂ) :
    ∑ k ∈ Finset.Icc (1 : ℕ) 1, ((k : ℝ) : ℂ) ^ (-w) = 1 := by
  simp

/-- **Crude growth bound.**  On `Re s ≥ 1/2` at height at least `2`, `ζ` grows at most linearly. -/
theorem norm_riemannZeta_le_crude {w : ℂ} (hre : 1 / 2 ≤ w.re) (him : 2 ≤ |w.im|) :
    ‖riemannZeta w‖ ≤ 2 + 2 * ‖w‖ := by
  have hw0 : 0 < w.re := by linarith
  have hsub : ‖w - 1‖ ≥ 2 := by
    have h1 : |(w - 1).im| ≤ ‖w - 1‖ := Complex.abs_im_le_norm _
    have h2 : (w - 1).im = w.im := by simp
    rw [h2] at h1
    linarith
  have hwne1 : w ≠ 1 := by
    intro hcon
    rw [hcon] at hsub
    simp at hsub
    linarith
  have hmain := norm_riemannZeta_le_partialSum hw0 hwne1 (N := 1) le_rfl
  rw [sum_Icc_one_one_cpow] at hmain
  have hone1 : ((1 : ℕ) : ℝ) ^ (1 - w.re) = 1 := by
    norm_num
  have hone2 : ((1 : ℕ) : ℝ) ^ (-w.re) = 1 := by
    norm_num
  rw [hone1, hone2] at hmain
  have hsubpos : (0 : ℝ) < ‖w - 1‖ := by linarith
  have hinv : 1 / ‖w - 1‖ ≤ 1 / 2 := by
    rw [div_le_div_iff₀ hsubpos (by norm_num)]
    linarith
  have hquot : ‖w‖ * (1 / w.re) ≤ 2 * ‖w‖ := by
    have h1 : 1 / w.re ≤ 2 := by
      rw [div_le_iff₀ hw0]
      linarith
    nlinarith [norm_nonneg w]
  simp only [norm_one] at hmain
  linarith

end RHTower.Sieve
