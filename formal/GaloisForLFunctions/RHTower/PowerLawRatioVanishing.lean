import Mathlib

/-!
# The ratio of two power-law asymptotics with different exponents vanishes

If `f(c) ~ A c^a E(c)` and `g(c) ~ B c^b E(c)` with a common factor `E` and `a < b`, then

```text
f(c) / g(c)  →  0 .
```

The common factor cancels identically, so it is irrelevant what it is — in the application it is the
exponentially small `e^{−2c}` shared by consecutive leakage rates, and only the difference of the
polynomial exponents survives.

This is the shape in which a Fuchs-type asymptotic `1 − λ_n(c) ~ A_n c^{n+1/2} e^{−2c}` delivers the
gap slack: consecutive rates differ by one power of `c`, so their ratio is `O(1/c)`.
-/

noncomputable section

open Filter Topology

namespace GaloisForLFunctions.RHTower

/-- **Vanishing of a power-law ratio.**  Two quantities with the same asymptotic shape but different
polynomial exponents have vanishing ratio, whatever the shared factor. -/
theorem tendsto_div_of_rpow_asymptotic {a b A B : ℝ} (hab : a < b) (hA : A ≠ 0) (hB : B ≠ 0)
    {f g E : ℝ → ℝ} (hE : ∀ᶠ c in atTop, E c ≠ 0)
    (hf : Tendsto (fun c => f c / (A * c ^ a * E c)) atTop (𝓝 1))
    (hg : Tendsto (fun c => g c / (B * c ^ b * E c)) atTop (𝓝 1)) :
    Tendsto (fun c => f c / g c) atTop (𝓝 0) := by
  have hratio : Tendsto (fun c => (f c / (A * c ^ a * E c)) / (g c / (B * c ^ b * E c)))
      atTop (𝓝 1) := by
    have h := hf.div hg one_ne_zero
    simpa [Pi.div_def] using h
  have hpow : Tendsto (fun c : ℝ => (A / B) * c ^ (-(b - a))) atTop (𝓝 0) := by
    have h := (tendsto_rpow_neg_atTop (by linarith : (0 : ℝ) < b - a)).const_mul (A / B)
    simpa using h
  have hprod : Tendsto
      (fun c => ((f c / (A * c ^ a * E c)) / (g c / (B * c ^ b * E c)))
        * ((A / B) * c ^ (-(b - a)))) atTop (𝓝 0) := by
    have h := hratio.mul hpow
    simpa using h
  refine hprod.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ), hE] with c hc hEc
  have hca : (0 : ℝ) < c ^ a := Real.rpow_pos_of_pos hc a
  have hcb : (0 : ℝ) < c ^ b := Real.rpow_pos_of_pos hc b
  have hden1 : A * c ^ a * E c ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero hA (ne_of_gt hca)) hEc
  have hden2 : B * c ^ b * E c ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero hB (ne_of_gt hcb)) hEc
  have hsub : c ^ (-(b - a)) = c ^ a / c ^ b := by
    rw [neg_sub, Real.rpow_sub hc]
  rw [hsub]
  by_cases hg0 : g c = 0
  · rw [hg0]
    simp
  · field_simp

end GaloisForLFunctions.RHTower

end
