import Mathlib

/-!
# Vanishing ratios from two-sided ladders, without sharp constants

Comparing two quantities that share an exponentially small factor and differ by a power needs no
asymptotic equality: an upper bound on the numerator and a lower bound on the denominator suffice,
and the shared factor cancels identically.

```text
0 ≤ f(c) ≤ A c^a E(c) ,     B c^b E(c) ≤ g(c) ,     a < b ,   A, B > 0
    ⟹    f(c) / g(c) → 0 .
```

This is the form in which a *two-sided ladder* replaces a sharp asymptotic constant.  For the
leakage rates of a fixed prolate mode, where `E(c) = e^{-2c}` and consecutive exponents differ by
one, it gives `d_k / d_{k+1} = O(1/c) → 0` from the ladder alone — the sharp constant `A_n` of the
Fuchs asymptotic is never needed for the ratio.
-/

noncomputable section

open Filter Topology

namespace GaloisForLFunctions.RHTower

/-- **A vanishing ratio from an upper and a lower power bound sharing a common factor.** -/
theorem tendsto_div_of_rpow_twoSided {f g E : ℝ → ℝ} {A B a b : ℝ}
    (hA : 0 < A) (hB : 0 < B) (hab : a < b)
    (hf : ∀ᶠ c : ℝ in atTop, 0 ≤ f c ∧ f c ≤ A * c ^ a * E c)
    (hg : ∀ᶠ c : ℝ in atTop, B * c ^ b * E c ≤ g c)
    (hE : ∀ᶠ c : ℝ in atTop, 0 < E c) :
    Tendsto (fun c : ℝ => f c / g c) atTop (𝓝 0) := by
  have hmaj : Tendsto (fun c : ℝ => (A / B) * c ^ (-(b - a))) atTop (𝓝 0) := by
    have h := (tendsto_rpow_neg_atTop (show (0 : ℝ) < b - a by linarith)).const_mul (A / B)
    simpa using h
  refine squeeze_zero' ?_ ?_ hmaj
  · filter_upwards [hf, hg, hE, eventually_gt_atTop (0 : ℝ)] with c hfc hgc hEc hcpos
    have hden : 0 < B * c ^ b * E c := by positivity
    exact div_nonneg hfc.1 (le_trans hden.le hgc)
  · filter_upwards [hf, hg, hE, eventually_gt_atTop (0 : ℝ)] with c hfc hgc hEc hcpos
    have hden : 0 < B * c ^ b * E c := by positivity
    have hnum : (0 : ℝ) ≤ A * c ^ a * E c := by positivity
    have hstep : f c / g c ≤ (A * c ^ a * E c) / (B * c ^ b * E c) := by
      gcongr
      exact hfc.2
    refine le_trans hstep (le_of_eq ?_)
    have hEne : E c ≠ 0 := ne_of_gt hEc
    have hpow : c ^ a / c ^ b = c ^ (-(b - a)) := by
      rw [← Real.rpow_sub hcpos]
      congr 1
      ring
    field_simp
    rw [← hpow]
    field_simp

/-- **Consecutive leakage rates of a fixed mode.**  With the common exponential factor `e^{-2c}` and
exponents differing by one, the ratio vanishes at rate `1/c`. -/
theorem tendsto_consecutive_leakage_ratio {f g : ℝ → ℝ} {A B : ℝ} {k : ℕ}
    (hA : 0 < A) (hB : 0 < B)
    (hf : ∀ᶠ c : ℝ in atTop,
      0 ≤ f c ∧ f c ≤ A * c ^ ((k : ℝ) + 1 / 2) * Real.exp (-2 * c))
    (hg : ∀ᶠ c : ℝ in atTop,
      B * c ^ ((k : ℝ) + 3 / 2) * Real.exp (-2 * c) ≤ g c) :
    Tendsto (fun c : ℝ => f c / g c) atTop (𝓝 0) := by
  refine tendsto_div_of_rpow_twoSided hA hB (by linarith) hf hg ?_
  filter_upwards with c
  exact Real.exp_pos _

end GaloisForLFunctions.RHTower

end
