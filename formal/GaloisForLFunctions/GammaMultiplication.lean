import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup

/-!
# Gauss multiplication for the Gamma function (up to constant)

The signed archimedean Gamma orbit-charge card reduces a scaled factor `Γ(λ s + μ)` to common-scale
factors `Γ((s + a)/H)` via Gauss multiplication `(6)`.  mathlib has only the `n = 2` doubling case;
the general finite-`n` formula is a stated mathlib TODO.  This file proves the general real formula
*up to its multiplicative constant* — which is all the orbit-charge reduction uses — by the
Bohr–Mollerup characterization: the product `∏_{k<n} Γ((s+k)/n) · n^s`, normalized to value `1` at
`s = 1`, satisfies the Gamma functional equation and log-convexity, hence equals `Γ`.
-/

open Real Finset
open scoped BigOperators

namespace GaloisForLFunctions

/-- The Gauss-multiplication product `∏_{k<n} Γ((s+k)/n) · n^s`.  Its normalization to value `1` at
`s = 1` is shown below to equal `Γ`. -/
noncomputable def multGammaProd (n : ℕ) (s : ℝ) : ℝ :=
  (∏ k ∈ Finset.range n, Real.Gamma ((s + k) / n)) * (n : ℝ) ^ s

/-- Each common-scale argument `(s+k)/n` is positive when `s > 0`. -/
theorem arg_pos {n : ℕ} (hn : 0 < n) {s : ℝ} (hs : 0 < s) (k : ℕ) : 0 < (s + k) / n := by
  apply div_pos
  · positivity
  · exact_mod_cast hn

/-- Positivity of the Gauss product on `s > 0`. -/
theorem multGammaProd_pos {n : ℕ} (hn : 0 < n) {s : ℝ} (hs : 0 < s) : 0 < multGammaProd n s := by
  apply mul_pos
  · apply Finset.prod_pos
    intro k _
    exact Real.Gamma_pos_of_pos (arg_pos hn hs k)
  · exact Real.rpow_pos_of_pos (by exact_mod_cast hn) s

/-- **Functional equation of the Gauss product:** `P(s+1) = s · P(s)` for `s > 0`.  The product
telescopes (`Finset.prod_range_succ`/`prod_range_succ'` peel the endpoints `Γ(s/n)` and
`Γ(s/n + 1) = (s/n)Γ(s/n)`), and the extra `n` from `n^{s+1}` cancels the `1/n`. -/
theorem multGammaProd_functional {n : ℕ} (hn : 0 < n) {s : ℝ} (hs : 0 < s) :
    multGammaProd n (s + 1) = s * multGammaProd n s := by
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  set F : ℕ → ℝ := fun j => Real.Gamma ((s + j) / n) with hF
  -- telescoping: (∏_{k<n} F(k+1)) * F 0 = (∏_{k<n} F k) * F n
  have htel : (∏ k ∈ Finset.range n, F (k + 1)) * F 0
      = (∏ k ∈ Finset.range n, F k) * F n := by
    rw [← Finset.prod_range_succ, ← Finset.prod_range_succ' F n]
  have hF0 : 0 < F 0 := Real.Gamma_pos_of_pos (by simpa using arg_pos hn hs 0)
  -- F n = (s/n) * F 0
  have hFn : F n = (s / n) * F 0 := by
    have : (s + (n : ℝ)) / n = s / n + 1 := by field_simp
    simp only [hF, Nat.cast_zero, add_zero]
    rw [this, Real.Gamma_add_one (by positivity)]
  -- so ∏ F(k+1) = (s/n) * ∏ F k
  have hprod : (∏ k ∈ Finset.range n, F (k + 1)) = (s / n) * (∏ k ∈ Finset.range n, F k) := by
    have h2 : (∏ k ∈ Finset.range n, F (k + 1)) * F 0
        = ((s / n) * (∏ k ∈ Finset.range n, F k)) * F 0 := by
      rw [htel, hFn]; ring
    exact mul_right_cancel₀ (ne_of_gt hF0) h2
  -- reindex the (s+1) product to F(k+1)
  have hreindex : (∏ k ∈ Finset.range n, Real.Gamma ((s + 1 + k) / n))
      = (∏ k ∈ Finset.range n, F (k + 1)) := by
    apply Finset.prod_congr rfl
    intro k _
    simp only [hF]
    congr 1
    push_cast
    ring
  rw [multGammaProd, multGammaProd, hreindex, hprod,
    Real.rpow_add hnR, Real.rpow_one]
  simp only [hF]
  have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hnR
  field_simp

end GaloisForLFunctions
