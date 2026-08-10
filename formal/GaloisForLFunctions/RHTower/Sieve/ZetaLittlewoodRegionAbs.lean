import GaloisForLFunctions.RHTower.Sieve.ZetaLittlewoodRegion

/-!
# Littlewood's region in the classical variables

`exists_littlewood_zero_free_region` is stated in the scale `wideScale γ = log(γ/2π)` of the
derivative-test chain and only for positive heights.  Replacing that scale by `log|γ|` costs a
factor two in the constant — `wideScale γ ≥ (log γ)/2` and `log (wideScale γ) ≥ (log log γ)/2` once
`log γ ≥ 100` — and the reflection `ζ(conj s) = conj (ζ s)` supplies the negative heights.

```text
∃ c > 0, ∃ T, ∀ β γ,  T ≤ |γ|,  β ≤ 1,  1 - c·log log|γ| / log|γ| < β  ⟹  ζ(β + iγ) ≠ 0 .
```

This is one logarithm better than `exists_zero_free_region`, whose width is `c/log|γ|`.
-/

namespace RHTower.Sieve

open Complex

/-- Zeros of `ζ` come in conjugate pairs, so a zero-free statement at height `γ` gives one at
height `-γ`. -/
theorem riemannZeta_ne_zero_neg_im {β γ : ℝ}
    (h : riemannZeta ((β : ℂ) + (γ : ℂ) * Complex.I) ≠ 0) :
    riemannZeta ((β : ℂ) + ((-γ : ℝ) : ℂ) * Complex.I) ≠ 0 := by
  intro hcon
  refine h ?_
  have hc : ((β : ℂ) + (γ : ℂ) * Complex.I)
      = (starRingEnd ℂ) ((β : ℂ) + ((-γ : ℝ) : ℂ) * Complex.I) := by
    apply Complex.ext <;> simp
  rw [hc, riemannZeta_conj, hcon, map_zero]

set_option maxHeartbeats 800000 in
/-- **Littlewood's zero-free region.**  The width is `c·log log|γ| / log|γ|`. -/
theorem exists_littlewood_zero_free_region_abs :
    ∃ c T : ℝ, 0 < c ∧ 3 ≤ T ∧
      ∀ β γ : ℝ, T ≤ |γ| → β ≤ 1 →
        1 - c * Real.log (Real.log |γ|) / Real.log |γ| < β →
        riemannZeta ((β : ℂ) + (γ : ℂ) * Complex.I) ≠ 0 := by
  obtain ⟨T₀, hT₀, hreg⟩ := exists_littlewood_zero_free_region
  have hπ := Real.pi_pos
  have hπd : (3.14 : ℝ) < Real.pi := Real.pi_gt_d2
  have hπu : Real.pi < 3.15 := Real.pi_lt_d2
  have hlog2 : Real.log 2 ≤ 7 / 10 := by
    have := Real.log_two_lt_d9; linarith
  have hlog2pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2π : Real.log (2 * Real.pi) ≤ 21 / 10 := by
    have h8 : Real.log (2 * Real.pi) ≤ Real.log 8 :=
      Real.log_le_log (by positivity) (by linarith)
    have h8eq : Real.log ((8 : ℝ)) = 3 * Real.log 2 := by
      rw [show (8 : ℝ) = 2 ^ (3 : ℕ) by norm_num, Real.log_pow]; norm_num
    rw [h8eq] at h8
    linarith
  refine ⟨1 / 64000, max T₀ (Real.exp 100), by norm_num, le_trans hT₀ (le_max_left _ _), ?_⟩
  intro β γ hγT hβ1 hβc
  -- the positive-height case
  have key : ∀ g : ℝ, max T₀ (Real.exp 100) ≤ g →
      1 - (1 / 64000) * Real.log (Real.log g) / Real.log g < β →
      riemannZeta ((β : ℂ) + (g : ℂ) * Complex.I) ≠ 0 := by
    intro g hg hb
    have hgT₀ : T₀ ≤ g := le_trans (le_max_left _ _) hg
    have hgexp : Real.exp 100 ≤ g := le_trans (le_max_right _ _) hg
    have hg0 : (0 : ℝ) < g := lt_of_lt_of_le (Real.exp_pos 100) hgexp
    set X : ℝ := Real.log g with hXdef
    have hX100 : (100 : ℝ) ≤ X := by
      rw [hXdef, Real.le_log_iff_exp_le hg0]
      exact hgexp
    have hXpos : (0 : ℝ) < X := by linarith
    -- the two scales
    have hW : wideScale g = X - Real.log (2 * Real.pi) := by
      rw [wideScale, Real.log_div (ne_of_gt hg0) (by positivity), hXdef]
    have hWlow : X / 2 ≤ wideScale g := by rw [hW]; linarith
    have hWhigh : wideScale g ≤ X := by
      rw [hW]
      have : (0 : ℝ) ≤ Real.log (2 * Real.pi) :=
        Real.log_nonneg (by linarith)
      linarith
    have hWpos : (0 : ℝ) < wideScale g := by linarith
    -- the two logarithms
    have hlogX : (2 : ℝ) ≤ Real.log X := by
      have h64 : Real.log ((64 : ℝ)) ≤ Real.log X :=
        Real.log_le_log (by norm_num) (by linarith)
      have h64eq : Real.log ((64 : ℝ)) = 6 * Real.log 2 := by
        rw [show (64 : ℝ) = 2 ^ (6 : ℕ) by norm_num, Real.log_pow]; norm_num
      rw [h64eq] at h64
      have := Real.log_two_gt_d9
      linarith
    have hlogW : Real.log X / 2 ≤ Real.log (wideScale g) := by
      have h1 : Real.log (X / 2) ≤ Real.log (wideScale g) :=
        Real.log_le_log (by positivity) hWlow
      have h2 : Real.log (X / 2) = Real.log X - Real.log 2 :=
        Real.log_div (ne_of_gt hXpos) (by norm_num)
      rw [h2] at h1
      linarith
    -- the width comparison
    have hwidth : (1 / 64000 : ℝ) * Real.log X / X
        ≤ Real.log (wideScale g) / (32000 * wideScale g) := by
      rw [div_le_div_iff₀ hXpos (by positivity)]
      have hA : (0 : ℝ) ≤ Real.log X := by linarith
      nlinarith [hlogW, hWhigh, hWpos, hXpos, hA]
    refine hreg β g hgT₀ hβ1 ?_
    exact lt_of_le_of_lt (sub_le_sub_left hwidth 1) hb
  rcases le_or_gt 0 γ with hγ | hγ
  · have habs : |γ| = γ := abs_of_nonneg hγ
    rw [habs] at hγT hβc
    exact key γ hγT hβc
  · have habs : |γ| = -γ := abs_of_neg hγ
    rw [habs] at hγT hβc
    have h := key (-γ) hγT hβc
    have hneg : ((-(-γ) : ℝ) : ℂ) = (γ : ℂ) := by push_cast; ring
    have := riemannZeta_ne_zero_neg_im (β := β) (γ := -γ) h
    rwa [hneg] at this

end RHTower.Sieve
