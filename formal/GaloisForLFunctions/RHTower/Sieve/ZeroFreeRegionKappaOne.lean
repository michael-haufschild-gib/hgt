import GaloisForLFunctions.RHTower.Sieve.DeLaValleePoussinInequality
import GaloisForLFunctions.HTGeometry.LogBelowLinear

/-!
# A zero-free region of exponent one

Choosing `δ = c₀/log|γ|` in the de la Vallée Poussin inequality turns it into

```text
(4/(c₀ + c) - 3/c₀ - 400)·log|γ|  <  480 √(log|γ|) + K,
```

with `K` an absolute constant, once a zero is assumed at distance less than `c/log|γ|` from the
abscissa.  With `c₀ = 1/500` and `c = 1/10000` the bracket is `100/21 > 0`, and the right side is
`O(√(log|γ|))`, so the inequality fails for large `|γ|`: there is no such zero.

The only inputs are `dlvp_inequality` and the elementary bound `log x ≤ 2√x`.
-/

namespace RHTower.Sieve

open Complex

/-- `log x ≤ 2 √x`. -/
theorem log_le_two_sqrt {x : ℝ} (hx : 0 < x) : Real.log x ≤ 2 * Real.sqrt x :=
  GaloisForLFunctions.HTGeometry.log_le_two_mul_sqrt hx

/-- The quadratic threshold that rules the inequality out. -/
theorem quad_pos {u K : ℝ} (hu : 202 ≤ u) (huK : K + 1 ≤ u) :
    480 * u + K < 100 / 21 * u ^ 2 := by
  have hu0 : (0 : ℝ) < u := by linarith
  have h1 : 480 * u < 50 / 21 * u ^ 2 := by nlinarith
  have h2 : K < 50 / 21 * u ^ 2 := by nlinarith
  nlinarith [h1, h2]

/-- **A zero-free region of exponent one for `ζ`, with the constant exposed.**  Only the threshold
is existential; the width is `1/(10000 log|γ|)`. -/
theorem exists_zero_free_region_explicit :
    ∃ T : ℝ, 3 ≤ T ∧
      ∀ β γ : ℝ, T ≤ |γ| → β ≤ 1 → 1 - 1 / 10000 / Real.log |γ| < β →
        riemannZeta ((β : ℂ) + (γ : ℂ) * Complex.I) ≠ 0 := by
  obtain ⟨A, hA⟩ := exists_pole_bound
  set K : ℝ := max (3 * A + 400 * Real.log 15 + 240 * Real.log 501) 0 with hKdef
  have hK0 : 0 ≤ K := le_max_right _ _
  set u₀ : ℝ := max 202 (K + 1) with hu₀def
  have hu₀202 : (202 : ℝ) ≤ u₀ := le_max_left _ _
  have hu₀K : K + 1 ≤ u₀ := le_max_right _ _
  have hu₀0 : (0 : ℝ) < u₀ := by linarith
  set L₀ : ℝ := u₀ ^ 2 with hL₀def
  refine ⟨max 3 (Real.exp L₀), le_max_left _ _, ?_⟩
  intro β γ hγT hβ1 hβc hzero
  have hγ3 : (3 : ℝ) ≤ |γ| := le_trans (le_max_left _ _) hγT
  have hγpos : (0 : ℝ) < |γ| := by linarith
  set L : ℝ := Real.log |γ| with hLdef
  -- `L` is past the threshold
  have hL₀L : L₀ ≤ L := by
    rw [hLdef, Real.le_log_iff_exp_le hγpos]
    exact le_trans (le_max_right _ _) hγT
  have hL₀big : (40804 : ℝ) ≤ L₀ := by
    rw [hL₀def]
    nlinarith [hu₀202]
  have hLbig : (40804 : ℝ) ≤ L := by linarith
  have hLpos : (0 : ℝ) < L := by linarith
  -- the parameters
  set δ : ℝ := (1 / 500) / L with hδdef
  have hδ0 : 0 < δ := by rw [hδdef]; positivity
  have hδ16 : δ ≤ 1 / 16 := by
    rw [hδdef, div_le_div_iff₀ hLpos (by norm_num)]
    linarith
  have hβdist : 1 - β < (1 / 10000) / L := by linarith [hβc]
  have hβ16 : 1 - β ≤ 1 / 16 := by
    have : (1 / 10000 : ℝ) / L ≤ 1 / 16 := by
      rw [div_le_div_iff₀ hLpos (by norm_num)]
      linarith
    linarith
  -- the de la Vallée Poussin inequality
  have hdlvp := dlvp_inequality hA hγ3 hδ0 hδ16 hβ16 hβ1 hzero
  -- the left side
  have hgap : 0 < 1 + δ - β := by linarith
  have hgapsmall : 1 + δ - β < (1 / 500 + 1 / 10000) / L := by
    rw [hδdef] at *
    have : (1 / 500 : ℝ) / L + (1 / 10000) / L = (1 / 500 + 1 / 10000) / L := by ring
    linarith [hβdist]
  have hLHS : (40000 / 21 : ℝ) * L < 4 / (1 + δ - β) := by
    have hpos : (0 : ℝ) < (1 / 500 + 1 / 10000) / L := by positivity
    have hstep : 4 / ((1 / 500 + 1 / 10000) / L) < 4 / (1 + δ - β) :=
      div_lt_div_of_pos_left (by norm_num) hgap hgapsmall
    have heq : 4 / ((1 / 500 + 1 / 10000 : ℝ) / L) = (40000 / 21) * L := by
      field_simp
      ring
    rw [heq] at hstep
    exact hstep
  -- the right side
  have hlogγ : Real.log (7 + 8 * |γ|) ≤ Real.log 15 + L := by
    have h1 : (7 : ℝ) + 8 * |γ| ≤ 15 * |γ| := by linarith
    have h2 : Real.log (7 + 8 * |γ|) ≤ Real.log (15 * |γ|) :=
      Real.log_le_log (by linarith) h1
    rw [Real.log_mul (by norm_num) (ne_of_gt hγpos)] at h2
    rw [hLdef]
    exact h2
  have hinvδ : 1 + 1 / δ = 1 + 500 * L := by
    rw [hδdef]
    field_simp
  have hlogδ : Real.log (1 + 1 / δ) ≤ Real.log 501 + 2 * Real.sqrt L := by
    rw [hinvδ]
    have h1 : (1 : ℝ) + 500 * L ≤ 501 * L := by linarith
    have h2 : Real.log (1 + 500 * L) ≤ Real.log (501 * L) :=
      Real.log_le_log (by linarith) h1
    rw [Real.log_mul (by norm_num) (ne_of_gt hLpos)] at h2
    have h3 : Real.log L ≤ 2 * Real.sqrt L := log_le_two_sqrt hLpos
    linarith
  have hRHS : 3 / δ + 3 * A
      + 320 * (5 / 4 * Real.log (7 + 8 * |γ|) + 3 / 4 * Real.log (1 + 1 / δ))
      ≤ 1900 * L + 480 * Real.sqrt L + K := by
    have hthree : (3 : ℝ) / δ = 1500 * L := by
      rw [hδdef]
      field_simp
      ring
    have hKge : 3 * A + 400 * Real.log 15 + 240 * Real.log 501 ≤ K := le_max_left _ _
    rw [hthree]
    linarith [hlogγ, hlogδ, hKge]
  -- the contradiction
  have hu : u₀ ≤ Real.sqrt L := by
    have h1 : Real.sqrt L₀ ≤ Real.sqrt L := Real.sqrt_le_sqrt hL₀L
    rw [hL₀def, Real.sqrt_sq hu₀0.le] at h1
    exact h1
  have hsq : Real.sqrt L ^ 2 = L := Real.sq_sqrt hLpos.le
  have hquad := quad_pos (u := Real.sqrt L) (K := K) (by linarith) (by linarith)
  rw [hsq] at hquad
  linarith [hLHS, hdlvp, hRHS, hquad]

/-- **A zero-free region of exponent one for `ζ`.** -/
theorem exists_zero_free_region :
    ∃ c T : ℝ, 0 < c ∧ 3 ≤ T ∧
      ∀ β γ : ℝ, T ≤ |γ| → β ≤ 1 → 1 - c / Real.log |γ| < β →
        riemannZeta ((β : ℂ) + (γ : ℂ) * Complex.I) ≠ 0 := by
  obtain ⟨T, hT, h⟩ := exists_zero_free_region_explicit
  exact ⟨1 / 10000, T, by norm_num, hT, h⟩

end RHTower.Sieve
