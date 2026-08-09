import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Pattern caps for finite-amplifier positivity engines

Three exact algebraic facts behind the finite-amplifier barrier.

1. **Two-point cap.**  A pattern `a + b·χ` nonnegative at both points of the two-element
   character set `χ = ±1` has detection coefficient at most its pole coefficient: `b ≤ a`.
   This is the algebraic core of the barrier for one real character: the detection/pole ratio
   on `ℤ/2` is capped at `1`, below the strict threshold an exclusion needs.

2. **Circle witness.**  On the circle the threshold is beatable at degree two:
   `3 + 4cos θ + cos 2θ = 2(1 + cos θ)² ≥ 0`, a nonnegative pattern with detection/pole ratio
   `4/3 > 1` — the classical positivity pattern.

3. **Width cap.**  The one-inequality engine: if the exclusion inequality
   `c·m/(a + w) > c₁/a + K` holds with all quantities positive, then
   `w < c·m/(c₁/a + K) − a`.  Instantiated at `w = δ·𝔏` this says any derivable
   zero-exclusion width obeys `δ·𝔏 < C(pattern data)` — the `1/𝔏` shape is forced.

All statements are universally quantified ordered-field algebra; no analytic input enters.
-/

namespace HTGeometry

/-- **Two-point pattern cap.**  Nonnegativity of `a + b·χ` at both `χ = 1` and `χ = -1`
forces the detection coefficient below the pole coefficient in absolute value. -/
theorem twoPoint_pattern_cap {a b : ℝ} (h₁ : 0 ≤ a + b) (h₂ : 0 ≤ a - b) : |b| ≤ a :=
  abs_le.mpr ⟨by linarith, by linarith⟩

/-- The two-point cap is tight: the extremal pattern `a = b` is admissible. -/
theorem twoPoint_pattern_cap_tight (a : ℝ) (ha : 0 ≤ a) :
    0 ≤ a + a ∧ 0 ≤ a - a ∧ ¬ a < a := by
  refine ⟨by linarith, by linarith, lt_irrefl a⟩

/-- **Circle pattern witness.**  The classical degree-two pattern is pointwise nonnegative:
`3 + 4cos θ + cos 2θ = 2(1 + cos θ)²`. -/
theorem circle_pattern_nonneg (θ : ℝ) :
    0 ≤ 3 + 4 * Real.cos θ + Real.cos (2 * θ) := by
  have h := Real.cos_two_mul θ
  nlinarith [sq_nonneg (1 + Real.cos θ), Real.neg_one_le_cos θ, Real.cos_le_one θ]

/-- The circle witness exceeds the two-point threshold: its detection/pole ratio is `4/3 > 1`. -/
theorem circle_pattern_ratio_exceeds_one : (1 : ℝ) < 4 / 3 := by norm_num

/-- **Width cap.**  From the exclusion inequality, the width is bounded by pattern data alone:
if `c·m/(a + w) > c₁/a + K` with `a, c₁, m, c > 0`, `K ≥ 0`, `w ≥ 0`, then
`w < c·m/(c₁/a + K) − a`.  At `w = δ·𝔏` this forces the `1/𝔏` shape of every derivable
exclusion. -/
theorem width_cap {a w c c₁ m K : ℝ} (ha : 0 < a) (hw : 0 ≤ w)
    (hc₁ : 0 < c₁) (hK : 0 ≤ K)
    (hexcl : c₁ / a + K < c * m / (a + w)) :
    w < c * m / (c₁ / a + K) - a := by
  have haw : 0 < a + w := by linarith
  have hden : 0 < c₁ / a + K := by positivity
  have h₁ : (c₁ / a + K) * (a + w) < c * m := (lt_div_iff₀ haw).mp hexcl
  have h₂ : a + w < c * m / (c₁ / a + K) := by
    rw [lt_div_iff₀ hden]
    calc (a + w) * (c₁ / a + K) = (c₁ / a + K) * (a + w) := by ring
    _ < c * m := h₁
  linarith

end HTGeometry
