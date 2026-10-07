import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Exact compensation on a two-prime divisor square

The real quadratic form on `(1,p,q,pq)` can attain the star budget
`sqrt (a^2+b^2)` by a unique choice of the composite entry. This classical
Schur-complement calculation explains why adding this one divisor alone
cannot sharpen the primitive-set bound. It constructs no full Weil source.
-/

noncomputable section

namespace RHTower.WeilSingularArithmetic

def divisorSquareForm (a b c x₀ xₚ xq xₚq : ℝ) : ℝ :=
  2 * a * (x₀ * xₚ + xq * xₚq) + 2 * b * (x₀ * xq + xₚ * xₚq) +
    2 * c * x₀ * xₚq

def divisorSquareMass (x₀ xₚ xq xₚq : ℝ) : ℝ :=
  x₀ ^ 2 + xₚ ^ 2 + xq ^ 2 + xₚq ^ 2

/-- The full signed remainder before choosing the sharp composite entry. -/
theorem divisorSquare_defect_identity (u a b c x₀ xₚ xq xₚq : ℝ) :
    u * (u * divisorSquareMass x₀ xₚ xq xₚq - divisorSquareForm a b c x₀ xₚ xq xₚq) =
      (u * xₚ - a * x₀ - b * xₚq) ^ 2 + (u * xq - b * x₀ - a * xₚq) ^ 2 +
        (u ^ 2 - a ^ 2 - b ^ 2) * (x₀ ^ 2 + xₚq ^ 2) -
        2 * (u * c + 2 * a * b) * x₀ * xₚq := by
  unfold divisorSquareMass divisorSquareForm
  ring

/-- The star budget holds for the entire real divisor square exactly at
this composite coefficient, including the degenerate zero case. -/
theorem divisorSquare_ceiling_iff (a b c : ℝ) :
    (∀ x₀ xₚ xq xₚq : ℝ, divisorSquareForm a b c x₀ xₚ xq xₚq ≤
      Real.sqrt (a ^ 2 + b ^ 2) * divisorSquareMass x₀ xₚ xq xₚq) ↔
        c = -2 * a * b / Real.sqrt (a ^ 2 + b ^ 2) := by
  let u := Real.sqrt (a ^ 2 + b ^ 2)
  have hu0 : 0 ≤ u := by positivity
  have hu2 : u ^ 2 = a ^ 2 + b ^ 2 := Real.sq_sqrt (by positivity)
  change (∀ x₀ xₚ xq xₚq : ℝ, divisorSquareForm a b c x₀ xₚ xq xₚq ≤
    u * divisorSquareMass x₀ xₚ xq xₚq) ↔ c = -2 * a * b / u
  rcases eq_or_lt_of_le hu0 with hu | hu
  · have ha : a = 0 := by nlinarith [sq_nonneg b]
    have hb : b = 0 := by nlinarith [sq_nonneg a]
    subst a b
    constructor
    · intro h
      have h₁ := h 1 0 0 1
      have h₂ := h 1 0 0 (-1)
      norm_num [divisorSquareForm, hu.symm] at h₁ h₂
      simpa using (show c = 0 by linarith)
    · rintro rfl
      simp [divisorSquareForm, hu.symm]
  · constructor
    · intro h
      let v := 2 * a * b + c * u
      have htest := h u a b (v / u)
      have hdef :
          u * divisorSquareMass u a b (v / u) -
            divisorSquareForm a b c u a b (v / u) = -(v ^ 2 / u) := by
        unfold divisorSquareMass divisorSquareForm
        dsimp [v]
        field_simp
        nlinarith [hu2]
      have hn : 0 ≤ -(v ^ 2 / u) := hdef ▸ sub_nonneg.mpr htest
      have hv : v = 0 := by
        have hpos : 0 ≤ v ^ 2 / u := div_nonneg (sq_nonneg v) hu.le
        have hz : v ^ 2 / u = 0 := by linarith
        have hz' : v ^ 2 = 0 := (div_eq_zero_iff).mp hz |>.resolve_right hu.ne'
        nlinarith
      apply (eq_div_iff hu.ne').mpr
      dsimp [v] at hv
      linarith
    · intro hc x₀ xₚ xq xₚq
      have huc : u * c + 2 * a * b = 0 := by
        rw [hc]
        field_simp
        ring
      have hid := divisorSquare_defect_identity u a b c x₀ xₚ xq xₚq
      rw [hu2] at hid
      have hs : a ^ 2 + b ^ 2 - a ^ 2 - b ^ 2 = 0 := by ring
      rw [hs, huc] at hid
      have hd : 0 ≤ u * (u * divisorSquareMass x₀ xₚ xq xₚq -
          divisorSquareForm a b c x₀ xₚ xq xₚq) := by
        rw [hid]
        nlinarith [sq_nonneg (u * xₚ - a * x₀ - b * xₚq),
          sq_nonneg (u * xq - b * x₀ - a * xₚq)]
      nlinarith

/-- The star vector attains the threshold for every composite coefficient. -/
theorem divisorSquare_star_equality (a b c : ℝ) :
    divisorSquareForm a b c (Real.sqrt (a ^ 2 + b ^ 2)) a b 0 =
      Real.sqrt (a ^ 2 + b ^ 2) *
        divisorSquareMass (Real.sqrt (a ^ 2 + b ^ 2)) a b 0 := by
  have hu := Real.sq_sqrt (show 0 ≤ a ^ 2 + b ^ 2 by positivity)
  unfold divisorSquareMass divisorSquareForm
  rw [hu]
  ring

end RHTower.WeilSingularArithmetic
