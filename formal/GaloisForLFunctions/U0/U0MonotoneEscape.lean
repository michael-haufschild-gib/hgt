/-
# Monotone escape above the fixed point of `t ↦ t² − B`

The real comparison dynamics behind the sharp-threshold window pass.  `xStar B` is the larger
fixed point of `g(t) = t² − B`; above it every orbit grows at least LINEARLY:

  `g^[n] t ≥ t + n·(t − xStar B)`,

because `g(t) − t = (t − xStar)(t + xStar − 2) + (t − xStar) ≥ t − xStar` once `xStar ≥ 1`.
Unboundedness then needs only `exists_nat_gt` — no geometric rate, no limit argument.  This is
what lets the far-field entry work arbitrarily close to the sharp threshold `‖b‖ = 2+√2`,
where the escape rate degenerates to `1`.

The sharp-threshold clearance: `xStar B < B − 1  ⟺  (B−2)² > 2  ⟸  B > 2+√2`
(`xStar_lt_of_sharp`), so a thin annulus around the unit circle clears the fixed point after
one quadratic step.
-/
import Mathlib.Analysis.SpecialFunctions.Sqrt

namespace U0MonotoneEscape

/-- The larger fixed point `(1+√(1+4B))/2` of `t ↦ t² − B`. -/
noncomputable def xStar (B : ℝ) : ℝ := (1 + Real.sqrt (1 + 4 * B)) / 2

/-- `xStar B` is a fixed point: `xStar² − xStar − B = 0`. -/
theorem xStar_fixed {B : ℝ} (hB : 0 ≤ B) : xStar B ^ (2 : ℕ) - xStar B - B = 0 := by
  have hs : Real.sqrt (1 + 4 * B) ^ (2 : ℕ) = 1 + 4 * B := Real.sq_sqrt (by linarith)
  rw [xStar]
  linear_combination hs / 4

/-- Above the escape threshold the fixed point exceeds `1`. -/
theorem one_lt_xStar {B : ℝ} (hB : 0 < B) : 1 < xStar B := by
  have h1 : (1 : ℝ) < Real.sqrt (1 + 4 * B) := by
    have := Real.sqrt_lt_sqrt (by norm_num : (0:ℝ) ≤ 1) (by linarith : (1:ℝ) < 1 + 4 * B)
    rwa [Real.sqrt_one] at this
  rw [xStar]
  linarith

/-- **Sharp-threshold clearance**: for `B > 2+√2` the unit circle clears the fixed point in one
quadratic step — `xStar B < B − 1`. -/
theorem xStar_lt_of_sharp {B : ℝ} (hB : 2 + Real.sqrt 2 < B) : xStar B < B - 1 := by
  have h2 : Real.sqrt 2 ^ (2 : ℕ) = 2 := Real.sq_sqrt (by norm_num)
  have hs2 : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hB3 : (3 : ℝ) < B := by nlinarith
  have hkey : Real.sqrt (1 + 4 * B) < 2 * B - 3 := by
    rw [Real.sqrt_lt' (by linarith)]
    nlinarith [sq_nonneg (B - 2 - Real.sqrt 2)]
  rw [xStar]
  linarith

/-- One step above the fixed point gains at least the initial clearance:
`t + (t − xStar) ≤ t² − B` for `t ≥ xStar`. -/
theorem step_ge {B t : ℝ} (hB : 0 < B) (ht : xStar B ≤ t) :
    t + (t - xStar B) ≤ t ^ (2 : ℕ) - B := by
  have hfix := xStar_fixed hB.le
  have h1 : (1 : ℝ) < xStar B := one_lt_xStar hB
  nlinarith [mul_nonneg (sub_nonneg.mpr ht) (show (0:ℝ) ≤ t + xStar B - 2 by linarith)]

/-- **Linear escape**: the orbit of `t ≥ xStar B` under `s ↦ s² − B` grows at least linearly in
the initial clearance — `t + n·(t − xStar B) ≤ g^[n] t`. -/
theorem iterate_linear_growth {B t : ℝ} (hB : 0 < B) (ht : xStar B ≤ t) (n : ℕ) :
    t + n * (t - xStar B) ≤ (fun s => s ^ (2 : ℕ) - B)^[n] t := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hδ : (0 : ℝ) ≤ t - xStar B := sub_nonneg.mpr ht
    have hu : xStar B ≤ (fun s => s ^ (2 : ℕ) - B)^[n] t := by
      have : (0 : ℝ) ≤ (n : ℝ) * (t - xStar B) := mul_nonneg (Nat.cast_nonneg n) hδ
      linarith
    have hstep := step_ge hB hu
    rw [Function.iterate_succ_apply']
    push_cast
    set u := (fun s => s ^ (2 : ℕ) - B)^[n] t with hudef
    have : u + (u - xStar B) ≤ u ^ (2 : ℕ) - B := hstep
    nlinarith [ih, hδ]

/-- **Unbounded escape** above the fixed point: the orbit exceeds every bound.  Replaces both
the geometric-rate argument and any limit argument near the sharp threshold. -/
theorem exists_iterate_gt {B t : ℝ} (hB : 0 < B) (ht : xStar B < t) (M : ℝ) :
    ∃ n : ℕ, M < (fun s => s ^ (2 : ℕ) - B)^[n] t := by
  have hδ : (0 : ℝ) < t - xStar B := sub_pos.mpr ht
  obtain ⟨n, hn⟩ := exists_nat_gt ((M - t) / (t - xStar B))
  refine ⟨n, lt_of_lt_of_le ?_ (iterate_linear_growth hB ht.le n)⟩
  have := (div_lt_iff₀ hδ).mp hn
  linarith

end U0MonotoneEscape
