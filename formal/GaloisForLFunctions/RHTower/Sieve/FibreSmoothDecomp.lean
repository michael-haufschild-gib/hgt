import GaloisForLFunctions.RHTower.Sieve.FibreSmoothQuasiConcave

/-!
# The smooth model as a difference of three pieces

`min B D = B − (B−D)⁺` and `max A C = A + (C−A)⁺`, so the length of the intersection splits as

```text
min B D − max A C = (B − A) − (B − D)⁺ − (C − A)⁺ ,
```

that is, `kernelDiff` minus the overshoot of the upper endpoint above `2√x` minus the shortfall of
the lower endpoint below `√x`.  Each of the three has total variation `O(h)` on the support:
`kernelDiff` because it is unimodal with range `O(h)` there, the overshoot because it decreases from
`≈ 2h` to `0`, the shortfall because it increases from `0` to `≈ h`.

Unlike the four-term `min`, this decomposition also behaves well *uniformly in the shift*: the
overshoot depends on the shift only through `i + k`, and `kernelDiff`'s increment is monotone in the
shift.
-/

noncomputable section

namespace RHTower.Sieve

open Finset

/-- The overshoot of the upper endpoint above the dyadic ceiling. -/
def fibreOver (x h : ℝ) (k i : ℕ) : ℝ :=
  max ((x + h * Real.sqrt x) / ((i : ℝ) + (k : ℝ)) - 2 * Real.sqrt x) 0

/-- The shortfall of the lower endpoint below the dyadic floor. -/
def fibreUnder (x : ℝ) (i : ℕ) : ℝ := max (Real.sqrt x - x / (i : ℝ)) 0

theorem fibreOver_nonneg (x h : ℝ) (k i : ℕ) : 0 ≤ fibreOver x h k i := le_max_right _ _

theorem fibreUnder_nonneg (x : ℝ) (i : ℕ) : 0 ≤ fibreUnder x i := le_max_right _ _

theorem min_eq_sub_max_sub (a b : ℝ) : min a b = a - max (a - b) 0 := by
  rcases le_total a b with hab | hab
  · rw [min_eq_left hab, max_eq_right (by linarith)]
    ring
  · rw [min_eq_right hab, max_eq_left (by linarith)]
    ring

theorem max_eq_add_max_sub (a b : ℝ) : max a b = a + max (b - a) 0 := by
  rcases le_total a b with hab | hab
  · rw [max_eq_right hab, max_eq_left (by linarith)]
    ring
  · rw [max_eq_left hab, max_eq_right (by linarith)]
    ring

/-- **The smooth model, decomposed.** -/
theorem fibreSmooth_decomp (x h : ℝ) (k i : ℕ) :
    fibreSmooth x h k i
      = max (kernelDiff x h k i - fibreOver x h k i - fibreUnder x i + 1) 0 := by
  have hinner : fibreHigh x h (i + k) - fibreLow x i
      = kernelDiff x h k i - fibreOver x h k i - fibreUnder x i := by
    rw [fibreHigh_shift_eq, fibreLow, kernelDiff, fibreOver, fibreUnder,
      min_eq_sub_max_sub ((x + h * Real.sqrt x) / ((i : ℝ) + (k : ℝ))) (2 * Real.sqrt x),
      max_eq_add_max_sub (x / (i : ℝ)) (Real.sqrt x)]
    ring
  rw [fibreSmooth, kernelSmooth, hinner]

end RHTower.Sieve

end
