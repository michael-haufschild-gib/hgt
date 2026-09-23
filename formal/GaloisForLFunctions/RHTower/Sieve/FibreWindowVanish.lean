import GaloisForLFunctions.RHTower.Sieve.FibreIncrementUniform

/-!
# The window on which the smooth model varies

The smooth model vanishes below `√x/2` — there the lower endpoint `x/n` already exceeds the dyadic
ceiling `2√x` by more than one — and above `√x + h` — there the upper endpoint `(x+h√x)/(n+k)` has
fallen below the dyadic floor `√x` by more than one.  So all its increments live in

```text
[ ⌊√x/2⌋ − 2 , ⌈√x + h⌉ + 3 ] ,
```

a window of length `√x/2 + h + O(1)`.  Restricting the shift-uniform majorant to this window is what
makes its total `O(h)` rather than `O(√x)`: the two truncated pieces telescope across the window to
`O(h)`, and `kernelDiff`'s range across it is `O(h)`.
-/

noncomputable section

namespace RHTower.Sieve

open Finset

/-- The left edge of the window on which the smooth model varies. -/
def fibreWinLo (x : ℝ) : ℕ := ⌊Real.sqrt x / 2⌋₊ - 2

/-- The right edge. -/
def fibreWinHi (x h : ℝ) : ℕ := ⌈Real.sqrt x + h⌉₊ + 3

theorem eight_le_sqrt {x : ℝ} (hx : 64 ≤ x) : (8 : ℝ) ≤ Real.sqrt x := by
  have h64 : Real.sqrt 64 = 8 := by
    rw [show (64 : ℝ) = 8 ^ (2 : ℕ) by norm_num, Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 8)]
  rw [← h64]
  exact Real.sqrt_le_sqrt hx

/-- **The smooth model vanishes when the inner variable is small.** -/
theorem fibreSmooth_eq_zero_of_small {x h : ℝ} {n : ℕ} (hn : 1 ≤ n) (k : ℕ)
    (hsmall : (n : ℝ) * (2 * Real.sqrt x + 1) ≤ x) :
    fibreSmooth x h k n = 0 := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hdiv : 2 * Real.sqrt x + 1 ≤ x / (n : ℝ) := by
    rw [le_div_iff₀ hn0]
    linarith [hsmall]
  have hlow : 2 * Real.sqrt x + 1 ≤ fibreLow_fibreKernelExact x n := le_trans hdiv (div_le_fibreLow x n)
  have hhigh : fibreHigh_fibreKernelExact x h (n + k) ≤ 2 * Real.sqrt x := fibreHigh_le_two_sqrt x h (n + k)
  rw [fibreSmooth, kernelSmooth, max_eq_right (by linarith)]

/-- **The smooth model vanishes when the inner variable is large.** -/
theorem fibreSmooth_eq_zero_of_ge {x h : ℝ} (hx : 64 ≤ x) (hh : 0 ≤ h)
    (hhx : h ≤ Real.sqrt x) {n k : ℕ} (hk : 1 ≤ k)
    (hn : Real.sqrt x + h + 5 ≤ (n : ℝ)) :
    fibreSmooth x h k n = 0 := by
  have hs8 : (8 : ℝ) ≤ Real.sqrt x := eight_le_sqrt hx
  have hsq : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt (by linarith)
  have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hden : (0 : ℝ) < ((n + k : ℕ) : ℝ) := by
    have : (n : ℝ) ≤ ((n + k : ℕ) : ℝ) := by push_cast; linarith
    linarith
  have hkey : x + h * Real.sqrt x ≤ (Real.sqrt x - 1) * ((n + k : ℕ) : ℝ) := by
    have hnk : Real.sqrt x + h + 6 ≤ ((n + k : ℕ) : ℝ) := by push_cast; linarith
    nlinarith [hnk, hs8, hsq, hhx, hh]
  have hhigh : fibreHigh_fibreKernelExact x h (n + k) ≤ Real.sqrt x - 1 := by
    refine le_trans (fibreHigh_le_div x h (n + k)) ?_
    rw [div_le_iff₀ hden]
    exact hkey
  have hlow : Real.sqrt x ≤ fibreLow_fibreKernelExact x n := sqrt_le_fibreLow x n
  rw [fibreSmooth, kernelSmooth, max_eq_right (by linarith)]

/-- **Below the window the smooth model is constantly zero.** -/
theorem fibreSmooth_increment_zero_below {x h : ℝ} (hx : 64 ≤ x) (k : ℕ) {j : ℕ}
    (hj : j < fibreWinLo x) :
    fibreSmooth x h k (j + 2) - fibreSmooth x h k (j + 1) = 0 := by
  have hs8 : (8 : ℝ) ≤ Real.sqrt x := eight_le_sqrt hx
  have hsq : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt (by linarith)
  have hfl : (2 : ℝ) ≤ Real.sqrt x / 2 := by linarith
  have hfl2 : 2 ≤ ⌊Real.sqrt x / 2⌋₊ := Nat.le_floor (by push_cast; linarith)
  have hjR : ((j : ℕ) : ℝ) + 2 ≤ Real.sqrt x / 2 - 1 := by
    have hjn : j + 3 ≤ ⌊Real.sqrt x / 2⌋₊ := by
      rw [fibreWinLo] at hj
      omega
    have : ((j + 3 : ℕ) : ℝ) ≤ Real.sqrt x / 2 := by
      refine le_trans ?_ (Nat.floor_le (by positivity))
      exact_mod_cast hjn
    push_cast at this
    linarith
  have hsmall : ∀ m : ℕ, (m : ℝ) ≤ Real.sqrt x / 2 - 1 →
      (m : ℝ) * (2 * Real.sqrt x + 1) ≤ x := by
    intro m hm
    have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    nlinarith [hm, hs8, hsq, hm0]
  have h1 : fibreSmooth x h k (j + 1) = 0 := by
    refine fibreSmooth_eq_zero_of_small (Nat.le_add_left 1 j) k (hsmall _ ?_)
    push_cast
    linarith
  have h2 : fibreSmooth x h k (j + 2) = 0 := by
    refine fibreSmooth_eq_zero_of_small (by omega) k (hsmall _ ?_)
    push_cast
    linarith
  rw [h1, h2]
  ring

/-- **Above the window the smooth model is constantly zero.** -/
theorem fibreSmooth_increment_zero_above {x h : ℝ} (hx : 64 ≤ x) (hh : 0 ≤ h)
    (hhx : h ≤ Real.sqrt x) {k : ℕ} (hk : 1 ≤ k) {j : ℕ} (hj : fibreWinHi x h < j) :
    fibreSmooth x h k (j + 2) - fibreSmooth x h k (j + 1) = 0 := by
  have hceil : Real.sqrt x + h ≤ ((⌈Real.sqrt x + h⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
  have hjR : Real.sqrt x + h + 5 ≤ ((j : ℕ) : ℝ) + 1 := by
    have hjn : ⌈Real.sqrt x + h⌉₊ + 4 ≤ j := by
      rw [fibreWinHi] at hj
      omega
    have : ((⌈Real.sqrt x + h⌉₊ + 4 : ℕ) : ℝ) ≤ (j : ℝ) := by exact_mod_cast hjn
    push_cast at this
    linarith
  have h1 : fibreSmooth x h k (j + 1) = 0 := by
    refine fibreSmooth_eq_zero_of_ge hx hh hhx hk ?_
    push_cast
    linarith
  have h2 : fibreSmooth x h k (j + 2) = 0 := by
    refine fibreSmooth_eq_zero_of_ge hx hh hhx hk ?_
    push_cast
    linarith
  rw [h1, h2]
  ring

end RHTower.Sieve

end
