import GaloisForLFunctions.RHTower.Sieve.ChebyshevKappaOneData

/-!
# The balanced truncation height at the width-`1/log` rectangle

The left edge saves `exp(-log x/(40000 log T))` and the truncation error carries
`x^{1/log T}/T`.  With

```text
chebHeightOne x = exp( 2√(log x) )
```

the first is exactly `exp(-√(log x)/80000)` and the second is exactly
`exp(√(log x)/2 - 2√(log x)) = exp(-(3/2)√(log x))`.  Both are `exp(-c√(log x))`, which is the
saving the exponent-one zero-free region supports.

The factor `2` is what separates the two sides: at `log T = √(log x)` the truncation term's
`x^{1/log T} = exp(√(log x))` exactly cancels `1/T`, and nothing is saved there.
-/

namespace RHTower.Sieve

/-- The balanced truncation height. -/
noncomputable def chebHeightOne (x : ℝ) : ℝ := Real.exp (2 * Real.sqrt (Real.log x))

theorem chebHeightOne_pos (x : ℝ) : 0 < chebHeightOne x := Real.exp_pos _

theorem one_le_chebHeightOne (x : ℝ) : 1 ≤ chebHeightOne x := by
  rw [chebHeightOne]
  exact Real.one_le_exp (by positivity)

theorem log_chebHeightOne (x : ℝ) :
    Real.log (chebHeightOne x) = 2 * Real.sqrt (Real.log x) := by
  rw [chebHeightOne, Real.log_exp]

theorem four_le_sqrt_log {x : ℝ} (hx : 16 ≤ Real.log x) : 4 ≤ Real.sqrt (Real.log x) := by
  have h : Real.sqrt 16 ≤ Real.sqrt (Real.log x) := Real.sqrt_le_sqrt hx
  have h16 : Real.sqrt 16 = 4 := by
    rw [show (16 : ℝ) = 4 ^ (2 : ℕ) by norm_num, Real.sqrt_sq (by norm_num)]
  linarith [h, h16]

theorem eight_le_log_chebHeightOne {x : ℝ} (hx : 16 ≤ Real.log x) :
    8 ≤ Real.log (chebHeightOne x) := by
  rw [log_chebHeightOne]
  linarith [four_le_sqrt_log hx]

/-- The left edge's exponent, as an identity in the square root. -/
theorem saving_identity {s : ℝ} (hs : 0 < s) : 1 / 40000 / (2 * s) * (s * s) = s / 80000 := by
  field_simp
  ring

/-- The right line's exponent, as an identity in the square root. -/
theorem right_identity {s : ℝ} (hs : 0 < s) : 1 / (2 * s) * (s * s) = s / 2 := by
  field_simp

/-- **The left edge's saving at the balanced height.** -/
theorem saving_exponent_one {x : ℝ} (hx : 16 ≤ Real.log x) :
    1 / 40000 / Real.log (chebHeightOne x) * Real.log x = Real.sqrt (Real.log x) / 80000 := by
  rw [log_chebHeightOne]
  have hs0 : (0 : ℝ) < Real.sqrt (Real.log x) := Real.sqrt_pos.mpr (by linarith)
  have hsq : Real.sqrt (Real.log x) * Real.sqrt (Real.log x) = Real.log x :=
    Real.mul_self_sqrt (by linarith)
  have h := saving_identity hs0
  rw [hsq] at h
  exact h

/-- **The right line's growth at the balanced height.** -/
theorem right_exponent_one {x : ℝ} (hx : 16 ≤ Real.log x) :
    1 / Real.log (chebHeightOne x) * Real.log x = Real.sqrt (Real.log x) / 2 := by
  rw [log_chebHeightOne]
  have hs0 : (0 : ℝ) < Real.sqrt (Real.log x) := Real.sqrt_pos.mpr (by linarith)
  have hsq : Real.sqrt (Real.log x) * Real.sqrt (Real.log x) = Real.log x :=
    Real.mul_self_sqrt (by linarith)
  have h := right_identity hs0
  rw [hsq] at h
  exact h

/-- **The truncation height beats the right line's growth**, with `exp(-(3/2)√(log x))` to spare. -/
theorem exp_right_le_chebHeightOne {x : ℝ} (hx : 16 ≤ Real.log x) :
    Real.exp (1 / Real.log (chebHeightOne x) * Real.log x)
      = Real.exp (-(3 / 2) * Real.sqrt (Real.log x)) * chebHeightOne x := by
  rw [right_exponent_one hx, chebHeightOne, ← Real.exp_add]
  ring_nf

end RHTower.Sieve
