import GaloisForLFunctions.RHTower.AnharmonicChebyshevMovingFiber

/-!
# Derivative of the anharmonic cubic quotient

For the degree-three anharmonic quotient `q(s) = (s - 2)(s + 1)(2s - 1) / (2s(s - 1))`, this
module computes the complex derivative away from the poles: `q'(s) = 1 + 1/s² + 1/(s - 1)²`,
which equals the perfect square `((s² - s + 1) / (s(s - 1)))²`. It deduces that `q'` does not
vanish at real points other than the poles.

## Main results

- `chebyshevAnharmonicQ_deriv`: for `s ≠ 0, 1`, `deriv q s = chebyshevAnharmonicQPrime s`,
  i.e. `1 + 1/s² + 1/(s - 1)²`.
- `chebyshevAnharmonicQ_deriv_sq`: for `s ≠ 0, 1`, `q'(s) = ((s² - s + 1) / (s(s - 1)))²`.
- `chebyshevAnharmonicQ_deriv_ofReal_ne_zero`: for real `s ≠ 0, 1`, `q'(s) ≠ 0`.

## Hypotheses

Unconditional; the only premises are `s ≠ 0` and `s ≠ 1`, which exclude the poles of `q`.
-/

open Complex

namespace RHTower

/-- Away from the poles `s = 0, 1`, the derivative of the anharmonic quotient
`q(s) = (s - 2)(s + 1)(2s - 1) / (2s(s - 1))` is `1 + 1/s² + 1/(s - 1)²`. -/
theorem chebyshevAnharmonicQ_deriv
    {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    deriv chebyshevAnharmonicQ s = chebyshevAnharmonicQPrime s := by
  have hden : 2 * s * (s - 1) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num) hs0) (sub_ne_zero.mpr hs1)
  have ha₁ : HasDerivAt (fun z : ℂ => z - 2) 1 s := (hasDerivAt_id s).sub_const 2
  have ha₂ : HasDerivAt (fun z : ℂ => z + 1) 1 s := (hasDerivAt_id s).add_const 1
  have ha₃ := (((hasDerivAt_id s).const_mul 2).sub_const 1)
  have ha := (ha₁.mul ha₂).mul ha₃
  have hb₁ := (hasDerivAt_id s).const_mul 2
  have hb₂ : HasDerivAt (fun z : ℂ => z - 1) 1 s := (hasDerivAt_id s).sub_const 1
  have hb := hb₁.mul hb₂
  have hq := ha.div hb hden
  have hfun : (((fun z : ℂ => z - 2) * fun z => z + 1) *
        (fun x => 2 * id x - 1)) /
        ((fun y => 2 * id y) * fun z => z - 1) = chebyshevAnharmonicQ := by
    funext z
    rfl
  rw [hfun] at hq
  have hder := hq.deriv
  have hnum :
      ((1 * (s + 1) + (s - 2) * 1) * (2 * s - 1) +
        (s - 2) * (s + 1) * 2) * (2 * s * (s - 1)) -
        ((s - 2) * (s + 1) * (2 * s - 1)) *
          (2 * (s - 1) + 2 * s) =
        4 * (s ^ 2 - s + 1) ^ 2 := by ring
  have hval : deriv chebyshevAnharmonicQ s =
      (4 * (s ^ 2 - s + 1) ^ 2) / (2 * s * (s - 1)) ^ 2 := by
    simp only [one_mul, mul_one] at hnum
    simp only [Pi.mul_apply, id_eq, one_mul, mul_one] at hder
    rw [hnum] at hder
    exact hder
  rw [hval]
  simp only [chebyshevAnharmonicQPrime]
  field_simp [hs0, sub_ne_zero.mpr hs1]
  ring

/-- For `s ≠ 0, 1`, the derivative of the anharmonic quotient is a perfect square:
`q'(s) = ((s² - s + 1) / (s(s - 1)))²`. -/
theorem chebyshevAnharmonicQ_deriv_sq
    {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    deriv chebyshevAnharmonicQ s =
      ((s ^ 2 - s + 1) / (s * (s - 1))) ^ 2 := by
  rw [chebyshevAnharmonicQ_deriv hs0 hs1]
  simp only [chebyshevAnharmonicQPrime]
  field_simp [hs0, sub_ne_zero.mpr hs1]
  ring

/-- At every real point `s ≠ 0, 1` the derivative of the anharmonic quotient is nonzero, so `q`
has no real critical points. -/
theorem chebyshevAnharmonicQ_deriv_ofReal_ne_zero
    {s : ℝ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    deriv chebyshevAnharmonicQ (s : ℂ) ≠ 0 := by
  rw [chebyshevAnharmonicQ_deriv (by exact_mod_cast hs0) (by exact_mod_cast hs1)]
  exact chebyshevAnharmonicQPrime_ofReal_ne_zero s

end RHTower
