import GaloisForLFunctions.RHTower.Sieve.ChebyshevKappaOneShaped

/-!
# The shape's coefficient is a constant times `(1+Cr)(1+W) log²T`

After `cheb_kappa_one_terms_shaped` the whole contour bound is

```text
( 2SW + ci(4 + 2W) + 2·wd·(W + 1) + M(4 + 2W) + 2·wd·M·W ) · (Z · E),
```

and at the width-`1/log` rectangle the five ingredients are `S ≤ 8 log²T`, `ci = 40000 log T`,
`wd ≤ 2/log T`, `M = Cr log²T`.  Every product is then at most a constant times
`(1+Cr)(1+W) log²T`; the largest contribution is `ci·4 = 160000 log T`, which is why the constant
is of that size.

The reciprocal `wd ≤ 2/log T` is what keeps the horizontal edges from contributing a third power
of the logarithm.
-/

namespace RHTower.Sieve

/-- **The shape's coefficient.** -/
theorem cheb_kappa_one_coeff_le {S W ci wd M Cr Lg Wb : ℝ}
    (hLg : 8 ≤ Lg) (hW0 : 0 ≤ W) (hWb : W ≤ Wb) (hCr0 : 0 ≤ Cr)
    (hS : S ≤ 8 * Lg ^ (2 : ℕ)) (hci : ci = 40000 * Lg)
    (hwd0 : 0 ≤ wd) (hwd : wd ≤ 2 / Lg) (hM : M = Cr * Lg ^ (2 : ℕ)) :
    2 * S * W + ci * (4 + 2 * W) + 2 * wd * (W + 1) + M * (4 + 2 * W) + 2 * wd * M * W
      ≤ 250000 * (1 + Cr) * (1 + Wb) * Lg ^ (2 : ℕ) := by
  have hLg0 : (0 : ℝ) < Lg := by linarith
  have hWb0 : (0 : ℝ) ≤ Wb := le_trans hW0 hWb
  have hLg2 : (64 : ℝ) ≤ Lg ^ (2 : ℕ) := by nlinarith
  have hwd4 : wd ≤ 1 / 4 := by
    refine le_trans hwd ?_
    rw [div_le_div_iff₀ hLg0 (by norm_num)]
    linarith
  -- the four monomials
  have m1 : (0 : ℝ) ≤ Lg ^ (2 : ℕ) := by positivity
  have m2 : (0 : ℝ) ≤ Lg ^ (2 : ℕ) * Wb := mul_nonneg m1 hWb0
  have m3 : (0 : ℝ) ≤ Cr * Lg ^ (2 : ℕ) := mul_nonneg hCr0 m1
  have m4 : (0 : ℝ) ≤ Cr * Lg ^ (2 : ℕ) * Wb := mul_nonneg m3 hWb0
  -- the five summands
  have t1 : 2 * S * W ≤ 16 * (Lg ^ (2 : ℕ) * Wb) := by nlinarith [hS, hWb, hW0, m1, hWb0]
  have t2 : ci * (4 + 2 * W) ≤ 160000 * Lg ^ (2 : ℕ) + 80000 * (Lg ^ (2 : ℕ) * Wb) := by
    rw [hci]
    have hLgle : Lg ≤ Lg ^ (2 : ℕ) := by nlinarith
    nlinarith [hLgle, hWb, hW0, hLg0, hWb0]
  have t3 : 2 * wd * (W + 1) ≤ 1 / 2 * (Lg ^ (2 : ℕ) * Wb) + 1 / 2 * Lg ^ (2 : ℕ) := by
    have hWle : W ≤ Wb := hWb
    nlinarith [hwd4, hwd0, hW0, hWb0, m1, hLg2]
  have t4 : M * (4 + 2 * W) ≤ 4 * (Cr * Lg ^ (2 : ℕ)) + 2 * (Cr * Lg ^ (2 : ℕ) * Wb) := by
    rw [hM]
    nlinarith [hWb, hW0, hCr0, m1, hWb0]
  have t5 : 2 * wd * M * W ≤ 1 / 2 * (Cr * Lg ^ (2 : ℕ) * Wb) := by
    rw [hM]
    nlinarith [hwd4, hwd0, hWb, hW0, hCr0, m1, hWb0, m4]
  -- sum
  nlinarith [t1, t2, t3, t4, t5, m1, m2, m3, m4]

end RHTower.Sieve
