import GaloisForLFunctions.RHTower.Sieve.ChebyshevKappaOneCoeff
import GaloisForLFunctions.RHTower.Sieve.ChebyshevLittlewoodThreshold

/-!
# The shape's coefficient at depth `A`

`cheb_kappa_one_coeff_le` hard-codes the two shape quantities of the exponent-one rectangle: the
pole coefficient `ci = 40000·Lg` and the width `wd ≤ 2/Lg`.  At depth `A` they are

```text
ci = Lg / A ,        wd ≤ (1 + A) / Lg ,
```

so the pole coefficient *shrinks* with the depth while the width grows.  Both stay inside the same
envelope: `ci ≤ Lg` once `A ≥ 1`, and `wd ≤ 1/4` once `8A ≤ Lg`.  The conclusion is therefore the
same `250000(1 + Cr)(1 + Wb)Lg²`, with room to spare — the exponent-one constant `250000` is set by
`ci = 40000 Lg`, which the depth-`A` rectangle never approaches.
-/

namespace RHTower.Sieve

/-- **The shape's coefficient at depth `A`.** -/
theorem cheb_littlewood_coeff_le {S W ci wd M Cr Lg Wb A : ℝ}
    (hLg : 8 ≤ Lg) (hW0 : 0 ≤ W) (hWb : W ≤ Wb) (hCr0 : 0 ≤ Cr)
    (hS : S ≤ 8 * Lg ^ 2) (hA1 : 1 ≤ A) (hALg : 8 * A ≤ Lg)
    (hci : ci = Lg / A) (hwd0 : 0 ≤ wd) (hwd : wd ≤ (1 + A) / Lg) (hM : M = Cr * Lg ^ 2) :
    2 * S * W + ci * (4 + 2 * W) + 2 * wd * (W + 1) + M * (4 + 2 * W) + 2 * wd * M * W
      ≤ 250000 * (1 + Cr) * (1 + Wb) * Lg ^ 2 := by
  have hLg0 : (0 : ℝ) < Lg := by linarith
  have hA0 : (0 : ℝ) < A := by linarith
  have hWb0 : (0 : ℝ) ≤ Wb := le_trans hW0 hWb
  have hLg2 : (64 : ℝ) ≤ Lg ^ 2 := by nlinarith
  have hLgle : Lg ≤ Lg ^ 2 := by nlinarith
  -- the width is still at most a quarter
  have hwd4 : wd ≤ 1 / 4 := by
    refine le_trans hwd ?_
    rw [div_le_div_iff₀ hLg0 (by norm_num)]
    linarith
  -- the pole coefficient is at most `Lg`
  have hcile : ci ≤ Lg := by
    rw [hci, div_le_iff₀ hA0]
    nlinarith [hLg0, hA1]
  have hci0 : (0 : ℝ) ≤ ci := by
    rw [hci]; positivity
  -- the four monomials
  have m1 : (0 : ℝ) ≤ Lg ^ 2 := by positivity
  have m2 : (0 : ℝ) ≤ Lg ^ 2 * Wb := mul_nonneg m1 hWb0
  have m3 : (0 : ℝ) ≤ Cr * Lg ^ 2 := mul_nonneg hCr0 m1
  have m4 : (0 : ℝ) ≤ Cr * Lg ^ 2 * Wb := mul_nonneg m3 hWb0
  -- the five summands
  have t1 : 2 * S * W ≤ 16 * (Lg ^ 2 * Wb) := by nlinarith [hS, hWb, hW0, m1, hWb0]
  have t2 : ci * (4 + 2 * W) ≤ 4 * Lg ^ 2 + 2 * (Lg ^ 2 * Wb) := by
    nlinarith [hcile, hci0, hWb, hW0, hLg0, hWb0, hLgle]
  have t3 : 2 * wd * (W + 1) ≤ 1 / 2 * (Lg ^ 2 * Wb) + 1 / 2 * Lg ^ 2 := by
    nlinarith [hwd4, hwd0, hW0, hWb0, m1, hLg2, hWb]
  have t4 : M * (4 + 2 * W) ≤ 4 * (Cr * Lg ^ 2) + 2 * (Cr * Lg ^ 2 * Wb) := by
    rw [hM]
    nlinarith [hWb, hW0, hCr0, m1, hWb0]
  have t5 : 2 * wd * M * W ≤ 1 / 2 * (Cr * Lg ^ 2 * Wb) := by
    rw [hM]
    nlinarith [hwd4, hwd0, hWb, hW0, hCr0, m1, hWb0, m4]
  nlinarith [t1, t2, t3, t4, t5, m1, m2, m3, m4]

end RHTower.Sieve
