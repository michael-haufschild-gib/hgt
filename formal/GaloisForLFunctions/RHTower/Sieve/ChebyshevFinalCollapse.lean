import GaloisForLFunctions.RHTower.Sieve.ChebyshevCollapseOne

/-!
# The final collapse

Putting the coefficient bound and the two collapse steps together: the shaped bound

```text
250000(1+Cr)(1+Wb) · log²T · (Z · E),      log²T = 4 log Z = 4 s²,
```

becomes a constant times `Z · exp(-s/480000)`.  The coefficient `(1+Wb)·E` is replaced first —
that is where the smoothing's price meets the left edge's saving — and only then is the polynomial
`s²` absorbed, halving the exponent one last time.
-/

namespace RHTower.Sieve

/-- **The final collapse.** -/
theorem cheb_final_collapse {Cr Cm Z s Wb E : ℝ}
    (hCr : 0 ≤ Cr) (hCm : 0 ≤ Cm) (hZ0 : 0 ≤ Z) (hs : 0 ≤ s)
    (hlogZ : Real.log Z = s ^ 2)
    (hWbE : (1 + Wb) * E ≤ (3 + 27 * Cm) * Real.exp (-(s / 240000))) :
    250000 * (1 + Cr) * (1 + Wb) * (4 * Real.log Z) * (Z * E)
      ≤ 250000 * (1 + Cr) * (3 + 27 * Cm) * (4 * (4 * 480000 ^ 2)) * Z
          * Real.exp (-(s / 480000)) := by
  rw [hlogZ]
  have hA : (0 : ℝ) ≤ 250000 * (1 + Cr) * 4 * s ^ 2 * Z :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (by linarith)) (by norm_num))
      (sq_nonneg s)) hZ0
  have step1 : 250000 * (1 + Cr) * (1 + Wb) * (4 * s ^ 2) * (Z * E)
      ≤ 250000 * (1 + Cr) * 4 * s ^ 2 * Z * ((3 + 27 * Cm) * Real.exp (-(s / 240000))) := by
    have h := mul_le_mul_of_nonneg_left hWbE hA
    nlinarith [h]
  have hB : (0 : ℝ) ≤ 250000 * (1 + Cr) * (3 + 27 * Cm) * 4 * Z :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (by linarith))
      (by linarith)) (by norm_num)) hZ0
  have step2 := mul_le_mul_of_nonneg_left (sq_mul_exp_neg_le hs) hB
  nlinarith [step1, step2]

end RHTower.Sieve
