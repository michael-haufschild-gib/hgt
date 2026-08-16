import GaloisForLFunctions.HTGeometry.HermiteOriginValues

/-!
# The closed form of the Hermite centre values

The card's identity `a_j² = a_0² q_j` with `q_j = binom(4j, 2j)/16^j` is the even case of

```text
hermiteOriginValue (2m)² = sqrt 2 · centralBinom m / 4^m ,
```

which follows by induction from the two-step origin recursion and the central binomial recursion,
both already available.  The two ratios agree exactly:

```text
a_{2m+2}²/a_{2m}² = (2m+1)/(2m+2) ,
[centralBinom (m+1)/4^{m+1}] / [centralBinom m/4^m] = 2(2m+1)/(4(m+1)) = (2m+1)/(2m+2) .
```

Every power of `π` cancels between the square of the origin value and the normalisation, which is
why the answer is rational times `sqrt 2`.
-/

noncomputable section

open Real

namespace GaloisForLFunctions.RHTower

open GaloisForLFunctions

/-- **The closed form of the squared Hermite centre values at even index.** -/
theorem hermiteOriginValue_sq_two_mul (m : ℕ) :
    hermiteOriginValue (2 * m) ^ 2 = Real.sqrt 2 * (Nat.centralBinom m : ℝ) / 4 ^ m := by
  induction m with
  | zero =>
      rw [Nat.mul_zero, hermiteOriginValue_sq_zero]
      norm_num [Nat.centralBinom]
  | succ k ih =>
      have hpi : (π : ℝ) ≠ 0 := Real.pi_ne_zero
      have hrec := eval_zero_hermitePoly_add_two (2 * k)
      have hidx : 2 * (k + 1) = 2 * k + 2 := by ring
      have hfact : (Nat.factorial (2 * k + 2) : ℝ)
          = ((2 * (k : ℝ) + 2) * (2 * (k : ℝ) + 1)) * (Nat.factorial (2 * k) : ℝ) := by
        rw [Nat.factorial_succ, Nat.factorial_succ]
        push_cast
        ring
      have hfact0 : (Nat.factorial (2 * k) : ℝ) ≠ 0 :=
        Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
      have hcb := Nat.succ_mul_centralBinom_succ k
      have hcbR : ((k : ℝ) + 1) * (Nat.centralBinom (k + 1) : ℝ)
          = 2 * (2 * (k : ℝ) + 1) * (Nat.centralBinom k : ℝ) := by
        exact_mod_cast congrArg (fun t : ℕ => (t : ℝ)) hcb
      -- the two squared origin values
      have hval : hermiteOriginValue (2 * k + 2) ^ 2
          = ((2 * (k : ℝ) + 1) / (2 * (k : ℝ) + 2)) * hermiteOriginValue (2 * k) ^ 2 := by
        rw [hermiteOriginValue_sq, hermiteOriginValue_sq, hrec, hfact]
        push_cast
        field_simp
        ring
      rw [hidx, hval, ih]
      have hk2 : (2 * (k : ℝ) + 2) ≠ 0 := by positivity
      have hkp : ((k : ℝ) + 1) ≠ 0 := by positivity
      have hfour : (4 : ℝ) ^ (k + 1) = 4 ^ k * 4 := by
        rw [pow_succ]
      rw [hfour]
      have hcbval : (Nat.centralBinom (k + 1) : ℝ)
          = 2 * (2 * (k : ℝ) + 1) * (Nat.centralBinom k : ℝ) / ((k : ℝ) + 1) := by
        field_simp
        linarith [hcbR]
      rw [hcbval]
      have h4 : (4 : ℝ) ^ k ≠ 0 := by positivity
      field_simp
      ring

/-- **The card's `(4)`**: the squared centre values along the ladder `n = 4j` are
`a_0² · binom(4j, 2j) / 16^j`. -/
theorem hermiteOriginValue_sq_four_mul (j : ℕ) :
    hermiteOriginValue (4 * j) ^ 2
      = hermiteOriginValue 0 ^ 2 * (Nat.choose (4 * j) (2 * j) : ℝ) / 16 ^ j := by
  have hidx : 4 * j = 2 * (2 * j) := by ring
  have hcb : Nat.centralBinom (2 * j) = Nat.choose (4 * j) (2 * j) := by
    rw [Nat.centralBinom, hidx]
  have hpow : (4 : ℝ) ^ (2 * j) = 16 ^ j := by
    rw [pow_mul]
    norm_num
  rw [hidx, hermiteOriginValue_sq_two_mul, hcb, hpow, hermiteOriginValue_sq_zero, hidx]

end GaloisForLFunctions.RHTower

end
