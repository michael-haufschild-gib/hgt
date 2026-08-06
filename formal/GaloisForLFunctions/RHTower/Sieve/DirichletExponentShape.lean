import GaloisForLFunctions.RHTower.Sieve.DirichletPowerTwoShape

/-!
# The shape in exponent form

With a power-of-two split every quantity in the hypotheses is a power of two, so the two bounds on
`t` become a single sandwich between explicit exponents:

```text
8π · 2^(R/3)  ≤  t  ≤  2π · 2^(K + (S+1)(K-1) - (S+1)/3).
```

The hypotheses are then elementary inequalities among `S`, `R`, `K`, `ε` and `t`; the only
transcendental constants left are `π` and `log 2`.  In particular the sandwich is consistent exactly
when

```text
2 ≤ K + (S+1)(K-1) - (S+1)/3 - R/3,
```

which is the arithmetic form of the compatibility between the split point, the top of the range and
the order.
-/

namespace RHTower.Sieve

open Finset

/-- A power of two raised to a natural power and to a real power, merged into a single real
exponent. -/
private theorem two_pow_merge (m : ℕ) (j : ℕ) (c : ℝ) :
    ((2 ^ m : ℕ) : ℝ) ^ j * ((2 ^ m : ℕ) : ℝ) ^ (c : ℝ)
      = (2 : ℝ) ^ (((m : ℝ) * (j : ℝ)) + (m : ℝ) * c) := by
  have h2 : (0 : ℝ) < 2 := by norm_num
  have hcast : ((2 ^ m : ℕ) : ℝ) = (2 : ℝ) ^ (m : ℕ) := by push_cast; ring
  rw [hcast, ← Real.rpow_natCast (2 : ℝ) m, ← Real.rpow_natCast ((2 : ℝ) ^ ((m : ℕ) : ℝ)) j,
    ← Real.rpow_mul h2.le, ← Real.rpow_mul h2.le, ← Real.rpow_add h2]

/-- **Exponent form.**  Both bounds on `t` are explicit powers of two. -/
theorem norm_dirichlet_partial_littlewood_exponent {t : ℝ} (ht : 0 < t) {S R K : ℕ} (hSR : S < R)
    {ε : ℝ} (hε : 0 < ε) (hε' : ε ≤ 2560) (hK : 2 ≤ K)
    (hfacS : Nat.factorial (K - 1) ≤ 2 ^ (S + 1))
    (hlowTop : 8 * Real.pi * (2 : ℝ) ^ ((R : ℝ) / 3) ≤ t)
    (hhighS : t ≤ 2 * Real.pi * (2 : ℝ) ^ (((S : ℝ) + 1) * ((K : ℝ) - 1)
      - ((S : ℝ) + 1) / 3) * (2 : ℝ) ^ K)
    (hdeepS : 3 * (2 : ℝ) ^ K * Real.log (2560 / ε) ≤ ((S : ℝ) + 1) * Real.log 2) :
    ‖∑ n ∈ Finset.Ico (1 : ℕ) (2 ^ (R + 1)), (n : ℂ) ^ (-1 - Complex.I * (t : ℂ))‖
      ≤ 1 + ((S : ℝ) + 1) * Real.log 2 + ((R - S : ℕ) : ℝ) * ε := by
  have hKcast : ((K - 1 : ℕ) : ℝ) = (K : ℝ) - 1 := by
    have : 1 ≤ K := by omega
    push_cast [Nat.cast_sub this]
    ring
  refine norm_dirichlet_partial_littlewood_pow_two ht hSR hε hε' hK hfacS ?_ hdeepS ?_
  · -- upper bound on `t`
    refine le_trans hhighS (le_of_eq ?_)
    have h1 : ((2 ^ (S + 1) : ℕ) : ℝ) ^ (K - 1) * ((2 ^ (S + 1) : ℕ) : ℝ) ^ (-(1 / 3) : ℝ)
        = (2 : ℝ) ^ (((S : ℝ) + 1) * ((K : ℝ) - 1) - ((S : ℝ) + 1) / 3) := by
      rw [two_pow_merge (S + 1) (K - 1) (-(1 / 3) : ℝ)]
      congr 1
      push_cast [hKcast]
      ring
    calc 2 * Real.pi * (2 : ℝ) ^ (((S : ℝ) + 1) * ((K : ℝ) - 1) - ((S : ℝ) + 1) / 3)
          * (2 : ℝ) ^ K
        = 2 * Real.pi * (2 : ℝ) ^ K
            * ((2 : ℝ) ^ (((S : ℝ) + 1) * ((K : ℝ) - 1) - ((S : ℝ) + 1) / 3)) := by ring
      _ = 2 * Real.pi * (2 : ℝ) ^ K
            * (((2 ^ (S + 1) : ℕ) : ℝ) ^ (K - 1)
              * ((2 ^ (S + 1) : ℕ) : ℝ) ^ (-(1 / 3) : ℝ)) := by rw [h1]
      _ = 2 * Real.pi * (2 : ℝ) ^ K * ((2 ^ (S + 1) : ℕ) : ℝ) ^ (K - 1)
            * ((2 ^ (S + 1) : ℕ) : ℝ) ^ (-(1 / 3) : ℝ) := by ring
  · -- lower bound on `t`
    refine le_trans (le_of_eq ?_) hlowTop
    have hcast : ((2 ^ R : ℕ) : ℝ) = (2 : ℝ) ^ (R : ℕ) := by push_cast; ring
    rw [hcast, ← Real.rpow_natCast (2 : ℝ) R, ← Real.rpow_mul (by norm_num)]
    congr 2
    ring

end RHTower.Sieve
