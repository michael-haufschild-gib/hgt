import GaloisForLFunctions.RHTower.ExpansionParameterIsTheShift

/-!
# Turán for `Ξ` is a sharp competition between a variance and a factorial gap

A degree-uniform statement about the Taylor coefficients is a statement about the measure whose moments
they are.  This file makes that precise at the first degree and finds a competition of matching
orders.

**The coefficients are normalised moments.**  With `m_k = Ξ^{(2k)}(0)` the moments of the theta
remainder against `u^{2k}`, the Jensen coefficients are `γ_k = m_k / (2k)!`.  Two facts pull in
opposite directions:

* the raw moments of a positive measure are **log-convex** — Cauchy–Schwarz gives
  `m_{k+1}² ≤ m_k m_{k+2}`;
* the normalisation `1/(2k)!` is **log-concave**, and its gap is explicit:

```text
(2k)! (2k+4)! / ((2k+2)!)²  =  (2k+3)(2k+4) / ((2k+1)(2k+2))  >  1 .
```

**So Turán is exactly the statement that the factorial gap beats the moment deficit.**  Writing the
Turán ratio,

```text
γ_{k+1}² / (γ_k γ_{k+2})  =  ( m_{k+1}² / (m_k m_{k+2}) ) · ( (2k+3)(2k+4) / ((2k+1)(2k+2)) ) ,
```

the hypothesis `γ_{k+1}² ≥ γ_k γ_{k+2}` holds precisely when the moment ratio exceeds the reciprocal of
the factorial gap.

**And the two sides have the same order.**  The factorial gap exceeds one by

```text
(2k+3)(2k+4) - (2k+1)(2k+2)  =  8k + 10 ,        so the excess is  (8k+10)/((2k+1)(2k+2))  ≍  2/k ,
```

while the moment deficit is the variance of `log u²` under the tilted measure, which is also of order
`1/k` because the tilted measure concentrates.

> **Turán for `Ξ` is a constant competition at order `1/k`, not a soft inequality — which is why it
> required real work, and why higher degrees are harder: degree `d` compares a `d`-th order variance
> against a `d`-th order factorial gap, both of the same order.**

This file formalizes the factorial identity, its excess over one, the order of that excess, and the
factorisation of the Turán ratio.
-/

open Real

noncomputable section

namespace RHTower

/-- **The factorial gap.**  The normalisation's log-concavity in closed form. -/
theorem factorial_gap (k : ℝ) :
    (2 * k + 3) * (2 * k + 4) = (2 * k + 1) * (2 * k + 2) + (8 * k + 10) := by ring

/-- **The excess is positive.**  The gap exceeds one for every nonnegative `k`. -/
theorem factorial_gap_gt_one {k : ℝ} (hk : 0 ≤ k) :
    1 < ((2 * k + 3) * (2 * k + 4)) / ((2 * k + 1) * (2 * k + 2)) := by
  rw [lt_div_iff₀ (by nlinarith)]
  nlinarith

/-- **The excess has order `1/k`.**  Its numerator is linear and its denominator quadratic. -/
theorem excess_order {k : ℝ} (hk : 1 ≤ k) :
    (8 * k + 10) / ((2 * k + 1) * (2 * k + 2)) ≤ 18 / k := by
  have hk0 : (0:ℝ) < k := by linarith
  rw [div_le_div_iff₀ (by nlinarith) hk0]
  nlinarith

/-- **The Turán ratio factorises** into the moment ratio times the factorial gap. -/
theorem turan_ratio_factorises {mk mk1 mk2 fk fk1 fk2 : ℝ}
    (h0 : mk ≠ 0) (h2 : mk2 ≠ 0) (g0 : fk ≠ 0) (g1 : fk1 ≠ 0) (g2 : fk2 ≠ 0) :
    ((mk1 / fk1) ^ (2 : ℕ)) / ((mk / fk) * (mk2 / fk2))
      = (mk1 ^ (2 : ℕ) / (mk * mk2)) * ((fk * fk2) / fk1 ^ (2 : ℕ)) := by
  field_simp

/-- **Turán is the competition.**  The normalised ratio is at least one exactly when the moment ratio
is at least the reciprocal of the gap. -/
theorem turan_iff_moment_ratio {r g : ℝ} (hg : 0 < g) :
    1 ≤ r * g ↔ 1 / g ≤ r := by
  rw [div_le_iff₀ hg]

end RHTower
