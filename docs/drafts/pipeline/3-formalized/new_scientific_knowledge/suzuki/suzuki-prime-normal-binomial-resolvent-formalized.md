# The complete Suzuki prime normal flow is an exact binomial resolvent

- **ID:** `suzuki-prime-normal-binomial-resolvent`
- **Stage:** 3 — formalized in Lean 4
- **Claim:** `[PROVED] [UNCONDITIONAL]`
- **Paper proof:** `./suzuki-prime-normal-binomial-resolvent.md`
- **Lean:**
  - `formal/GaloisForLFunctions/HTGeometry/PrimeNormalBinomialResolvent.lean`
  - `formal/GaloisForLFunctions/HTGeometry/PrimeNormalFlowResolvent.lean`
  - `formal/GaloisForLFunctions/HTGeometry/PrimeNormalFlowEquation.lean`
  - `formal/GaloisForLFunctions/HTGeometry/PrimeNormalFlowExpansion.lean`
  - `formal/GaloisForLFunctions/HTGeometry/PrimeNormalFlowUniqueness.lean`
  - `formal/GaloisForLFunctions/RHTower/SuzukiVolterraLogGradeRecurrence.lean`

## Formal content

```text
flowSymbol L t      = (sqrt (L - t/2))^(-1)
primeNormalFlow T L = cfc (flowSymbol L) T                     -- F(L) = (L I - T/2)^(-1/2)
sqrtFlow T L        = cfc (fun t => sqrt (L - t/2)) T          -- S(L) = (L I - T/2)^(1/2)
primeNormalCoeff k  = centralBinom k / 8^k                     -- theta_k
gradeCoeff L k      = primeNormalCoeff k * ((L^k)^(-1) * (sqrt L)^(-1))
```

| Card | Lean |
|---|---|
| `(2)` definition of `F_beta` | `primeNormalFlow` |
| `(1)` `(2L I - T) F' + F = 0` | `primeNormalFlow_equation` |
| `(10)` `d/dL A_L^(-1/2) = -(1/2) A_L^(-3/2)` | `hasDerivAt_primeNormalFlow` |
| `(3)` `sqrt(L) F(L) -> I` | `tendsto_sqrt_smul_primeNormalFlow` |
| uniqueness of the strong solution with a given trace | `primeNormalFlow_unique` |
| `(13)` `(1-z)^(-1/2) = sum binom(2k,k) z^k/4^k` | `hasSum_centralBinom_rpow` |
| `(4)` `F_beta(L) = sum theta_k L^(-k-1/2) T^k beta` | `hasSum_primeNormalFlow` |
| `(5)` `theta_k = binom(2k,k)/8^k` | `primeNormalCoeff` |
| `(14)` `theta_(k+1)/theta_k = (2k+1)/(4k+4)` | `primeNormalCoeff_succ` |
| `(15)` the same ratio from the Volterra grade recurrence | `suzukiVolterraRaisedCoefficient_recurrence` |
| `(16)` `theta_1 = 1/4`, `theta_k > 0`, `theta_k <= 2^(-k)` | `primeNormalCoeff_one`, `primeNormalCoeff_pos`, `primeNormalCoeff_le_two_pow` |
| `(19)` `sum theta_k (M/L)^k = (1 - M/(2L))^(-1/2)` | `hasSum_primeNormalCoeff`, `tsum_gradeMajorant` |
| `(6)`--`(7)` absolute convergence and the norm bound for `L > M/2` | `summable_gradeTerm`, `norm_tsum_gradeTerm_le` |
| `(7)` operator form `‖F(L)‖ <= (L - ‖T‖/2)^(-1/2)` | `norm_primeNormalFlow_le` |

Supporting declarations: `ringChoose_succ`, `ringChoose_neg_half`, `rpow_neg_half_eq`,
`abs_flowSlope_le`, `flowSlopeSymbol`, `abs_flowSlopeSymbol_le`, `continuousOn_flowSymbol`,
`flow_shift_pos`, `abs_le_norm_of_mem_spectrum`, `flowDerivSymbol`, `abs_traceSymbol_le`,
`tendsto_traceBound`, `hasSum_flowSymbol`, `gradeCoeff_nonneg`, `summable_gradeMajorant`,
`norm_gradeTerm_le`, `cfc_gradePartial`, `abs_sqrtSlope_le`, `sqrtSlopeSymbol`,
`abs_sqrtSlopeSymbol_le`, `hasDerivAt_sqrtFlow`, `sqrtFlow_mul_primeNormalFlow`,
`primeNormalFlow_mul_sqrtFlow`, `two_smul_sqrtFlow_sq`, `tendsto_inv_sqrt_smul_sqrtFlow`.

## The gap the card declared open is closed

The card's `## 8` says: *"Formalizing `(2)` itself requires the unbounded-in-parameter continuous
functional calculus derivative for `A_L^{-1/2}`; the paper proof uses the spectral theorem directly.
An abstract axiom for that derivative would be rejected."*

No axiom is used.  The derivative is proved.  The mechanism is that the isometric functional
calculus turns a **uniform** estimate on the symbol into a norm estimate on the operator, so a
second-order scalar estimate suffices:

```text
|(b^(-1/2) - a^(-1/2))/(b-a) + (1/2) a^(-3/2)| <= |b-a| / (2 s^5)      whenever s^2 <= a, b
```

and this is not Taylor's theorem but an algebraic identity — in `p = sqrt a`, `q = sqrt b` the
defect equals `(q-p)(q+2p)/(2 p^3 q (p+q))`, and `q - p = (b-a)/(p+q)`.  Restricting the increment
to half the spectral gap makes `s` uniform over the spectrum, so `tendsto_norm_cfc_zero` converts
the scalar estimate into norm convergence of the operator difference quotient.  The same argument
run on `sqrt(L - t/2)` (defect `(b-a)/(2p(p+q)^2)`, bound `|b-a|/(8 s^3)`) gives the derivative of
the square-root flow, which is what uniqueness needs.

## Three further things the formalization fixes

**The coefficient identity is not folklore in mathlib.**  mathlib has the generalized binomial
series (`Real.one_add_rpow_hasFPowerSeriesOnBall_zero`, coefficients `Ring.choose a n`) but not the
closed form of `Ring.choose (-1/2) n`.  `ringChoose_neg_half` proves
`Ring.choose (-1/2) n = (-1)^n binom(2n,n)/4^n` by induction off `descPochhammer_succ_right` and
`Nat.succ_mul_centralBinom_succ`.  This is the card's `(13)`, and everything downstream — `(4)`,
`(5)`, `(19)` — rests on it.

**Uniqueness is an operator statement, not a fibrewise one.**  The card argues fibrewise "for almost
every spectral value".  The Lean proof is global: `S(L) G(L)` has derivative
`(1/2) F G + S G' `, the equation gives `2 S² G' = -G`, and `S F = 1` makes the two terms cancel, so
`S G` is constant by `constant_of_has_deriv_right_zero` on every `[L₀, L]`; the trace pins the
constant because `(sqrt L)^(-1) S(L) -> 1`.  No spectral decomposition and no measure theory enters.

**`(6)`--`(7)` hold in any Banach algebra, not just a C\*-algebra.**  `summable_gradeTerm` and
`norm_tsum_gradeTerm_le` are stated for a complete normed algebra with `‖1‖ = 1`, which covers the
card's `l^1` valuation carrier — the setting where `X_1 = l^1(V)` is not a C\*-algebra.  The
functional-calculus statements `(1)`, `(2)`, `(3)`, `(4)` are stated for a C\*-algebra, the card's
`l^2` setting, where `(2)` is defined at all.

## Hypotheses

`T` is a self-adjoint element of a C\*-algebra (for `(6)`--`(7)`, any element of a Banach algebra),
and `L > ‖T‖/2`.  Both are the card's own standing conditions — `T = T*` and `L > ‖T‖/2` — not
imported theorems.  `primeNormalFlow_unique` takes the competing solution's differentiability, its
equation, and its trace, which are exactly the card's hypotheses on "another strong solution with
the same trace".

No `sorry`, `axiom`, `opaque`, `unsafe`, RH premise, or numerical computation occurs.  Every cited
declaration audits to `[propext, Classical.choice, Quot.sound]`.

## Open boundary

The card's `(20)`, the Duhamel coupling of this resolvent to the Gamma jump and the corrected
exterior forcing, is explicitly the card's open connector and is not formalized here — it is not a
claim of this card.  Section 4's literal word expansion (`T = sum_s w_s U_s`, every length-`k` word
appearing with product weight) is the elementary multinomial expansion of `T^k` for a specific
adjacency; what is formalized is the coefficient `theta_k` that grades it and the absolute mass
bound `theta_k M_a^k <= (M_a/2)^k` that makes the sum converge.
