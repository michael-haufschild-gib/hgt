# Prime-log critical cubic-kernel unboundedness law

- **ID:** ULF-PLCCKU-001
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Parents:** ULF-PCOB-001, ULF-PLCIE-001
- **Status:** `[PAPER-PROVED] [LEAN-PROVED] [NOT RH]`
- **Lean:** `formal/GaloisForLFunctions/RHTower/PrimeLogCriticalCubicKernelUnboundedness.lean`

## 1. Big-picture meaning

The inverse prime-heat orbit does not reach its trace-ideal wall as a bounded operator.  Its raw
critical cubic Cauchy kernel has finite compressions with unbounded operator norm.  Therefore the
new completion datum cannot be the endpoint operator, a trace subtraction, or a compact
perturbation.  If this orbit survives, it must do so through the canonical graph projection or
bounded transform of a closed unbounded endpoint relation.

## 2. Statement

For primes `p,q`, put

```text
h(p)=log(p)/p,
c(p,q)=2 sqrt(log(p)log(q))/(log(p)+log(q)),
K(p,q)=sqrt(h(p)h(q)) c(p,q)^3.                         (PLCCKU.1)
```

Apart from the fixed positive scalar `8d/U_d`, this is the prime kernel obtained from PCOB's
`A_d` after inverse congruence reaches `u=d`.  Let

```text
S_n={p prime : n<p<=n^2},       M_n=sum_(p in S_n) h(p). (PLCCKU.2)
```

Then, for `n>=2`,

```text
3/2 (log n)^2 -117 log n -50 <= 2 log n M_n,             (PLCCKU.3)
```

so `M_n` is unbounded.  Moreover

```text
sum_(p,q in S_n) h(p)h(q)c(p,q)^3 >= (1/8) M_n^2.        (PLCCKU.4)
```

Consequently no bounded operator on `ell2(Primes)` has matrix coefficients `K(p,q)`.  Equivalently,
the raw endpoint finite-compression norms are unbounded.

## 3. Proof

Write

```text
A(N)=sum_(p<=N) (log p)^2/p,
B(N)=sum_(k<=N) Lambda(k)^2/k.
```

Corpus theorems `sum_prime_log_sq_div_ge` and
`abs_vonMangoldtHarmonicSquareSum_sub_le` give

```text
A(n^2) >= 2(log n)^2-78log n-25,
A(n) <= B(n) <= 1/2(log n)^2+39log n+25.
```

Subtracting gives a lower bound

```text
sum_(p in S_n) (log p)^2/p >= 3/2(log n)^2-117log n-50.
```

Since `log p<=2log n` on `S_n`, this is `(PLCCKU.3)`.  The right side divided by
`2log n` tends to infinity.

For `p,q in S_n`, their positive logarithms `x=log p` and `y=log q` lie in
`(log n,2log n]`.  Therefore

```text
sqrt(xy) >= log n,       x+y <= 4log n,
2sqrt(xy)/(x+y) >= 1/2.
```

Cubing and summing proves `(PLCCKU.4)`.  Apply the putative operator to the finite vector with
coordinates `sqrt(h(p))` on `S_n`.  Its squared norm is `M_n`, while its quadratic form is the
left side of `(PLCCKU.4)`.  The Rayleigh quotient is at least `(1/8)M_n`, contradicting boundedness.

## 4. Exact consequence

- Raw endpoint `T_(d,d)` is not a bounded completion-extension element.
- Trace normalization returns the already-known moving positive aperture family and cannot create
  a new index by itself.
- Surviving object must be a source-canonical closed unbounded relation with bounded transform or
  graph projection.  This is not permission to choose a regularization: closability, domain, and
  transform must be forced by the literal cubic Gram form.
- Next gate is to construct that relation and prove its bounded transform has a nonconstant
  source-framed quotient class.  If its quotient is the universal cone class, retire PHCCED.

## Lean certificate

- [x] 2 → 3: Lean `GaloisForLFunctions.RHTower.PrimeLogCriticalCubicKernelUnboundedness`, `GaloisForLFunctions.RHTower.PrimeLogCriticalCubicKernelNoBoundedOperator`; `lake env lean` + module build pass; axiom audit `[propext, Classical.choice, Quot.sound]` only

Modules `GaloisForLFunctions.RHTower.PrimeLogCriticalCubicKernelUnboundedness` (13 constants) and
`GaloisForLFunctions.RHTower.PrimeLogCriticalCubicKernelNoBoundedOperator` (11 constants, added 2026-09-28); axiom audit clean.

| Claim | Lean declaration |
|-|-|
| (PLCCKU.1) `h`, `c`, `K` | `primeLogCriticalWeight`, `primeLogCriticalCubicCorrelation`, `primeLogCriticalCubicKernel` |
| (PLCCKU.2) `S_n`, `M_n` | `primeLogCriticalBlock`, `primeLogCriticalPrimeBlock`, `primeLogCriticalBlockMass` |
| (PLCCKU.3) `3/2 (log n)² - 117 log n - 50 ≤ 2 log n M_n`; `M_n` unbounded | `primeLogCriticalBlockMass_growth`, `tendsto_primeLogCriticalBlockMass_atTop` |
| (PLCCKU.4) `∑ h h c³ ≥ M_n²/8` (via `c ≥ 1/2` on `S_n`) | `primeLogCriticalCubicCorrelation_ge`, `primeLogCriticalCubicRayleighNumerator_ge` |
| Rayleigh quotients unbounded | `not_exists_primeLogCriticalCubicRayleigh_bound` |
| test vector: `‖∑ √h(p) e_p‖² = M_n`, quadratic form = Rayleigh numerator | `primeLogCriticalTestVector`, `norm_sq_primeLogCriticalTestVector`, `inner_primeLogCriticalTestVector_apply` |
| no bounded operator on `ℓ²(Primes)` (real or complex) has matrix coefficients `K(p,q)` | `not_exists_bounded_operator_primeLogCriticalCubicKernel` |

## Log

- 2026-09-28 — Lean certificate audited; every numbered claim mapped to a declaration; moved to 3-formalized.
