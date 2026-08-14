# Route P primitive collision subquantum

- **ID:** `route-p-primitive-collision-subquantum`
- **Label:** P-G175
- **Stage:** 1-in-progress
- **Type:** OWN CONJECTURE / THEOREM (Lean) / SHARP SOURCE CAPACITY GAP
- **RH status:** open
- **Computation used:** no
- **Parent:** `route-p-primitive-collision-trace-budget.md`
- **Lean target:**
  `formal/GaloisForLFunctions/RHTower/RoutePPrimitiveCollisionSubquantum.lean`

## Conjecture

P-G174 leaves its global source trace budget as an unevaluated convergent series. The zero-side
cubic collision diagonal at horizontal displacement `0<a<=1/2` obeys

```text
C_R(a,a;0)=115/(864a^3) >= 115/108.                    (175.1)
```

Conjecture: the entire primitive Euler source budget is already strictly smaller than the
right-hand side of `(175.1)`:

```text
B_P := sum_(p prime,e>=0)
  115/[864(e+1)^3 p^(e+1)(log p)^2] < 115/108.         (175.2)
```

If the missing completed incidence is trace-nonincreasing, `(175.2)` excludes even one off-line
zero. Thus completed carrier transport would now close RH directly; no `N/4`, density, or
full-line amplification layer remains.

## Proof

For `x>=2`, the function

```text
f(x)=1/[x(log x)^2]
```

is decreasing. Integral comparison and the exact improper integral give

```text
sum_(n>=3) 1/[n(log n)^2] <= integral_2^infinity f(x) dx = 1/log 2.
```

Mathlib's certified inequality `9/10<log 2` implies the weaker rational estimate
`2/3<log 2`. Consequently

```text
1/[2(log 2)^2] < 2,       1/log 2 < 2,
sum_(n>=0) invNatLogSq(n) < 4.                          (175.3)
```

The primitive weight satisfies the pointwise geometric majorant

```text
w(p,e) <= (115/864) invNatLogSq(p) (1/2)^e.
```

Summing depth exactly and injecting primes into natural numbers yields

```text
B_P
 <= (115/432) sum_(p prime) invNatLogSq(p)
 <= (115/432) sum_(n>=0) invNatLogSq(n)
 < (115/432) 4
 = 115/108.
```

Every step is symbolic; no finite cutoff or numerical evaluation occurs.

## Higher principle

The cubic exponent does more than repair summability: it creates a **subquantum source**. One
completed primitive carrier contains less total cubic trace than the least indivisible
strict-right zero charge. Earlier `N/4` and `75%` receivers were shadows of leaving the total Euler
capacity unevaluated. After exact capacity comparison, Route P becomes a zero-or-one exclusion
problem rather than a density problem.

## Novelty and anti-theatre audit

The summability of the cubic Euler weight and the zero-side quantum predate this card. P-G175's new
content is their strict global comparison, with a closed rational margin and no prime computation.
Corpus search found no prior theorem evaluating this primitive trace budget against one cubic zero
quantum.

This is not RH. It proves a capacity gap between two still-distinct carriers. Without an exact
completed coefficient-faithful incidence/contraction, spending `B_P` on zero trace is invalid.
Replacing that missing map by equality of scalar constants, a post-divisor hypothesis, or an
RH-equivalent transport interface would be theatre.

## Lean certificate

`RoutePPrimitiveCollisionSubquantum.lean` proves:

- `routePInvLogSqContinuous_antitoneOn`
- `tsum_invNatLogSq_lt_four`
- `routePPrimitiveCollisionCubicTraceBudget_lt_quantum`

Scratch and single-module targeted compilation passed. Axiom audit reports only `propext`,
`Classical.choice`, and `Quot.sound`; forbidden-token scan is clean. Umbrella import is wired and
umbrella is intentionally not built.

## Gates

- [x] symbolic monotonicity and improper-integral tail
- [x] ambient integer logarithmic series `<4`
- [x] geometric prime-depth majorant summed exactly
- [x] primitive source budget `<115/108`
- [x] targeted compile, forbidden-token scan, and axiom audit
- [x] umbrella import wired without umbrella build
- [ ] completed coefficient-faithful trace contraction
- [ ] unconditional RH closure

## Log

- 2026-08-14 — Proved exact subquantum source capacity in Lean. This removes every
  positive-proportion/amplification debt after carrier transport and sharpens Route P's sole hard
  seam to one completed coefficient-faithful trace contraction.
