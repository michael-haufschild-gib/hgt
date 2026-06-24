# Euler-Factor Degree-Ladder Audit

- **ID:** euler-factor-degree-ladder-audit
- **Stage:** 0-backlog
- **Type:** AUDIT / KILL-GATE
- **Source:** W4 Euler-factor Riccati / degree-doubling chat claim, 2026-06-23
- **Verdict:** KILL as promoted knowledge unless a precise invariant and minimality theorem are supplied.

## Candidate

For finite Euler products

`F_k(s) = prod_{j=1}^k (1 - exp(-c_j s))^{-1}`,

each factor satisfies a Riccati equation. The proposed claim was that the product has a degree `2^k` algebraic ODE and that this gives a precise complexity ladder to hypertranscendence at `k = infinity`.

## What Is Correct

For one factor

`f(s) = 1/(1-exp(-c s))`,

there is a first-order nonlinear algebraic differential equation:

`f' = c(f^2 - f)` up to the sign convention for `c`.

Thus each finite product is differentially algebraic: introduce the finitely many factor variables and eliminate them from their Riccati system.

## Corrections

1. **DA is not D-finite.** Over `C(s)`, `f` has infinitely many poles at `s = -2*pi*i*n/c`. A nonzero D-finite meromorphic function over `C(s)` has finite singularities only among the finite zero set of the leading coefficient. So the Euler factor is DA, not D-finite.

2. **The Galois story was wrong.** The natural differential Galois group of `exp(-c s)` is multiplicative, not `{±1}`. The proposed `({±1})^k` / group-size `2^k` explanation is not a valid source of the degree ladder.

3. **`2^k` is not a canonical invariant as stated.** Nonlinear algebraic ODEs are not unique. Different eliminations, higher orders, extraneous factors, and different degree conventions can change the observed degree. One must specify degree in the highest derivative, total differential-polynomial degree, order-degree pair, irreducibility, and base field.

4. **Direct k=2 elimination contradicts the simple reading.** Eliminating two hidden Riccati factors from `Y=gh`, `Y'`, and `Y''` gives an order-2 relation quadratic in `Y''`, not degree 4 in the highest derivative. Therefore the naive `2^k` claim cannot be promoted as the minimal highest-derivative degree.

## Theatre-Test Status

Steelman promptability check with singularity reasoning gives the DA / non-D-finite distinction immediately and rejects `2^k` as noncanonical without definitions.

Current conclusion:

- `S`: finite Euler products are DA by finite Riccati systems.
- `P`: first-order Riccati equations plus elimination.
- `M`: label stripping exposes DA-vs-D-finite and degree-convention ambiguity.
- `T`: missing. The route reduces to known finite-prime DA versus infinite-prime HT structure unless a new invariant is defined and proved minimal.

## Rescue Condition

To revive the idea, state a precise invariant:

1. base differential field;
2. allowed order;
3. degree notion;
4. irreducibility/minimality criterion;
5. proof that the invariant equals `2^k` generically;
6. proof that it changes something about the infinite-prime HT transition beyond the known "finite primes DA, infinite primes HT" story.

Until then: KILL as novel/significant knowledge.
