# RP: exact arithmetic cusps of the unsigned dilation source

- **ID:** RP-28
- **Stage:** 5-failed
- **Type:** FALSIFIED (continuous kernel-shape candidate; not Route RP or RH)
- **Source:** Literal divisor source, its square-root cell interpolation, and its exact local increment.
- **Candidate:** Use eventual log-concavity of the unsigned dilation kernel as a joint-pair sign ingredient for timely Möbius assembly.
- **Novelty:** Corpus extension; external novelty unaudited.

## Hard problem and scope

The joint complementary Möbius source and smooth term remain unpaid at the critical normalization. The largest-prime decomposition retains two supercritical terms that must cancel jointly. Existing local payment, nested checkpoints, and initial Boolean signs do not bound the completed source at every original cutoff.

This attempt tests a proposed shape property of the actual unsigned source, before using it in a quadratic pair estimate. It does not establish that this shape property alone would imply RH. Failure of continuous log-concavity does not exclude an arithmetic-only inequality sampled at distinct prime ratios.

## Exact positive survivor

Write U(x)=divisorContinuousUnitHead(x), D(n)=primeFreeDivisorDefect(n), and

    b(n)=log(n)-tau(n)+2*gamma = D(n)-D(n-1).

The corpus supplies the exact interpolation U(x)=U(n)+(sqrt(x)-sqrt(n))*D(n) on [n,n+1]. Strict positivity at every integer n>=2 follows from the signed Abel identity: all cumulative D-prefixes are nonnegative, the first is strictly positive, and the half-order clock has a strictly positive first difference. Hence the first term alone gives a positive contribution to U(n).

For n>=2 define the actual multiplicative midpoint minor

    Q_n(t)=U(n*exp(-2t))*U(n*exp(2t))-U(n)^2.

For sufficiently small t>0, each argument stays in its original adjacent integer cell. Put A=U(n). The exact two branches are

    U(n*exp(-2t)) = A+sqrt(n)*D(n-1)*(exp(-t)-1),
    U(n*exp( 2t)) = A+sqrt(n)*D(n)  *(exp( t)-1).

Differentiate the product at zero from the right. The common A^2 term cancels and the slope is

    lim_(t down to 0) Q_n(t)/t = sqrt(n)*U(n)*b(n).

This is a signed arithmetic cusp law, retaining all three components of the forcing. Its sign is exactly that of b(n), since U(n)>0.

## Two cofinal opposite sign families

For a prime p, b(p)=log(p)-2+2*gamma>0 once p is sufficiently large. Infinitely many primes give arbitrarily late centers, and the positive slope gives Q_p(t)>0 on arbitrarily short positive windows. These are strict violations of multiplicative midpoint log-concavity.

For n=2^k, b(n)=k*log(2)-(k+1)+2*gamma. Since log(2)<1, this is negative for every sufficiently large k. Thus Q_(2^k)(t)<0 on arbitrarily short positive windows at arbitrarily late centers. The opposite eventual midpoint inequality fails too.

The same product minor applies to U(x)/sqrt(x): the two denominator factors multiply to n. No numerical experiment or sign certification at a finite list of primes is used.

## No-go closure

- **Retired:** Eventual continuous multiplicative midpoint log-concavity of the literal unsigned kernel, and its opposite sign extension.
- **Strongest positive survivor:** Strict integer positivity, the exact all-integer cusp formula, and cofinal prime/power-of-two families with opposite minor signs.
- **Surviving hard problem:** Joint signed payment of the arithmetic cusps and complementary source. Neither per-cell curvature sign nor unsigned global kernel concavity supplies that payment.
- **Limit:** No claim about failure of a discrete prime-grid Rayleigh inequality; no RH proof or falsification; neither native square debt is paid.
- **Lean status:** `RoutePUnsignedSourceCusp.lean` (228 lines, seven public theorems) passed final foreground `lake --old env lean <leaf> -o <olean>`, exit 0 without diagnostics. A separate `/tmp` axiom audit passed: all seven lists are exactly `[propext, Classical.choice, Quot.sound]`. Wired once into RHTower; no umbrella build. Index refresh passed. Global lint fails on ten unrelated unreachable modules; this leaf is unflagged.

## Log

- 2026-10-02 — Retrieved current timely-assembly frontier, tested the exact source's shape, derived the coefficient-exact cusp law and two opposite cofinal sign families.
- 2026-10-02 — Final leaf and all seven axiom audits passed. Retired only the continuous kernel-shape ingredient, with the exact signed arithmetic cusp law retained as the positive survivor.
