# Terminal-conditioned Xi valuation aperture metric

- **ID:** `xi-terminal-conditioned-true-aperture-hilbert-metric`
- **Stage:** `3-formalized / needs-audit`
- **Type:** THEOREM / POSITIVE SURVIVOR / RH-PROOF-SHAPE RECUT
- **Scientific status:** `[PROVED HERE] [FORMALIZED UNCONDITIONALLY IN LEAN]`
  `[CANDIDATE NEW RH-PROOF-SHAPE KNOWLEDGE] [SOURCE-SPECIFIC ASSEMBLY]`
  `[PARENT SZEGŐ/RKHS ALGEBRA STANDARD] [EXTERNAL SOURCE-SPECIFIC NOVELTY UNVERIFIED]`
- **Parents:** `XiMobiusContinuousApertureSzegoMetric.lean`,
  `XiTransversePrimeSourceProjectiveTangent.lean`, the physical low/high response-joining no-go,
  and the oriented physical-aperture Brownian-bridge metric.

## Exact theorem

Fix a prime `p`, a terminal aperture `A>0`, and put

```text
c_p = p^(-1)/(1+p^(-1)),
x_a = p^(-a),
K_p(a,b) = c_p^2 (1-x_a)(1-x_b)/(1-x_a x_b).
```

The live Lean theorem identifies `K_p` with the completed Gram of the actual continuous
Möbius--Schur valuation differences.  Remove the terminal ray by its Hilbert projection:

```text
K_(p,A)^perp(a,b)
 = K_p(a,b)-K_p(a,A)K_p(A,b)/K_p(A,A).                 (TC1)
```

The exact factorization is

```text
K_(p,A)^perp(a,b)
 = c_p^2 (1-x_a)(1-x_b)(x_a-x_A)(x_b-x_A)
     / ((1-x_a x_b)(1-x_a x_A)(1-x_b x_A)).            (TC2)
```

Equivalently, with

```text
d_(p,A)(a)=c_p (1-x_a)(x_a-x_A)/(1-x_a x_A),
```

one has

```text
K_(p,A)^perp(a,b)=d_(p,A)(a)d_(p,A)(b)/(1-x_a x_b)
                 =sum_(e>=0) d_(p,A)(a)x_a^e
                              d_(p,A)(b)x_b^e.           (TC3)
```

For `0<a,b<A` the metric is strictly positive, while `a=A` or `b=A` is exactly its terminal
radical.  More strongly, terminal conditioning changes no projective aperture angle:

```text
Kperp(a,b)^2/(Kperp(a,a)Kperp(b,b))
 = (1-x_a^2)(1-x_b^2)/(1-x_a x_b)^2.                   (TC4)
```

The right side is the normalized correlation of the unconditioned true-aperture metric.

There is also an exact quantitative radial law.  Put

```text
delta_(p,A)(a)=(x_a-x_A)/(1-x_a x_A).
```

Then for `0<a<A`,

```text
0<delta_(p,A)(a)<x_a=p^(-a),                             (TC5)
K_(p,A)^perp(a,a)=K_p(a,a) delta_(p,A)(a)^2
                 <p^(-2a) K_p(a,a).                     (TC6)
```

Thus terminal joining supplies a strict additional prime-aperture power at every fixed positive
aperture.  The gain degenerates only in the non-uniform tangent regime `a -> 0+`, which is now the
precise remaining radial boundary rather than an unspecified correlation problem.

## Paper proof

Substitute the displayed rational form of `K_p` into `(TC1)`.  The common factor `c_p^2` remains
after division by `K_p(A,A)`.  On a common denominator, the only nontrivial numerator is

```text
(1-x_a x_A)(1-x_b x_A)
  -(1-x_A^2)(1-x_a x_b)
 = (x_a-x_A)(x_b-x_A).
```

This proves `(TC2)`, and geometric summation proves `(TC3)`.  Since `a<A` implies
`0<x_A<x_a<1`, every factor in `(TC2)` is positive in the interior.  At the terminal aperture one
factor vanishes.  Finally all four terminal radial factors cancel from the normalized quotient,
leaving `(TC4)`.

## Scientific consequence

The physical response join is a rank-one conditioning, not an uncontrolled cancellation of two
Jordan masses.  In the actual Xi valuation Hilbert geometry it removes exactly the terminal radial
mode and preserves every normalized pseudohyperbolic aperture correlation.  Therefore no RH gain
can come from terminal/constant-mode joining alone.  Any successful source-to-response theorem
must change or control the radial weights across primes while retaining the already-faithful
transverse aperture angles.

This is stronger than saying that a Schur complement is positive.  The source-specific content is
closure inside the same weighted Szegő family and the exact invariance of the normalized aperture
correlation.  The underlying RKHS/Blaschke algebra is standard parent theory, so broad external
novelty is not claimed without a separate audit.

## Gates

- [x] exact live source metric identified
- [x] false transfer from the unrelated `{0,1,4}` Toeplitz protection rejected
- [x] dependency-closed algebraic paper proof written
- [x] hostile proof audit in Lean
- [x] permanent unconditional Lean formalization
- [ ] external source-specific novelty audit

## Lean realization

The permanent module
`formal/GaloisForLFunctions/RHTower/XiMobiusTerminalConditionedApertureMetric.lean` proves:

1. `xiMobiusPrimeTerminalConditionedApertureMetric_eq_factorized` -- `(TC2)`;
2. `tsum_xiMobiusPrimeTerminalConditionedApertureFeature_mul_eq_metric` -- the canonical Hilbert
   feature realization `(TC3)`;
3. both terminal radical laws and strict positivity of every interior diagonal;
4. `xiMobiusPrimeTerminalConditionedAperture_metricRatio_eq_correlation` -- `(TC4)`.
5. `xiMobiusPrimeTerminalConditioningGain_lt_diskNode` and
   `xiMobiusPrimeTerminalConditionedApertureMetric_self_lt_diskNode_sq_mul` -- the strict
   extra-aperture-power law `(TC5)`--`(TC6)`.

The direct Lean check and exact module build pass.  The axiom audit reports only `propext`,
`Classical.choice`, and `Quot.sound` for all headline declarations.  The module is imported by the
`RHTower` umbrella.

## Log

- 2026-07-19 -- Rejected transfer from the unrelated protected `{0,1,4}` Toeplitz kernel to the
  three-node Euler response.  Pivoted through the full HT valuation source geometry and identified
  terminal conditioning as the exact missing representation change.
- 2026-07-19 -- Proved and formalized the terminal Schur factorization, its geometric-depth Hilbert
  realization, terminal radical, interior positivity, and normalized-correlation invariance.
- 2026-07-19 -- Extracted the stronger radial theorem: the terminal Blaschke gain is strictly below
  `p^{-a}`, so the conditioned diagonal has an additional `p^{-2a}` suppression.  This moves the
  open core to uniform control of the tangent regime `a -> 0+`.
