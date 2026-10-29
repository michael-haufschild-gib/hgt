# Explicit inverse-log-cube decay of greatest prime-tail gaps

- **ID:** ACP-PRIME-TAIL-GAP-RATE
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Parent:** ../3-formalized/arithmetic-counting-finite-prime-energy-moment.md
- **Lean:** `PrimeTailGapsHaveAnInverseLogCubeBound.lean`

## Statement

Let F_BQ consist of primes B<p<=Q. Write C1=mertensFirstConst,
C2=mertensSecondLowerConst, S_B=sum_(p<=B)1/p, and
`D_B=exp(2(C2+1+S_B))>0`. Then

`c_(F_BQ)<=D_B/(log Q)^2` for Q>=2,

`M_(F_BQ)<=(16/3)(log Q+C1)` for Q>=1,

and, for each fixed B, eventually

`delta_(F_BQ)<=(64/3)D_B^2/(log Q)^3`.

Thus the actual attained greatest hyperplane gaps have an explicit
O_B((log Q)^(-3)) upper bound. Each finite stage still has a positive gap.

## Complete proof

For every prime p, the shifted-reciprocal correction satisfies
`1/p-1/(p+1)=1/(p(p+1))<=1/(p(p-1))`.
Extend the nonnegative correction sum to all integers 2<=k<=Q. The already
proved telescoping identity bounds it by `1-1/Q<=1`. Hence
`sum_(p<=Q)1/(p+1)>=S_Q-1`. Removing primes at most B costs at most S_B,
including when Q<B. The elementary Mertens lower bound therefore gives

`sum_(p in F_BQ)1/(p+1)>=log log Q-(C2+1+S_B)`.

Each density factor is positive and
`log((p-1)/(p+1))<=((p-1)/(p+1))-1=-2/(p+1)`.
Sum logarithms of the finite product and exponentiate, using log Q>0.
This proves the stated density bound with the explicit constant D_B.

For p>=2, clearing positive denominators gives
`4p/(p^2-1)<=16/(3p)`, equivalent to p^2>=4. Multiplying by log p>=0,
summing over F_BQ, and extending to all primes at most Q yields
`M_(F_BQ)<=(16/3)sum_(p<=Q)log p/p`.
The elementary first Mertens bound gives the asserted moment estimate.

Since log Q tends to infinity, eventually
`log Q>=max(1,C1,2D_B)` and Q>=2. Then log^2 Q>=log Q>=2D_B, so the
density bound gives `0<c_(F_BQ)<=1/2`. This forces F_BQ nonempty. Thus the
already formalized first-moment gap bound applies. Also
`c^2/(1-c^2)<=2c^2` and `M<=(32/3)log Q`, with M>=0. Consequently

`delta<=c^2 M/(1-c^2)<=2c^2 M
 <=2 D_B^2/(log Q)^4 * (32/3)log Q
 =(64/3)D_B^2/(log Q)^3`.

Every comparison uses nonnegative factors and explicitly positive
denominators. No limit exchanges between integer horizon and prime cutoff
are used. All analytic inputs are existing unconditional Mertens theorems;
no prime number theorem or numerical experiment is required.

## Lean closure

The three public endpoints are
`finiteFlipHarmonicDensity_primeTail_le`,
`finiteFlipConductorEnergyMoment_primeTail_le`, and
`eventually_primeTailGreatestGap_le_inverse_log_cube`.
The explicit constant is `primeTailDensityConstant`.

Scratch 40081 and canonical 72117 exited zero without diagnostics. All three
transitive axiom lists contain only `propext`, `Classical.choice`, and
`Quot.sound`. Exact commands, source hash and actual output are retained in
`arithmetic-counting-prime-tail-gap-rate-audit.txt`.

The moment and qualitative prime-tail leaves received their first oleans
only because the actual rate draft imported them. Existing Mertens oleans
were preserved. No umbrella was compiled.

- [x] Dependency-complete paper proof and explicit constant.
- [x] Exact Lean endpoints, canonical check and transitive axiom audit.
- [x] Stage-three card, README, umbrella and durable evidence.

Arbitrary infinite prime sets, source selection among all multiplicative
weights, and complete-source positivity remain separate obligations. This
is an upper rate for each fixed lower prime cutoff, not a sharp asymptotic
or a bound uniform in growing B.
