# Canonical square-root core: quadratic bound fails

- **ID:** SZ-CANONICAL-SQUARE-ROOT-CORE
- **Stage:** 5-failed
- **Type:** FALSIFIED
- **Source:** `docs/reports/rh-current-frontier-map.md`, route SZ.
- **Statement:** Processing exactly the active primes with `p²≤N` does not give a uniform `O(N²)` bound for the literal selection energy.

## Exact result

Let `P_N={p∈mobiusDivisorSelectionPrimes N : p*p≤N}`. For every real C and natural N₀, there is an integer N≥max(N₀,2) such that

`C*N² < mobiusDivisorSelectionEnergy N P_N`.

The strict `<N` convention of `mobiusDivisorSmallSelectionPrimes` is not silently substituted for this core. No conclusion about all adaptive cores, or about RH, follows.

## Dependency-closed paper proof

Write A for the literal critical Abel source, F for its all-prime head, and
`G(x)=Σ_{p²≤x}sqrt(p)*A(x/p)`. The actual moving head is `R=A+Re F-G`.
With `M_R(δ)=∫₁∞x^(-5/2-δ)R(x)dx`, the source identities and endpoint
admission give

`(M_R(δ)+T_G(0))/(δ*log(1/δ)) → H/3 > 0`.

Here H is the literal divisor harmonic boundary. A has a finite simple
Mellin jet; G has a finite right slope. Thus neither removes F's positive
logarithmic jet. The nonzero baseline `-T_G(0)` is retained.

If R(x)≥-Kx globally, the nonnegative compensated source R(x)+Kx would give
a decreasing Mellin transform `M_R(δ)+K/(1/2+δ)`. Its right-boundary value
is finite, while the centered jet gives infinite positive right slope, a
contradiction. Finite-source local boundedness makes the negative linear
excursions cofinal.

For N≤x<N+1, exact old-prime cancellation gives

`R(x)-R(N)=(sqrt(x)-sqrt(N))*(psiDefect(N)+Σ_{p≤N,N<p²}psiDefect(N/p))`.

The quotient in psiDefect is natural division. The corpus's unconditional
linear defect bound gives a uniform O(N) cell-variation bound: each
surviving quotient N/p is at most sqrt(N), and
`(sqrt(x)-sqrt(N))*sqrt(N)≤1`. Applying continuum escape at an increased
linear level therefore gives `R(N)<-B*N` at arbitrarily large integers for
every B. This argument does not cross a prime-square jump.

The actual terminal-source identity identifies R(N) with the fibre at
P_N. The extra endpoint prime p=N in the continuous finite sum has A(1)=0.
Selection energy contains the square of this fibre, so choosing B>0 with
B²>C proves the result.

## No-go closure

- **Killing theorem:** `RHTower.criticalMovingSquareCore_energy_escape` in `MobiusDivisorCriticalMovingCoreObstruction.lean`.
- **Positive survivor:** exact centered logarithmic Mellin classification, exact source interpolation on every half-open integer cell, and a simultaneous signed correction law for all extensions at the escaping cutoffs. These retain the actual source, prime-square convention and boundary mass.
- **Signed correction law:** for every B,C,N₀ there is one N≥max(N₀,2) such that every set U of unprocessed active primes satisfies either `head(P_N∪U)<-B*N` or `Σ_{p∈U}sqrt(p)*A(N/p)<-C*N`. The proof uses the exact balance `head(P_N∪U)=R(N)-Σ_U sqrt(p)*A(N/p)`. Thus a bounded-head extension must process negative signed child mass; an unsigned or positive-child-only correction cannot supply the required repair.
- **New insight:** the canonical threshold already has superlinear negative head excursions at its own integer cutoff. Adaptive source control must include this signed admission cost together with mixed correlations and old-cutoff transport.
- **Status:** complete paper arguments and five directly checked Lean leaves. The final combined API/axiom audit exited successfully; all eighteen exported theorem axiom queries report only `propext`, `Classical.choice`, `Quot.sound`. No external review claimed. The latest global lint reports eleven unrelated unreachable modules and no forbidden declarations.

## Formal sources

- `formal/GaloisForLFunctions/RHTower/MobiusDivisorCriticalMovingHeadMellin.lean`
- `formal/GaloisForLFunctions/RHTower/MobiusDivisorCriticalMovingHeadNegativeEscape.lean`
- `formal/GaloisForLFunctions/RHTower/MobiusDivisorCriticalMovingHeadFiniteSource.lean`
- `formal/GaloisForLFunctions/RHTower/MobiusDivisorCriticalMovingHeadIntegerEscape.lean`
- `formal/GaloisForLFunctions/RHTower/MobiusDivisorCriticalMovingCoreObstruction.lean`

All five leaves are wired into RHTower. Audits used one foreground
`lake --old env lean <leaf> -o <olean>` process at a time. No full or umbrella
build, numerical experiment, additional axiom, heartbeat increase, commit
or push was used.

## Log

- 2026-10-02 — exact canonical-core no-go and source survivors formalized; full SZ signed-residual/Wronskian estimate remains open.

## Pointwise positive survivor, 2026-10-02

The stronger source conjecture is now formalized without premises:

`R(x)*log(x)^2/x^(3/2) → -H/3`, where `H=divisorHarmonicBoundary>0`.

This is a direct source asymptotic, not a converse inference from the Mellin
jet. Put `a(t)=exp(-3t/2)*A(exp t)` and let v be its actual right derivative.
The admitted quadratic source moments give `integral a=0`,
`integral t*a=-H/3`, and integrability of `(1+t^2)*v`. The exact finite
primitive and integrability of a force `integral v=0`; consequently
`a(t)=-integral_t^infinity v` and `t^2*a(t)->0`.

Old-prime cancellation leaves the exact late-prime convolution. Finite
interchange identifies it with
`integral_0^(t/2) v(s)*(mertensS(floor(exp(t-s)))-mertensS(floor(exp(t/2)))) ds`.
The actual Mertens remainder E satisfies `u^2*E(u)->0`, including the real
floor correction. Its scaled increment has the fixed integrable majorant
`8*|v(s)|`, hence contributes zero in the limit. Right-derivative integration
by parts turns the remaining logarithmic increment into
`integral_0^(t/2) a(s)/(t-s) ds`, with both boundary products zero.

Subtracting `t*a(s)` inside the scaled Cauchy integrand preserves the exact
zero mass. The compensated integrand converges to `s*a(s)` and has an
admitted fixed majorant. Its integral therefore tends to `-H/3`. Combining
the actual source identities proves the stated all-real-cutoff limit.

Eight directly audited and wired leaves contain 23 public theorems:
`MobiusDivisorCriticalLogProfile`, `MobiusDivisorCriticalLogProfilePrimitive`,
`MobiusDivisorCriticalLogProfileTail`, `MobiusDivisorCriticalCompensatedCauchy`,
`MobiusDivisorCriticalPrimeTailSource`, `MobiusDivisorCriticalMertensLogError`,
`MobiusDivisorCriticalPrimeTailError`, and `MobiusDivisorCriticalMovingHeadAsymptotic`.
All 23 axiom queries, plus the arithmetic Mertens input, return only
`propext`, `Classical.choice`, and `Quot.sound`. The final theorem is
`RHTower.tendsto_criticalMovingPrimeHead_pointwise_scaled`.

The survivor determines the actual signed correction scale. It does not
bound cumulative signed mixed products at original cutoffs, prove the
source Wronskian estimate, or decide RH.
