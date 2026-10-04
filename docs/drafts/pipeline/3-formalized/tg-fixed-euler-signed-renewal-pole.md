# TG: actual signed Euler renewal and its harmonic pole

- **ID:** TG-C9.23
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** Route TG, C9.20 arithmetic admission; `CCMPrimeDeficitEulerRenewal` and `CCMPrimeDeficitDilationSourceBounds`.
- **Statement:** Every fixed positive Euler modulus excites a strictly positive logarithmic exponential pole in the actual signed renewal; the full finite source Hessian has an exact rank-one leading term and harmonic-neutral nullspace.

## Exact statements

Write D for `ccmLogChebyshevDeficitPrimitive`, F for
`ccmPrimeDeficitDilationSource`, H for `ccmPrimeDeficitDivisorSource`,
and c = Euler's constant + 1. Then

`H(T)/(T exp(T)) -> c`.

For every finite labelled set S, arbitrary real coefficients v and arbitrary
real shifts u, retain the complete form

`Q(T) = sum_(i,j in S) v_i v_j H(T-u_i-u_j)`.

Its limit is

`Q(T)/(T exp(T)) -> c (sum_(i in S) v_i exp(-u_i))^2`.

The normalized form tends to zero **if and only if** the displayed signed
moment vanishes. For shifts `u_i = log n_i`, this is precisely the harmonic
moment `sum v_i/n_i`. No pair terms are discarded, and no sign hypothesis
on v is imposed.

For every fixed positive integer P, the unchanged finite Euler action A_P
and the actual rough-squared renewal R_P of D satisfy

`A_P(T)/(T exp(T)) -> -c (totient(P)/P)^2`,

`R_P D(T)/(T exp(T)) -> c (totient(P)/P)^2`.

Neither A_P nor R_P D admits a uniform absolute bound C exp(T). The latter
is evaluated on the literal signed Chebyshev primitive; it is stronger
than the pre-existing obstruction for positive comparison profiles.

## Dependency-closed paper proof

1. The admitted elementary source estimate gives
   `F(T)=c exp(T)+O(1+T^2)` on T >= 0. The exponential series bounds the
   complete remainder by `K exp(T/2)` with a fixed K; no arithmetic error
   estimate is inserted.
2. The exact divisor-source identity is
   `H(T)=sum_(1<=n<=floor(exp T)) F(T-log n)`. Every included delay is
   nonnegative. Its total error is at most
   `K exp(T/2) sum_(n<=floor(exp T)) 1/sqrt(n) <= 2K exp(T)`.
   The main term is `c exp(T)` times the harmonic sum. The harmonic error
   and `floor(exp T) <= exp T < floor(exp T)+1` give
   `harmonic(floor(exp T))-T=O(1)`. Thus
   `H(T)=c T exp(T)+O(exp(T))`, proving the first limit.
3. For each fixed shift u, the ratio `(T-u)/T` tends to one and
   `exp(T-u)/exp(T)=exp(-u)`. Finite sums preserve limits. Applying this
   to both labels yields the exact square of the signed exponential
   moment. Since c > 0, uniqueness of limits identifies the nullspace.
4. At all sufficiently large T for a fixed P, the two Euler coefficient
   sums contain every divisor of P. The literal action becomes
   `2 sum_d mu(d) F(T-log d) - sum_(d,e) mu(d)mu(e) H(T-log d-log e)`.
   The first term is O(exp(T)); the second has the rank-one pole above.
   Möbius inversion of `sum_(d|P) totient(d)=P` proves
   `sum_(d|P) mu(d)/d=totient(P)/P>0`.
5. The elementary Chebyshev estimate gives `|D(T)|<=C_0 exp(T)`. The
   corpus's exact renewal identity `R_P D=D-A_P` therefore gives the
   stated positive limit for the unchanged signed residual. Any putative
   C exp(T) bound would force its normalized limit to zero, contradicting
   the strictly positive coefficient.

## Positive survivor and remaining frontier

The survivor is the exact rank-one law and its full harmonic-neutral
nullspace, proved in the same leaf as the obstruction. It identifies which
finite signed coefficient directions cancel the leading source pole.
This is not a native prime-count energy estimate.

The fixed-P limit cannot be exchanged with a moving modulus. In particular,
the existing factorial-half identity makes the adaptive Euler action equal
to D at its prescribed horizon. The next TG arithmetic attempt must control
that actual moving signed source, retaining the harmonic correction and
all unequal-label covariance terms. Native energy summability, completed
joint Hardy cubic compatibility, and strict contraction remain open.

## Lean certificate

Leaf: `formal/GaloisForLFunctions/RHTower/CCMPrimeDeficitEulerSignedPole.lean`.
Seven public theorems, including `ccmPrimeDeficitDivisorSource_finite_pair_pole_limit`,
`ccmPrimeDeficitDivisorSource_finite_pair_pole_vanishes_iff`, and
`ccmPrimeDeficitEulerSignedRenewal_not_exponential_bound`.

- Foreground final `lake --old env lean` with explicit leaf output: exit 0,
  no diagnostics; `/tmp/tg-c923-signed-pole-final.log`.
- Separate `/tmp` foundations audit: all seven declarations depend only on
  `propext`, `Classical.choice`, `Quot.sound`; exit 0;
  `/tmp/tg-c923-signed-pole-axioms.lean` and `.log`.
- Wired into `formal/GaloisForLFunctions/RHTower.lean`; no umbrella build.
- Index exit 0; all seven names verified in `formal/LEAN_API.md`;
  `/tmp/tg-c923-signed-pole-index.log`.
- Authoritative lint exit 1: 15 unrelated unreachable modules, no finding
  in this leaf; `/tmp/tg-c923-signed-pole-lint.log`.
- No numerical experiments, added axioms, proof holes, heartbeat overrides,
  full builds, commits, or subagents.

## Log

- 2026-10-04: Corpus searches and actual source proofs supplied no native
  cancellation estimate. The fixed-Euler signed-absorption attempt instead
  exposed the source pole above. Both the obstruction and its strongest
  established positive survivor are now formalized. RH remains unresolved.
