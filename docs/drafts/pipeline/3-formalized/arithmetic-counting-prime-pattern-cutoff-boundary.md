# Positive Euler density is exactly harmonic cutoff completeness

- **ID:** ACP-PRIME-PATTERN-CUTOFF-BOUNDARY
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Parent:** ../1-in-progress/arithmetic-counting-positivity.md
- **Lean target:** PositiveEulerDensityIsExactlyHarmonicCutoffCompleteness.lean
- **Input:** ../3-formalized/arithmetic-counting-all-prime-pattern-harmonic-density.md

## Exact statements

Let P be any prime pattern, F_Q its finite prime cutoff, c_Q>0 the finite
Euler density and c>=0 the full Euler density. Write

D(P,Q,N)=sum_(1<=n<=N)(omega_P(n)-omega_(F_Q)(n))^2/(n H_N).

The exact statements are:

1. D(P,Q,N)=0 whenever N<=Q, including N=0.
2. The residual pattern P without primes at most Q has density c/c_Q.
3. For every N>=1, D(P,Q,N)=2(1-C_tail(N)).
4. For every fixed Q, D(P,Q,N)->2(1-c/c_Q) as N increases.
5. The following equivalence holds without any hypothesis on P:

   [for every epsilon>0, there is Q0 such that for every Q>=Q0,
    eventually in N, D(P,Q,N)<epsilon] if and only if c>0.

The eventual integer horizon may depend on Q. No simultaneous uniform
horizon for all cutoffs is required or asserted.

## Density factorization

For N>=Q the finite visible prime set is the disjoint union of F_Q and
the visible residual primes. The finite densities therefore satisfy

c_(tail,N)*c_Q=c_(P,N).

Both density sequences have the already proved Euler-product limits.
Taking the limit in this identity gives c_tail*c_Q=c. Since c_Q>0,
c_tail=c/c_Q, also when c=0. No reciprocal mass condition is assumed.

## Exact squared distance

The sign decomposes pointwise as omega_P=omega_(F_Q)*omega_tail. Every
factor squares to one, including the zero coordinate. Consequently

(omega_P(n)-omega_(F_Q)(n))^2=2(1-omega_tail(n)).

Sum against 1/n and divide by H_N>0 for N>=1. This gives the exact distance
identity. The arbitrary-pattern harmonic-mean theorem for the residual
pattern, followed by the density factorization, yields the fixed-Q limit.

For the other order of exhaustion, N<=Q ensures all prime divisors of
every n<=N are present in the finite prime cutoff. The full and truncated
signs agree term by term. Thus D=0 exactly, including the empty horizon.

## Completeness boundary

If c>0, then c_Q->c gives c/c_Q->1, so
2(1-c/c_Q)->0 as Q increases. Given epsilon>0, all sufficiently large Q
have limiting squared distance strictly below epsilon. For each such Q,
the fixed-Q distance limit makes the actual squared distance eventually
less than epsilon. This is precisely the stated completeness property.

Conversely, if c is not positive then c=0, since c>=0. For every fixed Q,
the actual squared distance then tends to two. The completeness property
with epsilon=1 would produce a fixed Q with eventual squared distance
less than one. Passing to its limit would give 2<=1, a contradiction.

Thus the order of exhaustion is sharply classified: fixed-horizon prime
cutoffs always become exact, while taking the integer-horizon limit first
and then increasing prime cutoffs gives zero for c>0 and two for c=0.

## Scope and audit

This strengthens the reciprocal-mass upper bound to an exact asymptotic
error and a necessary-and-sufficient harmonic approximation criterion.
It supplies the metric boundary needed before any infinite spectral
transfer. It does not transfer an unbounded quadratic form merely from
norm approximation, determine the optimal gap at c=0, or prove complete
Weil positivity.

The input's four endpoints passed both standard-axiom and canonical
installed-source audits. This exact
five-endpoint result has its matching full Lean draft at
/tmp/acp-prime-pattern-cutoff-boundary-check.lean; no unproved analytic
assumption is added to any target.

- [x] Complete paper proof, including both product regimes and limit orders.
- [x] Immediate full Lean draft with the same five endpoints.
- [x] Scratch and transitive axiom audit.
- [x] Canonical source check, umbrella and durable evidence.

## Lean endpoints and audit

PositiveEulerDensityIsExactlyHarmonicCutoffCompleteness.lean proves
primeSetCutoffDistanceSq_eq_zero_of_le, primeSetHarmonicDensity_tail,
primeSetFlip_cutoff_distance_sq_eq, primeSetFlip_cutoff_distance_sq_tendsto
and primeSetFlip_harmonic_cutoffs_complete_iff. Scratch 62197 and canonical
96931 exited zero without diagnostics. All five transitive audits use only
propext, Classical.choice and Quot.sound. The adjacent audit preserves the
commands, source SHA256 and actual axiom output.
