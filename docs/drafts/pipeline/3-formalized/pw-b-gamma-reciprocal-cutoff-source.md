# PW-B original reciprocal source and retained cutoff bounds

- **ID:** PW-B-GAMMA-RECIPROCAL-CUTOFF-SOURCE-2026-09-11
- **Status:** Eighteen public theorems passed scratch verification and the targeted leaf build (43 seconds). Final index and repository formal lint passed.
- **Route:** PW-B remains live. RH is not proved.
- **Depends on:** [complete signed moment detector](pw-b-gamma-moment-detector.md).
- **Continuation:** [actual reversible pairing](../1-in-progress/pw-b-gamma-reversible-pairing.md).

## Exact original source

For every complex z, write

`S_z(t)=M_z(1/t)/Q(1/t)-1`,

`H_z(v,h)=exp(-h)*(S_z(v+h)-S_z(v))/h`.

The full signed exponential expansion of S_z is retained. For every requested
natural m there is a finite nonnegative C such that

`norm(S_z(t))<=C*t^m` for `0<t<=1`.

There also exist a natural p and a finite nonnegative C with the global bound
`norm(S_z(t))<=C*t^p` for all positive t. Constants can depend on z and the
requested order. No uniform bound as order grows is claimed.

The normalized H_z is exactly the original same-source response divided by
Q(v). It is absolutely integrable on h>0, with

`integral_(h>0) H_z(v,h) dh = SameSourceCurrent_z(v)/Q(v)`.

For every m, the complete original near integral satisfies

`norm(integral_(0<h<v) H_z(v,h) dh)<=C*v^(m+1)` for `0<v<=1`.

## All endpoint coefficients admitted

For each natural j define the original integral

`B_j(z)=integral_(t>0) exp(-t)*S_z(t)/t^(j+1) dt`.

Every B_j is absolutely admitted, including j=0 and j=1. For any fixed j and
requested m, both its integrand and its removed initial integral obey

`norm(exp(-t)*S_z(t)/t^(j+1))<=C*t^m` for `0<t<=1`,

`norm(integral_(0<t<v) exp(-t)*S_z(t)/t^(j+1) dt)<=C*v^(m+1)`.

The identification `B_(k+2)(z)=J_k(z)` is exact, where J_k is the complete
high-order source moment in the preceding detector theorem.

## Proof

Choose N at least norm(z). The actual signed coefficient obeys
`norm(c_n(z))<=2^(N+1)*(n+1)^(N+1)`. Dividing by `(n+1)^p`, with p>=N+3,
gives a summable reciprocal-square majorant. The elementary bound
`exp(-a/t)<=p!*t^p/a^p` therefore passes through the entire signed source.
Increasing p produces each requested local power; one fixed p supplies the
global polynomial bound and exponential-damped admission at infinity.

For the response, the already proved flat positive-kernel bound passes through
the same complete signed norm majorant. Integrating on 0<h<v supplies the
additional factor v. The weighted translation and source reflection identities
prove that this is the actual normalized operator response.

For B_j, on t<=1 its norm is bounded by the already admitted J_j integrand;
on t>=1 it is bounded by the exponentially damped source. Their sum is an
integrable majorant. Taking a higher flat source power proves the removed
initial-piece bound. These proofs use no convergent endpoint power series.

## Consequences and remaining obstacle

The [finite original-current expansion](pw-b-gamma-reciprocal-cutoff-expansion.md)
now retains the near response, removed moments, far finite resolvent remainder
and source loss in one exact identity, and proves the power remainder bound.
The [current valuation and corrected-scalar obstruction](../5-failed/pw-b-corrected-gamma-scalar-occurrence.md)
then extract a finite first nonzero moment at every complex parameter and
exclude the specified unit-ground-corrected scalar equation. Both consequences
passed scratch verification and targeted leaf builds. Full adjoints, actual
Xi occurrence and independently forced Ward balance remain open.

## Verification

`ThetaCuspHawkingParikhWilczekGammaReciprocalCutoffSource.lean` is the exact
scratch-verified source, with one RHTower umbrella import. Scratch exited 0
without diagnostics; the targeted leaf build completed successfully in43s.
No full umbrella build, numerical experiment or axiom-print check was used.
Search records and primary-source transfer limits are in
[iteration30](../1-in-progress/pw-b-source-orientation-attack.md#iteration30-original-cutoff-coefficient-extraction).
