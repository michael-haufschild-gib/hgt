# EDQ complete divisor-flux weight replacement

Stage: 3-formalized. RH remains unproved. This theorem controls one
aggregate correction to the open EDQ signed-flux estimate.

## Exact theorem

Lean module: `GaloisForLFunctions.RHTower.EulerDeletionFluxWeightReplacement`.
Namespace: `RHTower.DeletionFlux`.

For positive d set
`P_d(k)=(k mod d)*((k mod d)-d)/(2*d)` and
`U_N(k)=sum_(1<=d<=N)mu(d)*P_d(k)`.
The actual full divisor channel beyond N uses
`k=d*(floor(N/d)+j+1)` for every j>=0. These are exactly all positive
multiples of d strictly greater than N, each once.

Define

```
stepFlux(N) = sum_(d=1..N) mu(d)
  * sum_(j>=0) U_N(d*(floor(N/d)+j+1)) / [k*(k+1)],
reciprocalFlux(N) = sum_(d=1..N) mu(d)
  * sum_(j>=0) U_N(d*(floor(N/d)+j+1)) / k^2,
```

where k is the same displayed sampled coordinate in each summand.
`channels_summable` proves both complete channel series converge.
`flux_weight_replacement` proves, for every natural N,

`|reciprocalFlux(N)-stepFlux(N)| <= harmonic(N)/4`.

There are no arithmetic premises, RH inputs, added axioms or numerical
certificates. N=0 is included by the empty finite divisor sum. The two
channel convergence statements assume only 0<d<=N.

## Proof

The corpus's exact primitive bound and |mu(d)|<=1 give
`|U_N(k)|<=N*(N+1)/16`. For a fixed d<=N put q=floor(N/d)>=1 and
k=d*(q+j+1). Then

```
1/k^2 <= 1/[d^2*(q+j)*(q+j+1)],
1/k^2-1/[k*(k+1)] = (1/k^2)/(k+1)
                  <= 1/[N*d^2*(q+j)*(q+j+1)].
```

The reciprocal majorant telescopes to 1/q. The inequality N<=2*d*q,
together with N+1<=2*N, bounds the complete absolute channel difference
by 1/(4*d). Summing all actual Möbius-weighted channels gives harmonic(N)/4.
The same majorant proves convergence before the infinite sums are subtracted.
No finite tail truncation is substituted for a complete sum.

## Remaining mathematical obligation

The homogeneous signed flux still lacks the cofinal subpower bound needed
in the full source estimate. Its boundary, mean and gradient terms must
remain coupled as described on the
[active proof card](../1-in-progress/edq-full-covariance-core-attack.md).
The new flux starts at k>N. The earlier Abel split starting at a=N+1
requires removal and retention of its k=N+1 atom, or use a=N instead.

The Bernoulli-series representation and the complete-kernel correction
`(M(N)-H(N))/2` on that card are paper identities; this leaf does not
formalize those further identifications or prove a cancellation sign.

## Validation

- Scratch: `LEAN_NUM_THREADS=1 lake env lean /tmp/edq_flux_root.lean`, clean.
- Final audit: `LEAN_NUM_THREADS=1 lake build --old GaloisForLFunctions.RHTower.EulerDeletionFluxWeightReplacement`, passed; only this leaf compiled, 3.2 seconds.
- Five new public declarations audited from a separate /tmp file: only `propext`, `Classical.choice`, `Quot.sound`.
- Imported by the RHTower umbrella; no umbrella or full build run.
- Repository formal lint passed; existing large-file warnings only. Scoped diff check passed.
- No numerical computation used.
