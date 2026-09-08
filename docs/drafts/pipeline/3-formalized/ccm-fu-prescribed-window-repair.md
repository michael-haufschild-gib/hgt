# CCM-FU: actual prescribed-prime repair in fixed source windows

- **Stage:** 3-formalized.
- **Scope:** Finite repair at one cutoff, uniform in the processed core.
- **RH status:** No unconditional RH proof or falsification.

## Exact statement

Let P0 be the primes below 15 other than 2. There is a fixed integer b>=15
such that, for every C>0, there is A>0 with the following property for all
sufficiently large N. Set M=14(b+1)N. Let W be the union of the actual prime
windows

`(b*(14/K)*N, (b+1)*(14/K)*N]`, for K=2,7,14.

Suppose P contains P0, leaves 2 unprocessed, and contains no prime of W.
Suppose its full successor envelope satisfies Psi(M,P)<=C*M^2. For every
available prime q with 15<=q<M and floor(M/q)<=14, there is a finite set L
such that

- q belongs to L, and L is contained in {q} union W;
- `card(L)=ceil(A*sqrt(M))+1`;
- `Psi(M,P union L)+M <= Psi(M,P)`.

The threshold in N and A are independent of P and q. The envelope is the
maximum of current energy and all available one-prime successor energies.
The statement imposes no exact real balance, circuit-weight realization,
experimental sign, or RH premise.

## Proof

Write `I_p=(I_{p,0},I_{p,2})` for the exact adjacent-cutoff interpolated source
in the two surviving coordinates. Define the normalized physical packet

`v_p = sqrt(p/M) * I_p`.

Since P contains P0 and excludes 2, both child fibres at every cutoff
through 15 equal the previously established two-coordinate source profile.
This equality holds for arbitrary additional processed primes. Every
window prime has floor(M/p)=K in {2,7,14}, and its clipping weight w obeys
`0<=w` and `b*w<=420`. Choose b large enough to enter both the common
source-cone neighborhood and the common square-reserve neighborhood.

The existing analytic source signs at 2,7,14 give a positive uniform
inward margin c0. Continuity and the nonvanishing merged source coordinates
give d0>0 bounding both `I_p,0^2+I_p,2^2` and `(I_p,0+I_p,2)^2` below.
The floor quotient bound gives M<=16p, hence sqrt(p/M)>=1/4. Therefore
normalized packets have inward margin c=c0/4, and each window prime
contributes at least d*M to both physical reserves, where d=d0/16.

Every available p distinct from 2 with floor(M/p)<=14 obeys ||v_p||<=9
in the product norm. Indeed each actual prime-containing fibre is bounded
by its full absolute mass, at most `(3/5)*sqrt(M)*floor(M/p)`. Exact prime
reflection and division by sqrt(M) give the coordinate bounds. This also
bounds the prescribed initial packet v_q without a processed-cardinality
factor.

Start at z=v_q. At each step choose an unused window prime with
`z dot v_p <= -c*||z||`. If `c*||z||>=9^2`, the squared Euclidean length
cannot increase. Otherwise each coordinate after the step has absolute
value at most `9^2/c+9`. Induction keeps the squared length below
`2*(9^2/c+9)^2`, including the initial vector. Consequently the final
sum has coordinate absolute sum at most H=2*(9^2/c+9).

Let kappa be the minimum of the three window cardinalities. Whenever
fewer than kappa-1 primes have been selected, each window contains a prime
outside the selected set and {q}. The prime number theorem gives
`kappa/sqrt(M) -> infinity`. Set

`A = (2*sqrt(C)*H+H^2+1)/d`, `n=ceil(A*sqrt(M))`.

For sufficiently large N, n<=kappa-1. The greedy construction therefore
supplies exactly n distinct repair primes other than q. Together with q
they form the actual set L of the claimed cardinality. No numerical
optimization or rounding of real circuit weights is involved.

Let X,Y be the physical displacement sums over L, and put D=|X|+|Y|.
The normalized bound gives D<=H*sqrt(M). The n repair primes give
R,T>=d*n*M for the two reserves

`R=sum_(p in L) p*(I_p,0^2+I_p,2^2)`,
`T=sum_(p in L) p*(I_p,0+I_p,2)^2`.

The prescribed prime's two contributions are nonnegative. All selected
primes are at least 15, while their adjacent child cutoffs are at most 15;
thus no selected prime acts on another selected prime's child source.

The complete batch transport identity gives, without exact balance,

`Psi(M,P union L)+min(R,T) <= E+2*sqrt(E)*D+D^2`,

where E=Psi(M,P). For current energy, and for every successor other than
2, the error is controlled by its receiving coordinates, each bounded by
sqrt(E). Prime 2 uses its merged receiving coordinate and X+Y. Its removed
reserve is T. The other cases remove R. This covers the complete envelope.

Finally, E<=C*M^2, D<=H*sqrt(M), M>=1, and the chosen n imply

`2*sqrt(E)*D+D^2+M <= d*n*M <= min(R,T)`.

Subtracting the reserve proves the endpoint inequality.

## Lean sources and validation

- `MobiusDivisorCoupledTwoSourceCone.lean`: common positive clipped square reserves.
- `BoundedPlaneDisplacementBatch.lean`: distinct greedy batch with bounded displacement.
- `MobiusDivisorApproximateTwoReserve.lean`: full envelope reserve with receiving error.
- `MobiusDivisorSquareRootWindowCapacity.lean`: PNT window capacity above sqrt(M).
- `MobiusDivisorPrescribedWindowRepair.lean`: actual prescribed-prime producer.

Scratch checks and exact `lake env lean` leaf emissions passed, including
the square-root cardinality bound. The four new leaves compile without
warnings; the appended source lemma leaves three existing source-file
warnings unchanged. The six new public declarations were each audited
once and depend only on `propext`, `Classical.choice`, and `Quot.sound`.
No experimental result or added axiom enters these proofs.

All four new leaves are wired into `GaloisForLFunctions.RHTower`. Generated
indexes were refreshed. The repository-wide `scripts/formal_tools.py lint
--check-generated` check reports thirteen unrelated unwired modules in
HTGeometry/HilbertMetric and stale LEAN_API/LEAN_OVERVIEW files during
concurrent work; it reports no proof-debt or RHTower wiring error. The
package audit with `lake build` remains pending because its known dependency
expansion would rebuild broad stale prerequisites. No full or umbrella
build was run. Owned scratch files and Lean processes were cleaned.

## Remaining obstacle

The finite producer handles bounded quotients and initially unused windows.
Its square-root batch size conserves most of the available window supply,
but the theorem does not replenish consumed primes or assert that a later
processed core still meets the untouched-window condition. It also does not
handle a prescribed prime with unbounded M/q, especially the retained prime
2, or the overlapping child profiles that appear there. The theorem bounds
the admitted endpoint; it does not itself give a full exhaustive order or
its global signed Abel estimate. Those remain necessary for CCM-FU to prove RH.
