# Prime--archimedean Bernstein exact exponential threshold

## Status

`[FORMALIZED; BRIDGE; RH-BEARING SPECIALIZATION]`

## Claim

For the endpoint-normalized reciprocal-square Xi atoms, false RH produces an attained maximal
Bernstein amplitude `B` satisfying
\[
 1<B<\frac{501}{500}.
\]
The positive endpoint purity then has exact exponential threshold `B^2`: normalization above
`B^2` tends to zero, while normalization by every base strictly between `1` and `B^2` tends to
positive infinity.  Initial energy plus cumulative Dirichlet dissipation has the identical exact
threshold, because it is exactly `(M+1) Pi_M`.  Thus the false phase has one source-defined
critical exponent, rather than separate spectral and dissipative rates or only an unspecified
surviving exponent inside the five-per-mille chamber.

## Positive RH obligation

The source must force the attained maximal amplitude to remain at its critical value `B=1`.
Equivalently, it must keep the cumulative Bernstein Dirichlet dissipation cofinally linear.

## Formalization target

`formal/GaloisForLFunctions/RHTower/PrimeArchBernsteinExactExponentialThreshold.lean`

## Gates

- [x] Existing maximal-mode and sector declarations located
- [x] Exact upper-threshold decay proved
- [x] Exact lower-threshold divergence proved
- [x] Combined phase theorem proved
- [x] No placeholder declarations
- [x] Accepted axioms only
- [x] Manuscript integrated

## Primary declarations

- `PrimeArchEndpointBernsteinExactExponentialExponent`
- `primeArchEndpointBernsteinExactExponentialExponent_unique`
- `exists_primeArchEndpointBernstein_exactExponentialThreshold_of_not_rh`
- `PrimeArchEndpointBernsteinAttainedExactThreshold`
- `exists_primeArchEndpointBernsteinAttainedExactThreshold_of_not_rh`
- `existsUnique_primeArchEndpointBernsteinExactExponentialExponent`
- `primeArchEndpointBernsteinCumulativeDissipationExactExponent_iff_purity`
- `existsUnique_primeArchEndpointBernsteinPurityDissipationExactExponent`
- `primeArchBernsteinNarrowSectorDissipationMaster`

## Reflected branch-point interpretation

The paper value relation
[`prime-arch-bernstein-legendre-double-source-kernel.md`](../../2-fully-proven/not_new_scientific_knowledge/prime-arch-bernstein-legendre-double-source-kernel.md)
shows that for a normalized endpoint coordinate `u`, the conjugate-paired Legendre kernel has
radicand

\[
 (1-B_+(u)^2t)(1-B_-(u)^2t),
 \qquad B_\pm(u)=|u|\pm|1-u|.
\]

Therefore the attained exact threshold `B^2` in this card and the exact Abel radius `B^(-2)` are
the exponential and analytic sides of the same reflected algebraic branch point.  The associated
source-only collar task is
[`prime-arch-bernstein-reflected-kernel-collar.md`](../../1-in-progress/prime-arch-bernstein-reflected-kernel-collar.md).

Equivalently, the Möbius-pullback law in
[`prime-arch-bernstein-mobius-pullback-gutzmer-law.md`](../../2-fully-proven/not_new_scientific_knowledge/prime-arch-bernstein-mobius-pullback-gutzmer-law.md)
shows that `B^(-1)` is the first radius at which a pulled-back prime--Gamma pole reaches the Gutzmer
torus; squaring the torus radius produces the Abel branch point `B^(-2)`.
