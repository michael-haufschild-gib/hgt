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
