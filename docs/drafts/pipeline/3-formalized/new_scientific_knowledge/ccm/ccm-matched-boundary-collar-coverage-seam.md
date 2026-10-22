# Matched boundary collar and autocorrelation coverage seam

## Status

Formalized unconditionally in
`GaloisForLFunctions.RHTower.CCM.CCMActualHeadMatchedBoundaryCoverageSeam`.

Targeted source check and exact-module build pass. Axiom audit reports only `propext`,
`Classical.choice`, and `Quot.sound`. No RH premise, numerical certificate, added axiom, or
conditionally convergent rearrangement is used.

## Conjecture loop

1. **Conjecture:** the all-prime matched family can replace the physical prime block directly.
   **Failure:** local symmetric cells do not partition the true polar interval. The missing term is
   a signed coverage seam, so direct substitution would erase the RH-bearing overlap/gap data.
2. **Conjecture:** reciprocal-Gamma or wall-light positivity signs the missing seam.
   **Failure:** the corpus already proves reciprocal-Gamma square divergence, and the available
   light-cone completion signs a reflected wall current rather than the oscillatory matched Suzuki
   integral. Both routes were rejected rather than weakened into assumptions.
3. **Conjecture:** aperture extinction converts the apparent all-prime tail into a local boundary
   object. **Proved:** every post-cutoff matched cell equals its autocorrelation integral only on the
   part crossing `2a`; cells beginning at or beyond `2a` vanish exactly.
4. **Conjecture:** nonzero boundary packets are arithmetically confined much more sharply than the
   coarse logarithmic support `log n < 2a + 1`. **Proved:** a nonzero packet forces

   `n - exp(2a) < Lambda(n)/2`

   and therefore `n` is a prime power in

   `exp(2a) < n < exp(2a) + a + 1/2`.

## New exact identities

- A matched symmetric exponential cell has scalar mass exactly
  `criticalMellinAtomWeight n`.
- Prime atom minus matched polar cell is an exact same-head autocorrelation transport.
- Beyond the physical cutoff it is exactly the boundary collar

  `2 * integral_[log n - rho_n, 2a] exp(h/2) C_f(h) dh`.

- The all-prime matched `tsum` is the physical matched finite block plus that collar.
- The collar `tsum` is actually a finite sum on the explicit additive finset

  `Ioc (floor(exp(2a))) (floor(exp(2a) + a + 1/2))`.

- Endpoint coefficient plus matched coverage seam cancels every scalar mass. What remains is
  `4 ||f||^2` plus true polar autocorrelation minus matched-cell autocorrelation.
- Consequently the actual restricted-Weil source has an exact finite normal form consisting of
  scalar Gamma, higher Gamma energy, endpoint reserve, finite even matched residual, signed Suzuki
  current, and one literal autocorrelation coverage seam.

## Higher principle exposed

Mass matching is not merely a convergence device. Combined with the aperture quotient, it turns a
nominal remote prime tail into a **boundary transport law**. The local cell width is calibrated so
strongly that a cell crossing `2a` forces its integer center into a von-Mangoldt-width additive
strip. Thus remote arithmetic is absent; the surviving obstruction is geometric coverage of the
physical polar interval by locally mass-matched cells.

This changes the next question. It is not whether the prime tail converges, and not whether
autocorrelation is pointwise nonnegative. It is whether the local matched-cell cover can be
transported to the monotone quantile partition with a Gamma-payable displacement. In exponential
polar coordinate, both cell families carry the same mass. Their boundary displacement is governed
by the cumulative critical-Mellin error, making matched-versus-quantile transport the exact next
hard core.

## Hostile audit

- No sign is claimed for an individual collar: physical autocorrelation can be negative.
- Thin arithmetic support does not prove positivity of the remaining coverage seam.
- Matched cells may overlap or leave gaps; treating them as a partition is invalid.
- Wall-light Gram completion does not directly apply to the sine-weighted Suzuki current.
- Result is significant localization and cancellation progress, not an RH proof.

## Next conjecture

Decompose the matched coverage seam cellwise against the equal-mass monotone quantile cells. Prove
an exact transport identity whose displacement coordinate is the cumulative critical-Mellin error,
then test whether higher Gamma energy controls that displacement as a Gram or characteristic-kernel
remainder. Pivot if the required domination reduces to an already-retired completed-error bound.
