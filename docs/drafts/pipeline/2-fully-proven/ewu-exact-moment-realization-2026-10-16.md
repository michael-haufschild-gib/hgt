# EWU: exact joint trace and energy realization

Status: dependency-closed paper proof; Lean verification in progress. Sources: current Lean
corpus only. No numerical experiments, web search, or novelty audit.

## Target

For every finite nonnegative mixture of arbitrary compact C² Weil sources, construct one
compact smooth even source with both pole values zero, exactly the same whole arithmetic
trace, and exactly the same archimedean energy. No RH or positivity premise in the capstone.

## Conjecture loop

1. Exact-fibre density alone gives exact moments. Rejected: convergence does not provide
   a source at an unattained endpoint. The obstruction is boundary attainment, not accuracy.
2. A nonzero compact source can attain the canonical lower boundary when that boundary
   exists. Rejected by the following rigidity mechanism: under RH zero Weil energy forces
   the transform to vanish at every Xi zero; SuzukiTitchmarshUniqueness forces the entire
   transform to vanish; Fourier injectivity forces the source to vanish.
3. Exact joint moments are realizable. Paper proof closed below; formalization in progress.

## Proof mechanism and dependency audit

* ArchimedeanNodeValueFunction: under RH each full fibre has infimum equal to its
  von Mangoldt pairing; otherwise every fibre is unbounded below.
* Compact boundary rigidity: a positive mixture containing a nonzero source lies strictly
  above that infimum under RH. Thus every nontrivial actual mixture has a full mixture of
  smaller energy in exactly the same fibre, in either branch.
* EvenSectorSingleSourceFibreRecovery turns that strict margin into a single smooth even
  pole-free source of strictly smaller energy and exactly the desired trace.
* Construct a nonzero smooth even pole-free bump in a sufficiently small aperture,
  below the first integer lag. SuzukiSmallApertureGroundEnergy gives positive energy;
  its entire integer trace is zero. This supplies an upward energy direction.
* Add a positive scalar multiple of that blind bump to the lower source as a two-row
  smooth mixture. Choose the coefficient to give the target energy exactly.
  EvenSectorScalarizationMoments then produces one smooth even pole-free source.
* If all active rows are zero functions, both observables vanish and the zero source works.

This is an equality of actual moment images, stronger than equality of closed epigraphs.
It makes no claim about the sign of blind energy and does not prove RH.

## Endpoint and upward-direction details

For a compact C² source, the absolute convergence of the actual Weil series is already
proved in XiGaussianHeatWindowNyquistExclusion. Under RH its real summands are positive
multiplicities times squared transform norms. If the total is zero, every transform value
on the zeta carrier vanishes. Apply SuzukiTitchmarshUniqueness to F(z) = paperFT(f)(-z):
the centred Xi coordinate has gammaOf(1/2 - i z) = -z. Compact support gives finite
exponential type. The resulting identically zero transform implies f = 0 by continuous
Fourier inversion. A positive mixture with any nonzero active row therefore has strictly
positive Weil excess. The known fibre-infimum theorem supplies a strictly lower actual
mixture. If RH fails, fibre unboundedness supplies that mixture directly.

For the upward direction choose a positive aperture a smaller than both the existing
small-aperture positivity threshold and log(2)/2. Choose j large enough that
3 r_j < a, where r_j = 1/(4(2j+3)). The existing evenPolarProfile j is smooth, even,
pole-free, supported in [-3 r_j, 3 r_j], and equals 1 at zero. Its autocorrelation is
supported below the first integer lag, so its whole arithmetic trace vanishes. Its
positive CCM source energy equals its Weil energy, hence its archimedean energy B > 0.
If the lower recovered source has energy A < E, the positive mixture with coefficients
1 and (E-A)/B has exactly the required trace and energy. Existing whole-profile
scalarization realizes both by one actual smooth even pole-free source.

## Verification

Pending: dependency-closed Lean proofs, individual foreground builds with --old,
direct lake env lean audits, axiom audit, umbrella wiring, and formal lint.
