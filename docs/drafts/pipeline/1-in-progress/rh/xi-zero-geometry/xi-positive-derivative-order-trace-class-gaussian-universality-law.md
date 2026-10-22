# Xi positive derivative-order trace-class Gaussian universality law

## Status

`[LEAN PROVED — LITERATURE AUDITED]`

## Lean-derived conjecture

For a finite completed-Xi derivative dictionary `order`, the following elementary stratum:

- derivative orders are pairwise distinct;
- every derivative order is positive;
- packet rank is at least two;

is equivalent to one joint certificate, uniformly in source prime, metric prime, jet depth, and
nonnegative Gaussian scale:

- complex cofinite reconstruction of the arbitrary Xi jets;
- real-channel and complex-coefficient real-channel cofinite reconstruction;
- exact successor-aperture Hilbert reconstruction;
- channelwise trace-class prime response gain;
- summability after the canonical counterterm, with that counterterm exactly zero;
- global Gaussian log-determinant concavity;
- strict Gaussian curvature;
- nonnormality of the induced square-root channel operator.

## Corpus inputs

- `xiDerivativeOrder_successorGaussianCurvatureCertificate_iff`
- `xiAperture_traceClassGaussianCurvatureCertificate_iff`
- `xiDerivativeOrderSuccessorAperture_injective_iff`
- `xiDerivativeOrderSuccessorAperture_ne_zero`

## New connector

Successor relabeling preserves derivative-order collisions. Its trace-class threshold is:

`2 ≤ order(j) + 1  ↔  order(j) ≠ 0`.

Thus positivity of the arbitrary derivative dictionary is exactly the missing condition joining
the arbitrary-jet reconstruction certificate to the trace-class/counterterm curvature
certificate on the identical successor aperture packet.

No numerical computation is used.

## Novelty protocol

Literature search was deferred until the theorem passed

`lake env lean GaloisForLFunctions/RHTower/XiPositiveDerivativeOrderTraceClassGaussianUniversalityLaw.lean`.

Nearest sources found:

- Dong, Eriksson, Nickisch, Bindel, Wilson, *Scalable Log Determinants for Gaussian Process
  Kernel Learning*, arXiv:1711.03481;
- Cortinovis and Kressner, *On randomized trace estimates for indefinite matrices with an
  application to determinants*, arXiv:2005.10009;
- Ameli and Shadden, *Interpolating Log-Determinant and Trace of the Powers of Matrix
  A+tB*, arXiv:2009.07385.

These treat scalable or randomized log-determinant/trace evaluation, not the exact completed-Xi
successor-aperture equivalence joining arbitrary cofinite jet reconstruction, real-channel
reconstruction, trace-class gain, zero counterterm, Gaussian concavity and strict curvature,
and nonnormality. No source stating the combined iff law was found.

## Lean target

`formal/GaloisForLFunctions/RHTower/XiPositiveDerivativeOrderTraceClassGaussianUniversalityLaw.lean`
