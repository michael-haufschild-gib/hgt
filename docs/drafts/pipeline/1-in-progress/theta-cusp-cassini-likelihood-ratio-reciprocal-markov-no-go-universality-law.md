# Theta-cusp Cassini likelihood-ratio / reciprocal-Markov no-go universality law

## Status

`[LEAN PROVED — CORPUS-NOVEL EXACT SYNTHESIS; LITERATURE AUDITED]`

## Lean-derived conjecture

Reading `RHTower/ThetaCuspCassiniHyperbolicSourceLaw.lean` against
`RHTower/ThetaCuspCassiniMarkovBoundaryTransport.lean` exposes a sharp representation boundary
for one and the same explicit likelihood source.

At every positive aperture `0 < t < 1`, the genuine Cassini response is the positive real ratio
of flux and partition transforms of the aperture-independent likelihood carrier.  Nevertheless,
the raw reciprocal-square-gap pushforward of that carrier cannot represent the whole Cassini
boundary as a compact Markov transform.  The obstruction is not lack of positivity or compact
support: it is the incompatible total-mass normalization proved by analytic transport.

## Corpus inputs

- `RHTower.thetaCuspCassiniInwardCoordinateResponse_one_sub_sq_eq_likelihoodCarrierRatio`
- `RHTower.thetaCuspCassiniInwardCoordinateResponse_one_sub_sq_re_pos`
- `RHTower.thetaCuspCassiniInwardCoordinateResponse_one_sub_sq_im_eq_zero`
- `RHTower.not_thetaCuspCassiniReciprocalLikelihoodBoundaryIdentity`

## Novelty protocol

No literature search was performed before the exact Lean proof.

Post-proof targeted searches covered Riemann-Xi theta kernels, hyperbolic flux/partition
representations, compact Markov transforms, and reciprocal-gap measures.  The nearest relevant
literature found studies classical Xi theta-kernel transforms, Jensen polynomials, or Markovian
cycle constructions, but does not state the exact common-carrier phase boundary formalized here:

- Watson, *The Riemann Xi-function from primitive Markovian cycles I: A canonical construction*,
  arXiv:2602.01248, develops a Markovian-cycle theta representation, not the Cassini
  flux/partition ratio or the reciprocal-gap mass obstruction:
  <https://arxiv.org/abs/2602.01248>
- Griffin--Ono--Rolen--Thorner--Tripp--Wagner, *Jensen Polynomials for the Riemann Xi Function*,
  arXiv:1910.01227, concerns Xi Taylor coefficients and hyperbolicity, not this representation
  boundary:
  <https://arxiv.org/abs/1910.01227>

Verdict: exact theorem is absent from the Lean corpus and was not found in targeted literature.
Novelty claim is restricted to the joint representation/no-go formulation; its component
integral identities and mass-obstruction lemmas were already formalized separately.

## Lean target

`formal/GaloisForLFunctions/RHTower/ThetaCuspCassiniLikelihoodRatioReciprocalMarkovNoGoUniversalityLaw.lean`

## Verification

- scratch proof exact, warning-free:
  `lake env lean /tmp/hgt_law289.lean`
- source proof exact, warning-free:
  `lake env lean GaloisForLFunctions/RHTower/ThetaCuspCassiniLikelihoodRatioReciprocalMarkovNoGoUniversalityLaw.lean`
- final module build deferred to terminal audit
