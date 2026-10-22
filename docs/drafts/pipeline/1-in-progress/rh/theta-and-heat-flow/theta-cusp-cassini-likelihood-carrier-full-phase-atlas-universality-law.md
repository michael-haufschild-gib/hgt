# Theta-cusp Cassini likelihood-carrier full-phase atlas universality law

## Status

`[LEAN PROVED — CORPUS-NOVEL EXACT SYNTHESIS; LITERATURE AUDITED]`

## Lean-derived conjecture

Reading the terminal Cassini likelihood-ratio/Markov no-go theorem against
`RHTower/ThetaCuspModularColdCurvatureUniversalityLaw.lean` exposes a larger certificate for the
same fixed theta likelihood carrier:

- strict positivity and all-order strict spectral Hankel blocks at every positive source point;
- exact positive-real Cassini flux/partition response at every aperture `0 < t < 1`;
- failure of the raw reciprocal-gap compact Markov boundary identity;
- positivity of every modular cold-curvature factor and signed slope;
- every all-degree modular cold-slope strict fluctuation inequality.

## Corpus inputs

- `RHTower.thetaCuspCassiniLikelihoodRatio_reciprocalMarkovNoGo_universality`
- `RHTower.thetaCuspCassiniLikelihoodBaseDensity_pos_and_spectralHankel`
- `RHTower.thetaCuspModularColdCurvatureFactor_pos`
- `RHTower.thetaCuspModularColdSignedSlopeCoefficient_pos`
- `RHTower.thetaCuspModularColdSignedSlope_strictFluctuation`

## Novelty protocol

No literature search was performed before the exact Lean proof.

Post-proof targeted searches extended the prior Cassini audit to theta-kernel moment Hankel
positivity and all-degree special-function curvature inequalities.  Search found the classical
moment/Hankel mechanism and unrelated special-function Hankel hierarchies, but not this exact
theta-cusp carrier atlas:

- Novi Inverardi--Tagliani--Stoyanov, *Maximum Entropy Criterion for Moment Indeterminacy of
  Probability Densities*, reviews moment sequences and their Hankel matrices:
  <https://doi.org/10.3390/e26020121>
- Salazar, *Order-Moment Transport and Hankel Determinants in Special-Function Inequalities*,
  arXiv:2606.31647, develops a general moment route to higher Hankel inequalities for other
  special functions:
  <https://arxiv.org/abs/2606.31647>

Verdict: moment-induced Hankel positivity is classical.  Exact joint theta-cusp statement,
including Cassini response, reciprocal-Markov mass obstruction, and every modular
cold-curvature fluctuation inequality, is absent from the Lean corpus and was not found in
targeted literature.

## Lean target

`formal/GaloisForLFunctions/RHTower/ThetaCuspCassiniLikelihoodRatioReciprocalMarkovNoGoUniversalityLaw.lean`

## Verification

- source proof exact, warning-free:
  `lake env lean GaloisForLFunctions/RHTower/ThetaCuspCassiniLikelihoodRatioReciprocalMarkovNoGoUniversalityLaw.lean`
- umbrella already imports target module
- final module build deferred to terminal audit
