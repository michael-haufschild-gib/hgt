# Xi Ward prime-log synchronized-detector universality law

- **ID:** `xi-ward-prime-log-synchronized-detector-universality-law`
- **Law:** LAW508
- **Stage:** 1-in-progress
- **Type:** THEOREM (dependency-closed paper proof)
- **Register:** `[UNIVERSAL-LAW] [CORPUS-SYNTHESIS]`
- **Target:** `formal/GaloisForLFunctions/RHTower/XiWardPrimeLogSynchronizedDetectorUniversalityLaw.lean`

## Theorem

Past one cutoff, every sufficiently large prime-log sample family has a common two-phase
classification.

- The Ward edge measure vanishes exactly when the ordinary sampled scalar budget, the
  margin-relaxed sampled scalar budget, and every sampled finite boundary-Gram positivity law
  all hold.
- The Ward edge measure is nonzero exactly when one arithmetic height simultaneously exceeds the
  margin-relaxed scalar budget and makes its one-node four-unit boundary Gram non-positive.

Thus a non-RH state cannot require different arithmetic samples for scalar and matrix detection:
one signed prime logarithm or one point of the finite auxiliary grid witnesses both failures.

## Theorem-generated derivation

Whole-corpus leaf comparison exposed four separately proved mechanisms sharing the same detection
cover:

- `exists_cutoff_xiWardDetectionCover_primeLogSampleSet`;
- `normSq_continuedXiAntiCausalWardResponse_marginWindow_gt_four_add`;
- `xiWardZeroFreeMargin_close_le_two_mul`;
- `continuedXiWardFourUnitBoundaryGram_marginWindow_not_posSemidef`;
- `riemannHypothesis_iff_xiWardEdgeMeasure_eq_zero`.

The existing edge-measure sampling capstone synchronizes measure nonvanishing only with Gram
failure.  The scalar and merged-slack completeness files prove their converse directions using
the same window but do not retain the common height.  No corpus declaration states the joint
one-node scalar/Gram witness.

## Dependency-closed paper proof

Fix a cutoff supplied by the prime-log detection-cover theorem and a larger `Y`.

Under RH, the continued anti-causal Ward response vanishes throughout the right half-plane.
Hence both sampled scalar laws hold, every sampled boundary Gram is positive semidefinite, and
the edge measure is zero.

Assume non-RH.  Choose an upper strict-right zero pair `q`, then use the common detection cover at
its centered height `b` to choose one sample `t`.  The margin-window theorem gives

```text
4 + 2 m(b) < |r(1/2+it)|^2.
```

The window radius is at most one, so log-slow variation gives `m(t) <= 2 m(b)`.  Therefore

```text
4 + m(t) < |r(1/2+it)|^2,
```

which simultaneously refutes both the ordinary and relaxed scalar laws.  The same window
hypothesis makes the one-node four-unit boundary Gram at `t` non-PSD.  Conversely either strict
scalar excess or Gram failure contradicts RH because RH makes the response zero and all boundary
Grams PSD.  Finally `RH ↔ edge measure = 0` labels the two synchronized detector phases.  No
numerical computation is used.

## Strict corpus delta

Existing results provide three separate RH-complete sampled tests and a measure/Gram capstone.
The new law proves a common-witness theorem: one locally finite arithmetic sample jointly detects
the strict relaxed scalar excess and matrix positivity failure, then identifies this joint event
exactly with nonvanishing of the continuous Ward edge measure.

## Lean result

`formal/GaloisForLFunctions/RHTower/XiWardPrimeLogSynchronizedDetectorUniversalityLaw.lean`
proves:

- `not_riemannHypothesis_iff_continuedXiWardSynchronizedOneNodeFailure`;
- `exists_cutoff_xiWardEdgeMeasure_primeLogSynchronizedDetectorUniversality`.

Direct exact check passed without warnings:

`lake env lean GaloisForLFunctions/RHTower/XiWardPrimeLogSynchronizedDetectorUniversalityLaw.lean`

The module is imported by `GaloisForLFunctions/RHTower.lean`.

## Post-proof novelty audit

Performed only after dependency-closed Lean proof passed.  Targeted searches recovered classical
Weil positivity, Nyman--Beurling/Li-type positivity criteria, RH statements derived from prime
statistics, and generic positive-measure or matrix formulations.  They did not recover a
continued Ward response, this polylogarithmic zero-free margin, this locally finite signed-prime-log
sample family, or a common arithmetic node synchronizing strict relaxed scalar excess with
one-node Gram failure and continuous-measure nonvanishing.

Verdict: `[NOVELTY PLAUSIBLE — SEARCH NOT EXHAUSTIVE]`.  Novelty is claimed for the exact
synchronized detector theorem, not for generic RH-equivalent positivity criteria.

## Gates

- [x] Whole-corpus theorem-leaf discovery
- [x] Prior corpus and failed-route audit
- [x] Dependency-closed paper proof
- [x] Lean formalization; direct `lake env lean`
- [x] Post-proof literature audit
- [ ] Axiom and umbrella audit
