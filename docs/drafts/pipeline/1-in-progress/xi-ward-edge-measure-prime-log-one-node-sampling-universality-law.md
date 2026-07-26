# Xi Ward edge-measure prime-log one-node sampling universality law

Status: **Stage 3 — formalized in Lean**

## Discovery

Whole-corpus theorem-posting closure joined:

- `XiWardEdgeMeasureDefect`: RH is equivalent to vanishing of the positive Ward edge measure;
- `XiWardZeroFreeMarginPrimeLogSampling`: past one cutoff, signed prime logarithms plus a finite
  grid detect every strict-right zero margin; and
- `XiWardPrimeLogSampledGramLaw`: any detection cover makes sampled four-unit boundary-Gram
  positivity equivalent to RH, with a one-node non-PSD witness inside every detected margin.

No theorem identifies vanishing/nonvanishing of the continuous edge measure directly with discrete
prime-log Gram data.

## Universal law

There is `y₁≥3` such that for every `Y≥y₁`, writing `S_Y` for the locally finite prime-log sample
set:

1. `xiWardEdgeMeasure = 0` iff every finite four-unit boundary Gram sampled from `S_Y` is positive
   semidefinite; and
2. `xiWardEdgeMeasure ≠ 0` iff one single `t∈S_Y` already makes the one-node four-unit boundary
   Gram non-positive-semidefinite.

Thus a continuous positive measure has an exact locally finite arithmetic sampler, and every
nonzero measure admits a rank-one sampled witness.

## Dependency-closed paper proof

1. Take the cutoff and detection-cover family from
   `exists_cutoff_xiWardDetectionCover_primeLogSampleSet`.
2. `riemannHypothesis_iff_xiWardEdgeMeasure_eq_zero` and
   `riemannHypothesis_iff_continuedXiWardSampledBoundaryGramLaw` give the vanishing equivalence.
3. If the measure is nonzero, RH is false; hence
   `nonempty_xiRightUpperZeroCopy_for_boundaryLift` supplies a strict-right upper pair.
4. Detection cover supplies `t∈S_Y` inside that pair's zero-free-margin window.
5. `continuedXiWardFourUnitBoundaryGram_marginWindow_not_posSemidef` gives the one-node witness.
6. Conversely, if the measure vanished then RH would hold, and
   `continuedXiWardSampledBoundaryGramLaw_of_riemannHypothesis` would make every sampled one-node
   Gram positive semidefinite, contradicting the witness.

No computation or RH assumption enters.

## Formal targets

- `ContinuedXiWardOneNodeSampleFailure`
- `exists_cutoff_xiWardEdgeMeasure_primeLogOneNodeSamplingUniversality`

## Novelty audit

Post-proof searches covered `positive measure + prime logarithm sampling + one-node Gram witness`,
`Riemann Xi Ward edge measure + sampled Gram`, and `locally finite arithmetic sampling + matrix
positivity`.  Results concerned numerical Gram-point computations, generic RH positivity criteria,
ordinary locally finite measures, or unrelated prime-grid Schur approximations.  None stated exact
continuous Ward-measure vanishing/nonvanishing detection by one locally finite prime-log
rank-one Gram.  Representative adjacent sources:

- [High-Precision Approximation of Riemann Zeros via the Truncated Weil Form](https://arxiv.org/abs/2605.20224)
- [A positivity conjecture related to the Riemann zeta function](https://arxiv.org/abs/2011.02847)
- [Measures with locally finite support and spectrum](https://pmc.ncbi.nlm.nih.gov/articles/PMC4812708/)
- [Li's criterion](https://en.wikipedia.org/wiki/Li%27s_criterion)

No exact collision found in this scoped audit. **[NOVELTY UNVERIFIED]**

## Lean formalization

Formal source:
`formal/GaloisForLFunctions/RHTower/XiWardEdgeMeasurePrimeLogOneNodeSamplingUniversalityLaw.lean`.

Verified with:

`lake env lean GaloisForLFunctions/RHTower/XiWardEdgeMeasurePrimeLogOneNodeSamplingUniversalityLaw.lean`

Umbrella:
`formal/GaloisForLFunctions/RHTower.lean`.
