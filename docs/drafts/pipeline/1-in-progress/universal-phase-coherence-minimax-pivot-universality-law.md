# Universal phase-coherence minimax-pivot universality law

## Status

Fully proven on paper; Lean 4 formalization in progress.

## Theorem-first source

- `universalPhaseCoherenceTime_isDeadline`: the corpus-defined minimax clock supplies a near-unit
  amplitude witness for every finite frequency packet.
- `exists_phasePivot_sum_norm_sub_sq_le`: every near-unit equal-weight phase centroid supplies a
  packet pivot with controlled total squared chordal dispersion.
- `phaseClockAmplitude_eq_equalPhaseAmplitude`: the recurrence amplitude is literally that Hilbert
  centroid.
- `universalPhaseCoherence_dimensionResolution_sandwich`: the least amplitude deadline obeys the
  exact Haar/Dirichlet entropy sandwich.

The earlier `exists_phaseClockPivot_halfEntropy_quantitative` only records a pivot below the crude
Dirichlet ceiling. Reading the minimax and centroid statements together exposes that the least
amplitude deadline itself can always carry the pivot certificate.

## Universal law

In positive dimension, requiring every universal coherent-clock witness to carry a phase pivot
with total squared dispersion at most `4 * recurrencePhaseDefect Q * d` does not change the class
of universal deadlines. Hence `universalPhaseCoherenceTime` is also the least pivot-certified
deadline, with the same dimension--resolution entropy sandwich.

## Paper proof

A pivot-certified deadline is an amplitude deadline by forgetting its pivot. Conversely, take the
amplitude witness supplied for each frequency packet, rewrite its amplitude as the Hilbert
centroid of its unit phases, and apply centroid pivot geometry. Thus the two deadline predicates
are equivalent. Minimality follows from the `Nat.find` definition of the minimax time, and the
existing entropy sandwich transfers unchanged. No numerical computation is used.

## Lean formalization

Module:
`GaloisForLFunctions.RHTower.UniversalPhaseCoherenceMinimaxPivotUniversalityLaw`.

## Novelty audit

Pending literature audit after exact Lean formalization. Corpus audit is negative.
