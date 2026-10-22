# Finite affine cyclic permutation Laurent-residue universality law

## Status

`[LEAN-DERIVED CANDIDATE — PROOF IN PROGRESS; LITERATURE UNOPENED]`

## Lean-derived conjecture

Reading
`HTGeometry/FiniteShiftedLaurentCyclicDivisorMomentUniversalityLaw.lean` against
`RHTower/FiniteAffineCyclicMomentResidueCharacterUniversalityLaw.lean` exposes a missing
connector.  An explicit primitive cyclic permutation of a finite, injectively indexed,
center-free affine spectrum should force one common certificate containing:

- cyclic multiset symmetry and the sharp centered natural-moment vanishings;
- covariance of the centered characteristic product;
- center-cardinality congruence, cyclic character, and logarithmic-derivative residue;
- for every complex weight vector and every integer Laurent window, equivalence between
  permutation invariance of the weights and vanishing of every nontrivial-character moment in
  that window.

The first three clauses forget the labeling and recover analytic order/residue data; the final
clause retains arbitrary labeled divisor weights and extends through all positive and negative
moment windows.

## Corpus inputs

- `GaloisForLFunctions.cyclicPushWeight_fixed_iff_shiftedSignedLaurentCharacterMoments_vanish`
- `GaloisForLFunctions.finiteAffineCyclicSpectrum_fixed_iff_firstCenteredCharacterMoments_vanish`
- `GaloisForLFunctions.finiteAffineCyclicMomentResidueCharacterUniversality`

## Novelty protocol

No literature search before an exact Lean proof.

## Lean target

`formal/GaloisForLFunctions/RHTower/FiniteAffineCyclicPermutationLaurentResidueUniversalityLaw.lean`

## Verification

- scratch proof pending
- source proof pending
- final module build deferred to terminal audit
