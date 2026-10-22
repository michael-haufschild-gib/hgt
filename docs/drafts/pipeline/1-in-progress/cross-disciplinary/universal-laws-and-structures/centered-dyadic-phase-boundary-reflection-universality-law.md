# Centered dyadic phase/boundary-reflection universality law

## Status

Exact Lean check passed with
`lake env lean GaloisForLFunctions/RHTower/CenteredDyadicPhaseBoundaryReflectionUniversalityLaw.lean`.

## Lean-generated inputs

- `XiOPUCParaorthogonalPhaseGate.lean`: exact norm formula for the dyadic logarithmic Xi phase and
  its one-way unit-modulus gate to the centered real axis.
- `BoundaryModulus.lean`: boundary-normalized prime coordinate is unimodular exactly on
  `Re(s) = 1/2`.
- `BoundaryReflection.lean` and `CanonicalBranch.lean`: that prime-boundary locus is exactly the
  fixed locus of functional-equation line reflection.
- `XiEntireReal.lean`: centered chart `s = 1/2 + z i` used by `XiC`.

## Survivor

For every complex centered coordinate `z`, three tests are equivalent: unimodularity of the dyadic
Xi paraorthogonal phase; unimodularity of the normalized dyadic Bohr boundary coordinate at
`s = 1/2 + z i`; and fixedness of that `s` under line reflection. This identifies two previously
separate finite gates as charts of one universal critical-locus condition.

## Formal target

`GaloisForLFunctions.xiDyadicLogPhase_unit_iff_boundaryReflection_fixed`

## Novelty audit

Pending post-formalization literature search.
