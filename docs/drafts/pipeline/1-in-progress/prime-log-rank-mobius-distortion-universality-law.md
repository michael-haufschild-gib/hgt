# Prime-log rank versus Möbius phase-distortion universality law

Status: source written; exact Lean audit deferred until final module build because
`CriticalPrimePoissonGCDMobiusVacuum.olean` is not cached.

## Theorem-first origin

- `PrimeLogPhaseBudget.primeLog_primesBelow_linearIndependent` gives free prime-log family below
  every cutoff, indexed by `primeCounting'` elements.
- `CriticalPrimePoissonGCDMobiusVacuum.one_add_four_mul_primeHarmonicSum_le_phaseDistortion` bounds
  antipodal/vacuum distortion by prime-harmonic mass.
- Every prime below `X+1` is at most `X`, so harmonic mass is at least `primeCounting'(X+1)/X`.

## Universal law

For every `X ≥ 2`, same finite prime packet has integer-linearly independent logarithmic phase
family of exact prime-counting cardinality and critical Möbius phase distortion at least
`1 + 4 primeCounting'(X+1)/X`.

## Novelty and verification

Corpus scan found phase rank and critical energy distortion in separate terminal modules, with no
rank-controlled distortion inequality. External literature audit pending. Exact Lean check deferred
to final permitted module-build phase because required parent olean is currently absent.
