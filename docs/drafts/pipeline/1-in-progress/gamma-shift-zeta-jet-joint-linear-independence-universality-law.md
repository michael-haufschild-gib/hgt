# Gamma-shift/zeta-jet joint linear-independence universality law

## Status

Exact Lean check passed with
`lake env lean GaloisForLFunctions/RHTower/GammaShiftZetaJetJointLinearIndependenceUniversalityLaw.lean`.

## Lean-generated inputs

- `GammaShiftSimultaneousFactorization.lean`: mixed square evaluation matrix whose Gamma columns
  are arbitrary confluent jets at finite shifts and whose other columns are arbitrary supplied
  functions.
- `GammaShiftZetaJetFlag.lean`: for distinct shifts and the first `q` zeta jets, determinant of
  that mixed matrix is eventually nonzero on the real axis.
- Mathlib matrix algebra: a square matrix with nonzero determinant has trivial `mulVec` kernel.

## Survivor

For every finite distinct Gamma-shift packet, every multiplicity profile, and every finite initial
zeta-jet packet, all shifted Gamma jets and zeta jets are jointly linearly independent as functions
over `ℂ`. Eventual determinant supplies one invertible consecutive-evaluation packet, so every
global constant-coefficient relation has zero coefficient vector. No pole-free side condition
survives in the conclusion.

## Formal target

`GaloisForLFunctions.RHTower.gammaZetaJetMixedFamily_linearIndependent`

## Novelty audit

Pending post-formalization literature search.
