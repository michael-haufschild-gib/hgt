# Actual matched CCM source as a chiral nodal line

- **ID:** `ccm-projective-gauge-chiral-nodal-line`
- **Stage:** 3-formalized
- **Type:** NEW SCIENTIFIC KNOWLEDGE
- **Source:** whole-corpus weld: actual matched CCM chiral Schatten frame × `SourceOrderedPairComplexStructure` × odd skew-packet singularity × finite Hankel Krein crossing
- **Lean module:** `GaloisForLFunctions.RHTower.CCMActualHeadMatchedPhaseProjectiveGaugeChiralNodalLine`
- **Status:** closed and unconditional; not an RH proof

## Result

The two fixed anchors of the actual matched CCM projective gauge compress its chiral Schatten
operator to the corpus ordered-source complex structure

`J = [[0, 1], [-1, 0]]`, with `J² = -1`.

Adjoining arithmetic atom `n` gives the exact skew compression

`[[0, 1, aₙSₙ], [-1, 0, -aₙ], [-aₙSₙ, aₙ, 0]]`.

After multiplication by `i` this is a Hermitian matrix obtained by literal compression of the
self-adjoint chiral Schatten observable. Lean proves its full zero eigenspace classification:

`M z = 0 ↔ z = (-z₂) • (aₙ, aₙSₙ, -1)`.

Thus the kernel is exactly one projective line, not merely singular. Its unique representative
with last coordinate `-1` is `(aₙ, aₙSₙ, -1)`. The division-free incidence
`z₁ = z₀ Sₙ` holds for every natural atom, including zero-weight indices; on every nonzero-weight
atom the coordinate ratio `z₁/z₀` is exactly the intact signed matched source. Every finite actual
matched prime--polar block is consequently the spectral integral of projective coordinates of
these canonically normalized operator-derived nodal lines.

## Formal endpoints

- `ccmActualHeadMatchedPhaseProjectiveGaugeChiralAnchorCompression_eq_sourceOrderedPair`
- `ccmActualHeadMatchedPhaseProjectiveGaugeChiralAnchorCompression_sq`
- `ccmActualHeadMatchedPhaseProjectiveGaugeAtomChiralCompression_eq_operatorMatrix`
- `ccmActualHeadMatchedPhaseProjectiveGaugeAtomHermitianOrientationCompression_eq_operatorMatrix`
- `ccmActualHeadMatchedPhaseProjectiveGaugeAtomHermitianOrientationCompression_isHermitian`
- `ccmActualHeadMatchedPhaseProjectiveGaugeAtomChiralCompression_mulVec_eq_zero_iff`
- `ccmActualHeadMatchedPhaseProjectiveGaugeAtomNodalVector_unique_normalized`
- `ccmActualHeadMatchedPhaseProjectiveGaugeAtomNodalVector_source_incidence`
- `ccmActualHeadMatchedPhaseProjectiveGaugeAtomNodalReporter_eq`
- `ccmActualHeadMatchedPrimePolarFiniteBlock_eq_chiralNodalLine`

## New principle

The matched source is not only a ratio of positive-kernel entries or a chiral matrix coefficient.
It is an intrinsic coordinate of the unique null axis created when the universal source-pair
complex structure is enlarged by one arithmetic atom. This supplies a source-faithful nodal
object directly compatible with the corpus Krein-crossing, spectral-flow, relative-nodal, and
orientation-collapse mechanisms. It also explains why squaring or taking positive covariance
loses the decisive datum: both operations forget which side of the moving null axis is selected.

The result does not force a preferred side of that nodal axis. Next problem is to transport its
canonical normalization into a quantized crossing or source/reflection obstruction without
assuming an RH-equivalent landing.

## Verification

- direct check: `lake env lean GaloisForLFunctions/RHTower/CCMActualHeadMatchedPhaseProjectiveGaugeChiralNodalLine.lean`
- exact leaf build: `lake build GaloisForLFunctions.RHTower.CCMActualHeadMatchedPhaseProjectiveGaugeChiralNodalLine`
- selected theorem axiom audit: only `propext`, `Classical.choice`, `Quot.sound`
- module wired into `GaloisForLFunctions/RHTower.lean`

## Research log

- 2026-08-21 — Broad search found `SourceOrderedPairComplexStructure`, `FiniteHankelBoundaryKreinCrossing`, odd skew-packet singularity, and nodal-collapse mechanisms.
- 2026-08-21 — Exact anchor complex structure, Hermitian atom compression, full null-line classification, normalized source reconstruction, and finite actual-block identity proved and leaf-built.

## Gates

- [x] 0 → 1 in-progress
- [x] 1 → 2 fully-proven
- [x] 2 → 3 formalized
- [ ] 3 → 4 publication-ready
