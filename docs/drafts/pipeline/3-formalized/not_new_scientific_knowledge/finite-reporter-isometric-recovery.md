# Finite reporter isometric recovery and preserved clock information

- **ID:** `finite-reporter-isometric-recovery`
- **Stage:** 3-formalized
- **Type:** THEOREM, `[BRIDGE]`, equality/recovery case of reporter data processing
- **Scientific status:** `[PROVED] [FORMALIZED] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Lean modules:**
  - `GaloisForLFunctions.HTGeometry.FiniteReporterIsometricRecovery`
  - `GaloisForLFunctions.RHTower.XiLogDerivReporterIsometricRecovery`

## Equality and recovery theorem

Let `R` be a Hilbert-valued finite derivative-clock reporter and let `V` be an isometric linear
postprocessor.  Then every reported-jet inner product is unchanged, hence

```text
Gram_N(V o R) = Gram_N(R)                               (1)
det Gram_N(V o R) = det Gram_N(R).                      (2)
```

On complete Hilbert spaces, the adjoint is an exact recovery map:

```text
V* o V o R = R.                                         (3)
```

The existing quantitative data-processing inequality applied first to `V` and then to the
recovery `V*` gives both inequalities and therefore

```text
conditionalInfo_N(V o R) = conditionalInfo_N(R)         (4)
```

for every derivative order, including singular preceding blocks.  Coefficient packets are also
recovered exactly.

## Positive statement

The result classifies a nontrivial equality case rather than merely extending the no-go.  Lossless
recoding is exactly harmless at the entire finite observation level: all Gram/Fisher geometry,
all D-optimal determinants, and all sequential innovation values survive.  The adjoint gives an
explicit recovery operator.

This sharply separates observation loss from representation change.  Isometric encoding can
move or enlarge the output Hilbert space without changing what the clock reveals; it cannot repair
a blind direction that was already erased by the original reporter.

## Quantum-information provenance

Preservation of information under a sufficient channel and recovery by an adjoint/Petz-type map
is the equality side of quantum data processing.  Relevant primary sources:

- L. Gao, H. Li, I. Marvian, and C. Rouze, *Sufficient statistic and recoverability via Quantum
  Fisher Information metrics*, arXiv:2302.02341.
- B. Schumacher and M. D. Westmoreland, *Approximate quantum error correction*,
  arXiv:quant-ph/0112106.
- C. Beny and O. Oreshkov, *General conditions for approximate quantum error correction and
  near-optimal recovery channels*, arXiv:0907.5391.

The formal statement is the exact Hilbert-valued isometric case.  It does not claim a general
density-matrix Petz theorem.

## Xi application

For finite-dimensional reporters of `logDeriv xi`, an isometric downstream encoding is perfectly
recoverable and preserves the complete conditional-information tower.  Nevertheless, the
unconditional Xi collapse order remains zero-information after encoding.  Applying the adjoint
returns the original reporter, including its blind direction, while the underlying Xi derivative
is still independent of its predecessors.

This replaces the ambiguous phrase “no recovery” by the exact distinction:

```text
reporter representation: perfectly recoverable;
source direction erased by reporter: not recreated downstream.       (5)
```

## Lean surface

- `finiteDerivativeReporterGram_postcomp_linearIsometry`
- `det_finiteDerivativeReporterGram_postcomp_linearIsometry`
- `finiteDerivativeReporter_isometricAdjointRecovery`
- `finiteDerivativeReporterMap_isometricAdjointRecovery`
- `finiteDerivativeReporterConditionalInformation_postcomp_linearIsometry`
- `xiLogDerivReporter_isometric_information_and_recovery`
- `exists_xiLogDeriv_isometricReporterRecovery_collapse`

## RH impact and boundary

This does not supply an RH sign or source determinant.  Its value is structural: it identifies
which observation-frame changes are exactly lossless and prevents downstream encoding choices
from being mistaken for arithmetic information.  Any RH-facing reporter route may quotient out
isometric recodings without changing its finite information obligations.

## Verification

- [x] exact HT target built and cached
- [x] exact Xi specialization target built and cached
- [x] both touched files check directly
- [x] no numerical computation used
