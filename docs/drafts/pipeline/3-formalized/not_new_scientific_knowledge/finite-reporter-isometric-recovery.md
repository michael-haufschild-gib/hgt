# Finite reporter isometric recovery and preserved clock information

- **ID:** `finite-reporter-isometric-recovery`
- **Stage:** 3-formalized
- **Type:** THEOREM, `[BRIDGE]`, equality/recovery case of reporter data processing
- **Scientific status:** `[PROVED] [FORMALIZED] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Lean modules:**
  - `GaloisForLFunctions.HTGeometry.FiniteReporterIsometricRecovery`
  - `GaloisForLFunctions.HTGeometry.ZetaJetFreeness`
  - `GaloisForLFunctions.RHTower.XiJetFreeness`
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

The same-witness capstone makes that distinction generic.  If the source derivative tower has no
constant-coefficient relation and `R` has finite-dimensional output, then one
`k <= finrank(output R)` is new at the source but redundant both under `R` and under `V o R`.
Both reported dependence witnesses use the same `k`, while `V* o V o R = R` proves that the
representation itself is recovered perfectly.

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

## Xi and zeta applications

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

The generic theorem now supplies the same full witness for completed `xi` and `riemannZeta`
directly from their unconditional hypertranscendence theorems.  The older `logDeriv xi` theorem
keeps its public signature but now specializes the generic capstone from the actual simple pole,
removing its source-local collapse/recovery proof.

## Lean surface

- `finiteDerivativeReporterGram_postcomp_linearIsometry`
- `det_finiteDerivativeReporterGram_postcomp_linearIsometry`
- `finiteDerivativeReporter_isometricAdjointRecovery`
- `finiteDerivativeReporterMap_isometricAdjointRecovery`
- `finiteDerivativeReporterConditionalInformation_postcomp_linearIsometry`
- `exists_finiteDerivativeReporter_isometricRecovery_collapse`
- `xiLogDerivReporter_isometric_information_and_recovery`
- `exists_xiLogDeriv_isometricReporterRecovery_collapse`
- `exists_xi_isometricReporterRecovery_collapse`
- `exists_riemannZeta_isometricReporterRecovery_collapse`

## RH impact and boundary

This does not supply an RH sign or source determinant.  Its value is structural: it identifies
which observation-frame changes are exactly lossless and prevents downstream encoding choices
from being mistaken for arithmetic information.  Any RH-facing reporter route may quotient out
isometric recodings without changing its finite information obligations.

## Verification

- [x] exact HT target built and cached
- [x] exact Xi specialization target built and cached
- [x] both touched files check directly
- [x] generic target built `8526/8526`
- [x] Xi-log target built `8686/8686`
- [x] completed-Xi target built `8951/8951`
- [x] zeta target built `8532/8532`
- [x] generic and all three source capstones use only `propext`, `Classical.choice`, and
  `Quot.sound`
- [x] repository formal lint and targeted diff checks pass
- [x] no numerical computation used
