# Law-history survival, refactorization, and split transgression -- Lean certification

- **ID:** ULF-LHSM-1
- **Paper card:**
  `docs/drafts/pipeline/2-fully-proven/universal-law-field/law-history-spectral-mechanics/finite-history-survival-filtration-refactorization-and-split-transgression-law.md`
- **Lean module:**
  `GaloisForLFunctions.HTGeometry.ConstitutiveLawHistorySpectralMechanics`
- **Umbrella:** `GaloisForLFunctions.HTGeometry.UniversalLawField`
- **Status:** [LEAN-CERTIFIED] [NO PROJECT AXIOMS] [MECHANISM NOT OBJECT]
  [FINITE HISTORY] [NOT RH]

## Certified declarations

- `tail`, `totalDefect`, `transition`, and `layer`;
- `range_tail_mono`, `layer_mono`, `layer_zero`, `layer_last`,
  `finiteFiltration_closed`;
- `stagePrefix`, `stageMap`, `stageTail`, `stageSurvivorEquiv`,
  `finiteHistoryStage_closed`;
- `refactorInnerMap`, `refactorInnerToCoarse`, `refactorCoarseToOuter`,
  `range_refactorInnerToCoarse_eq_ker`, `refactorization_short_exact`;
- `splitResidual`, `splitTransgression`, `splitTransgressionEquiv`;
- `scalarSplitInclusion_not_surjective`, `scalarSplitProjection_not_injective`, and
  `splitTransgression_closed`.

## Exact content

Every finite linear history has an exhaustive future-tail image filtration of its total cokernel.
Its stage grade is the local stage modulo both past attainment and the kernel of its entire future.
Refactoring one transition through an intermediate carrier resolves one old grade into a canonical
short exact sequence. A split inclusion followed by its retraction supplies the sharp cancellation
cell: both local defects are nonzero, their composite is the identity, and the local cokernel is
canonically equivalent to the later kernel.

This certifies a mechanism law. It does not construct a stable spectral sequence, a completion
differential, an observer comparison theorem, an infinite-history convergence theorem, or any RH
endpoint.

## Verification

Foreground checks:

```text
lake env lean GaloisForLFunctions/HTGeometry/ConstitutiveLawHistorySpectralMechanics.lean
lake build GaloisForLFunctions.HTGeometry.ConstitutiveLawHistorySpectralMechanics
lake build GaloisForLFunctions.HTGeometry.UniversalLawField
```

Leaf build completed 8,700 jobs. Umbrella build completed 11,581 jobs. `#print axioms` on
`finiteFiltration_closed`, `finiteHistoryStage_closed`, `refactorization_short_exact`,
`splitTransgressionEquiv`, and `splitTransgression_closed` reports exactly `propext`,
`Classical.choice`, and `Quot.sound`. No `sorry`, `admit`, project axiom, `opaque`, `unsafe`, or
computational certificate occurs in the module.

The theorem index includes the module. Repository-wide lint was clean before concurrent
theorem-area additions; a later concurrent audit was blocked by unrelated newly owned modules not
yet wired into their own umbrellas. The LHSM module is wired and its direct and umbrella builds are
green.
