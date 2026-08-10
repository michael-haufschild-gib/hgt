# Closure-doctrine serial birth, two-defect homology, and exactness law — formalized

- **ID:** ULF-CHM-1
- **Stage:** 3-formalized
- **Paper:**
  `docs/drafts/pipeline/2-fully-proven/universal-law-field/closure-doctrine-serial-birth-two-defect-homology-and-exactness-law.md`
- **Lean module:** `GaloisForLFunctions.HTGeometry.ConstitutiveClosureDoctrineHomology`
- **Umbrella:** `GaloisForLFunctions.HTGeometry.UniversalLawField`
- **Status:** [LEAN-CERTIFIED] [AXIOM-AUDITED] [UMBRELLA-BUILT]

## Certified declarations

| paper clause | Lean declaration |
|---|---|
| doctrine secondary and primary maps | `doctrineSecondaryMap`, `doctrinePrimaryMap` |
| source homology / injectivity criterion | `ker_doctrineSecondaryMap`, `doctrineSecondaryMap_injective_iff` |
| primary surjectivity and complex identity | `doctrinePrimaryMap_surjective`, `doctrineSerial_complex` |
| middle exactness iff target defect vanishes | `doctrineSerial_exact_middle_iff` |
| complete short-exactness criterion | `doctrineSerial_shortExact_iff` |
| canonical closure layers and their containments | `serialInnerClosure`, `serialCompositeClosure`, `serialOuterClosure`, `serialInnerClosure_le_comapCompositeClosure`, `serialCompositeClosure_le_outerClosure` |
| separated serial maps and exactness criterion | `separatedSerialSecondaryMap`, `separatedSerialPrimaryMap`, `separatedSerial_shortExact_iff` |
| independent source-only and target-only doctrine cells | `sourceCompletionDefect_without_targetDefect`, `targetCompletionDefect_without_sourceDefect`, `completionHomologyDefects_independent` |
| genuine topological target-only completion defect | `gammaReporter_targetCompletionDefect_only` |

## Verification

Foreground direct elaboration passed:

```text
lake env lean GaloisForLFunctions/HTGeometry/ConstitutiveClosureDoctrineHomology.lean
```

Source-level axiom audit of the two exactness equivalences, independence capstone, and Gamma
topological cell reports only `propext`, `Classical.choice`, and `Quot.sound`. The module contains no
`sorry`, `admit`, `axiom`, `opaque`, `unsafe`, or computation-backed proof.

Final foreground umbrella audit:

```text
lake build GaloisForLFunctions.HTGeometry.UniversalLawField
```

Build completed successfully with `11,545` jobs. New module builds cleanly; emitted warnings are
from unrelated pre-existing modules.

Global lint was attempted and is currently blocked by unrelated shared-worktree debt in
`EulerQGammaDirichlet.lean` and unrelated unwired modules; this card does not claim a global lint
pass until that external debt clears.
