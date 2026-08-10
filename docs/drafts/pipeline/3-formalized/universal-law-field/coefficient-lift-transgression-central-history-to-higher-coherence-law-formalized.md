# Coefficient-lift transgression — Lean certification

- **Paper card:**
  `docs/drafts/pipeline/2-fully-proven/universal-law-field/coefficient-lift-transgression-central-history-to-higher-coherence-law.md`
- **Lean module:**
  `GaloisForLFunctions.HTGeometry.ConstitutiveCoefficientLiftTransgression`
- **Status:** [FORMALIZED] [NO PROJECT AXIOMS] [WIRED INTO ULF UMBRELLA]

## Certified core

Lean proves:

1. a coarse cocycle makes every fine lift associator land in the coefficient kernel;
2. the kernel-valued ternary defect satisfies pentagon coherence;
3. a kernel correction changes the defect by the corresponding ternary coboundary;
4. the defect is coboundary-trivial iff a strict fine cocycle lift exists;
5. defects from different fine lifts are cohomologous;
6. an additive coefficient splitting produces a strict cocycle lift;
7. the coarse cross-parity cocycle on `(ZMod 2)^2` is closed but admits no `ZMod 4` cocycle lift;
8. its binary-digit lift has explicit associator value `2`;
9. a two-term linear coefficient complex has the same no-lift behavior;
10. an unconditional capstone bundles both laboratories.

## Verification

- direct foreground elaboration:
  `lake env lean GaloisForLFunctions/HTGeometry/ConstitutiveCoefficientLiftTransgression.lean`;
- formal lint: `scripts/formal_tools.py lint`;
- axiom audit through a `/tmp` scratch import;
- final umbrella audit:
  `lake build GaloisForLFunctions.HTGeometry.UniversalLawField`.

No `sorry`, `admit`, added axiom, `opaque`, `unsafe`, `native_decide`, or computational certificate
appears in the module.

## Paper-only frontier

General degree-`n` cochains, iterated coefficient towers, spectral-sequence convergence, topology,
and admission-relative liftability remain open.  They do not count as Lean-certified consequences.
