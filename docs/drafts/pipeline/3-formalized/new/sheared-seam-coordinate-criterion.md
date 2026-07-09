# Sheared Seam Coordinate Criterion

- **ID:** sheared-seam-coordinate-criterion
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) — `[PROVED]`
- **Door grade:** BRIDGE. The statement is two-by-two local algebra, not native by itself. Its use is
  as a gatekeeper coordinate chart for the source-side Sonin/prolate cutoff realization problem.
- **Lean file:** `formal/GaloisForLFunctions/RHTower/CutoffCochain.lean`
- **Support file:** `formal/GaloisForLFunctions/RHTower/SigmaDivisorJet.lean`

## Statement

Let

`A_m = [[X^m, 1], [0, 1]]`

be the non-split sheared torsion seam presentation over `Q[X]`. For every defect matrix `Delta`,

`tr(adj(A_m) Delta) = Delta_00 - Delta_10 + X^m Delta_11`.

Therefore its Fitting boundary class modulo `X^m` is exactly

`jetClass (Delta_00 - Delta_10)`.

Equivalently, the sheared seam is boundary-blind to `Delta` iff

`X^m | (Delta_00 - Delta_10)`.

## Lean Declarations

- `jetClass_add_X_pow_mul`
- `fittingBoundaryTrace_shearTorsion_apply`
- `fittingBoundaryClass_shearTorsion_apply`
- `fittingBoundaryClass_shearTorsion_ne_zero_iff`
- `fittingBoundaryClass_shearTorsion_eq_zero_iff`

Existing declarations reused:

- `shearTorsionPresentation`
- `shearTorsionPresentation_det`
- `polynomialLowerCrossing`
- `fittingBoundaryTrace_shearTorsion_lowerCrossing`

## Consequence

The open Sonin/prolate cutoff realization no longer has to compute the whole adjugate trace. In a
local sheared chart it must compute one residue:

`Delta_{p,lambda,00} - Delta_{p,lambda,10} mod X^m`.

If this residue has a nonzero coefficient below `m`, the source-side cutoff defect is determinant-
transverse. If the residue is divisible by `X^m` for every actual Sonin chart, this handle dies.

## Verification

Run on 2026-07-09:

```bash
cd formal
lake env lean GaloisForLFunctions/RHTower/SigmaDivisorJet.lean
lake build GaloisForLFunctions.RHTower.SigmaDivisorJet
lake env lean GaloisForLFunctions/RHTower/CutoffCochain.lean
lake build GaloisForLFunctions.RHTower.CutoffCochain
lake env lean GaloisForLFunctions/RHTower/CutoffTorsionSeam.lean
lake env lean GaloisForLFunctions/RHTower/TorsionSeamClassification.lean
cd ..
scripts/formal_tools.py index
scripts/formal_tools.py lint --check-generated
```

Axiom check on 2026-07-09:

```text
RHTower.jetClass_add_X_pow_mul: [propext, Classical.choice, Quot.sound]
RHTower.fittingBoundaryTrace_shearTorsion_apply: [propext, Classical.choice, Quot.sound]
RHTower.fittingBoundaryClass_shearTorsion_apply: [propext, Classical.choice, Quot.sound]
RHTower.fittingBoundaryClass_shearTorsion_ne_zero_iff: [propext, Classical.choice, Quot.sound]
RHTower.fittingBoundaryClass_shearTorsion_eq_zero_iff: [propext, Classical.choice, Quot.sound]
```

## Object-Level Packaging

Added on 2026-07-09 in `formal/GaloisForLFunctions/RHTower/CutoffTorsionSeam.lean`:

- `shearedTorsionSeam`
- `shearedTorsionSeam_boundaryClass`
- `shearedTorsionSeam_boundaryTraceDivisible_iff`
- `shearedTorsionSeam_hasDeterminantTransverseDefect_iff`
- `shearedTorsionSeam_defectNonmember_of_entryResidue_not_dvd`
- `shearedTorsionSeam_defectLeftNonmember_of_entryResidue_not_dvd`

These package any concrete defect matrix `Delta` as a one-label `TorsionSeamPresentation` with
presentation `[[X^m,1],[0,1]]`.  In that object, determinant transversality is equivalent to
nondivisibility of the entry residue `Delta_00 - Delta_10`, and residue nondivisibility gives both
right and left nonfake seam defects.

Additional verification on 2026-07-09:

```bash
cd formal
lake env lean GaloisForLFunctions/RHTower/CutoffTorsionSeam.lean
lake build GaloisForLFunctions.RHTower.CutoffTorsionSeam
cd ..
scripts/formal_tools.py index
scripts/formal_tools.py lint --check-generated
```

Axiom check:

```text
RHTower.shearedTorsionSeam_boundaryClass: [propext, Classical.choice, Quot.sound]
RHTower.shearedTorsionSeam_boundaryTraceDivisible_iff: [propext, Classical.choice, Quot.sound]
RHTower.shearedTorsionSeam_hasDeterminantTransverseDefect_iff: [propext, Classical.choice, Quot.sound]
RHTower.shearedTorsionSeam_defectNonmember_of_entryResidue_not_dvd: [propext, Classical.choice, Quot.sound]
RHTower.shearedTorsionSeam_defectLeftNonmember_of_entryResidue_not_dvd: [propext, Classical.choice, Quot.sound]
```

## Standard-Cutoff Source-Action Gate

Added on 2026-07-09 in `formal/GaloisForLFunctions/RHTower/CutoffTorsionSeam.lean`:

- `standardCutoff_crossBoundary_lowerLeft`
- `fittingBoundaryClass_shearTorsion_standardCutoff_crossBoundary`
- `shearedStandardCutoffTorsionSeam_hasDeterminantTransverseDefect_iff`
- `shearedStandardCutoffTorsionSeam_defectNonmember_of_lowerLeft_not_dvd`
- `shearedStandardCutoffTorsionSeam_defectLeftNonmember_of_lowerLeft_not_dvd`

In a chart where the cutoff idempotent is `standardCutoff`, Lean proves

`crossBoundary standardCutoff sigma = [[0,0],[sigma_10,0]]`,

so the sheared boundary class is `jetClass(-sigma_10)`.  Thus a source action `sigma` gives a
nonfake sheared torsion seam defect as soon as its lower-left crossing entry survives modulo `X^m`
(up to sign).

Additional axiom check on 2026-07-09:

```text
RHTower.standardCutoff_crossBoundary_lowerLeft: [propext, Classical.choice, Quot.sound]
RHTower.fittingBoundaryClass_shearTorsion_standardCutoff_crossBoundary: [propext, Classical.choice, Quot.sound]
RHTower.shearedStandardCutoffTorsionSeam_hasDeterminantTransverseDefect_iff: [propext, Classical.choice, Quot.sound]
RHTower.shearedStandardCutoffTorsionSeam_defectNonmember_of_lowerLeft_not_dvd: [propext, Classical.choice, Quot.sound]
RHTower.shearedStandardCutoffTorsionSeam_defectLeftNonmember_of_lowerLeft_not_dvd: [propext, Classical.choice, Quot.sound]
```
