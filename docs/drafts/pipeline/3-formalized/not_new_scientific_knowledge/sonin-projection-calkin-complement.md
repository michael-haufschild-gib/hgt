# Sonin projection is the two-cutoff complement modulo compact operators

- **ID:** sonin-projection-calkin-complement
- **Stage:** 3-formalized
- **Type:** BRIDGE (Lean)
- **Lean endpoint:** `formal/GaloisForLFunctions/RHTower/SoninProjectionCalkin.lean`
- **Consumers:** `../new_scientific_knowledge/even-sonin-euler-corner-noncompact.md`,
  `../../2-fully-proven/new_scientific_knowledge/sonin-mixed-calkin-partial-isometry-law.md`

## Statement

For closed forbidden subspaces `A,B` in a complex Hilbert space, assume the alternating block

`T=P_B P_A P_B`

has norm below one and both mixed blocks `P_AP_B`, `P_BP_A` are compact. If `Q` is the orthogonal
projection onto `A^perp intersect B^perp`, Lean proves

`Q-(1-P_A-P_B)`

is compact.

For the concrete physical and Fourier central cutoffs on `L^2(R)`, all hypotheses are discharged.
Thus, for every `a>0`,

`centralSoninProjection a - (1-indicatorCutoff a-fourierCutoff a)`

is compact. The theorem is also restricted to the actual even Hilbert carrier:

`evenCentralSoninProjection a - (1-evenIndicatorCutoff a-evenFourierCutoff a)`

is compact.

## Exact mechanism

Lean first proves the operator identity

`Q=P_(A^perp)-P_(A^perp)(1-T)^(-1)P_BP_(A^perp)`.

The difference `(1-T)^(-1)-1` factors through the compact block `T`. Expanding the formula leaves
only bounded multiples and sums of `P_AP_B`, `P_BP_A`, and `T`, hence a compact remainder.

The pre-existing source supplied compactness of `P_BP_A`. The opposite order is proved directly:
inverse Fourier transform is forward Fourier transform followed by reflection, the central physical
cutoff commutes with reflection, and the remaining finite time--band block is compact.

## Formal surface

- `soninProjectionResolvent`
- `soninIntersectionProjection_eq_resolventFormula`
- `isCompactOperator_soninIntersectionProjection_sub_complement`
- `fourierUnitary_symm_eq_reflection_fourier`
- `isCompactOperator_centralPhysicalFourierBlock`
- `isCompactOperator_centralSoninProjection_sub_complement`
- `isCompactOperator_evenCentralSoninProjection_sub_complement`

## Status

- `[FORMALIZATION]` The abstract two-projection identity is standard operator geometry.
- `[BRIDGE]` The concrete theorem removes the missing quotient-level hypothesis from the exact
  Sonin Euler Calkin calculation.
- `[PROVED]` Every analytic premise is discharged on the actual even physical-and-Fourier carrier.
- `[OPEN CORE]` The mixed Gram partial-isometry law still requires formal cutoff/dilation covariance
  and the final compact-modulo multiplication calculation.

## Verification

- The exact endpoint module passes Lean.
- No full project build or project-wide lint is part of this card.

## Gates

- [x] 0 -> 1: exact two-projection correction formula isolated
- [x] 1 -> 2: compact-complement proof completed
- [x] 2 -> 3: abstract, ambient Sonin, and even-carrier theorems formalized
