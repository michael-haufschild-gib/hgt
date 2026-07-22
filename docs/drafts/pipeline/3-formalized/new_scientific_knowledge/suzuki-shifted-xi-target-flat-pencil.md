# Suzuki shifted Xi target flat pencil and multiplicity fingerprint

- **ID:** `suzuki-shifted-xi-target-flat-pencil`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Paper proof:**
  `docs/drafts/pipeline/2-fully-proven/new_scientific_knowledge/suzuki-shifted-xi-target-flat-pencil.md`
- **Lean module:**
  `GaloisForLFunctions.RHTower.SuzukiShiftedXiTargetFlatPencil`
- **RH used:** no
- **Computation used:** no

## Formalized result

> **One-sided coordinate note (2026-07-22).** Generic pencil is unchanged.  For physical positive
> Carleman sheet, use `eta=-i lambda/2` and multiplier phase `i`; interval input in Xi-real exterior
> algebra is `-iT_phys`.  Earlier `eta=-i lambda` identifies full-symbol projective coordinate,
> not selected half-sheet.

The module defines the exact boundary-free shift pencil

```text
suzukiShiftedXiDenominator eta z = deriv XiC z - eta * XiC z
suzukiShiftedXiTarget eta z      = z^2 * XiC z / D_eta(z)
suzukiXiShiftTransport alpha beta z = D_alpha(z)/D_beta(z).
```

It proves unconditionally:

1. `suzukiShiftedXiDenominator_sub` and
   `XiC_eq_suzukiShiftedXiDenominator_secant`: two distinct fibres recover `XiC` exactly;
2. `suzukiXiShiftTransport_target`, `suzukiXiShiftTransport_cocycle`, and
   `suzukiShiftedXiTarget_mobius_cross`: exact flat shift holonomy;
3. `suzukiShiftedXiTarget_reciprocal_translation`: reciprocal targets differ by the shift;
4. `analyticOrderAt_suzukiShiftedXiDenominator_eq_pred_of_XiC_zero`: an Xi zero of order `m`
   gives denominator order `m-1` for every shift;
5. `meromorphicOrderAt_suzukiShiftedXiTarget_eq_one_of_XiC_zero`: every Xi zero becomes a simple
   zero of every shifted target's meromorphic normal form;
6. `exists_multiplicity_meromorphicTrailingCoeffAt_suzukiShiftedXiTarget` and
   `meromorphicTrailingCoeffAt_suzukiShiftedXiTarget_of_XiC_zero`: the exact target coefficient is
   `z^2/m`, so multiplicity survives as an inverse first-coefficient fingerprint;
7. `hasDerivAt_suzukiShiftedXiTarget_parameter` and its Riccati corollary: exact parameter flow;
8. `hasDerivAt_suzukiShiftedXiTarget_of_simple_XiC_zero`: every shifted target has first jet
   `z^2` at a simple Xi zero.

The legacy SOTA target is now definitionally connected to the zero fibre through
`suzukiXiCharacteristicTarget_eq_shifted_zero`.

## Frontier consequence

The cofinal Suzuki operator problem no longer needs an admissible shift converging to zero.  Any
non-erasing finite shift cluster has the same Xi divisor and exact multiplicity fingerprint.  A
second viable attack is common-gauge convergence of two distinct normalized shift fibres followed
by affine secant recovery of Xi.

Finite-aperture Neumann boundary convergence, common-gauge entire-pair normality, and zero linear
Nevanlinna mass remain open.  No finite-aperture Fourier diagonalization is claimed.

## Audit

```text
lake env lean GaloisForLFunctions/RHTower/SuzukiShiftedXiTargetFlatPencil.lean
  PASS

lake build GaloisForLFunctions.RHTower.SuzukiShiftedXiTargetFlatPencil
  PASS (8600/8600)

lake env lean GaloisForLFunctions/RHTower/RiemannHypothesisSOTA2026.lean
  PASS

#print axioms capstones
  [propext, Classical.choice, Quot.sound]
```

Scoped `git diff --check` and forbidden-token audits pass.  Repository-wide
`scripts/formal_tools.py lint` reached an unrelated concurrent unimported module,
`XiSquaredEulerApertureDiagonalControlObstruction.lean`; no Suzuki lint defect was reported and
that other agent's umbrella scope was left untouched.

## Gates

- [x] complete paper proof
- [x] arbitrary-multiplicity theorem, not a simple-zero surrogate
- [x] exact source-specific Lean definitions
- [x] exact module build
- [x] SOTA connector check
- [x] axiom audit
- [ ] finite-aperture Neumann boundary convergence
- [ ] common-gauge pair normality and zero linear mass
- [ ] RH

## Log

- 2026-07-21 — exact affine, local-order, trailing-coefficient, and Riccati theorems formalized in
  `SuzukiShiftedXiTargetFlatPencil.lean`; exact build and capstone axiom audit passed.
