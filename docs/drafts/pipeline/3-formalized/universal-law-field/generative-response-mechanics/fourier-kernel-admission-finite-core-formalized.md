# Fourier-kernel admission finite core — Lean certification

- **Paper card:**
  `docs/drafts/pipeline/2-fully-proven/universal-law-field/generative-response-mechanics/fourier-kernel-admission-reconstruction-and-contact-localization-law.md`
- **Lean module:** `GaloisForLFunctions.HTGeometry.FourierKernelAdmission`
- **Umbrella:** `GaloisForLFunctions.HTGeometry.UniversalLawField`
- **Status:** `[FINITE CORE FORMALIZED] [NO SORRY] [NO ADDED AXIOMS]`

## Certified declarations

- `finiteKernelQuadratic`
- `finiteCoordinatePacket`
- `finiteKernelQuadratic_coordinate`
- `finiteKernelQuadratic_nonneg_of_nonneg`
- `finiteKernelQuadratic_nonneg_iff`
- `finiteKernelQuadratic_injective`
- `finiteKernelPencil`
- `finiteKernelPencil_eq`
- `dominatedAt_iff_finiteKernelPencil_nonneg`
- `finiteContactPenalty`
- `finiteSpectralExcess`
- `finiteContactPenalty_le_spectralExcess`
- `finiteKernelAdmission_contact_capstone`

## Exact boundary

Lean certifies the finite algebraic heart: canonical quadratic tests reflect positivity, reconstruct
the signed carrier, identify compensated admission, and force contact localization. Bochner
reconstruction for arbitrary finite measures, the Radon--Nikodym essential-supremum formula,
rational-frequency cofinal convergence, and the reflected exponential escape theorem remain
paper-level.

## Audit

```text
lake env lean GaloisForLFunctions/HTGeometry/FourierKernelAdmission.lean
lake build GaloisForLFunctions.HTGeometry.FourierKernelAdmission
lake build GaloisForLFunctions.HTGeometry.UniversalLawField
```

The module build passed with 8,656 jobs; the wired universal-law umbrella passed with 11,616 jobs.
Axiom audit of the capstone, admission equivalence, and contact inequality reports only `propext`,
`Classical.choice`, and `Quot.sound`. Full-repository lint reached only pre-existing unrelated
umbrella-reachability errors; it reported no defect in this module.
