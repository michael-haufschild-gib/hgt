# Positive overlap-defect mechanics (2026-08-10)

## Higher pivot
Static minimal failure kernels are arbitrary clutters: every clutter is realizable as the exact minimal kernel family of an extensive, monotone, idempotent consequence operator. Therefore static kernel axioms do not force matroid, antimatroid, Helly, or exchange geometry.

First route-independent nontrivial law found at operation exchange: a finite observer pushforward preserves addition strictly but pointwise meet only laxly.

## Certified theorem
Module: `GaloisForLFunctions.HTGeometry.ConstitutivePositiveOverlapDefect`.
Umbrella: `GaloisForLFunctions.HTGeometry.UniversalLawField`.

For profiles u,v and observer f define
`Omega_f = f_!u ∧ f_!v - f_!(u ∧ v)`.
Lean certifies:
- nonnegativity;
- exact serial law `Omega_{g f}=Omega_g(f_!u,f_!v)+g_!Omega_f`;
- total defect mass equals total-variation loss;
- universal zero defect iff f injective;
- constant observer on two atoms creates unit false overlap.

Direct elaboration, lint, standard axiom audit, and final umbrella build pass (11,482 jobs). No computational proof.

## Open mechanism research
1. multiway overlap and Möbius irreducibility;
2. measure/Banach-lattice completion and tightness;
3. restricted-profile reconstruction of observer partitions;
4. normalized positive budget ceiling versus unbounded lifted history.

Do not regress into RH-route-specific source selection. Treat route instances only as later falsifiers/calibrations of the abstract mechanism.