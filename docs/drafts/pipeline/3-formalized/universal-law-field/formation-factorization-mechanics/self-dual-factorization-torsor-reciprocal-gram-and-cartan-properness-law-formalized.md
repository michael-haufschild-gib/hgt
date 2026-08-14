# Self-dual factorization torsor, reciprocal Gram, and Cartan properness — Lean certificate

- **ID:** ULF-FFM-2-LEAN
- **Stage:** 3-formalized
- **Paper parent:**
  `self-dual-factorization-torsor-reciprocal-gram-and-cartan-properness-law.md`
- **Lean modules:**
  `GaloisForLFunctions.HTGeometry.ConstitutiveSelfDualFactorizationGeometry`,
  `GaloisForLFunctions.HTGeometry.CartanWorkProperness`,
  `GaloisForLFunctions.HTGeometry.ConstitutiveSelfDualFactorizationMatrixRay`
- **Status:** `[LEAN-CERTIFIED FULL SURFACE] [NO SORRY] [NO ADMIT] [NO AXIOM]`
  `[NO OPAQUE] [NO UNSAFE] [UMBRELLA WIRED] [NO OPEN PAPER CLAUSE]`

## Certified theorem surface

Lean certifies the complete dependency-closed mechanism:

1. exact recovery factorizations form a gauge torsor (`exactRecoveryFactorizationEquiv`);
2. adjoint gauge reversal is involutive and its fixed locus is exactly the balanced/unitary
   stratum;
3. semantic and lineage Gram gauges are reciprocal and exchanged by reversal;
4. finite Cartan-mode and packet work is nonnegative, reversal invariant, rigid at zero, and
   globally selecting under bounded depth;
5. matrix Cartan work has the exact positive-eigenvalue formula, zero locus, two-sided spectral
   sublevel bounds, determinant floor, polynomial closed-locus presentation, and compact sublevels;
6. `factorizationMatrixRay X Y t = e^{tY}e^{tX}` is the literal operator ray;
7. `factorizationMatrixReversal_ray` proves the exact adjoint-reversal formula `(CT.22)`;
8. Hermitian spectral diagonalization proves
   `cartanWork (factorizationMatrixRay X Y t) = ∑ⱼ 4 sinh²(tλⱼ)`, equation `(CT.23)`;
9. the real skew-Hermitian phase orbit has compact closure and returns to identity at unbounded
   natural times;
10. bounded operator work is equivalent to `X = 0`, and bounded work along every sequence with
    `|t_n| → ∞` also forces `X = 0`.

The matrix-ray capstones are:

- `factorizationMatrixReversal_ray`;
- `cartanWork_factorizationMatrixRay`;
- `isCompact_closure_range_skewHermitianPhase`;
- `skewHermitianPhase_recurrent`;
- `bounded_cartanWork_factorizationMatrixRay_iff`;
- `eq_zero_of_bounded_cartanWork_along_cobounded`.

## Verification

```text
lake env lean GaloisForLFunctions/HTGeometry/ConstitutiveSelfDualFactorizationMatrixRay.lean
exit 0

lake build GaloisForLFunctions.HTGeometry.ConstitutiveSelfDualFactorizationMatrixRay
Build completed successfully (8659 jobs).

lake env lean GaloisForLFunctions/HTGeometry/UniversalLawField.lean
exit 0
```

Kernel axiom audits of all listed capstones report only:

```text
[propext, Classical.choice, Quot.sound]
```

No module in this certificate uses `sorry`, `admit`, a project axiom, `opaque`, or `unsafe`.

## Boundary

This remains the exact finite-dimensional factorization theorem stated by the paper.  It assumes
the paper's self-adjoint/adjoint generator conditions and proves no arithmetic source realization
or RH endpoint.
