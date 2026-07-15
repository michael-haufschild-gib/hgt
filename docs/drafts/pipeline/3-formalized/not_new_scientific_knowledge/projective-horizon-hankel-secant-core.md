# Formal core: projective-horizon Hankel secant conversion

- **ID:** `projective-horizon-hankel-secant-core`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Scientific status:** `[FORMALIZED BRIDGE] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Paper theorem:**
  `../../2-fully-proven/not_new_scientific_knowledge/projective-horizon-hankel-secant-stratification.md`
- **Lean module:** `formal/GaloisForLFunctions/HTGeometry/ProjectiveHorizonHankelSecant.lean`

## Formalized claim

For every field-valued coefficient sequence, positive matrix size, and shift `s`, reversing the
columns of the critical rectangular Schur--Toeplitz horizon matrix at depth `n=s+m-1` produces the
consecutive square Hankel matrix

```text
(h_(s+r+j))_(0<=r,j<m).
```

Consequently the Toeplitz and Hankel presentations have equal rank and identical corank
thresholds.  Over every integral domain, the Hankel determinant vanishes exactly when there is a
nonzero coefficient vector `c` satisfying

```text
sum_(j<m) h_(s+r+j)c_j=0        for every 0<=r<m.
```

The recurrence vector is the finite invisible horizon mode.

## Lean declarations

- `shiftedHorizonHankel`
- `rectangularSchurToeplitz_reindex_rev_eq_shiftedHorizonHankel`
- `rectangularSchurToeplitz_rank_eq_shiftedHorizonHankel`
- `rectangularSchurToeplitz_corank_ge_iff_hankel_corank_ge`
- `shiftedHorizonHankel_det_eq_zero_iff_exists_windowRecurrence`

## Verification

The module passes a targeted direct Lean check.  It introduces no axiom, placeholder, unsafe
declaration, or opaque constant.  The paper-level identification of the resulting minor ideals
with rational-normal-curve secant varieties remains outside this formal core.

## RH impact

The theorem supplies no RH implication.  It identifies the universal finite recurrence strata
that any Euler-marked refinement would have to cut non-generically.

