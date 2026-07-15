# The `A2` Laurent residue seam is invisible on either one-sided horizon half

- **ID:** `projective-horizon-laurent-residue-seam`
- **Stage:** 3-formalized
- **Type:** POSITIVE NO-GO / AFFINE-CURRENT LOCAL MODEL
- **Scientific status:** `[PROVED] [LEAN-FORMALIZED] [CLASSICAL PARENT] [UNIFIED-FIELD CORE]`
- **Lean:**
  `formal/GaloisForLFunctions/HTGeometry/ProjectiveHorizonLaurentResidueSeam.lean`

## Theorem

For pure modes of the Laurent `A2` current algebra define

```text
omega(A t^m,B t^n)=n delta_(m+n,0) trace(AB).              (1)
```

Then:

1. `omega(A t^m,B t^n)=-omega(B t^n,A t^m)`;
2. the cyclic Lie `2`-cocycle identity holds;
3. `omega` vanishes when both degrees are nonnegative;
4. `omega` vanishes when both degrees are nonpositive;
5. on all three opposite Chevalley-root pairs of `sl3`,

```text
omega(E_ij t^m,E_ji t^(-m))=-m,                           (2)
```

so every nonzero opposite mode has a nontrivial central seam in characteristic zero.

## Proof

Alternation follows from cyclicity of matrix trace and `m+n=0`.  For the cocycle identity,

```text
trace([A,B]C)=trace([B,C]A)=trace([C,A]B),
```

so the cyclic sum is `(l+m+n) trace([C,A]B)`, which vanishes on the only degree locus where the
residue terms can be nonzero.  Same-sign degrees can sum to zero only at degree zero, where the
differential coefficient in `(1)` vanishes.  Direct matrix multiplication gives
`trace(E_ij E_ji)=1`, proving `(2)`.

## Scientific role

The algebraic cocycle is classical affine Kac--Moody theory, so `(1)`--`(2)` are not claimed as a
new theorem in isolation.  Their role is a sharp positive no-go for the HT program:

```text
every one-sided polynomial horizon current algebra is central-seam blind.
```

Consequently the existing polynomial `A2` rank jump, despite being genuinely higher rank, cannot
by itself see the proposed unified topological obstruction.  A source-derived negative Laurent
half is mathematically necessary, not optional vocabulary.  If such a half exists, every opposite
root direction carries a canonical nonzero seam rather than an arbitrary added scalar.

## Lean declarations

```text
a2LaurentResiduePairing
a2LaurentResiduePairing_swap
a2LaurentResiduePairing_nonneg_zero
a2LaurentResiduePairing_nonpos_zero
a2LaurentResiduePairing_cocycle
a2LaurentResiduePairing_opposite_chevalley_roots
a2LaurentResiduePairing_opposite_E01_ne_zero
```

## Verification

- dependency cache checked before building;
- exactly one targeted build:
  `lake build +GaloisForLFunctions.HTGeometry.ProjectiveHorizonLaurentResidueSeam`;
- final direct source check:
  `lake env lean GaloisForLFunctions/HTGeometry/ProjectiveHorizonLaurentResidueSeam.lean`;
- both succeeded; the final direct check emitted no warnings;
- no full or concurrent Lean build was run.

## Open source gate

The mode parameter in the existing horizon algebra is the nonnegative arc degree.  Projective
inversion of a target coordinate does not invert that parameter.  The negative half must be
derived from a punctured source chart or multiplicative scale completion defined independently of
the Xi divisor.  Until that construction exists, this theorem is an exact obstruction and local
model, not an RH implication.
