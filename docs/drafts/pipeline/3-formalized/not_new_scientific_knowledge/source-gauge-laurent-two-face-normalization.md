# Source-gauge Laurent two-face normalization

- **ID:** `source-gauge-laurent-two-face-normalization`
- **Stage:** 3-formalized
- **Type:** POSITIVE NO-GO / TWO-FACE GAUGE LOCAL MODEL
- **Scientific status:** `[PROVED] [LEAN-FORMALIZED] [CLASSICAL PARENT]`
  `[NOT NEW SCIENTIFIC KNOWLEDGE] [UNIFIED-FIELD CONSTRAINT] [NOT AN RH RESULT]`
- **Lean:**
  `formal/GaloisForLFunctions/HTGeometry/SourceGaugeLaurentTwoFace.lean`
- **Inertia parent:** `source-rigidification-face-inertia.md`
- **Residue-seam parent:** `../projective-horizon-laurent-residue-seam.md`

## Theorem

Let `K[X,X^(-1)]` be the finite-character shadow of the one-periodic gauge field under
`X=exp(2 pi i z)`.  Define

```text
Reg_0(f)     iff f_n=0 for n<0,
Reg_infty(f) iff f_n=0 for n>0.                            (1)
```

Lean proves, over every nontrivial semiring where required:

```text
Reg_0(X^n)       iff n>=0;
Reg_infty(X^n)   iff n<=0;
Reg_0(f(X^-1))   iff Reg_infty(f);
Reg_infty(f(X^-1)) iff Reg_0(f);                           (2)

Reg_0(f) and Reg_infty(f)
  iff f is constant;                                      (3)

Reg_0(f) and Reg_infty(f) and f_0=0
  implies f=0.                                             (4)

P contained in Reg_0 and invariant under X <-> X^(-1)
  implies every f in P is constant.                        (5)
```

Each face alone is nonconservative: `X` survives the zero face and `X^(-1)` survives the infinity
face.  The two faces jointly retain only the scalar gauge, and one scalar normalization kills it.
Equation `(5)` is the orientation-surgery no-go: no nontrivial inversion-invariant normalization
can canonically choose one of the two faces.  The maximal canonical object is their unordered
polarized pair; selecting a face is extra orientation data.

## No-go and positive successor

```text
[NO-GO]
The one-sided prediction
  X^m mod X^(m+1) <-> exp(2 pi i m z), m>=1,
cannot classify all born source inertia.  The valid periodic gauge exp(-2 pi i z) is X^(-1) and
lies outside every positive normal layer.

[POSITIVE]
Finite character inertia has an exact two-face polarization.  Positive weights are the zero-face
sector, negative weights are the infinity-face sector, orientation reversal exchanges them, and
their normalized joint-fixed intersection is zero.
```

This is the maximal correct finite-character theorem.  The full analytic periodic gauge field is
larger than Laurent polynomials: functions on the punctured quotient may have infinite tails or
essential singularities at either face.  Its completion must therefore be annular/Tate-like; a
one-sided formal Laurent field is still too small.

## Scientific role

The algebra is classical and is not a paper-level novelty claim.  It supplies three hard design
constraints on the proposed HT obstruction object:

1. the object needs two opposite lattices/faces, not one filtration;
2. a bare source cannot choose a transverse counterface, by the common-kernel reconstruction
   theorem;
3. the canonical datum is the relative position of source inertia and an independently supplied
   counterface, not a canonically reconstructed solution.

Together with the already-formalized Laurent residue seam, `(2)`--`(4)` identify the finite local
model as a self-dual polarized Tate object: same-face modes are seam-blind, opposite modes pair,
and joint transversality removes the normalized gauge.  Constructing that assignment naturally
for nonlinear HT constraints is the candidate-new theorem; this card does not claim it.

## Lean declarations

```text
LaurentRegularAtZero
LaurentRegularAtInfinity
laurentRegularAtZero_T_iff
laurentRegularAtInfinity_T_iff
laurentRegularAtZero_invert_iff
laurentRegularAtInfinity_invert_iff
laurent_eq_C_coeff_zero_of_biFace
laurent_biFace_iff_eq_C
laurent_inversionInvariant_zeroSubface_rigid
laurent_biFace_normalized_eq_zero
laurent_zeroFace_not_rigid
laurent_infinityFace_not_rigid
```

## Verification

- the required Laurent dependency cache was present;
- exactly one targeted build was run because the new module's `.olean` was missing:
  `lake build +GaloisForLFunctions.HTGeometry.SourceGaugeLaurentTwoFace`;
- `lake env lean GaloisForLFunctions/HTGeometry/SourceGaugeLaurentTwoFace.lean` passed silently;
- axiom inspection reports only `propext`, `Classical.choice`, and `Quot.sound`;
- no full or concurrent Lean build was run.

## Gates

- [x] negative-mode falsifier for the one-sided model identified
- [x] nontrivial positive replacement proved
- [x] opposite-face exchange proved
- [x] normalized common gauge calculated exactly
- [x] Lean formalization unconditional
- [x] parent algebra separated from the candidate-new HT assignment
