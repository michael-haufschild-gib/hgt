# Exact scalar triangle holonomy law

Stage: 3-formalized

Status: `[LITERATURE] [PAPER-PROVED] [LEAN PROVED]`

Source: Theorem 6.2 of *Locally Quantum, Globally Non-Hilbertizable* (Zenodo 21982163).

## Exact claim

For amplitudes `a,b,c` in `[0,1]` and a unit complex phase `z`, the Hermitian sector

```text
[ 1    a    c conj(z) ]
[ a    1    b         ]
[ c z  b    1         ]
```

is positive semidefinite exactly when

```text
a^2 + b^2 + c^2 - 2abc Re(z) <= 1.
```

This is the scalar spectral wall consumed by the operator-valued triangle law after unitary gauge
reduction and diagonalization of loop holonomy.

## Proof and boundary audit

Necessity follows from the three two-point test vectors and nonnegativity of the determinant.  For
`a<1`, an exact `LDL*` square decomposition proves sufficiency.  At the singular boundary `a=1`,
the determinant margin decomposes as

```text
-(b-c)^2 - 2bc(1-Re(z)).
```

Its nonnegativity forces `b=c`; if the common amplitude is nonzero, unit norm and `Re(z)=1` force
`z=1`.  The remaining quadratic form is an explicit sum of two nonnegative squares.  Thus no
invertibility assumption silently discards the perfect-coherence boundary.

## Lean status

`formal/GaloisForLFunctions/HTGeometry/TriangleHolonomySectorLaw.lean`, headline declaration
`TriangleSectorDatum.posSemidef_iff`.  Amplitude and unit-phase constraints are intrinsic fields of
`TriangleSectorDatum`; theorem has no external premises and introduces no axioms.
