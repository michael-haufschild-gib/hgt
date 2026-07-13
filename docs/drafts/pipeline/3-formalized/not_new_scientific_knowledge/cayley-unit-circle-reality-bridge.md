# Cayley unit-circle reality bridge

- **ID:** `cayley-unit-circle-reality-bridge`
- **Stage:** 3-formalized
- **Type:** `[BRIDGE] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Lean:** `formal/GaloisForLFunctions/HTGeometry/CayleyUnitCircleReality.lean`
- **Parent:** `../../1-in-progress/xi-cayley-paraorthogonal-opuc-rh.md`

## Statement

For

```text
C(z)=(z-i)/(z+i),
```

Lean proves

```text
|C(z)|=1  <->  Im(z)=0.                                  (1)
```

It also records the equivalent membership statement for the unit sphere in `C`.  The proof is
the exact identity

```text
|z-i|^2-|z+i|^2=-4 Im(z).
```

Thus any proof that the Cayley images of all zeros of a polynomial or entire function lie on the
unit circle immediately gives real-rootedness of the original object.  In the OPUC successor,
`(1)` is the terminal transport from paraorthogonal unit-circle roots to Xi/Jensen real roots.

## Positive statement

The Cayley change of variables is not itself a positivity theorem.  Its useful positive content is
that a unitary spectral model on the circle and a self-adjoint spectral model on the line have an
exact pointwise root-location dictionary.  The source burden remains construction of the unitary
model.

## Lean surface

```text
lineCayley
norm_lineCayley_eq_one_iff_im_eq_zero
lineCayley_mem_unitCircle_iff_real
```

## Gates

- [x] norm-one/reality equivalence formalized
- [x] unit-circle membership form formalized

