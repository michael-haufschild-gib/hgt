# Theta Mellin pair Krein signature

- **ID:** `theta-mellin-pair-krein-signature`
- **Stage:** 3-formalized
- **Type:** UNCONDITIONAL LINEAR-ALGEBRA CORE / HILBERT--POLYA CARRIER LAW
- **Scientific status:** `[PROVED IN LEAN] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Lean module:** `GaloisForLFunctions/RHTower/ThetaMellinPairSignature.lean`

## Statement

For real parameters `C,d` define the affine logarithmic pair core

```text
K(u,v)=C-d(u+v).
```

Then every two-point determinant is

```text
K(u,u)K(v,v)-K(u,v)K(v,u)=-d^2(u-v)^2.                  (1)
```

More generally, after arbitrary diagonal weighting

```text
K_w(i,j)=w_i w_j [C-d(u_i+u_j)],
```

one has

```text
det K_w|_{i,j}
 =-[w_i w_j d(u_i-u_j)]^2.                              (2)
```

Thus nonzero weights, `d!=0`, and distinct logarithmic coordinates force a strictly negative
two-point determinant.  The corresponding symmetric two-dimensional block is indefinite.  In
fact its quadratic form has the light-cone normal form

```text
Q(x,y)=(x+y)[C(x+y)-2d(ux+vy)],                           (3)
```

and, when `d!=0` and `u!=v`, represents every real scalar.  Hence positive and negative
directions are constructed explicitly rather than inferred from an unformalized spectral theorem.

## Hilbert--Polya meaning

In the absolute-convergence half-plane, the ordered theta-Mellin pair kernel has exactly this
form after removing a diagonal unitary phase.  Formula `(2)` therefore proves the algebraic core
of the statement that every two distinct theta atoms form a Krein plane.  It does not formalize
the analytic Mellin integral or the interchange of the differentiated infinite sum.

The positive carrier obligation is:

> Orientation must be proved on the distinguished completed all-prime section.  It cannot be
> obtained by making the ambient atom-coefficient kernel positive or by assigning a positive Gram
> vector to every ordered pair.

This conclusion is elementary two-by-two determinant algebra.  Its use in the Hedenmalm route is
structural, but the theorem itself is conservatively classified as not new scientific knowledge.

## Formal declarations

- `thetaMellinPairCore`
- `thetaMellinPairCore_comm`
- `thetaMellinPairCore_twoPoint_det`
- `thetaMellinPairCore_twoPoint_det_neg`
- `thetaMellinPairQuadratic`
- `thetaMellinPairQuadratic_eq`
- `exists_thetaMellinPairQuadratic_eq`
- `thetaMellinPairQuadratic_has_both_signs`
- `thetaMellinWeightedPairCore`
- `thetaMellinWeightedPairCore_twoPoint_det`
- `thetaMellinWeightedPairCore_twoPoint_det_neg`
- `thetaMellinPairPhase`
- `thetaMellinPairPhase_mul_swap`
- `thetaMellinPhasedPairCore`
- `thetaMellinPhasedPairCore_twoPoint_det`

## Verification boundary

The Lean theorem uses no RH hypothesis, no zero data, and no positivity assumption.  The exact
Hedenmalm atom Mellin factorization and its analytic summation domain remain paper-level inputs in
`theta-wigner-eisenstein-orientation-current.md` and are not claimed formalized here.
