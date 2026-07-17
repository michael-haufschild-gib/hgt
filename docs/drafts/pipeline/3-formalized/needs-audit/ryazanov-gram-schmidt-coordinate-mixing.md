# Gram--Schmidt coordinates do not preserve the first original-basis coefficient

- **ID:** ryazanov-gram-schmidt-coordinate-mixing
- **Stage:** 3-formalized / needs-audit
- **Type:** THEOREM (paper)
- **Source:** Vladimir Ryazanov, *A disproof of the Riemann hypothesis on zeros of zeta-function*, arXiv:1808.10774v9, Theorem 1
- **Statement:** In the nested Nyman--Beurling spaces used by Ryazanov, the coefficient of `a_1` in the original basis is not the coefficient of `e_1` in the Gram--Schmidt basis; all later orthonormal vectors contribute to the former coordinate.

## Goal

Audit the coordinate substitution on which the preprint's contradiction rests.
This is a route discriminator, not an RH theorem.

## Gates

- [x] 0 -> 1 in-progress: the claimed contradiction reduces to one basis-coordinate identification
- [x] 1 -> 2 fully-proven: exact change-of-basis identity proved below, `[PROVED HERE]`
- [x] 2 -> 3 formalized: exact coordinate identity, first-coordinate decomposition, and explicit
  normalized Gram--Schmidt counterexample checked in Lean
- [ ] 3 -> 4 publication-ready

## Theorem `[PROVED HERE]`

Let `a_1,...,a_n` be a linearly independent family in a real Hilbert space.
Let `e_1,...,e_n` be the orthonormal family obtained by Gram--Schmidt in that
order, and write

```text
e_k = sum_{j<=k} c_{k,j} a_j.
```

If

```text
phi_n = sum_{k<=n} <chi,e_k> e_k
       = sum_{j<=n} h_j^(n) a_j,
```

then

```text
h_1^(n) = sum_{k<=n} <chi,e_k> c_{k,1}.
```

In particular, because `e_1=a_1/||a_1||`,

```text
h_1^(n)
  = <chi,e_1>/||a_1||
    + sum_{k=2}^n <chi,e_k> c_{k,1}.
```

There is no general identity between `h_1^(n)` and either
`<chi,e_1>` or `<chi,e_1>/||a_1||`.

### Proof

Substitute the triangular change of basis into the orthogonal expansion:

```text
phi_n
  = sum_{k<=n} <chi,e_k> sum_{j<=k} c_{k,j}a_j
  = sum_{j<=n} (sum_{k=j}^n <chi,e_k>c_{k,j})a_j.
```

Uniqueness of the coefficients in the linearly independent original family
gives the formula.  The displayed specialization follows from
`c_{1,1}=1/||a_1||`.  `QED`

## The omitted term is present in the cited construction

For the second Gram--Schmidt vector,

```text
e_2 = [a_2 - (<a_2,a_1>/||a_1||^2)a_1] / ||b_2||.
```

In the preprint's Nyman--Beurling realization, `a_1(t)={t}` and
`a_2(t)={t/2}` are nonnegative and simultaneously positive on a set of
positive measure in `L^2((0,infinity);t^(-2)dt)`.  Hence
`<a_2,a_1> > 0`, so `c_{2,1} != 0`.  Coordinate mixing is therefore not a
merely abstract possibility; it occurs at the first nontrivial step.

## Application to the claimed contradiction

Ryazanov's Lemma 1 states that if

```text
phi_n = sum_{j<=n} h_j^(n) a_j -> chi,
```

then `h_1^(n) -> -1`.  This controls the original `a_1` coordinate.  In the
proof of Theorem 1, the orthogonal projection is instead written as

```text
phi_n = sum_{k<=n} <chi,e_k>e_k,
```

and the fixed positive coefficient `<chi,e_1>` is treated as though Lemma 1
forced it to converge to a negative number.  The theorem above shows exactly
what is missing: the changing sum of `a_1` components from `e_2,...,e_n`.
Those terms can make `h_1^(n)` converge to `-1` while `<chi,e_1>` remains a
fixed positive number.  Therefore no contradiction follows.

## Lean status

The full linear-algebra surface is formalized unconditionally in
`formal/GaloisForLFunctions/RHTower/RyazanovGramSchmidtCoordinateMixing.lean`:

```text
changeOfBasis_sum
coordinate_eq_sum_changeOfBasis
projection_originalCoordinate
projection_firstOriginalCoordinate
ryazanovOriginalPair_linearIndependent
ryazanovOrthonormalPair_orthonormal
gramSchmidtNormed_ryazanovOriginalPair
ryazanovOrthonormalPair_triangular
ryazanov_coordinateMixing_counterexample
```

The concrete pair is proved to be Mathlib's normalized Gram--Schmidt output, not merely an
unrelated orthonormal basis.  Its second orthonormal vector has zero first orthonormal coordinate
but coefficient `-1` on the first original vector.  The exact module build, direct single-file
verification, and `#print axioms` audit passed; the load-bearing theorems use only Mathlib's standard
foundational axioms (`propext`, `Classical.choice`, and `Quot.sound`).

## Status

The linear-algebra obstruction is complete.  External bibliographic audit of
the current preprint version remains, so the card stays in `needs-audit`.
