# Countable semilocal Gram diagonal to RH

- **ID:** `countable-semilocal-gram-diagonal-to-rh`
- **Stage:** 1-in-progress
- **Type:** CONJECTURE / `[RH-SUFFICIENT SOURCE ROUTE]`
- **Source:** `XiTraceHankelCountableCriterion.lean`, `XiRelativeResolventFlux.lean`, and the
  principal-relative Sonin trace stack
- **Statement:** It is enough to realize, separately for each `P in Int[X]`, the source-defined Xi
  trace-Hankel value as a limit of nonnegative compact-support semilocal Gram energies. No universal
  positive operator, all-moment equality, or uniformity in the polynomial degree is required.

## Goal

Let

```text
Q(P) = Re(xiCentralTraceHankel(P mapped to Real)).
```

For every `P : Polynomial Int`, construct source-defined Hilbert--Schmidt kernels `K(P,j)` from
finite prime--archimedean semilocal test data such that

```text
hsNormSq(K(P,j)) -> Q(P).                                      (1)
```

Each term on the left is nonnegative. Therefore `Q(P)>=0` for every integer polynomial, and the
formal theorem

```text
xiCentralTraceHankelIntNonnegative_iff_riemannHypothesis
```

proves RH.

The kernels must be constructed before reading the Xi divisor. Equality `(1)` may use the already
proved source identity between the continued prime--archimedean relative trace and the Xi relative
resolvent, but positivity may not be imported from an RH-equivalent divisor or Weil criterion.

## Gates

- [x] 0 -> 1 in-progress: exact countable endpoint and source-pure sufficient statement isolated
- [ ] 1 -> 2 fully-proven: construct the per-test kernels and prove `(1)` for every integer polynomial
- [ ] 2 -> 3 formalized: source construction, convergence, and composition with the countable Lean
  criterion
- [ ] 3 -> 4 publication-ready: standalone semilocal source proof and Lean certificate

## Why this is strictly weaker than the previous Sonin weld

The previous target asked for one positive trace-class operator `T` satisfying

```text
Tr(T^(n+1)) = xiCentralReciprocalMoment(n)   for every n.       (2)
```

That forces one coherent Stieltjes moment sequence, all mixed polynomial identities, and one
operator valid at every degree. The countable criterion needs none of this. For a polynomial of
degree `d`, `Q(P)` uses only the finite block of moments with indices at most `2d`; the aperture,
finite prime support, renormalization, and Gram carrier may all depend on `P`. Only the scalar limit
`(1)` must be correct.

Thus the new chain is

```text
per-integer-test compact-support source Gram convergence
  -> Q(P)>=0 for every P in Int[X]
  -> countable trace-Hankel criterion
  -> RH.
```

It does not follow formally from the universal-moment route: `(1)` permits incompatible Gram
realizations for different tests and requires no operator whose powers generate them all.

## Source-side attack

For fixed `P` of degree `d`:

1. use the continued source trace
   `continuedPrimeArchSourceRelativeTrace`, which contains only `-zeta'/zeta` and the fixed
   archimedean/boundary factor;
2. extract only the finite local jet needed for the moments `0,...,2d`;
3. approximate that jet by a compact-support prime-power test whose cutoff is allowed to depend on
   `P`;
4. realize the resulting scalar quadratic combination as the squared Hilbert--Schmidt norm of a
   principal-relative log-coordinate test operator;
5. pass to the scalar limit.

The countable reduction removes every uniform-in-degree and simultaneous-moment requirement. A
diagonal enumeration of `Int[X]` can be used after the individual tests are constructed, but no
diagonalization is needed for the logical implication to RH.

## Positive exclusions inherited from the Sonin audit

The residual-only block-diagonal operator cannot supply `(1)`: its powers square the regularized
Euler coefficients and delete mixed prime words. The fixed projection-correction scalarization
also cannot supply `(1)`: its geometric response is uniformly bounded, whereas the required local
von-Mangoldt response contains the unbounded scale `m log p`.

Consequently a successful per-test kernel must positively retain the principal shell and the
logarithmic scale length. The appropriate object is a genuine log-coordinate convolution or
semilocal trace-formula test operator, allowed to vary with `P`.

## Open core

`[OPEN RH CORE]` For one arbitrary integer polynomial `P`, construct a source-defined
principal-relative compact-support kernel and prove `(1)`. The first decisive case is not a
monomial but a two-term polynomial `P=X^r+cX^s`, because it tests whether the construction carries
the mixed anti-diagonal moment rather than only positive diagonal energies.

## Log

- 2026-07-11 -- Countable integer-polynomial RH criterion formalized; universal all-moment Sonin
  weld weakened to independent per-test Gram convergence.
