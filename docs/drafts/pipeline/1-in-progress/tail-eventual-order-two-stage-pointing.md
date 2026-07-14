# Tail eventual order and two-stage prime pointing

- **ID:** `tail-eventual-order-two-stage-pointing`
- **Stage:** 1-in-progress
- **Type:** GENERAL HT CONSTRAINT LAW
- **Scientific status:** `[NOVELTY UNVERIFIED]`; the quotient-order core is `[BRIDGE]`

## Statement

For an arbitrary coordinate set `I`, put

```text
T_I = R^I / R^(I),
```

where `R^(I)` is the subspace of finitely supported functions.  Define

```text
[a] <=_tail [b]
  iff b(i)-a(i) >= 0 outside a finite subset of I.             (1)
```

Then `(1)` is a well-defined partial order on `T_I`.  Its positive cone has the exact fibre
description

```text
0 <=_tail [a]
  iff [a] has a coordinatewise nonnegative representative
  iff {i : a(i)<0} is finite.                                 (2)
```

The cone is pointed: if both `[a]` and `-[a]` are positive, then `[a]=0`.  Translation and
multiplication by positive real scalars preserve and reflect the order.

For Boolean prime orientations `epsilon(p) in {+1,-1}`, `(2)` specializes to

```text
0 <=_tail [epsilon]  iff  [epsilon]=[+1].                     (3)
```

Thus the eventual cone selects exactly the all-positive tail class.  If `w_p>0` are atomic
weights, positivity of every atom `epsilon(p)w_p` then selects the unique all-positive
representative inside that class.  Prime orientation therefore has a canonical two-stage
pointing:

```text
differential tail class --eventual cone--> [+1]
                         --atomic positivity--> +1.           (4)
```

## HT interpretation

The differential algebra of a finite prime-Dirichlet family is controlled by tail classes.  Exact
coordinatewise positivity is not a function of a tail class, but the weaker and canonical
existential statement “this class has a positive representative” is a function of the class and
defines the order `(1)`.  Hence a tail differential matroid is not intrinsically orderless: over
real coefficients it has a canonical eventual cone.

This corrects the stronger no-go formulation that positivity simply does not descend.  What does
not descend is the exact positive representative.  The quotient cone chooses the coarse class;
spectral or atomic positivity chooses the point in its finite-support fibre.

## RH application boundary

For the prime-zeta orientation, the eventual cone canonically selects the zeta tail class, while
Bochner positivity of the vertical trace selects the exact all-positive Euler representative.
This still does not imply RH.  An RH-ready carrier must additionally retain the analytically
continued divisor and the reflection-odd defect, because neither is determined by the ordered
tail point.

The positive architectural statement is:

> A prime-Dirichlet HT carrier capable of expressing an RH criterion must be at least a three-layer
> object: ordered operator-tail class, exact spectral pointing in its finite-support fibre, and
> continued reflection/divisor polarization.

## Proof

Finite-support equivalence preserves finiteness of negative support.  Closure of the eventual cone
under addition follows because `a(i)+b(i)<0` forces `a(i)<0` or `b(i)<0`.  Closure under a
nonnegative scalar is immediate.  If both `a` and `-a` have finite negative support, every nonzero
coordinate of `a` lies in their union, so `a` is finitely supported.  These facts give reflexivity,
transitivity, and antisymmetry of `(1)` on the quotient.

For a Boolean orientation, a sign differs from `+1` exactly at its negative coordinates.  It is
eventually nonnegative exactly when that set is finite, which is exactly equality with `[+1]` in
`T_I`.  Strict positivity of every weighted atom is equivalent to every sign being `+1`.

## Attacks

1. **Ordered-vector-space collision.**  Quotients by order ideals and eventual orders are
   classical.  The abstract order theorem is a bridge, not new scientific knowledge.
2. **Boolean triviality attack.**  Equation `(3)` is elementary in isolation.  Potential
   significance can only lie in its exact compatibility with the operator-tail differential
   field classifier and the subsequent unique spectral pointing.
3. **Topology attack.**  Tail-equivalence classes are dense in the product orientation cube, so
   the quotient order is not represented by a nonconstant continuous observable on the raw cube.
   The order is algebraic, not a compact-Hausdorff coordinate.
4. **RH upcast attack.**  Equations `(1)`--`(4)` select the Euler orientation but do not see zeros
   after analytic continuation.  Reflection/divisor data remain transverse.
5. **Novelty gate.**  Search ordered quotient spaces, reduced products, germs modulo finite sets,
   ordered matroids, and differential-field realizations before making any scientific novelty
   claim.

## Formal surface

`formal/GaloisForLFunctions/HTGeometry/TailEventualOrder.lean` contains:

- `eventuallyNonnegative_iff_exists_positiveRepresentative`;
- `eventuallyNonnegative_congr`;
- `finiteTailEquivalent_zero_of_eventuallyNonnegative_neg`;
- `tailEventuallyLE_trans` and `tailEventuallyLE_antisymm`;
- the `PartialOrder (RealTailQuotient I)` instance;
- `tailEventuallyLE_add_iff` and `tailEventuallyLE_smul_iff`;
- `primeOrientation_eventuallyNonnegative_iff_allPositiveTail`;
- `primeOrientation_twoStagePointing`.

## Gates

- [x] exact quotient order isolated
- [x] complete paper proof
- [x] source-level formal proof without project hypotheses
- [x] narrow module build
- [x] axiom audit: only `propext`, `Classical.choice`, and `Quot.sound`
- [ ] connect to the analytic operator-tail capstone after the external classical bridge lands
- [ ] complete parent-theory and literature audit
- [ ] determine whether the combined two-stage prime pointing is scientifically non-routine
