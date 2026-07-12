# Rational-coefficient prime-log differential-relation escape

- **ID:** `rational-coefficient-prime-log-differential-relation-escape`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) — `[PROVED] [FORMALIZED] [BRIDGE]`
- **Lane:** rational differential coefficients; pole-safe finite-jet avoidance
- **Statement:** Every nonzero finite differential relation over `C(X)` has a canonical nonzero
  simultaneous denominator clearing, an upper-half-plane specialization away from every
  coefficient pole, and an actual prime-log differential-jet escape inside every bounded-gauge
  neighborhood.

## The theorem

For

```text
Q in K(X)[Y_s:s in S]
```

with finite support, define

```text
D_Q=product_(d in supp Q) denom(coeff_d Q),

Q_clear=sum_(d in supp Q)
  Y^d num(coeff_d Q) product_(e in supp Q, e!=d) denom(coeff_e Q).
```

Then

```text
D_Q!=0,
Q!=0 implies Q_clear!=0,
map(Q_clear)=D_Q Q                                          (1)
```

in `K(X)[Y_s:s in S]`.  Thus simultaneous denominator clearing preserves the relation exactly and
cannot annihilate a nonzero relation.

For `K=C`, every height `H` admits `z` with

```text
Im z>H,
D_Q(z)!=0,
Q_clear(z,Y)!=0.                                            (2)
```

The proof chooses a supported coefficient of `Q_clear` and avoids the finite root set of its
product with `D_Q` on an infinite vertical ray.  At such a point coefficientwise rational
evaluation is honest and satisfies

```text
D_Q(z) Q(z,Y)=Q_clear(z,Y).                                 (3)
```

Hence `Q(z,Y)` is nonzero.

For a finite injective shift packet, choose `H` high enough that every translated node lies in the
upper half-plane.  Actual prime-log differential-jet controllability then breaks `Q(z,Y)` by an
arbitrarily small finitely supported positive mass perturbation, represented by a bounded gauge
inside any prescribed uniform gauge ball.

## Positive law

> **Pole-safe finite-relation fullness.** Rational differential coefficients add a finite pole
> divisor but no new local rigidity: every fixed nonzero `C(X)`-coefficient relation can be tested
> off that divisor and escaped within every bounded positive prime-log gauge neighborhood.

This is stronger than polynomial-coefficient escape because it reaches the original rational
relation after an exact pole-safe specialization.  It does not by itself give one gauge avoiding
all `C(X)`-coefficient relations simultaneously.  Since `C` is uncountable, the remaining generic
HT step must package all coefficient vectors with one fixed finite monomial support and coefficient
degree into a single evaluation-matrix rank-defect locus.  Countable enumeration of individual
relations is not a valid substitute.  The generic finite-dimensional packet theorem underlying
that packaging is now formalized in `finite-full-rank-evaluation-packet`; its specialization to
expanded jet monomials and the bounded-gauge topology remains.

## Lean certificate

`GaloisForLFunctions.HTGeometry.RationalCoefficientClearing` proves:

- `ratFuncCommonDenominator_ne_zero`;
- `clearRatFuncCoefficients_ne_zero`;
- `map_clearRatFuncCoefficients`;
- `exists_upper_specialization_avoiding_polynomial`;
- `specializeRatFuncCoefficients_clearing` and
  `specializeRatFuncCoefficients_ne_zero`;
- `primeDyadic_actualRationalDifferentialRelation_has_gaugeBall_escape`.

The module builds unconditionally.  The principal theorems have only the standard Lean axioms
`propext`, `Classical.choice`, and `Quot.sound`; there is no `sorry`, `admit`, project axiom, opaque
postulate, or unsafe declaration.

## Classification

Simultaneous localization denominators, finite-root avoidance, and polynomial jet escape are
classical mechanisms.  Their exact composition closes a required formal bridge but is not the
candidate-new scientific object.  The candidate novelty remains the facet-sewn universal HT
constraint geometry.

## Gates

- [x] 0 → 1: exact canonical denominator and pole-safe escape statement isolated
- [x] 1 → 2: complete unconditional proof
- [x] 2 → 3: clearing, specialization, pole avoidance, and actual differential escape formalized
- [ ] 3 → 4: no standalone publication planned; classified as a bridge
