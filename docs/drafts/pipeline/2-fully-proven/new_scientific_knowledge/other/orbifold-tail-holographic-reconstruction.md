# The hypertranscendental tail reconstructs its parabolic orbifold

- **ID:** `orbifold-tail-holographic-reconstruction`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Scientific status:** `[PROVED HERE] [CANDIDATE NEW SCIENTIFIC KNOWLEDGE]`
- **Depends on:** `rational-coarse-graining-orbifold-tail-classification`
- **Statement:** A nontrivial rational coarse-graining tail is a complete invariant of the
  parabolic orbifold retained at infinite depth: two rational maps have the same embedded tail
  field exactly when they preserve the same parabolic orbifold.

## Theorem

Let `C` be the complex numbers with trivial derivation, let `y` be differentially transcendental
over `C`, and let `R_1,R_2 in C(z)` have degree at least two.  Suppose their rational
coarse-graining tails are nonconstant.  For `i=1,2`, let

```text
tau_i = q_i(z)(dz)^(k_i)
```

be the minimal parallel orbifold tensor of `R_i`, and put

```text
Q_i = q_i(y)(delta y)^(k_i).
```

Then the following are equivalent.

1. `Tail(R_1)=Tail(R_2)` as embedded differential subfields of `C<y>`.
2. `k_1=k_2` and `tau_2=s tau_1` for some `s in C^*`.
3. `R_1` and `R_2` preserve the same parabolic orbifold structure on the projective line.

Consequently the nonconstant embedded tail fields are in bijection with the parabolic orbifold
structures on `P1` that admit a degree-at-least-two self-cover.

## Proof

The tail classification theorem gives

```text
Tail(R_i)=C<Q_i>.                                            (1)
```

Assume the two fields in (1) are equal.  Both `Q_1` and `Q_2` are differentially transcendental
and each generates that common scalar differential rational field.  Differential-order
additivity applied to the two mutually inverse expressions therefore forces both expressions to
have order zero.  Hence there are `a,b,c,d in C`, with `ad-bc != 0`, such that

```text
Q_2 = (a Q_1+b)/(c Q_1+d).                                  (2)
```

Now work in the ordinary rational function field

```text
C(y)(t),   t=delta y.
```

The first jet `t` is transcendental over `C(y)`, because the full jet family of `y` is
algebraically independent.  Substituting `Q_i=q_i(y)t^(k_i)` into (2) and clearing the denominator
gives

```text
c q_1 q_2 t^(k_1+k_2)
  + d q_2 t^(k_2)
  - a q_1 t^(k_1)
  - b = 0.                                                   (3)
```

Both `k_i` are positive and both `q_i` are nonzero.  The unique highest power in (3) is
`t^(k_1+k_2)`, so its coefficient forces `c=0`.  Nondegeneracy then gives `a,d != 0`, and (3)
reduces to

```text
d q_2 t^(k_2) - a q_1 t^(k_1) - b = 0.                     (4)
```

The constant coefficient forces `b=0`.  Linear independence of the powers of the transcendental
`t` now forces

```text
k_1=k_2,      q_2=(a/d)q_1.                                 (5)
```

This proves `1 => 2`; `2 => 1` is immediate from (1).

For a parabolic orbifold, its minimal parallel tensor determines the ramification weights: the
fractional orders in the tensor divisor are `-k(1-1/n_p)`.  Thus proportional minimal tensors
determine the same orbifold, proving `2 => 3`.  Conversely a parabolic orbifold has a
one-dimensional space of minimal parallel tensors, so maps preserving the same orbifold have
proportional tensors.  This proves `3 => 2`.

## Physical interpretation

The infinite-depth field is a holographic boundary in a literal algebraic sense.  It does not
merely say that some information survived.  Its embedding in the free HT jet field reconstructs

```text
the holonomy order,
the orbifold divisor,
and therefore the complete parabolic topology
```

of the coarse-graining law.  Position information is erased by dense deck translations, but the
finite holonomy is exactly recoverable from the power with which invariant velocity survives.

This is static constraint mathematics: no carrier or time evolution is attached to the HT source.
The topology is relational data between a free source and a chosen coarse-graining operation.

## Novelty and significance gate

- The proof uses the tail classification theorem plus elementary differential-generator and
  polynomial rigidity.
- Classical orbifold dynamics classifies exceptional maps, but no checked source identifies the
  embedded differential tail as a complete reconstruction invariant for the orbifold.
- The theorem upgrades a zero-one detector to a completeness theorem: the boundary field retains
  all of the exceptional topology and no positional data.
- The novelty status remains provisional pending specialist database review.

## RH impact audit

There is no direct RH consequence.  The theorem says that any future nontrivial rational
coarse-graining tail of a completed `L`-function would determine its parabolic orbifold uniquely.
No such coarse-graining or orbifold is currently supplied by the zeta functional equation, so
this is a diagnostic constraint, not an RH bridge.

## Lean status

`SchwarzianProjectiveInvariant.lean` formalizes the projective generator invariant used by the
tail classification.  `OrbifoldTailReconstruction.lean` now formalizes:

```text
monomial_mobius_cleared_rigidity
firstJet_mobius_rigidity
hypertranscendentalOver_deriv_transcendental_adjoin_self
hypertranscendental_orbifoldCurrent_mobius_rigidity
```

Thus the complete first-jet coefficient separation in (3)--(5) is machine checked.  Assembly with
the still-paper-level Casale and exceptional fixed-field inputs remains before the entire theorem
can move to stage 3.

## Gates

- [x] 0 -> 1: exact reconstruction claim and proof route isolated
- [x] 1 -> 2: complete paper proof
- [ ] 2 -> 3: first-jet Möbius rigidity is formalized; assemble with the complete tail interface
- [ ] 3 -> 4: independent novelty audit and standalone publication

## Lean status — the order calculus and the scaling branch

The classification this card consumes advanced in the pass-4 section of
`rational-coarse-graining-orbifold-tail-classification.md`: the signed order on `RatFunc`, its
composition law, the transport of the invariance relation along the map, forward and backward
orbits, and the degree obstruction for weight-zero relations are all unconditional Lean theorems
(`HTGeometry/RationalOrder.lean`, `RationalOrderComposition.lean`, `RationalInvariantOrbit.lean`,
`RationalBackwardOrbit.lean`).  For `z^2+1` and `(z-1)^2` they already give the complete
non-existence of invariant rational differentials
(`HTGeometry/QuadraticNoInvariantDifferential.lean`), hence no nonconstant scaling eigenvector of
the substitution (`HTGeometry/QuadraticOrbifoldTail.lean`).  The remaining input for this card is
unchanged: the fixed branch `Phi_R(u) = u` of the tail classification.

## Lean status — the tail interface is one condition, and holds through jet order two

`HTGeometry/JetFixedFieldShift.lean` proves that at jet level `M >= 2` a normalizing shift *is* a
`Phi_R`-fixed element of jet order exactly `M` (`hasNormalizingShift_iff_exists_fixed`), so the
complete-tail interface this card assembles with is equivalent to a single family of statements:

```text
quadOne_forall_fixed_isConst_iff,  quadTwo_forall_fixed_isConst_iff
  (HTGeometry/QuadraticTailShiftEquivalence.lean) :
  Tail(R) = C   <=>   no jet level of order at least two carries a normalizing shift.
```

Level two is settled — neither quadratic map admits a rational affine connection, hence no shift at
level two — so `quadOne_fixed_of_order_two` and `quadTwo_fixed_of_order_two` give unconditionally
that a fixed element of jet order at most two is constant.  Higher levels are reduced by
`HTGeometry/QuadraticShiftDescentBranches.lean` to the polynomial branches of degree one and two in
the top coordinate; the degree-zero branch is closed by `∂_(N+2) sigma_(N+3) = (N+3)·R''·y_1 ≠ 0`.
