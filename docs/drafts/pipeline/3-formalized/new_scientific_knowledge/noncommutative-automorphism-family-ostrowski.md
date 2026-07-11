# Noncommutative automorphism-family Ostrowski theorem

- **ID:** `noncommutative-automorphism-family-ostrowski`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Scientific status:** `[CANDIDATE NEW SCIENTIFIC KNOWLEDGE]`
- **Statement:** Algebraic dependence of additive primitives for an arbitrary, possibly
  noncommuting family of compatible field automorphisms forces one nonzero fixed-field linear
  combination of all increment cocycles to be the simultaneous coboundary of a single base-field
  element. The corresponding all-jet nonsummability condition implies differential algebraic
  independence.

## Theorem

Let `C -> K -> L` be a tower of fields with `char(K)=0`. Let

```text
tau_i   : K ≃+* K,
sigma_i : L ≃+* L                    (i in I)
```

be an arbitrary family of automorphisms satisfying

```text
sigma_i(algebraMap(K,L)(k)) = algebraMap(K,L)(tau_i(k)).
```

No relation, composition law, or pairwise commutativity is imposed on the family. Assume that
every `sigma_i` fixes the image of `C` and that the common fixed field in `L` is exactly the image
of `C`. Let `x_a in L` and `b_(i,a) in K` satisfy

```text
sigma_i(x_a) = x_a + algebraMap(K,L)(b_(i,a)).
```

If the family `(x_a)` is algebraically dependent over `K`, then there are a nonzero finitely
supported coefficient vector `c : A ->_0 C` and one element `k in K` such that, simultaneously
for every `i in I`,

```text
tau_i(k) - k = sum_a c_a b_(i,a).
```

The index types `I` and `A` may be infinite; the conclusion is finite because `c` is finitely
supported.

If `K -> L` is a differential field extension, every `sigma_i` commutes with the derivation, and
the displayed simultaneous telescoping equation has no solution for any nonzero finite
fixed-field linear combination of the full jet family

```text
(delta^n b_(i,a))_(a,n),
```

then `(x_a)` is differentially algebraically independent over `K`.

## Proof

Assume first that `(x_a)` is algebraically dependent. In characteristic zero, the universal
Kähler differentials `(d x_a)` are linearly dependent over `L`. Let `W` be their coefficient
relation space in the finitely supported free module `A ->_0 L`.

For each `i`, conjugation of a `K`-derivation by `tau_i` and `sigma_i` shows that `W` is stable
under coordinatewise application of `sigma_i`. Choose a nonzero vector of least support in `W`
and normalize one supported coordinate to one. Its image under any `sigma_i` has the same support,
the same normalized coordinate, and still belongs to `W`. The difference would otherwise be a
nonzero relation with strictly smaller support. Hence the normalized vector is fixed by every
`sigma_i`. Exactness of the common fixed field therefore gives a nonzero relation vector with
coefficients in `C`.

Let

```text
g = sum_a c_a x_a.
```

Then `d g = 0`. The characteristic-zero kernel theorem for universal Kähler differentials gives
that `g` is algebraic over `K`. Moreover

```text
sigma_i(g) = g + algebraMap(K,L)(sum_a c_a b_(i,a)).
```

Write `P=minpoly_K(g)`. Naturality of the minimal polynomial under the compatible pair
`(tau_i,sigma_i)` and translation by the increment imply

```text
tau_i(P.nextCoeff)
  = P.nextCoeff - degree(P) * sum_a c_a b_(i,a).
```

Since the characteristic is zero, division by `degree(P)` is valid. Thus the trace coordinate

```text
z = g + algebraMap(K,L)(P.nextCoeff / degree(P))
```

is fixed by every `sigma_i`. Consequently `z` lies in `C`, so `g` is a base-field element plus a
joint constant. Taking every automorphism defect gives the claimed simultaneous equation with
the same base element in all directions.

For the differential statement, apply the algebraic theorem to the family

```text
x_(a,n) = delta^n x_a.
```

Commutation with the derivation gives increments `delta^n b_(i,a)`. Algebraic dependence of this
jet family would produce the excluded finite simultaneous telescoper. Therefore the jet family is
algebraically independent, which is exactly differential algebraic independence of `(x_a)`.

At no point is `sigma_i sigma_j = sigma_j sigma_i` used.

## Significance

1. The usual parameterized Picard--Vessiot torsor, differential Galois group, and fixed-field
   correspondence are not needed for additive primitives. A Kähler circuit plus a minimal
   polynomial trace coordinate gives the dependence-to-telescoping theorem directly.
2. The theorem is not restricted to one difference operator or to commuting lattices. It applies
   to arbitrary nonabelian symmetry families, opening a hypertranscendence route for functions
   controlled by modular, monodromy, or deck-transformation actions.
3. It is an exact finite-certificate principle despite arbitrary index sets: every differential
   algebraic relation forces one finite fixed-field jet combination and one common base primitive.
4. For the multiple elliptic gamma route it strictly strengthens the needed paired commuting-shift
   lemma and removes the outstanding PPV dependency.

The theorem does not by itself prove hypertranscendence of a concrete function. Each application
still requires an analytic or arithmetic proof that the relevant simultaneous coboundary equation
has no solution in the chosen base field.

## Novelty audit

Classical Kolchin--Ostrowski theory treats antiderivatives for a derivation. Parameterized
Kolchin--Ostrowski and parameterized telescoping results treat commuting differential/difference
settings or a single distinguished difference operator. Pogudin's several-operator primitive
element theorem explicitly assumes commuting operators. The two-operator independence literature
located in the audit likewise studies structured commuting pairs. No source located in the
primary-literature search states the arbitrary noncommuting automorphism-family theorem above,
the simultaneous single-base-element conclusion, or its all-jet differential-independence
contrapositive.

This is affirmative evidence, not a proof of absence from the literature. The scientific novelty
label remains provisional pending independent expert and MathSciNet/Zentralblatt review.

## Lean certificate

`formal/GaloisForLFunctions/AutomorphismFamilyOstrowski.lean` proves:

```text
automorphismFamily_algebraicPrimitive_traceCoordinate_fixed
automorphismFamily_algebraicPrimitive_eq_base_add_fixed
automorphismFamily_exists_nonzero_constant_kaehler_relation_of_dependent_base_shifts
automorphismFamily_exists_nonzero_constant_algebraic_linearCombination
automorphismFamily_exists_nonzero_constant_simultaneous_telescoping
automorphismFamily_algebraicIndependent_of_no_constant_simultaneous_telescoping
automorphismFamily_differentialIndependent_of_no_constant_simultaneous_jet_telescoping
```

The main theorem and differential corollary build under the repository toolchain. Their axiom
reports contain only Lean's standard `propext`, `Classical.choice`, and `Quot.sound` axioms.

## Gates

- [x] well-posed theorem with exact fixed-field hypotheses
- [x] complete paper proof
- [x] arbitrary and infinite index families
- [x] pairwise commutativity removed
- [x] all-jet differential criterion proved
- [x] unconditional Lean formalization
- [x] targeted build passes
- [x] formal lint passes
- [x] preliminary primary-literature search
- [ ] independent specialist novelty audit
- [ ] concrete nonabelian hypertranscendence application

## References checked

- E. R. Kolchin, *Algebraic groups and algebraic dependence*, 1968.
- C. Hardouin and M. F. Singer, *Differential Galois theory of linear difference equations*,
  2008.
- C. Schneider, *Parameterized Telescoping Proves Algebraic Independence of Sums*, 2008.
- G. Pogudin, *Primitive Element Theorem for Fields with Commuting Derivations and
  Automorphisms*, 2018.
- B. Adamczewski, T. Dreyfus, C. Hardouin, and M. Wibmer, *Algebraic independence and linear
  difference equations*, 2020.

## Log

- 2026-07-11 -- Extracted the arbitrary-family theorem from the several-shift elliptic-gamma
  proof after observing that neither Kähler circuit descent nor the algebraic trace-coordinate
  argument uses pairwise commutativity.
- 2026-07-11 -- Formalized the algebraic theorem and its full-jet differential-independence
  contrapositive in Lean without project axioms.
