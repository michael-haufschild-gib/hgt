# The stable core of a scalar free differential field is projective

- **ID:** `scalar-differential-inversive-core-projective-law`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Scientific status:** `[PROVED HERE] [CANDIDATE NEW SCIENTIFIC KNOWLEDGE]`
- **Statement:** The intersection of all forward images of an injective differential
  endomorphism of a scalar free differential field is either the constant field or another scalar
  free differential field, and the induced automorphism of every nonconstant stable core is a
  unique projective transformation of its generator.

## Theorem

Let `C` be a differential field of characteristic zero and let `y` be differentially
transcendental over `C`.  Put

```text
F = C<y>.
```

Let `Phi : F -> F` be an injective differential `C`-endomorphism and define its stable core

```text
Core(Phi) = intersection over n >= 0 of Phi^n(F).
```

Exactly one of the following holds.

1. `Core(Phi) = C`.
2. There is an element `u in F`, differentially transcendental over `C`, such that

   ```text
   Core(Phi) = C<u>
   ```

   and there is a unique matrix class

   ```text
   [a b; c d] in PGL_2(C)
   ```

   for which

   ```text
   Phi(u) = (a u + b) / (c u + d).
   ```

In particular, a nonconstant finite-order observable survives arbitrarily deep forward
coarse-graining only if the complete surviving observable field is again a free
hypertranscendental scalar and the coarse-graining becomes reversible projective dynamics on that
scalar.

## Proof

Write `T = Core(Phi)`.  Intersections of differential subfields are differential subfields, so
`T` is a differential intermediate field between `C` and `F`.

First, `Phi(T) = T`.  The forward inclusion is immediate: if `x` belongs to every `Phi^n(F)`, then
`Phi(x)` belongs to every positive image and also to `F`.  Conversely, take `x in T`.  Since
`x in Phi(F)`, write `x = Phi(z)`.  For every `n`, membership `x in Phi^(n+1)(F)` gives

```text
Phi(z) = Phi(Phi^n(w_n)).
```

Injectivity of `Phi` yields `z = Phi^n(w_n)`.  Hence `z in T`, proving surjectivity of the
restriction.  Therefore `Phi|_T` is a differential `C`-automorphism.

Assume `T != C`.  Every element of `F \ C` is differentially transcendental over `C`.  Indeed, if
`v in F \ C` were differentially algebraic over `C`, writing `v` as a nonconstant differential
rational function of `y` would give a nonzero differential equation for `y` over `C<v>`.  Thus `y`
would be differentially algebraic over a differentially algebraic extension of `C`, contradicting
the choice of `y`.

The Ritt--Kolchin differential Luroth theorem, which has no finite-generation hypothesis on the
intermediate field, now gives `u in T` such that

```text
T = C<u>.
```

It remains to classify the differential automorphisms of `C<u>`.  For a nonconstant differential
rational function `f`, let `ord(f)` be the largest derivative of its argument occurring in a
reduced rational expression.  If `f` and `g` are nonconstant, the differential chain rule at the
highest derivative gives

```text
ord(f composed-differentially with g) = ord(f) + ord(g).       (1)
```

More explicitly, if `m = ord(f)` and `n = ord(g)`, then the partial derivative of the composite
with respect to `u^(m+n)` is the product of the substituted highest partial derivative of `f` and
the highest partial derivative of `g`; both are nonzero.

Set `v = Phi(u)` and let `w` be the image of `u` under the inverse automorphism.  The two identities
obtained by composing `v` and `w` give, by `(1)`,

```text
0 = ord(u) = ord(v) + ord(w).
```

Thus both orders are zero.  Hence `v in C(u)`, `u in C(v)`, and the ordinary rational maps are
mutual inverses.  A birational self-map of the projective line has degree one, so

```text
v = (a u + b) / (c u + d)
```

for a unique class in `PGL_2(C)`.  This proves the dichotomy.

## Consequences

### Rational coarse-graining criterion

For `R in C(z)` of degree at least two, differential substitution

```text
Phi_R(delta^j y) = delta^j(R(y))
```

has a nonconstant stable core if and only if there are a nonconstant differential rational
function `u` and `M in PGL_2(C)` satisfying

```text
u(R(y), delta(R(y)), ...) = M(u(y, delta y, ...)).             (2)
```

Thus the remaining rational-dynamics problem is not an uncontrolled infinite intersection.  It is
the classification of finite-order differential semiconjugacies from a rational map to projective
dynamics.

### Positive-order erasure

If `Phi(y)` has positive differential order `r`, order additivity gives

```text
ord(Phi^n(a)) = ord(a) + n r
```

for every nonconstant `a`.  No fixed finite-order element can belong to every image, so
`Core(Phi) = C`.  A nontrivial stable core is possible only for an order-zero substitution.

## Novelty and significance audit

- The differential Luroth theorem is classical, due to Ritt and Kolchin.
- Highest-derivative order additivity is classical differential algebra.
- A preliminary exact-phrase and concept search found no source stating the stable-core dichotomy,
  its projective action, or the rational coarse-graining criterion `(2)`.
- The theorem is a short synthesis of strong parent results.  Its novelty label therefore remains
  provisional pending a specialist and MathSciNet/Zentralblatt audit; it is not being presented as
  a new proof of either parent theorem.
- Its significance is structural: an arbitrary infinite-depth scalar constraint tower collapses
  to a sharp constants-versus-projective-free-field dichotomy.

## Physical interpretation

The stable core is the algebra of observables visible after every finite number of identical local
coarse-grainings.  A scalar hypertranscendental source admits only two infinite-depth phases:

```text
complete information erasure,
or one hypertranscendental projective current.
```

No finite-dimensional flow is introduced.  The result concerns a static intersection of
constraint fields.

## RH impact audit

There is no direct RH consequence.  An RH application would first need a source-pure
coarse-graining endomorphism of the completed zeta differential field.  Neither the functional
equation nor the Euler product supplies such an endomorphism, so the theorem cannot presently act
as an RH bridge.

## Lean status

`formal/GaloisForLFunctions/HTGeometry/StableDifferentialCore.lean` formalizes the unconditional
field-theoretic core:

```text
mem_stableRangeCore_iff
stableRangeCore_map_mem
stableRangeCore_exists_preimage
stableRangeCoreAlgHom_bijective
stableRangeCoreAlgEquiv
algHom_pow_deriv
derivationClosed_stableRangeCore
```

The targeted leaf build and formal lint pass.  The axiom reports contain only Lean's standard
`propext`, `Classical.choice`, and `Quot.sound` axioms.

The card remains at stage 2 because the Ritt--Kolchin differential Luroth theorem and the
differential-order classification of automorphisms of `C<u>` are not yet formalized in this
toolchain.  No axiom or opaque placeholder is used for either missing parent.

## Gates

- [x] 0 -> 1 in-progress: exact theorem and proof architecture identified
- [x] 1 -> 2 fully-proven: complete paper proof with classical parent isolated
- [ ] 2 -> 3 formalized: stable-core automorphism is Lean-certified; differential Luroth and
  projective classification remain
- [ ] 3 -> 4 publication-ready: external novelty audit and standalone exposition

## Primary references checked

- J. F. Ritt, the ordinary differential Luroth theorem, 1932.
- E. R. Kolchin, unrestricted intermediate-field form of differential Luroth.
- L. D'Alfonso, G. Jeronimo, P. Solerno, *Effective Differential Luroth's Theorem*, 2014.
