# Nonautonomous HT tails form a projective local system over time

- **ID:** `nonautonomous-ht-tail-projective-time-law`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Scientific status:** `[PROVED HERE] [CANDIDATE NEW SCIENTIFIC KNOWLEDGE]`
- **Statement:** The persistent field of any time-dependent sequence of injective scalar
  differential constraints is either trivial or a one-dimensional projective local system.  In
  the nontrivial phase it carries a canonical, generator-independent Schwarzian observable that is
  transported unchanged through time.

## Setup

Let `C` be a characteristic-zero field with trivial derivation.  For every integer time `i>=0`, let

```text
F_i=C<y_i>
```

be a scalar free differential field and let

```text
phi_i : F_(i+1) -> F_i
```

be an injective differential `C`-homomorphism.  Write

```text
Phi_(i,n)=phi_i composed with ... composed with phi_(i+n-1)
```

and define the phase-`i` tail

```text
T_i=intersection_(n>=0) Phi_(i,n)(F_(i+n)).                 (1)
```

This is a static intersection of constraint fields.  No flow or carrier is assumed.

## Theorem

1. Every `T_i` is a differential field and

   ```text
   phi_i(T_(i+1))=T_i.                                      (2)
   ```

   Thus every microscopic injection becomes a differential-field isomorphism on persistent
   information.

2. Either every `T_i=C`, or every tail is nonconstant and there are differentially transcendental
   generators `u_i` with

   ```text
   T_i=C<u_i>.                                               (3)
   ```

3. In the nonconstant case there is a unique projective transition

   ```text
   M_i in PGL_2(C)
   ```

   satisfying

   ```text
   phi_i(u_(i+1))=M_i(u_i).                                 (4)
   ```

4. The element

   ```text
   H_i=S(u_i)
      =u_i'''/u_i'-(3/2)(u_i''/u_i')^2                     (5)
   ```

   is independent of the choice of differential generator in (3), is nonconstant, and obeys

   ```text
   phi_i(H_(i+1))=H_i.                                      (6)
   ```

Consequently a nontrivial scalar HT tail is canonically a flat `PGL_2(C)` local system on the time
graph, together with a nonconstant horizontal projective-curvature section.

## Proof

### Exact phase transport

Take `x in T_i`.  Membership at depth one gives `x=phi_i(y)` for some `y in F_(i+1)`.  For every
`n`, membership of `x` at depth `n+1` gives

```text
phi_i(y)=phi_i(Phi_(i+1,n)(z_n)).
```

Injectivity of `phi_i` implies `y in Phi_(i+1,n)(F_(i+n+1))` for every `n`, hence `y in T_(i+1)`.
This proves surjectivity in (2).  The forward inclusion follows directly by prefixing every depth
representation with `phi_i`.  Intersections of differential subfields are differential, proving
the first assertion.

### Scalar dichotomy and projective transition

If one tail is constant, (2) makes its neighbour constant; induction propagates this through all
times.  Otherwise the ordinary Ritt--Kolchin differential Luroth theorem applies to each
intermediate field `C subset T_i subset C<y_i>` and gives (3).

The restricted map in (2) is a differential `C`-isomorphism.  Therefore
`phi_i(u_(i+1))` and `u_i` are mutually generating differential rational functions.  Exact
differential-order additivity applied in both directions forces both generator changes to have
order zero.  They are mutually inverse rational maps of the projective line and hence a unique
Möbius pair, proving (4).

### Canonical projective curvature

Any two differential generators of `C<u_i>` differ by a Möbius transformation, and the Schwarzian
is Möbius invariant.  Thus (5) is intrinsic to the embedded tail field rather than to a coordinate
choice.  It cannot be constant: `S(u_i)=c` would be a nonzero third-order differential polynomial
relation for the differentially transcendental `u_i`.

Finally differential homomorphisms commute with the Schwarzian, so (4) gives

```text
phi_i(S(u_(i+1)))=S(phi_i(u_(i+1)))
                  =S(M_i(u_i))
                  =S(u_i),
```

which is (6).

## Autonomous and periodic specializations

- For a constant protocol `phi_i=phi`, the local system has one monodromy element in `PGL_2(C)`.
  This is the scalar stable-core projective law.
- For a period-`m` rational protocol, the product of the projective transitions is the
  stroboscopic monodromy.  If the period composite has degree at least two, the canonical
  Schwarzian is a nonconstant rational differential invariant of that composite.  Casale's
  theorem therefore forces the period composite to be power, Chebyshev, or Lattes type.
- The explicit `z^2+1`, `(z-1)^2` protocol realizes a nontrivial projective local system even though
  both autonomous snapshots have trivial tails.

## Physical interpretation

The result isolates a mathematically precise form of time for an HT source.  Persistent
information does not move as a point or state.  It is a projective coordinate chart whose changes
of frame form a `PGL_2` cocycle; the Schwarzian is its coordinate-free observable.

This resembles a one-dimensional gauge field or a projective connection, but the theorem makes no
quantum or gravitational assumption.  The geometry is forced solely by the absence of a finite
generative rule plus survival through every constraint depth.  Periodic orbifold memory is the
closed-monodromy sector of this more general projective time geometry.

## Novelty and significance gate

- Differential Luroth, automorphisms of a scalar differential rational field, and Schwarzian
  invariance are classical parents.
- The checked sources do not state the nonautonomous tail isomorphism, the resulting projective
  local-system law, or the canonical horizontal Schwarzian of persistent HT information.
- Unlike the autonomous orbifold classification, this theorem applies to arbitrary time-dependent
  injective scalar constraints and explains why the periodic topology can exist without static
  topology.
- The proof is short once the right object is defined.  Its significance is foundational and
  structural; external expert audit is still required before promoting its novelty status.

## RH impact audit

There is no direct RH theorem.  The result widens the admissible search space: a zeta-related HT
constraint geometry could be a nonautonomous projective cocycle even when no autonomous rational
coarse-graining exists.  Any claimed RH application must still construct source-pure maps
`phi_i` and a nonconstant phase tail; neither is supplied by the functional equation alone.

## Lean status

`NonautonomousStableCore.lean` now formalizes the finite protocol prefixes, phase tails, exact
identity (2), the induced algebra equivalence between successive tails, and derivation closure.
`SchwarzianProjectiveInvariant.lean` formalizes the canonical Schwarzian transport once the
paper-level differential-Luroth/projective generator step is supplied.  The targeted builds pass,
and axiom reports contain only `propext`, `Classical.choice`, and `Quot.sound`.

## Gates

- [x] 0 -> 1: nonautonomous tail and projective-time claim isolated
- [x] 1 -> 2: complete proof with classical parents separated
- [ ] 2 -> 3: phase-tail isomorphism and Schwarzian transport are formalized; differential Luroth
  and generator classification remain paper-level
- [ ] 3 -> 4: external novelty audit and standalone manuscript
