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
`SchwarzianProjectiveInvariant.lean` formalizes the canonical two-coordinate transport in
`schwarzian_transport_of_projective_transition`: if a differential homomorphism sends the next
phase generator `v` to a constant-coefficient Mobius transform of the current generator `u`, then
it sends `S(v)` exactly to `S(u)`.  The earlier autonomous fixed-Schwarzian theorem is now its
specialization.  Thus equation (6) is formalized once the paper-level differential-Luroth and
projective-generator step supplies the phase coordinates and transition.  The targeted direct
checks pass, and axiom reports contain only `propext`, `Classical.choice`, and `Quot.sound`.

## Gates

- [x] 0 -> 1: nonautonomous tail and projective-time claim isolated
- [x] 1 -> 2: complete proof with classical parents separated
- [x] exact two-coordinate Schwarzian phase transport formalized and autonomous duplication removed
- [ ] 2 -> 3: phase-tail isomorphism and Schwarzian transport are formalized; differential Luroth
  and generator classification remain paper-level
- [ ] 3 -> 4: external novelty audit and standalone manuscript

## Lean progress — the scalar dichotomy of part 2, first half

`GaloisForLFunctions/HTGeometry/NonautonomousTailDichotomy.lean` (wired, axiom-clean):

    eq_bot_of_algEquiv_base :
      an intermediate field isomorphic to the base OVER the base is the base
    nonautonomousTail_eq_bot_succ_iff :
      triviality of the tail transports across one step, in both directions
    nonautonomousTail_eq_bot_of_eq_bot
    nonautonomousTail_dichotomy :
      either every phase tail is the constants, or none is

The card's part 2 reads "If one tail is constant, `(2)` makes its neighbour constant; induction
propagates this through all times."  That half needs nothing beyond the exact phase transport already
formalized: the transition is a differential `C`-isomorphism of tails, and an intermediate field
isomorphic to the base over the base is the base, so triviality moves both forward and backward along
the protocol.  Running the induction down to phase `0` and back up reaches every phase from any one.

What is still paper-level in part 2 is the *other* branch: that a nonconstant tail is `C<u_i>` for a
single differentially transcendental generator.  That is the Ritt--Kolchin differential Luroth
theorem, a classical result of real size, and it is the only thing between the present state and
`(3)`; `(4)`, `(5)`, `(6)` are formalized or immediate once generators exist
(`schwarzian_transport_of_projective_transition`).

## Lean progress — the generator classification of `(4)`, and where it now stands

`GaloisForLFunctions/HTGeometry/RationalGeneratorMobius.lean` (wired, axiom-clean):

    exists_mobius_of_finrank_eq_one :
      a rational function that generates the whole rational function field is a Mobius transform of
      the coordinate -- its numerator and denominator are linear with invertible coefficient matrix

Two discoveries change what is left on this card.

1. **mathlib has Luroth's theorem** (`Mathlib/FieldTheory/RatFunc/Luroth.lean`), together with the
   degree lemma `RatFunc.finrank_eq_max_natDegree` -- the degree of `K(X)` over `K(f)` is the larger
   of the degrees of the numerator and denominator of `f`.  That lemma is what makes the Mobius
   classification a short argument: degree one forces both to be linear, and coprimality forces the
   coefficient matrix to be invertible.
2. **The order-zero step is already in the corpus.**  `ScalarDifferentialRationalOrder.lean` proves
   `differentialAlgEquiv_generator_mem_adjoin_singleton`: a differential automorphism of a scalar free
   differential field sends the generator into the ORDINARY rational function field `C(y)`, in both
   directions.  That is exactly the card's "exact differential-order additivity applied in both
   directions forces both generator changes to have order 0".

So `(4)` is now two known facts away from formal: compose the order-zero membership with the Mobius
classification.  What is still genuinely missing is `(3)` -- the Ritt--Kolchin *differential* Luroth
theorem, which is not classical Luroth and is not in mathlib: it concerns intermediate DIFFERENTIAL
fields of `C<y>`, whose ambient is a rational function field in infinitely many variables
`y, y', y'', ...`.

## Lean progress — `(4)`'s generator classification, in the abstract setting

Added to `RationalGeneratorMobius.lean` (wired, axiom-clean):

    exists_mobius_of_adjoin_eq_top      -- generation form of the classification
    exists_mobius_of_mutual_adjoin :
      if a transcendental `y` and an element `v` generate the same simple extension, then
      `v` is a Mobius transform of `y` with invertible coefficient matrix

This is the card's generator classification at the level the tail theorems need it: `v in C(y)` and
`y in C(v)` force `v = (a y + b)/(c y + d)` with `ad - bc /= 0`.  Combined with the corpus's
`differentialAlgEquiv_generator_mem_adjoin_singleton` -- which puts both `sigma y` and `sigma^(-1) y`
in the ordinary field `C(y)` -- this gives `(4)` for the differential automorphism transporting one
phase generator to the next.

The transfer runs through `RatFunc.algEquivOfTranscendental`: the simple extension `C(y)` is the
rational function field, an intermediate field maps injectively under an `AlgHom`, and the image of a
simple adjunction is the simple adjunction of the image, so "`v` generates" moves to "`F` adjoins to
everything" in `RatFunc C`, where `RatFunc.finrank_eq_max_natDegree` converts it into a degree bound.

`(3)` remains: Ritt--Kolchin differential Luroth, which is genuinely absent from mathlib and is not
implied by the classical Luroth theorem that is present.

## Lean progress — `(4)` AND `(6)` for the scalar automorphism model, unconditionally

`GaloisForLFunctions/HTGeometry/PhaseGeneratorMobius.lean` (wired, axiom-clean):

    exists_mobius_of_differentialAlgEquiv :
      a differential automorphism of a scalar free differential field sends the generator to a
      Mobius transform of it, with invertible coefficient matrix over the constants   -- (4)
    schwarzian_fixed_of_differentialAlgEquiv :
      hence it fixes the Schwarzian of the generator                                  -- (6)

Both were previously listed as needing the paper-level "differential Luroth and projective-generator
step".  Only `(3)` needed it.  `(4)` follows from two things already in the tree -- the order-zero
membership `differentialAlgEquiv_generator_mem_adjoin_singleton` and the new generator classification
-- and `(6)` then follows from `schwarzian_fixed_of_projective_semiconjugacy`, whose projective
hypothesis is exactly what `(4)` supplies.

Three side conditions of the transport theorem are discharged from hypertranscendence rather than
assumed:

* the determinant stays invertible downstairs, by injectivity of the structure map;
* the denominator `c y + d` cannot vanish -- otherwise `y` satisfies a linear polynomial over the
  constants, contradicting transcendence, and if `c = 0` then `d = 0` and the determinant dies;
* `y' /= 0` -- otherwise the order-one jet is `0`, which is algebraic, contradicting
  hypertranscendence.

### State of this card

| statement | Lean |
|---|---|
| `(1)`, `(2)` phase tail and exact transport | `NonautonomousStableCore` |
| part 2, constant branch | `nonautonomousTail_dichotomy` |
| part 2, `(3)` generator existence | **Ritt--Kolchin differential Luroth -- absent from mathlib** |
| `(4)` projective transition | `exists_mobius_of_differentialAlgEquiv` |
| `(5)` Schwarzian is a generator invariant | `schwarzian_mobius` |
| `(6)` Schwarzian transport | `schwarzian_fixed_of_differentialAlgEquiv` |

Everything except `(3)` is formal.  `(3)` is the one genuine mathlib-scale gap: classical Luroth is
present and is not enough, because the ambient of a differential Luroth statement is a rational
function field in infinitely many variables.
