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

## Lean progress — first step of `(3)`: one transcendental controls a scalar field

`GaloisForLFunctions/HTGeometry/ScalarDifferentialAlgebraicity.lean` (wired, axiom-clean):

    diffIndepOn_singleton_iff :
      independence of a singleton is hypertranscendence of its element
    mem_differentialClosure_singleton_of_cRank_one :
      in differential transcendence degree one, EVERY element is differentially algebraic over the
      differential field generated by any differentially transcendental element

This is the opening move of a differential Luroth argument, and it is now unconditional.  Given an
intermediate differential field `T` with some `w in T` not differentially algebraic over `C`, the
generator `y` is differentially algebraic over `C<w>` -- because two differentially independent
elements would give differential transcendence degree at least two, and a matroid's independent sets
are bounded by its rank.

That is the step Ritt's proof opens with.  What follows it -- the minimal differential polynomial of
`y` over `T`, clearing denominators to a primitive differential polynomial over `C{y}{Y}`, and the
rank comparison showing a coefficient ratio generates `T` -- is the remaining content of `(3)`, and
needs a reduction/characteristic-set layer.  The corpus already owns pieces of that layer
(`DifferentialPolynomialRank`, `DifferentialKernelCharacteristic`: leaders, leader degree,
separants), so the route is a build rather than a research question.

## Lean progress — second step of `(3)`: rank monotonicity in the coefficient field

`GaloisForLFunctions/HTGeometry/DifferentialRelationBaseChange.lean` (wired, axiom-clean):

    differentialPolynomialEvalOver_map_inclusion  -- evaluation ignores enlarging the coefficients
    mem_differentialIntermediateRelationIdeal_map -- a relation stays a relation
    scalarDifferentialPolynomialOrder_map
    scalarDifferentialPolynomialLeaderDegree_map  -- an injective coefficient map preserves the rank
    minimalRank_le_of_le :
      the minimal relation rank over a larger coefficient field is at most the rank of any relation
      over a smaller one

This is the comparison a Luroth argument runs: the rank of `y` over `C<w>` for a single coefficient
ratio `w`, against the rank over the whole intermediate field `T`.  One direction is now a theorem.

The corpus turns out to be much further along this road than the card's Lean-status note suggested.
`DifferentialKernelCharacteristic.lean` already owns the relation ideal of an intermediate field, its
primeness and properness, the existence of a minimal-rank relation, and
`exists_irreducible_minimal_differentialKernelCharacteristic` -- an irreducible minimal characteristic
for every nontrivial intermediate field inside a scalar differential adjunction.  With the two steps
added in this session, what remains of `(3)` is the *other* direction of the comparison: clearing
denominators to a primitive differential polynomial over `C{y}{Y}` and reading the rank back, which is
Ritt's degree count.

## Lean progress — third step of `(3)`: a relation descends to its own coefficient field

`GaloisForLFunctions/HTGeometry/MvPolynomialCoefficientDescent.lean` (wired, axiom-clean):

    descendCoefficients        -- rebuild a polynomial over a subfield containing its coefficients
    coeff_descendCoefficients  -- with the same coefficients
    map_descendCoefficients    -- and pushing it forward recovers the original

mathlib has `Polynomial.toSubring` for the univariate case but nothing multivariable, so this is new
infrastructure.  It is the move Ritt's proof makes right after choosing a minimal characteristic
relation `P` of `y` over the intermediate field `G`: replace `G` by the field generated by the
coefficients of `P`, over which `P` is still a relation, of the same rank -- the rank is preserved
because pushing coefficients forward injectively preserves order and leader degree, proved in the
previous section.

### Where `(3)` now stands

    step 1  one transcendental controls a scalar field         mem_differentialClosure_singleton_of_cRank_one
    step 2  rank monotonicity in the coefficient field         minimalRank_le_of_le
    step 3  descent to the coefficient field                   map_descendCoefficients
    step 4  Ritt's degree count -- OPEN

Steps 1-3 are unconditional.  Step 4 is the remaining mathematical content: comparing the rank of `y`
over the field generated by ONE coefficient ratio with the rank over the whole coefficient field, which
is where the two-variable degree symmetry of Ritt's argument enters.

## Lean progress — fourth step of `(3)`: the relation must use a coefficient outside the base

`GaloisForLFunctions/HTGeometry/RelationCoefficientOutsideBase.lean` (wired, axiom-clean):

    differentialPolynomialEvalOver_map_botEquiv  -- reading base coefficients in the base
    exists_coeff_notMem_bot_of_relation :
      a nonzero relation of a hypertranscendental element over an intermediate field always has a
      coefficient outside the base field

This is how Ritt's argument gets the element it will show generates the intermediate field: if every
coefficient of the minimal characteristic were a constant, the relation would descend to the base --
by the descent lemma of the previous section -- and a hypertranscendental element admits no nonzero
relation there.

    step 1  one transcendental controls a scalar field    DONE
    step 2  rank monotonicity in the coefficient field    DONE
    step 3  descent to the coefficient field              DONE
    step 4a a coefficient outside the base exists         DONE
    step 4b Ritt's degree count                           OPEN

What is left is exactly the degree count: that the intermediate field is generated by a single ratio
of coefficients of its minimal characteristic.  Every ingredient that feeds it is now formal.

## Lean progress — the reduction engine: pseudo-division (missing from mathlib)

`GaloisForLFunctions/HTGeometry/PolynomialPseudoDivision.lean` (wired, axiom-clean):

    exists_pseudo_div :
      for every `A` and nonzero `B` over a domain there are `k, Q, S` with
        `B.leadingCoeff ^ k . A = Q * B + S`  and  `deg S < deg B`

mathlib divides only by *monic* polynomials (`Polynomial.modByMonic`); there is no pseudo-division
over a general commutative ring or domain.  This is the engine every reduction algorithm in
differential algebra runs on, because there the divisor's leading coefficient -- the initial of a
differential polynomial -- is itself a polynomial, never a unit.

The proof is the classical one made structural: strong induction on the degree of the dividend, with
the inductive step cancelling leading terms in `lead(B) . A - lead(A) . X^m . B`.  Over a domain the
two scaled polynomials have equal degree and equal leading coefficient, so `degree_sub_lt` applies and
the induction descends.

With `(3)`'s steps 1-4a, this completes the toolkit Ritt's degree count needs: reduce an arbitrary
relation modulo the minimal characteristic, and read off that the intermediate field is generated by a
single coefficient ratio.

## Lean progress — the reduction step in the leader variable

`GaloisForLFunctions/HTGeometry/MvPolynomialLeaderPseudoDivision.lean` (wired, axiom-clean):

    mvPolynomialEquivPolynomialAt :
      singling out one variable is a ring EQUIVALENCE onto the univariate polynomial ring over the
      remaining variables (the corpus previously had only the forward map)
    exists_pseudo_div_at :
      reduction modulo a polynomial in a singled-out variable, at the cost of a power of that
      polynomial's leading coefficient in that variable -- its initial

Transporting the pseudo-division of the previous section through the equivalence gives Ritt's
reduction step where it actually lives: in the jet variable carrying the leader.

One trap worth recording: the corpus's `mvPolynomialAsPolynomialAt` is defined inside a `classical`
block, so an equivalence built with an ambient `[DecidableEq]` instance is NOT definitionally equal to
it -- the `rfl` fails and the elaborator burns its heartbeat budget trying.  Building the equivalence
inside `classical` as well makes the comparison `rfl` again.

## Lean progress — reduction stated with the initial

Added to `MvPolynomialLeaderPseudoDivision.lean` (wired, axiom-clean):

    mvPolynomialEquivPolynomialAt_rename_val :
      polynomials in the remaining variables are exactly the constants of the univariate view
    exists_initial_pseudo_div :
      for every `Q` and nonzero `P`,
        `initial_i(P)^k * Q = A * P + S`  with  `deg_i S < deg_i P`

The first lemma is the bridge that lets the univariate statement be read back in the multivariable
ring: the corpus's `mvPolynomialInitialAt` is the leading coefficient of the singled-out view renamed
back, so multiplying by it corresponds exactly to multiplying the univariate view by a constant.  With
it, reduction is stated in the language differential algebra uses -- the initial -- rather than in the
language of the auxiliary univariate ring.

This is the last general-purpose tool Ritt's argument needs.  What remains is specific to the Luroth
setting: apply reduction to an arbitrary relation, observe the remainder is a relation of strictly
lower rank, conclude it vanishes by minimality, and run the degree count on the resulting divisibility.

## Lean progress — reduction becomes divisibility

`GaloisForLFunctions/HTGeometry/MinimalRankRemainderVanishes.lean` (wired, axiom-clean):

    eq_zero_of_lower_rank_mem :
      a relation of no higher order and strictly smaller degree in the leader than the minimal
      relation is ZERO

Both escape routes are closed: a nonconstant remainder contradicts minimality of the characteristic,
and a constant one would be a unit in the relation ideal, making it the whole ring -- which the
relation ideal of an evaluation into a field never is.

Combined with `exists_initial_pseudo_div`, this says the minimal characteristic *pseudo-divides* every
partially reduced relation: `initial(P)^k * Q = A * P`.  That is the divisibility Ritt's degree count
operates on, and it is now available.

## CORRECTION — the pseudo-reduction layer already existed; three modules withdrawn

`GaloisForLFunctions/HTGeometry/DifferentialCharacteristicPseudoReduction.lean` already contains the
whole reduction layer:

    Polynomial.PseudoDivision (structure, with quotient/remainder/exponent and the degree bound)
    mvPolynomialPolynomialEquivAt, mvPolynomialPolynomialEquivAt_initial
    mvPolynomial_degreeOf_eq_natDegree_asPolynomialAt
    mvPolynomialPseudoDivision_step_degree_lt
    characteristicPseudoReduction_remainder_eq_zero
    exists_initial_separant_powers_mem_differentialPolynomialIterateIdeal
    exists_differentialKernelCharacteristic_with_pseudoReduction

The three modules recorded in the previous sections -- `PolynomialPseudoDivision`,
`MvPolynomialLeaderPseudoDivision`, `MinimalRankRemainderVanishes` -- duplicated it and have been
DELETED and unwired.  Their claims stand as corpus theorems, but under the existing names, and the
corpus versions are stronger: the reduction there also handles the ORDER using the separant and the
derivation-stable iterate ideal, whereas mine only handled a partially reduced dividend.

Why the duplication happened, so it does not repeat: the search that preceded that work looked for
"pseudo" in mathlib and read `DifferentialPolynomialRank` and `DifferentialKernelCharacteristic` in
the corpus, but never ran `formal_tools.py research "pseudo division"` -- which returns the module
immediately.  Search the corpus by the *mathematical operation*, not by the module names one already
knows.

### Revised state of `(3)`

With the reduction layer in hand, what `(3)` needs is exactly what that module's header calls the
"later two-copy coefficient-ratio theorem": Ritt's degree count comparing the rank of `y` over
`C<w>` for a coefficient ratio `w` against the rank over the whole intermediate field.  The steps
recorded earlier in this card that are NOT duplicates -- `mem_differentialClosure_singleton_of_cRank_one`,
`minimalRank_le_of_le`, `map_descendCoefficients`, `exists_coeff_notMem_bot_of_relation` -- remain the
new contributions toward it.

## CORRECTION 2 — the Mobius and coefficient layers existed too; the card's Lean status was stale

A proper corpus search (by mathematical operation, as the previous correction prescribed) finds an
entire differential-Luroth development already in the tree:

    TranscendentalMobius.lean            ratFunc_generator_mobius, adjoin_generator_mobius,
                                         algEquiv_generator_mobius_of_mem
    ClockCharacterSigmaMobius.lean       differentialAlgEquiv_generator_mobius
    DifferentialLurothCoefficient.lean   exists_differentialRelation_coefficientRatio_not_mem_bot,
                                         IsMinimalScalarDifferentialPolynomialRank.dvd_of_relation_order_le
    DifferentialLurothComponentTransfer.lean, DifferentialLurothScalarExtensionSquarefree.lean,
    DifferentialLurothVariableSupport.lean, LurothSaturationWitnesses.lean, OrdinaryLuroth.lean

So `RationalGeneratorMobius.lean` (duplicating `ratFunc_generator_mobius` and
`adjoin_generator_mobius`) and `RelationCoefficientOutsideBase.lean` (subsumed by
`exists_differentialRelation_coefficientRatio_not_mem_bot`, which gets a non-base *ratio* rather than
a single non-base coefficient) have been DELETED and unwired.  `PhaseGeneratorMobius.lean` has been
rebased: its duplicate projective-transition theorem is gone and the Schwarzian result now sits
directly on the corpus's `differentialAlgEquiv_generator_mobius`.

What survives as genuinely new from this card's sessions:

    schwarzian_fixed_of_differentialAlgEquiv   -- the transported observable  (6)
    nonautonomousTail_dichotomy                -- the constant/nonconstant dichotomy
    mem_differentialClosure_singleton_of_cRank_one
    descendCoefficients, map_descendCoefficients
    mem_differentialIntermediateRelationIdeal_map, scalarDifferentialPolynomialOrder_map,
      scalarDifferentialPolynomialLeaderDegree_map, minimalRank_le_of_le

**The card's Lean-status section is stale and should not be trusted**: it says "differential Luroth and
generator classification remain paper-level", but the generator classification is formal
(`adjoin_generator_mobius`) and the Luroth layer is far advanced.  The remaining question is which
capstone in that layer is still missing -- that must be read off the modules themselves, not off this
card.

## The real frontier of `(3)`, read off the modules

The differential-Luroth program in the tree is far along and its remaining gap is a single assembly.
The chain, with what exists:

1. premises jointly realized -- `exists_lurothSaturation_premises`
   (derivation closure, a minimal-rank characteristic, a primitive two-block characteristic)
2. cross-relation saturation -- `PrimitiveTwoBlockDifferentialCharacteristic.exists_mappedCrossRelation_saturation`
   the mapped coefficient cross-relation lies in the iterate ideal after multiplying by powers of the
   initial and the separant
3. divisibility from that membership -- `irreducible_dvd_of_order_le_of_separant_pow_mul_mem_iterateIdeal`
4. vanishing criterion -- `differentialPolynomialCrossDifference_eq_zero_iff`
   the cross-difference vanishes exactly when the two coefficients are proportional over the base
5. a non-base ratio always exists -- `exists_differentialRelation_coefficientRatio_not_mem_bot`

Steps 1-5 are formal.  The capstone that is NOT in the tree is the assembly: run 2 into 3, use the
degree/rank comparison to force the cross-difference to vanish, contradict 5 unless the coefficient
ratio generates, and conclude `G = C<w>`.  That is the whole of `(3)`, and it is one theorem, not a
layer.

Anyone continuing this card should start by reading `DifferentialLurothComponentTransfer.lean` and
`DifferentialLurothCoefficient.lean` end to end; the definitions there
(`PrimitiveTwoBlockDifferentialCharacteristic`, `differentialCharacteristicCoefficientCrossRelation`,
`differentialPolynomialIterateIdeal`) are what the assembly has to be written in terms of, and no
part of it should be re-derived.

## Lean progress — the cross-relation descends to its two coefficients

`GaloisForLFunctions/HTGeometry/CrossRelationCoefficientField.lean` (wired, axiom-clean):

    coeff_crossRelation_mem_adjoin :
      every coefficient of the characteristic coefficient cross-relation lies in `F(p, q)`
    crossRelation_descends :
      so the cross-relation is the image of a relation over `F(p, q)`

Checked against the corpus first this time: the cross-relation and its membership in the relation
ideal are the corpus's (`differentialCharacteristicCoefficientCrossRelation`,
`coefficientCrossRelation_mem`); the descent is this session's `descendCoefficients`.  Nothing here is
re-derived.

The point is structural.  The cross-relation is by construction
`C q * map P - C p * map Q` with `P, Q` over the BASE field, so each of its coefficients is
`q . a - p . b` with `a, b` in the base -- it never leaves `F(p, q)`.  Combined with
`coefficientCrossRelation_mem`, this says: two coefficients of the minimal characteristic already
carry a relation of `y` over the small field they generate.  That is the object Ritt's degree count
compares against the characteristic, and the comparison is what remains of `(3)`.

## Lean progress — two coefficients already carry a relation over the field they generate

`GaloisForLFunctions/HTGeometry/CrossRelationDescentRelation.lean` (wired, axiom-clean):

    descend_crossRelation_mem_relationIdeal :
      the descended coefficient cross-relation is a relation of `y` over `F(p, q)`

Composed from three pieces, none of them re-derived: the corpus's `coefficientCrossRelation_mem` (the
cross-relation is a relation over `G`), this session's `crossRelation_descends` (it descends to
`F(p, q)`), and this session's `differentialPolynomialEvalOver_map_inclusion` (evaluation is unchanged
when the coefficient field grows, so descending preserves being a relation).

State of the `(3)` capstone.  For a minimal characteristic `P` over `G` and two of its coefficients
`p, q`, we now have a relation of `y` over the small field `F(p, q) <= G`.  Rank monotonicity
(`minimalRank_le_of_le`) compares the minimal rank over `F(p, q)` with the rank of that relation, and
the corpus's cross-difference vanishing criterion plus non-base ratio existence say when the relation
is nonzero.  What is still missing is the degree count that forces `F(p, q) = G`.

## Lean progress — the small-field relation is nonzero

`GaloisForLFunctions/HTGeometry/CrossRelationNonvanishing.lean` (wired, axiom-clean):

    crossRelation_ne_zero :
      if the two characteristic coefficients have a ratio outside the base field, their
      cross-relation is nonzero

Checked against the corpus first: the corpus proves that such a pair of coefficients always EXISTS
(`exists_differentialRelation_coefficientRatio_not_mem_bot`); it does not record that the resulting
cross-relation is nonzero, which is what makes the comparison non-vacuous.

The three links of this session now say: for a minimal characteristic over `G` and a coefficient pair
with non-base ratio, there is a NONZERO relation of `y` over the small field `F(p, q) <= G`.  Together
with `minimalRank_le_of_le` this bounds the minimal rank over `F(p, q)` by the rank of that
cross-relation.  The remaining inference -- that the bound forces `F(p, q) = G` -- is the degree count.

## Lean progress — the comparison itself

`GaloisForLFunctions/HTGeometry/CrossRelationRankComparison.lean` (wired, axiom-clean):

    minimalRank_order_le_crossRelation :
      for a minimal characteristic over `G` and two of its coefficients with a non-base ratio,
        order(characteristic)  <=  order(descended cross-relation)

This is the assembled comparison.  Its three inputs are the links of the previous sections plus one
corpus lemma used rather than re-proved:

* the descended cross-relation is a relation over `F(p, q)`   (this session)
* it is nonzero                                                (this session)
* it is nonconstant -- a constant would be a unit in a proper relation ideal, and
  `mvPolynomial_vars_nonempty_of_ne_zero_of_not_isUnit` is the corpus's
* rank monotonicity in the coefficient field                   (this session)

So one direction of Ritt's comparison is formal.  The reverse bound -- that the cross-relation's order
does not exceed the characteristic's, which is where the two-block degree count enters -- is what
remains, and with it `(3)`.

## Lean progress — the cross-relation cannot raise the order

`GaloisForLFunctions/HTGeometry/CrossRelationOrderBound.lean` (wired, axiom-clean):

    order_crossRelation_le :
      order(cross-relation)  <=  max(order A, order B)   for its two entries `A, B`

Multiplying by a constant and subtracting introduce no jet variable, so the relation a coefficient
pair produces is never higher in order than the pair itself.  This is the structural half of the
reverse comparison; combined with the previous section,

    order(characteristic)  <=  order(cross-relation)  <=  max(order A, order B).

What is left of `(3)` is therefore one specific fact about the primitive two-block characteristic:
that its block coefficients `A, B` have order at most the order of the characteristic itself.  With
that, the two bounds close into an equality and Ritt's comparison is complete.

## Lean progress — the separant survives a coefficient map, and the assembly plan for `(3)`

`GaloisForLFunctions/HTGeometry/SeparantCoefficientMap.lean` (wired, axiom-clean):

    scalarDifferentialPolynomialLeader_map
    scalarDifferentialPolynomialSeparant_map :
      an injective coefficient map commutes with taking the separant

Needed because the corpus's divisibility bridge states its hypothesis with the separant of the MAPPED
characteristic, while the saturation theorem produces the MAPPED separant.  Searched first: no such
compatibility existed.

### The assembly that finishes `(3)`, with every hypothesis located

    bridge:      irreducible_dvd_of_order_le_of_separant_pow_mul_mem_iterateIdeal
                   (hAvars) (hAirreducible) (hQorder) (hmem : separant A ^ e * Q in iterateIdeal A)
                   ==> A dvd Q
    supply A :=  map phi P            (phi = differentialIntermediateToJetFraction)
    supply Q :=  map phi (initial P) ^ a * map phi (crossRelation ...)
    hmem   :=  exists_mappedCrossRelation_saturation   (rearranged with separant_map, above)
    hAvars, hAirreducible: from exists_differentialKernelCharacteristic_with_pseudoReduction
    hQorder: from order_crossRelation_le and the order-preservation of coefficient maps

Then `map phi P` divides `map phi (initial P)^a * map phi crossRel`; the characteristic does not divide
its own initial (lower rank), so it divides the mapped cross-relation; the order bounds of the two
previous sections force equality of ranks, and `differentialPolynomialCrossDifference_eq_zero_iff`
converts that into proportionality of the two coefficients over the base -- contradicting the non-base
ratio unless the intermediate field is generated by their ratio.

Every hypothesis in that chain now has a named source in the tree.  What remains is to write it.

### A correction to the previous section's plan

The "reverse bound" is NOT an order bound on the two-block coefficients `A, B`: clearing denominators
puts the denominators' jets into the left block, so their order is not bounded by the characteristic's.
The reverse comparison runs through the fraction-field saturation above instead.  The order bound
proved in the previous section is still what supplies `hQorder` there.

## Lean progress — the saturation now has the bridge's shape

`GaloisForLFunctions/HTGeometry/CrossRelationBridgeShape.lean` (wired, axiom-clean):

    exists_separant_pow_mul_mem_iterateIdeal_of_saturation :
      separant(map phi P)^b * (map phi (initial P)^a * map phi crossRel)
        in  differentialPolynomialIterateIdeal (map phi P)

The corpus's saturation theorem produces `initial^a * separant^b * crossRel` with the separant taken
before mapping; the divisibility bridge wants `separant(mapped)^e * Q`.  With the separant-map
compatibility of the previous section and one commutation, they are the same statement -- so the
bridge now applies verbatim, with

    A := map phi P,     Q := map phi (initial P)^a * map phi crossRel,     e := b.

Remaining for `(3)`: supply the bridge's other two hypotheses (`A.vars.Nonempty`, `Irreducible A`, both
from `exists_differentialKernelCharacteristic_with_pseudoReduction` after transporting irreducibility
along the map, and `hQorder` from `order_crossRelation_le`), then run the divisibility conclusion into
`differentialPolynomialCrossDifference_eq_zero_iff`.

## CORRECTION 3 — irreducibility does not survive the coefficient map; the route is via a factor

The assembly plan recorded two sections above said the bridge's `Irreducible A` hypothesis would come
"from `exists_differentialKernelCharacteristic_with_pseudoReduction` after transporting irreducibility
along the map".  That is wrong, and the corpus says so explicitly: the docstring of
`irreducible_map_squarefree_of_charZero` reads "Irreducibility need not survive the extension".  Only
SQUAREFREENESS survives.

The corpus's own route is therefore not through `map phi P` at all.  It works with an irreducible
FACTOR, over the base field, of the two-block polynomial:

    PrimitiveTwoBlockDifferentialCharacteristic.irreducible_factor_right_vars_eq
      (hAirreducible : Irreducible A) (hAdiv : A dvd C.polynomial) :
        (twoBlockEquiv A).vars = P.vars
    irreducible_map_factor_vars_eq
      (hP : Irreducible P) (hA : Irreducible A) (hdiv : A dvd map P) : A.vars = P.vars

so the divisibility bridge is to be applied to such a factor, whose irreducibility is genuine rather
than transported.

`exists_separant_pow_mul_mem_iterateIdeal_of_saturation` (previous section) remains a faithful
restatement of the saturation and is still the shape the bridge consumes; what changes is WHICH
polynomial plays the role of `A`.  Reading the two `irreducible_factor` theorems above is the
prerequisite for writing the final step -- and the lesson of this correction is the same as the two
before it: read the corpus's docstrings for what does NOT hold, not only for what does.

## Lean progress — producing the irreducible factor the corrected route needs

`GaloisForLFunctions/HTGeometry/TwoBlockIrreducibleFactor.lean` (wired, axiom-clean):

    mvPolynomial_vars_eq_empty_of_isUnit          -- a unit over a field is a constant
    mvPolynomial_not_isUnit_of_vars_nonempty
    exists_irreducible_factor_of_vars_nonempty :
      a nonzero polynomial with a variable has an irreducible factor

The corpus's `mvPolynomial_vars_nonempty_of_ne_zero_of_not_isUnit` is the converse implication; the
direction needed here -- unit implies no variables -- was not present, and it is what turns "the
characteristic has a variable" into "the cleared two-block polynomial is not a unit", hence into the
existence of the irreducible factor that the corrected route applies the divisibility bridge to.

Remaining for `(3)`: apply `irreducible_factor_right_vars_eq` to such a factor, feed the bridge with it
in place of `map phi P`, and run the divisibility into
`differentialPolynomialCrossDifference_eq_zero_iff`.

## Lean progress — the factor exists for the actual two-block characteristic

Added to `TwoBlockIrreducibleFactor.lean` (wired, axiom-clean):

    twoBlockPolynomial_not_isUnit :
      the cleared two-block polynomial is not a unit
    exists_irreducible_factor_twoBlockPolynomial :
      hence it has an irreducible factor

The argument runs entirely through the structure's own `clearing` field: a unit would stay a unit
after the two-block equivalence and after mapping to the jet fraction field, where the clearing
identity exhibits it as `C(scalar) * map P`; cancelling the unit scalar makes `map P` a unit, so `P`
would have no variables -- which minimality forbids.

This supplies the input of `irreducible_factor_right_vars_eq` and `irreducible_factor_right_vars`,
whose hypothesis is exactly `Irreducible A` together with `A dvd C.polynomial`.  The corrected route to
`(3)` can now be walked without any appeal to irreducibility surviving the coefficient map.

## Lean progress — the factor with the characteristic's exact support

Added to `TwoBlockIrreducibleFactor.lean` (wired, axiom-clean):

    exists_irreducible_factor_right_vars_eq :
      the cleared two-block characteristic has an irreducible factor whose two-block reading has
      EXACTLY the characteristic's variables

This is the object the corrected route needs, produced rather than assumed: the existence half is this
session's, the support equality is the corpus's `irreducible_factor_right_vars_eq`, and the two are now
one statement.

The chain for `(3)` as it stands:

    premises realized            exists_lurothSaturation_premises            (corpus)
    factor with exact support    exists_irreducible_factor_right_vars_eq     (this session + corpus)
    saturation in bridge shape   exists_separant_pow_mul_mem_iterateIdeal_of_saturation (this session)
    divisibility bridge          irreducible_dvd_of_order_le_of_separant_pow_mul_mem_iterateIdeal (corpus)
    vanishing criterion          differentialPolynomialCrossDifference_eq_zero_iff (corpus)
    non-base ratio exists        exists_differentialRelation_coefficientRatio_not_mem_bot (corpus)
    order bounds                 order_crossRelation_le, minimalRank_order_le_crossRelation (this session)

What is left is to run the bridge on the factor and read the conclusion through the vanishing
criterion.

## Lean progress — the factor, mapped, divides the characteristic

Added to `TwoBlockIrreducibleFactor.lean` (wired, axiom-clean):

    mapped_twoBlockFactor_dvd :
      a factor of the cleared two-block characteristic, read through the two-block equivalence and
      mapped to the jet fraction field, divides `map phi P`

The clearing identity presents the mapped two-block characteristic as `C(scalar) * map phi P` with
`scalar` a unit, so the unit drops out of the divisibility and the factor divides the mapped
characteristic outright.

This is what connects the factor produced in the previous section to the object the saturation
membership is stated about (`iterateIdeal (map phi P)`).  With it, the bridge's `A` and the
saturation's ambient are finally the same polynomial up to the divisibility just proved.

## Lean progress — the bridge's `A` now exists where the bridge lives

Added to `TwoBlockIrreducibleFactor.lean` (wired, axiom-clean):

    exists_irreducible_factor_mapped_characteristic :
      the mapped characteristic has a nonconstant irreducible factor, taken in the jet fraction
      field's own polynomial ring

This settles the point that correction 3 exposed.  The divisibility bridge needs `Irreducible A` for an
`A` in the single-block ring over the fraction field; irreducibility does not travel there along the
coefficient map, so the factor must be taken downstairs.  Unique factorization supplies it, the mapped
characteristic being nonzero and having a variable, and irreducibility gives nonconstancy for free.

All three of the bridge's hypotheses are now available:

    hAvars           this section
    hAirreducible    this section
    hmem             exists_separant_pow_mul_mem_iterateIdeal_of_saturation, with A dvd map phi P
    hQorder          order_crossRelation_le

The last one to arrange is `hmem` for the FACTOR rather than for `map phi P` -- the iterate ideal of a
divisor contains that of the multiple only in one direction, so this needs the corpus's iterate-ideal
monotonicity, which is the next thing to read.

## The last bridge hypothesis was already in the tree

`differentialPolynomialIterateIdeal_le_of_dvd` -- the differential ideal of a divisor contains that of
the multiple -- already exists in `DifferentialLurothComponentTransfer.lean` (line 212).  A module
re-deriving it was written and deleted before any build; the name collision is what caught it, one
step earlier than the previous three corrections.

So every hypothesis of the divisibility bridge is now available for an irreducible factor `A` of
`map phi P`:

    hAvars, hAirreducible   exists_irreducible_factor_mapped_characteristic   (this session)
    hmem                    exists_separant_pow_mul_mem_iterateIdeal_of_saturation (this session)
                              transported along differentialPolynomialIterateIdeal_le_of_dvd (corpus)
    hQorder                 order_crossRelation_le                           (this session)

The remaining work on `(3)` is to apply the bridge with these and read the resulting divisibility
through `differentialPolynomialCrossDifference_eq_zero_iff`.  No further infrastructure is missing --
what is left is the application itself.

## Two more prerequisites were already present; the real remaining obstacle named

Searched before writing, and found both:

    scalarDifferentialPolynomialSeparant_order_le      DifferentialKernelCharacteristic:608
    scalarDifferentialPolynomialSeparant_vars_subset   DifferentialKernelCharacteristic:602
    IsMinimalScalarDifferentialPolynomialRank.separant_not_mem                        :638

so no separant order lemma needs writing.

The application can also be arranged to avoid the separant mismatch entirely.  The bridge's hypothesis
is `separant A ^ e * Q in iterateIdeal A`; the saturation gives
`separant (map phi P) ^ b * Q in iterateIdeal (map phi P)`.  Taking `e := 0` and
`Q' := separant (map phi P) ^ b * Q` turns the saturation membership itself into the bridge's
hypothesis, after transporting along `differentialPolynomialIterateIdeal_le_of_dvd`.  The bridge then
yields `A dvd Q'`, and irreducibility plus `irreducible_not_dvd_scalarDifferentialPolynomialSeparant`
strips the separant power.

What genuinely remains is one technical mismatch: the factor-support theorem
`irreducible_map_factor_vars_eq` is stated along `algebraMap F K` for a polynomial over `F`, whereas
the map in play is `phi : G ->a[F] K` for a polynomial over `G`.  Matching them -- either by
instantiating `K` as a `G`-algebra through `phi` or by restating the support theorem for a general
injective coefficient map -- is the last technical step before the bridge's `hQorder` (which needs
`order A = order (map phi P)`) can be discharged.

## Lean progress — the last technical mismatch is gone

`GaloisForLFunctions/HTGeometry/MappedCharacteristicFactorSupport.lean` (wired, axiom-clean):

    irreducible_factor_mapped_vars_eq  :  an irreducible factor of `map phi P` has exactly `P`'s vars
    irreducible_factor_mapped_order_eq :  hence exactly `P`'s order

The obstacle named in the previous section dissolves without generalizing anyone's theorem: declaring
the jet fraction field an algebra over the intermediate field THROUGH `phi` makes `phi` the structure
map, and the corpus's `irreducible_map_factor_vars_eq` then applies verbatim.  A one-line `letI` where
a restatement looked necessary.

With `order A = order P`, the bridge's `hQorder` is now reachable from `order_crossRelation_le` and the
corpus's separant order bound, and every hypothesis of the divisibility bridge has a proof in the tree.

## The bridge's order hypothesis does not come from the cross-relation bound — obstruction located

Confirmed from the definitions rather than assumed:

    differentialPolynomialTwoBlockEquiv F :
      DifferentialPolynomial (Unit + Unit) F  =~  MvPolynomial (Unit x N) (DifferentialPolynomial Unit F)
    differentialPolynomialTwoBlockCoefficient m C = (twoBlockEquiv F C).coeff m

so a two-block coefficient is a polynomial in the LEFT block variables.  The coefficient
cross-relation `C q * map A - C p * map B` over `G` therefore has left-block jets as its variables, and
`order_crossRelation_le` bounds its order by `max(order A, order B)` -- a left-block quantity, which
clearing denominators makes as large as the denominators require.  It is NOT bounded by the
characteristic's order.

Consequently the bridge's `hQorder` cannot be discharged from `order_crossRelation_le`, and the
application planned in the previous sections does not go through as stated.  The order comparison the
bridge needs must be about the right-block variables -- the ones the mapped objects actually carry over
`K` -- so what is missing is a lemma relating the order of `map phi (crossRelation ...)` to the
right-block support of the two-block characteristic, whose equality with `P.vars` the corpus already
proves (`irreducible_factor_right_vars_eq`).

Recorded rather than papered over: writing the application with `hQorder` supplied by the wrong bound
would have produced a theorem whose hypothesis is unattainable, which is the same failure mode as the
vacuous no-go caught on the elliptic-shadow card.

## Lean progress — removing the separant weight

`GaloisForLFunctions/HTGeometry/SeparantPowerStrip.lean` (wired, axiom-clean):

    dvd_of_dvd_separant_pow_mul :
      an irreducible divides a separant-weighted multiple only by dividing the multiple

Searched first: the corpus has the reduction theorem that PRODUCES such a divisibility
(`irreducible_dvd_of_order_le_of_separant_pow_mul_mem_iterateIdeal`) and the non-divisibility fact it
rests on (`irreducible_not_dvd_scalarDifferentialPolynomialSeparant`), but not the cancellation step
between them.  It is three lines from primality, and every version of the final argument needs it.

This is independent of the order obstruction recorded above: whatever `Q` the eventual application
uses, the separant weight comes off the same way.

## The intended terminal step is a reciprocity argument, not a bridge application

Reading the two Luroth modules by their own section structure settles what the last step is meant to
be, and it is not what the previous sections of this card assumed.

`DifferentialLurothCoefficient.lean` opens: "This file builds the coefficient layer after
characteristic pseudo-reduction ... before the two-copy cross-difference argument.  No divisibility,
characteristic-set reduction, coefficient-ratio theorem, or field-generation conclusion is assumed."

`DifferentialLurothComponentTransfer.lean` runs through the sections

    The differential structure on the formal free-jet fraction field
    Total derivatives commute with coefficient embeddings
    Bounded multiplier cancellation on the general component
    Cleared Bezout cancellation away from one jet
    The coefficient cross-relation and characteristic saturation
    Equation (78), squarefree recombination, and the cleared characteristic
    Primitive products needed by the TERMINAL RECIPROCITY STEP

So the missing capstone has a name in the tree already -- the terminal reciprocity step -- and it is a
two-copy symmetry argument on the cross-difference, in the spirit of `Bivariate.swap` and the
`swap_theta = -theta` identity used in the pseudo-reduction module.  The divisibility bridge is used
INSIDE the corpus's own lemmas; applying it at top level to the coefficient cross-relation, as the
plan recorded above proposed, is not the intended route, and the order obstruction found in the
previous section is exactly the symptom of that mismatch.

Anyone continuing should therefore aim at the reciprocity step directly, with these as its inputs:

    PrimitiveTwoBlockDifferentialCharacteristic.exists_mappedCrossRelation_saturation
    PrimitiveTwoBlockDifferentialCharacteristic.mappedPolynomial_squarefree
    PrimitiveTwoBlockDifferentialCharacteristic.irreducible_factor_right_vars_eq
    MvPolynomialPrimitive.mul, MvPolynomialPrimitive.map_C_of_ne_zero
    differentialPolynomialCrossDifference_eq_zero_iff
    exists_differentialRelation_coefficientRatio_not_mem_bot

and with this session's `dvd_of_dvd_separant_pow_mul` for removing separant weights wherever they
appear.

## Confirmed absent, and one reciprocity lemma added

A scan for the field-generation conclusion (`G = differentialAdjoin F {w}`) finds nothing in the tree:
the terminal reciprocity step is genuinely unwritten, as the module headers say.

`GaloisForLFunctions/HTGeometry/CrossDifferenceAntisymmetry.lean` (wired, axiom-clean):

    differentialPolynomialCrossDifference_swap_args :  exchanging the entries negates it
    differentialPolynomialCrossDifference_self     :  a self cross-difference vanishes

The corpus records the antisymmetry of the two-copy BLOCK swap
(`differentialPolynomialTwoBlockSwap_crossDifference`); the antisymmetry in the ARGUMENTS was absent.
A reciprocity argument compares the two orderings of a coefficient pair, so it needs both.

## Lean progress — the reciprocity identity itself

Added to `CrossDifferenceAntisymmetry.lean` (wired, axiom-clean):

    differentialPolynomialTwoBlockSwap_crossDifference_eq_swap_args :
      swapping the two copies IS exchanging the two entries

This is the identity the terminal step is named after.  The corpus had each half separately -- the
block swap negates the cross-difference -- and this session added the argument swap; together they say
the two symmetries coincide, which is what allows a reciprocity argument to move between the two
copies and the two coefficients interchangeably.

Also recorded from reading `mappedPolynomial_squarefree`: the corpus uses the same
`letI : Algebra G K := phi.toRingHom.toAlgebra` device that this session used for
`irreducible_factor_mapped_vars_eq`, which confirms that module is written in the corpus's own idiom
rather than against it.

Inputs to the terminal reciprocity step, all now in the tree:

    saturation, squarefreeness, right-vars equality, primitive products      (corpus)
    diagonal vanishing of the cross-difference                              (corpus)
    block-swap and argument-swap antisymmetry, and their coincidence        (corpus + this session)
    vanishing criterion, non-base ratio existence                            (corpus)
    factor existence with full support, order equality                      (this session)
    separant-weight removal                                                  (this session)

## Prerequisite hunt closed: only the terminal proof is missing

Checked this turn, all present, none needing to be written:

    differentialPolynomialTwoBlockEquiv_left / _right   the block embeddings read through the equivalence
    MvPolynomialPrimitive.map_C_of_ne_zero              primitivity of a constants-extension
    MvPolynomialPrimitive.mul                           primitivity of products over a UFD
    differentialPolynomialEval_crossDifference_diagonal diagonal vanishing
    differentialPolynomialCrossDifference_eq_zero_iff   vanishing criterion

Together with everything listed in the previous section, the prerequisite hunt for the terminal
reciprocity step is closed: every auxiliary fact the argument is known to use exists in the tree.
What is missing is the terminal proof itself -- one large theorem combining saturation, squarefreeness,
right-variable support, primitivity, the diagonal vanishing and the reciprocity identity into
`G = C<w>`.

The next session should therefore not look for more prerequisites.  It should write that proof, in
`DifferentialLurothComponentTransfer`'s idiom, and expect it to be long.
