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

## Lean progress — the ratio field, and the normalized characteristic over it

`GaloisForLFunctions/HTGeometry/CharacteristicRatioField.lean` (wired, axiom-clean):

    characteristicRatioSet, characteristicRatioField    the field generated by the coefficient ratios
    characteristicRatioField_le                         it sits inside the intermediate field
    coeff_normalized_mem_ratioField                     the normalized characteristic's coefficients
                                                          lie in it
    map_descend_normalized                              so the normalized characteristic descends there

Dividing the characteristic by one of its coefficients replaces its coefficients by ratios, and those
ratios generate an intermediate field `R <= G` over which the normalized characteristic is defined.
This is the object a Luroth conclusion has to identify with `G` itself: the terminal reciprocity step
is exactly the statement that `R = G`, and by the corpus's non-base ratio theorem `R` is strictly
larger than the base whenever `G` is.

The descent uses this session's `descendCoefficients`; the normalization is a scalar multiple, so it
remains a relation of `y` over `R`.

## Lean progress — the Luroth target field, and a relation over it

Added to `CharacteristicRatioField.lean` (wired, axiom-clean):

    characteristicDifferentialRatioField      the DIFFERENTIAL field generated by the coefficient
                                                ratios -- the object `(3)` claims equals `G`
    characteristicDifferentialRatioField_le   it lies inside `G` (needs `G` derivation closed)
    coeff_normalized_mem_differentialRatioField
    descend_normalized_mem_relationIdeal      the normalized characteristic, descended, is a RELATION
                                                of `y` over that field

The ordinary adjoin of the ratios is not derivation closed, so the object the Luroth statement is
about is the differential adjoin; with `differentialAdjoin_le` and `G` derivation closed it still sits
inside `G`.  The descended normalized characteristic is a relation there because normalization is
multiplication by a scalar and the relation ideal is an ideal.

`(3)` is now the single statement

    characteristicDifferentialRatioField G P n  =  G

for a minimal characteristic `P` and a coefficient index `n` with `P.coeff n /= 0`.  One inclusion is
proved above; the other is the terminal reciprocity step.

## Lean progress — Ritt's first equality: the ratio field has the same minimal rank

`GaloisForLFunctions/HTGeometry/RatioFieldMinimalRank.lean` (wired, axiom-clean):

    scalarDifferentialPolynomialOrder_C_mul   normalizing does not change the order
    order_descend_normalized_eq               nor does descending to the ratio field
    minimalRank_ratioField_le                 so the minimal rank over the ratio field is at most
                                                the characteristic's

With `minimalRank_le_of_le` giving the opposite inequality (the ratio field sits inside `G`, so its
relations are relations over `G`), the two fields have the SAME minimal rank.  That is Ritt's first
equality, and it is what makes the terminal comparison possible: the ratio field is not merely a
subfield of `G`, it is one over which `y` has exactly the same relational complexity.

The remaining content of `(3)` is that same-rank forces equality of the fields, which is the
reciprocity step.

## Lean progress — Ritt's first equality, as one theorem

Added to `RatioFieldMinimalRank.lean` (wired, axiom-clean):

    minimalRank_ratioField_eq :
      the minimal relation rank over the ratio field EQUALS the minimal relation rank over the whole
      intermediate field

Both inequalities are now in one statement: the descended normalized characteristic gives one, and
monotonicity of the minimal rank in the coefficient field gives the other.  The claim recorded in the
previous section is therefore backed by a declaration rather than by a remark.

`(3)` is now: same minimal rank plus the reciprocity step implies the two fields coincide.

## Lean progress — the second rank coordinate is invariant too

Added to `RatioFieldMinimalRank.lean` (wired, axiom-clean):

    scalarDifferentialPolynomialLeaderDegree_C_mul   normalizing preserves the leader degree
    leaderDegree_descend_normalized_eq               and so does descending to the ratio field

Rank in this development is lexicographic in (order, leader degree, total degree).  The order
coordinate was handled in the previous section; this one handles the second, so the descended
normalized characteristic agrees with the characteristic in both.  The comparison the terminal step
runs is therefore between two relations of identical rank in the first two coordinates, which is what
Ritt's argument assumes when it turns to the degree count.

`MvPolynomial.degreeOf_C_mul` wants the scalar in `nonZeroDivisors`, not merely nonzero -- over a field
`mem_nonZeroDivisors_of_ne_zero` bridges them.

## Lean progress — the ranks agree in both coordinates

Added to `RatioFieldMinimalRank.lean` (wired, axiom-clean):

    minimalLeaderDegree_ratioField_eq :
      the minimal leader degree over the ratio field equals the minimal leader degree over the whole
      intermediate field

Both directions run through the same two facts, in the two directions: the descended normalized
characteristic is a relation over the ratio field of the characteristic's rank, and the ratio field's
own minimal relation pushes forward to a relation over `G` with its rank unchanged.  With the order
equality of the previous section, the minimal relations over the two fields now agree in order and in
leader degree.

That is as far as rank comparison alone can go: a lexicographic rank has a third coordinate, and
equality of all three still would not by itself force the fields to coincide -- that is precisely what
the reciprocity step supplies.

## Lean progress — the third rank coordinate is invariant as well

Added to `RatioFieldMinimalRank.lean` (wired, axiom-clean):

    support_C_mul_eq       normalizing preserves the support
    totalDegree_C_mul_eq   hence the total degree
    totalDegree_map_eq     an injective coefficient map preserves the total degree

mathlib has no `totalDegree_C_mul`; `totalDegree` unfolds to a `sup` over the support, so both
statements reduce to support preservation, which for a scalar multiple is a two-line coefficient
argument over a field.

All three rank coordinates -- order, leader degree, total degree -- are now known to survive
normalization and descent, so the descended normalized characteristic is a relation over the ratio
field of exactly the characteristic's rank.

`minimalTotalDegree_ratioField_eq` closes the lexicographic comparison: the minimal relation over the
ratio field and the minimal relation over the intermediate field agree in all three rank coordinates.
Proof shape identical to the leader-degree case -- the two inequalities come from feeding each
minimality predicate the other side's relation, with the first two coordinates already known equal so
the third clause of the predicate applies.

## Lean progress — (3) is CLOSED: the terminal reciprocity step is proved

`characteristicDifferentialRatioField G P n = G` is now a theorem
(`GaloisForLFunctions/HTGeometry/RatioFieldReciprocity.lean`, axiom-clean, wired into the umbrella).
The route is not the two-block cross-relation the earlier sections were pursuing -- that one stalled
on an order mismatch between a left-block quantity and the divisibility bridge -- but the degree
count in the tower of jet fields, which needs no two-block machinery at all.

The statement proved is more general than the ratio-field case:

    eq_of_characteristic_rank_eq :
      R <= G derivation-closed subfields of an intermediate field of F<y>,
      P a characteristic of y over G, P1 a characteristic of y over R,
      same order and same leader degree  ==>  G = R

and the ratio field is an instance because the descended normalized characteristic IS a
characteristic over the ratio field of exactly the original rank.

Six new modules carry it:

    JetAdjoinField                   the field B(y, ..., y^(m-1)) generated by a finite jet prefix
                                       over an intermediate field, and the fact that a relation whose
                                       variables all have order < m evaluates into it
    JetAdjoinDerivationClosed        differentiating a relation of order m gives
                                       D P = separant * y_(m+1) + (order <= m), so the fresh jet is
                                       rational in the old ones; hence the prefix field with jets up
                                       to m is derivation-closed and contains ALL of F<y>
    JetPrefixPolynomial              singling out the leader turns the characteristic into a
                                       univariate polynomial over the prefix field which annihilates
                                       the top jet, of degree the leader degree, with leading
                                       coefficient the evaluated initial (nonzero by minimality)
    JetPrefixClearing                the converse: every element of the prefix field is a fraction in
                                       the low jets, so a monic univariate relation clears
                                       denominators back into a differential relation of the same
                                       degree in the top jet.  Hence Ritt's degree equality
                                       `minpoly_natDegree_eq_leaderDegree`
    JetIndependenceDescent           the low jets are algebraically independent over the coefficient
                                       field (a relation among them would have order < m), and an
                                       element of the bigger field lying in the smaller prefix field
                                       lies in the smaller field
    RatioFieldCharacteristicMinimal  the descended normalized characteristic is minimal over the
                                       ratio field
    RatioFieldReciprocity            the tower argument and the theorem

The tower argument: with m the common order, d the common leader degree, W_R and W_G the two jet
prefix fields and N the prefix field of R with jets up to m, one gets N = W_R(y^(m)) = W_G(y^(m))
because G <= F<y> <= N; both relative degrees [N : W_R] and [N : W_G] equal d by the degree equality;
so mathlib's `relfinrank` tower law forces [W_G : W_R] = 1, i.e. W_G = W_R, and independence of the
low jets over G moves each coefficient of G into R.

`IntermediateField.relfinrank` (Mathlib.FieldTheory.Relrank) is what makes this painless: it is a
degree for a PAIR of intermediate fields, so no `Algebra` instance between two subfields has to be
introduced by hand, and its tower law has no finiteness side conditions.

### What the reciprocity theorem does and does not settle

`characteristicDifferentialRatioField_eq` gives `G = F<all coefficient ratios of P>`.  The support of
`P` is finite, so this already says `G` is a FINITELY generated differential field, generated by
explicit elements of `G`.  The card's `(3)` asks for ONE generator, so the remaining step is the
passage from finitely many ratios to a single one.

The tower machinery also shows that step cannot be softened.  Write `R <= G` for a subfield with
`y` differentially algebraic over it, `(m,d)` the rank over `G` and `(m2,d2)` the rank over `R`.  The
same structure theorem that drives the proof (`F<y> = B(y, ..., y^(m_B))`, jets below the order
algebraically independent over `B`) gives

    m2 = m + trdeg_R G                       additivity of transcendence degree in R <= G <= F<y>
    d2 = d * [ G(y,...,y^(m-1)) : R(y,...,y^(m-1)) ]        when m2 = m

so `(m2,d2) = (m,d)` holds **iff** `R = G`.  The rank equality fed to `eq_of_characteristic_rank_eq`
is therefore not a convenient sufficient condition that some clever choice of `w` might satisfy for
soft reasons: for a single ratio `w` it is equivalent to the conclusion `G = F<w>`.  What has to be
proved for a single generator is exactly Ritt's degree count -- that the cleared two-block
characteristic has the same order in the left block as in the right one -- which is the assembly the
earlier sections of this card were building (`CrossRelationOrderBound`, `CrossDifferenceAntisymmetry`,
`SeparantPowerStrip`, `MappedCharacteristicFactorSupport`) and where they stalled.

The value of the reciprocity theorem for that assembly: the target is no longer "G equals the field
generated by some ratio" but the numerical statement "the cleared characteristic's left-block order is
at most `m`", and once that is available `eq_of_characteristic_rank_eq` converts it into `G = F<w>`
with no further field-theoretic work.

## The single-generator step, analysed

With `eq_of_characteristic_rank_eq` the single-generator claim `G = F<w>` reduces to ONE numerical
fact about the primitive two-block clearing `Pc(U,Y)` of the characteristic:

    ord_U Pc <= m   and   deg_{U_m} Pc <= d           (the block-reciprocity bound)

Given it, take a nonconstant coefficient ratio `w = a(y)/b(y)` (corpus:
`exists_differentialRelation_coefficientRatio_not_mem_bot`); the cross-relation `a(U) - w b(U)` is a
nonzero relation of `y` over `F<w>` with order `<= m` and top-jet degree `<= d`, so the characteristic
over `F<w>` has rank exactly `(m,d)` and `eq_of_characteristic_rank_eq` gives `G = F<w>`.

Two things learned about that bound:

1. It is FALSE without minimality.  `Pc = U_5*(Y_1 - U_1) + (Y_0 - U_0)` is primitive, vanishes on the
   diagonal, has `ord_Y = 1` and `ord_U = 5`.  What fails is that the associated field is not one over
   which `y` has rank `(1,1)`: for the analogous `U_2*(Y_1 - U_1) + (Y_0 - U_0)` one computes
   `y' = (q' - p^2)/(p' + 1)` with `p = y''`, `q = y''y' + y`, so `y` itself lies in the field and the
   true order is 0.  Any proof of the bound must therefore use minimality, not just primitivity and
   diagonal vanishing.

2. The classical Luroth route to it (`Pc` divides the two-block cross-difference `H`, then a
   content/Gauss argument forces the quotient to be a unit, so `Pc` is antisymmetric up to a scalar
   and the two block orders agree) is CIRCULAR here: the differential divisibility bridge
   `irreducible_dvd_of_order_le_of_mul_mem_iterateIdeal` needs the relation's order to be `<= m`,
   which for `H` is `ord_U Pc` -- the very number being bounded.  That is the obstruction the earlier
   sections of this card hit, now identified precisely.

A promising non-circular route: slice `Pc` by the monomials in the jets `U_k, k > m`.  Because the
right-block monomials involve only `U_0..U_m` on the diagonal, EACH slice vanishes on the diagonal
separately, so each slice specializes at `U := y` to a relation of `y` of order `<= m` and leader
degree `<= d`, with coefficients rational in the jets `y, ..., y^(n-1)`.  If the slice ratios lie in
`G`, minimality plus `IsMinimalScalarDifferentialPolynomialRank.dvd_of_relation_order_le` forces each
slice to be a scalar multiple of the characteristic, hence the coefficient ratios of the
characteristic are rational in jets of order `< n`, and downward induction gives the bound.  The open
point is exactly whether the slice ratios lie in `G`; equivalently whether `y` still has rank `(m,d)`
over `F<G, slice ratios>`.

## The single-generator step: route found (literature-confirmed), and the circularity broken

Ritt's own finish (Differential Algebra II.42-43; restated as Proposition 7 of D'Alfonso-Jeronimo-
Solerno, *Effective Differential Luroth's Theorem*, J. Algebra 2014, arXiv:1202.6344) is the identity

    D(u,y) := Q0(u)P0(y) - P0(u)Q0(y)  =  a * C(u,y),   a in F,                        (RITT)

where `C` is the cleared two-block characteristic and `P0, Q0` are two of its coefficients with
`P0(u)/Q0(u)` not in `F`.  `(RITT)` immediately gives the block reciprocity `ord_U C = ord_Y C` and
the matching top-jet degrees, because `D` is antisymmetric under the block swap; and then the
cross-relation `P0(U) - w Q0(U)` is a relation of `y` over `F<w>` of rank exactly `(m,d)`.

Two things this session establishes about `(RITT)`:

* **The final step of the classical proof is no longer needed.**  Kolchin's proof (as reproduced in
  the partial-differential paper arXiv:2210.05469, Theorem 3.1) finishes from `(RITT)` with the
  differential-isomorphism criterion "no non-identity differential isomorphism over `F<v>` fixes
  `v` implies `G = F<v>`".  Our `eq_of_characteristic_rank_eq` replaces that entire step: from
  `(RITT)` the cross-relation has rank `(m,d)` and the theorem gives `G = F<w>` directly.  So the
  Galois-style machinery (differential isomorphisms, Kolchin's primitive-element criterion) never has
  to be formalized.

* **The circularity noted above is broken by the block swap.**  The divisibility `C | D` cannot be
  obtained in the `Y`-ranking (the order hypothesis is the number being bounded).  It must be run in
  the *reversed* ranking, where the leader is a `U`-jet: there the required bound is
  `ord_U D <= ord_U C`, which holds by construction because `P0, Q0` are coefficients of `C`.  The
  corpus already owns the swap and its transport of iterate-ideal membership
  (`differentialPolynomialTwoBlockSwap_mem_iterateIdeal`), so the certificate can be moved to the
  block where the bridge applies, and antisymmetry of `D` moves the conclusion back.

Given `C | D`, the passage to `(RITT)` is elementary and needs no ideal theory:
`deg_{U_k} D <= deg_{U_k} C` for every jet `k` (the coefficients of `D` in the `U` block are among
those of `C`), so the quotient has no `U` variable, i.e. `D = C * q(Y)`; and a common divisor
`q(Y)` of all `U`-coefficients `H_mu K(Y) - K_mu H(Y)` of `D` divides `c*K(Y)` and `c*H(Y)` for
`c = K_nu H_mu - K_mu H_nu`, which is nonzero for some pair exactly because `w` is not in `F`;
coprimality of `H, K` then forces `q` to be a unit.

## Lean progress — the Luroth criterion (the whole of `(3)` minus one divisibility)

`GaloisForLFunctions/HTGeometry/LurothLowRankCriterion.lean` (wired, axiom-clean):

    vars_nonempty_of_relation                 a nonzero relation is nonconstant
    eq_differentialAdjoin_of_relation_rank_le  ONE low-rank relation over `F<w>` forces `F<w> = G`
    eq_differentialAdjoin_of_ratio_rank_le     the same, packaged for a ratio `H(y)/K(y)` of two
                                                 differential polynomials over the base

The second is the exact interface Ritt's argument needs.  Its hypotheses are: the ratio lies in `G`
and not in `F`; `H` and `K` involve no jet above the characteristic's order `m`; and their degrees in
the `m`-th jet are at most the leader degree `d`.  Its conclusion is `F<H(y)/K(y)> = G` -- the card's
`(3)`.

So `(3)` is now reduced to a purely polynomial statement with no field theory left in it:

    (RITT-DVD)   the cleared two-block characteristic `C` divides the cross-difference
                 `D(U,Y) = H(U)K(Y) - K(U)H(Y)` of two of its coefficients,

from which the order and degree hypotheses of `eq_differentialAdjoin_of_ratio_rank_le` follow by
antisymmetry of `D` (see the previous section).  Everything downstream of `(RITT-DVD)` is formal.

## Lean progress — cross-difference rigidity: `C | D` now yields block reciprocity

`GaloisForLFunctions/HTGeometry/CrossDifferenceRigidity.lean` (wired, axiom-clean):

    differentialPolynomialTwoBlockCoefficient_left_mul   right-block coefficients scale by a
                                                           left-block factor
    degreeOf_twoBlockSwap_inl                            the swap exchanges the two block degrees
    exists_right_of_degreeOf_inl_eq_zero                 no left-block jet means a right-block
                                                           polynomial
    degreeOf_eq_zero_of_isUnit                           a unit has no jets
    degreeOf_eq_of_dvd_crossDifference                   RIGIDITY: a divisor of the cross-difference
                                                           dominating its left-block degrees has
                                                           exactly its degree in EVERY jet
    degreeOf_inl_eq_degreeOf_inr_of_dvd_crossDifference  hence the two block degrees of the divisor
                                                           agree at every jet

This is Ritt's degree argument, formal.  The proof is the one sketched above: the quotient has no
left-block jet by degrees, hence is a right-block polynomial; as such it divides every right-block
coefficient of the swapped identity, i.e. all the `K*H_m - H*K_m`; two of those combine to
`c*K` and `c*H` with `c = K_n H_m - K_m H_n` nonzero exactly when the ratio is not in the base, so
coprimality of `H` and `K` forces the quotient to be a unit and the degrees to agree.  Block
reciprocity then follows because the cross-difference is antisymmetric under the swap.

Only ONE input is now missing for `(3)`:

    (RITT-DVD)  C | differentialPolynomialCrossDifference H K

together with the bookkeeping that `H` and `K` (numerator and denominator of a coefficient ratio in
reduced form) have left-block degrees dominated by `C`.  Everything else is formal:
`degreeOf_inl_eq_degreeOf_inr_of_dvd_crossDifference` converts `(RITT-DVD)` into the order and degree
bounds, and `eq_differentialAdjoin_of_ratio_rank_le` converts those into `G = F<w>`.

### Plan for `(RITT-DVD)`, with the corpus lemmas located

The divisibility must be assembled factorwise, because the corpus bridge
`irreducible_dvd_of_order_le_of_mul_mem_iterateIdeal` applies to an irreducible only.  What is
available with no new theory:

1. Clear denominators in `exists_mappedCrossRelation_saturation` to a TWO-BLOCK membership
   `M * D in differentialPolynomialFamilyIterateIdeal C`.
2. `differentialPolynomialFamilyIterateIdeal_le_of_dvd` then gives `M * D in [A]` for EVERY factor
   `A | C` -- no extra work, because a differential ideal generated by a multiple sits inside the one
   generated by the divisor.
3. Map to the fraction field of `F{Y}` (the corpus already builds such a jet fraction field and its
   derivation) so that `A` becomes a scalar differential polynomial in the `U` block, and apply the
   bridge.  Its order hypothesis reads `ord_U D <= ord_U A`, which holds for every factor `A` of
   maximal `U`-order, since `ord_U D <= ord_U C`.
4. What is NOT yet available is the peeling for factors of smaller `U`-order: after dividing out the
   top-order factors the quotient must be shown to lie in the general component of the next factor.
   That is the one place where general-component theory (prime saturation, generic points) is really
   used; the corpus's bridge builds a generic point internally but does not expose `sat`.

So the remaining work is one module on general components of irreducible differential polynomials --
`sat(A)` prime, `B not in sat(A)` for a non-associate irreducible `B`, and membership transfer -- and
then the peeling induction.  Everything before and after it is already formal.

### `(RITT-DVD)`: the peeling, with the multiplier problem solved

Re-reading `exists_mvPolynomial_bezout_clear_away_from_variable` settles how the peeling avoids
general-component theory.  Its own docstring states the intent: "In the Ritt descent, `x` is the top
jet shared by every factor through equation (78).  The resulting multiplier has strictly lower order
in that block; after swapping blocks it is therefore eligible for
`irreducible_dvd_of_order_le_of_mul_mem_iterateIdeal`."

The obstruction in the peeling is that after dividing out a factor `B`, the certificate for the next
factor `A` carries `B` in its multiplier, and `B` has HIGHER order than `A`, which the bridge forbids.
Bezout removes it: with `W = U*A + V*B` free of the shared top jet `x`,

    W * (rest) = U*A*(rest) + V*(B*(rest))  is again in [A],

so `W` replaces `B` in the multiplier and has strictly lower order.  And `A` cannot divide `W`:
`A` involves `x` (equation 78) while `W` does not, so divisibility would force `deg_x A <= deg_x W = 0`.
That is exactly the hypothesis `hMnot` of the bridge.

The quotient's order is controlled by degrees, not by ideal theory: the factors of a given top jet
account for ALL of `C`'s degree at that jet, and `deg_{U_k} D <= deg_{U_k} C`, so after dividing out
that whole group the running quotient has degree `0` at the jet and its order drops.  The induction is
therefore over the finitely many jets occurring in `C`, in decreasing order.

Remaining to build, in order:

1. clearing of `exists_mappedCrossRelation_saturation` to a two-block membership
   `M * D in differentialPolynomialFamilyIterateIdeal C` (denominator clearing only);
2. the multiplier-reduction lemma (Bezout + "`A` involves `x`, `W` does not" gives `hMnot`);
3. the decreasing-jet induction producing `A | D` for every irreducible factor `A` of `C`;
4. squarefree recombination (`Squarefree.dvd_of_forall_irreducible_factor_dvd`, already in the corpus)
   to `C | D`.

After that `degreeOf_inl_eq_degreeOf_inr_of_dvd_crossDifference` and
`eq_differentialAdjoin_of_ratio_rank_le` close `(3)` with no further mathematics.

### Why the peeling is genuinely needed, stated exactly

The two views are each half-adapted, and this is the precise reason the assembly is not a one-liner:

| view | orders of the irreducible factors of `C` | bound available on `D` |
|---|---|---|
| `Y`-block (the corpus's native view) | ALL equal to `m`, by equation (78) (`irreducible_factor_right_vars_eq`) | `ord_Y D <= ord_Y C` is FALSE in general -- it is the number being bounded |
| `U`-block (after the swap) | not uniform; this is the peeling dimension | `ord_U D <= ord_U C` holds by construction |

The Bezout multiplier trick removes an already-divided factor `B` from the certificate only when the
divisor `A` involves the jet being removed, since that is what makes `A` fail to divide the Bezout
output.  In the `U`-view the removed jet is `B`'s top jet, which the lower-order `A` does not involve,
so the trick does not apply there as it stands.

Two ways out, in order of promise:

* **A left-block equation (78).**  If every irreducible factor of `C` had the same `U`-order, the
  `U`-view would be uniform and the bridge would apply to each factor with no peeling at all.  This
  would follow from equation (78) applied to `C^swap`, provided `C^swap` is (up to units) the clearing
  of a characteristic over the field generated by the `U`-coefficient ratios -- which is a statement
  of the same kind as the one being proved, so it must be checked, not assumed.
* **The general component as a prime.**  The corpus's `differentialPolynomialGeneralComponentJets`
  evaluation lands in a field, so its kernel is prime and supplies exactly the "`T` not in `sat(A)`
  implies `L` in `sat(A)`" step of Ritt's peeling.  What has to be added is the non-vanishing of an
  already-divided factor at the generic point of another factor, which in Ritt's own proof comes from
  all factors sharing a leader -- i.e. from equation (78) again, in whichever ranking the peeling is
  run.

So the single mathematical question left in this card is: **do all irreducible factors of the cleared
two-block characteristic have the same left-block order?**  If yes, `(3)` closes with the machinery
already built; if no, the peeling induction of Ritt's proof has to be formalized with the
general-component prime.

#### Two facts about `C`'s factorization, to save the next session the detour

* **`C` is NOT irreducible in general.**  One might hope that `C(y,Y) = c*P(Y)` with `P` irreducible
  over `G` forces `C` to be irreducible in `F{U,Y}`, so that the bridge applies to `C` directly and the
  peeling disappears.  It does not: for `G = F<y^2>` the primitive clearing is `C = Y_0^2 - U_0^2 =
  (Y_0-U_0)(Y_0+U_0)`, and `P = Y_0^2 - y^2` is irreducible over `G`.  The specialisation `U := y`
  factors over `F<y>`, not over `G`, so no contradiction arises.
* **What the specialisation does give.**  No nonzero element of `F{U}` vanishes at `y` (that is exactly
  differential transcendence), so the specialisation `U := y` cannot drop the `Y`-degree of a factor.
  Hence every factor of `C` specialises to a genuinely nonconstant relation of `y`, and the
  `Y`-supports of the factors are all equal (equation (78)).  In the `G = F<y^2>` example both factors
  also have the same `U`-order, which is what uniformity would predict.

### Testing left-block uniformity: the near-counterexample and what kills it

Take the four "roots" `y, -y, y'', -y''` and

    P = Y_0^4 - a*Y_0^2 + b,     a = y^2 + (y'')^2,   b = y^2 (y'')^2,   G := F<a,b>.

Then `P` vanishes at `y`, its coefficient ratios are exactly `a, b`, so `G` is the ratio field as the
reciprocity theorem demands, the clearing

    C = (Y_0^2 - U_0^2)(Y_0^2 - U_2^2)

is primitive and vanishes on the diagonal, and its two irreducible factors have left-block orders `0`
and `2` -- non-uniform.  So uniformity, if true, cannot follow from primitivity plus diagonal
vanishing; it must use minimality of the rank.

And minimality is exactly what this example fails, for the same reason as the earlier ones.  `P` is
the characteristic only if it is irreducible over `G`, i.e. only if `y^2` is NOT in `G`; and `y^2` lies
in `G` unless the pairing `(y^2, (y^2)') <-> ((y'')^2, ((y'')^2)')` extends to a differential
automorphism of `F<y>` over `F`.  It does not: such a map would need `sigma(y) = y''` and hence
`sigma(y'') = y^(4) /= y`.  So `y^2` is in `G`, `P` is reducible, the true characteristic is
`Y_0^2 - y^2`, and its clearing `Y_0^2 - U_0^2` is uniform again.

That is now the third time the same mechanism -- uniqueness of the derivation extension, i.e. the
rigidity of differential automorphisms -- has destroyed a candidate counterexample (the earlier two
were the fake `U_5` characteristic and the degree-two `y^(5)` example).  The evidence is that left-block
uniformity is TRUE and that its proof is the differential-automorphism rigidity, which is also the
engine of Kolchin's own proof.  A proof of uniformity along those lines, or a genuine counterexample,
is the next thing to settle; both would come from the same analysis.

### The next brick, located exactly

Every route to `(RITT-DVD)` starts by moving the corpus's saturation certificate out of the
`Y`-view (`K{Y}` with `K = Frac F{U}`) into the two-block ring `F{U,Y}`, and back up into the
`U`-view (`K'{U}` with `K' = Frac F{Y}`).  Both moves need ONE lemma that the corpus does not yet
have:

    differentialPolynomialTwoBlockEquiv intertwines the two-block total derivation with the
    total derivation of the coefficient ring F{U} acting on MvPolynomial (Unit x N) (F{U}).

Grep confirms there is no such lemma (`TwoBlockEquiv` never appears next to a derivation).  With it:

* the corpus's `map_differentialPolynomialIterateOver_of_commutes` transports iterate ideals along
  the equivalence and along `algebraMap F{U} K`;
* `mem_differentialPolynomialIterateIdeal_exists_upTo` plus `exists_mvPolynomial_fraction_clear`
  clear the denominators of the finite certificate, giving the two-block membership
  `C d * M * D in differentialPolynomialFamilyIterateIdeal C`;
* `differentialPolynomialFamilyIterateIdeal_le_of_dvd` then hands the same membership to every
  irreducible factor of `C`, and the `U`-view bridge applies to each factor of maximal left-block
  order.

Note also that `differentialPolynomialIterateIdeal` is defined only over a FIELD, so the descent must
land in the two-block `differentialPolynomialFamilyIterateIdeal` over `F` (which is the right target
anyway) and not in an `F{U}`-coefficient version.

## Lean progress — the two-block splitting is differential (the located brick, built)

`GaloisForLFunctions/HTGeometry/TwoBlockEquivDerivation.lean` (wired, axiom-clean):

    differentialPolynomialDifferential                     F{U} is itself a differential ring, by
                                                             the jet derivation
    diffPolyIterate                                        iterated total derivative over an
                                                             arbitrary differential coefficient RING
                                                             (the corpus's version is field-only)
    diffPolyIterate_eq_familyIterateOver                   over a field it is the corpus's iterate
    differentialPolynomialTwoBlockEquiv_overDerivation     THE BRICK: the splitting intertwines the
                                                             two-block total derivation with the
                                                             total derivation over `F{U}`
    differentialPolynomialTwoBlockEquiv_diffPolyIterate    hence with every iterate

The proof is the three-case induction: constants differentiate inside `F{U}`; a right-block variable
differentiates as a variable; a left-block variable becomes the constant `C (X_n)` whose derivative in
the coefficient ring is `C (X_{n+1})` -- which is exactly the statement that the left block's jets
keep their differential meaning after being demoted to coefficients.

With this, moving a differential-ideal certificate between the two views is bookkeeping:
`map_differentialPolynomialIterateOver_of_commutes` transports along `algebraMap F{U} K`, and
`mem_differentialPolynomialIterateIdeal_exists_upTo` + `exists_mvPolynomial_fraction_clear` clear the
denominators of the finite certificate.

## Lean progress — the certificate descends from the jet fraction field

`GaloisForLFunctions/HTGeometry/JetFractionDerivationTransport.lean` (wired, axiom-clean):

    algebraMap_jetFraction_deriv                        the inclusion `F{U} -> Frac F{U}` is
                                                          differential for the y-transported
                                                          derivation
    map_diffPolyIterate_of_commutes                     iterates commute with a derivation-preserving
                                                          coefficient map (CommRing version)
    diffPolyIterate_eq_iterateOver                      agreement with the corpus's scalar iterate
    exists_clear_mem_familyIterateIdeal_of_map_mem      DESCENT: a differential-ideal membership
                                                          holding in `K{Y}` holds in the two-block
                                                          ring after multiplying by one nonzero
                                                          left-block denominator

The descent is done by localization rather than by hand: `MvPolynomial (Unit x N) K` is a localization
of `MvPolynomial (Unit x N) (F{U})` at the constants from `nonZeroDivisors`, the `K`-iterate ideal is
literally the extension of the polynomial-level one (because iterates commute with the coefficient
map), and `IsLocalization.mem_map_algebraMap_iff` produces the denominator.  The two-block statement
is then recovered by pulling the membership back through the splitting, which is legitimate exactly
because the splitting is differential.

With this, step 1 of the `(RITT-DVD)` plan is DONE: the corpus's `exists_mappedCrossRelation_saturation`
can be turned into `left(d) * M * D in differentialPolynomialFamilyIterateIdeal C`, and
`differentialPolynomialFamilyIterateIdeal_le_of_dvd` hands it to every irreducible factor of `C`.

## Lean progress — the saturation certificate is now a TWO-BLOCK statement

`GaloisForLFunctions/HTGeometry/TwoBlockCrossSaturation.lean` (wired, axiom-clean):

    exists_twoBlock_crossDifference_saturation
        some two-block multiple of the cross-difference of two coefficients of the cleared
        characteristic lies in the differential ideal generated by that characteristic
    exists_twoBlock_crossDifference_saturation_of_dvd
        hence in the differential ideal generated by ANY divisor of it -- in particular by each
        irreducible factor

Steps 1 and 2 of the `(RITT-DVD)` plan are therefore complete.  The proof assembles four corpus
facts with this session's descent: the corpus's saturation in `K{Y}`; `map_coefficientCrossRelation`
and `clearing`, which say that both the cross-difference and the characteristic map to their `K{Y}`
counterparts up to the SAME clearing unit; `differentialPolynomialIterateIdeal_C_mul_unit`, which
makes the two differential ideals literally equal; and `exists_mvPolynomial_fraction_clear` to clear
the denominators of the initial/separant multiplier before descending.

What remains for `(3)` is only the factorwise use of the bridge:

    for each irreducible factor A of the cleared characteristic, apply
    irreducible_dvd_of_order_le_of_mul_mem_iterateIdeal in the U-view

whose order hypothesis `ord_U D <= ord_U A` holds for every factor of maximal left-block order, and
for the others needs either left-block uniformity or the peeling.  After that,
`Squarefree.dvd_of_forall_irreducible_factor_dvd` recombines to `C | D`,
`degreeOf_inl_eq_degreeOf_inr_of_dvd_crossDifference` converts it into the rank bounds, and
`eq_differentialAdjoin_of_ratio_rank_le` closes the card's `(3)`.

## Lean progress — the factor step is assembled

Added to `TwoBlockCrossSaturation.lean` (wired, axiom-clean):

    differentialPolynomialTwoBlockSwap_swap   the block swap is an involution
    dvd_of_saturation_bridge                  THE FACTOR STEP: a two-block certificate
                                                `M * Q in [A]`, read in the SWAPPED view, yields
                                                `A | Q` in the two-block ring

and to `JetFractionDerivationTransport.lean`:

    map_equiv_mem_iterateIdeal_of_mem_familyIterateIdeal        ascent of a certificate
    map_equiv_swap_mem_iterateIdeal_of_mem_familyIterateIdeal   the same in the swapped view

`dvd_of_saturation_bridge` is the entire Ritt descent step in one theorem: ascend the certificate to
the jet fraction field with the left block as the polynomial variables, cancel the multiplier with
the corpus's bridge, and contract the resulting divisibility back to the two-block ring by
primitivity (`MvPolynomialPrimitive.dvd_of_fraction_map_dvd`), then undo the swap.

Its hypotheses are exactly the remaining checklist for `(3)`, and nothing else:

    * the swapped factor is primitive and nonzero;
    * its image over the jet fraction field is irreducible with a nonempty variable set;
    * the multiplier has swapped-view order at most the factor's, and is not divisible by it;
    * the cross-difference has swapped-view order at most the factor's.

The last is where left-block uniformity or the peeling enters; the multiplier condition is what the
Bezout lemma `exists_mvPolynomial_bezout_clear_away_from_variable` was built for; irreducibility of
the image is Gauss for the primitive factor.

### The multiplier's left-block order is bounded -- so the top-order factors are already fine

Checking the remaining checklist item that looked most dangerous: the multiplier in the two-block
certificate is `left(d) * Z`, where `Z` clears the denominators of `I^a S^b` and `I, S` are the
initial and separant of the characteristic.  Their coefficients are polynomial expressions in the
coefficients of `P`, so as elements of `F<y>` they are rational functions of the SAME jets as those
coefficients: the left-block ORDER of the cleared multiplier is at most `ord_U C`, even though its
degree grows.  Hence for every irreducible factor `A` with `ord_U A = ord_U C` -- the top-order
factors, which always exist -- the hypothesis `ord_U M <= ord_U A` of `dvd_of_saturation_bridge`
holds automatically, exactly like `ord_U D <= ord_U A`.

So the ONLY factors that resist are those of strictly smaller left-block order, and the whole of
`(3)` now rests on the single question already isolated: do such factors exist?  Equivalently, do all
irreducible factors of the cleared two-block characteristic share their left-block order?  A negative
answer forces Ritt's peeling (for which the general component of an irreducible, available through
`differentialPolynomialGeneralComponentJets`, supplies the primality); a positive answer closes the
card with the machinery already built.

Note also what the Bezout lemma can and cannot do here: it lowers the multiplier's degree at ONE jet
that the divisor itself involves, which is what makes the divisor fail to divide the Bezout output.
It cannot remove jets ABOVE the divisor's order, since the divisor does not involve those.  This is
why the multiplier bound above -- not Bezout -- is what makes the top-order factors work.

### The card's open core, in one line

    [OPEN CORE]  Every irreducible factor of the primitive two-block clearing of a minimal-rank
                 characteristic has left-block order equal to its right-block order (= m).

Everything else in `(3)` is formal.  Three remarks that fix its status:

* It is NOT a consequence of primitivity plus diagonal vanishing.  `A = (Y_0 - U_0) + U_5*(Y_1 - U_1)`
  is irreducible, vanishes on the diagonal, and has `ord_Y = 1 < 5 = ord_U`.  Such an `A` can only
  fail to be a factor of a genuine characteristic's clearing, and the reason must be minimality.
* Equation (78) already gives the right-block half: every irreducible factor has the FULL right-block
  support, hence right-block order exactly `m`.  So the open core is exactly the left-block analogue
  of equation (78).
* If it holds, `dvd_of_saturation_bridge` applies to every factor (its multiplier and cross-difference
  hypotheses hold whenever `ord_U A = ord_U C`, as shown above), `Squarefree.dvd_of_forall_irreducible_factor_dvd`
  recombines, and the card closes.  If it fails, the peeling is required, and its missing ingredient is
  the primality of the general component -- available through `differentialPolynomialGeneralComponentJets`,
  whose evaluation lands in a field.

### The open core, reduced to a statement of the same type as what is already proved

Equation (78) in the corpus is `irreducible_map_factor_vars_eq`: an irreducible factor after a
SCALAR EXTENSION of the coefficient field has exactly the variable set of the original.  The corpus
applies it to `G -> K = Frac F{U}`, which is why every irreducible factor of the cleared
characteristic has the full RIGHT-block support.

To get the left-block half by the same lemma, one needs the swapped picture to be of the same shape:

    C^swap(y, Y) = C(Y, y)  is a relation of `y` (it vanishes on the diagonal), its coefficient
    ratios generate a field `G'`, and one needs it to be of MINIMAL rank over `G'`.

Given that, the corpus's own construction produces an irreducible characteristic over `G'` whose
clearing is `C^swap` up to units, equation (78) applies on that side, and every irreducible factor of
`C` has the full LEFT-block support -- in particular the same left-block order.  That is the open
core, and this is the cheapest known route to it: it needs no new machinery, only the statement

    [OPEN CORE, restated]  the swapped relation `C(Y, y)` has minimal rank over the field generated
                           by the ratios of the left-block coefficients of `C`.

Note that the reciprocity theorem proved in this card already gives half of the symmetry: whichever
block one reads `C` in, the field generated by the coefficient ratios is exactly the field over which
the corresponding relation lives.  What is missing is that minimality survives the swap.

## Lean progress — differentiation raises the jet order by exactly one

`GaloisForLFunctions/HTGeometry/JetOrderDerivative.lean` (wired, axiom-clean):

    pd_eq_zero_of_ordJet_lt                  above its order every partial derivative vanishes
    exists_pd_ne_zero_of_ordJet_ne_zero      at its order some partial derivative does not
    ordJet_deriv_le                          the derivative has order at most one more
    ordJet_deriv_eq                          and exactly one more, for an element of positive order
    ordJet_lt_ordJet_deriv                   so differentiating strictly raises the order

The corpus already owned the commutator `pd_deriv_succ`:
`pd (j,m+1) (u') = (pd (j,m+1) u)' + pd (j,m) u`, and the order characterization
(`ordJet_le_iff`, `mem_jetLevel_iff`).  What was missing was the sharp consequence, which is the
engine of every order bound for differential generators: since the fresh partial derivative of `u'`
is the previous partial derivative of `u`, it cannot vanish at the order.

This is the formal core of the literature's order bound (D'Alfonso-Jeronimo-Solerno, Prop. 5:
`ord(v) <= min_j ord(v_j)` for a Luroth generator).  In the card's terms it supplies half of the
open core: every coefficient ratio of the characteristic has jet order at least `m`.  The other half
-- at most `m` -- is what remains.

Added to the same module:

    ordJet_iterate            ordJet (y^(k) of u) = ordJet u + k
    ordJet_iterate_strictMono the jets of an element of positive order have strictly increasing order

`ordJet_iterate` is the exact statement used informally three times in this card to destroy candidate
counterexamples ("a differential automorphism with `sigma(y) = y''` would force `sigma(y'') = y^(4)`,
not `y`"), and it is the induction step of the literature's order bound.  It is now a theorem.

### Correction to the open core: uniformity is probably FALSE, and the real gap is a known theorem

Re-reading the peeling in the partial-differential paper (arXiv:2210.05469, Theorem 3.1) settles the
status of the "left-block uniformity" question posed above.  The experts organise the proof to handle
factors with DIFFERENT top left-block derivatives -- they enumerate
`theta_1(u_{e_1}) < ... < theta_r(u_{e_r})` and peel by decreasing `theta_i` -- so non-uniformity is
expected, not excluded.  The card should stop trying to prove uniformity.

What their peeling actually uses is a two-ranking argument about ONE ideal:

* `B_j not in sat(B_1)` is justified in the `z`-ranking, where ALL factors share the leader by
  equation (78), so a factor in the component would have to be divisible by `B_1` -- impossible for
  distinct irreducibles;
* the divisibility `B_1 | D` is concluded in the reversed ranking, where the order bound on the
  cross-difference holds.

Both statements are about the same prime `sat(B_1)`.  So the missing ingredient is not a new theorem
about characteristics but the classical fact that

    an irreducible differential polynomial's general component is a characteristic-set ideal in
    EVERY ranking (Wu-Ritt; [18, Lemma 2.6] of that paper),

i.e. the component is ranking-independent.  The corpus is unusually well placed for it: its
`differentialPolynomialGeneralComponentJets` evaluation lands in a FIELD, so the component is
automatically prime, and the corpus's bridge already proves the `Y`-ranking half
("in the component and of order at most `ord A` implies divisible by `A`").  What must be added is the
same statement in the `U`-ranking for the same ideal.

This is a reclassification, not a retreat: the remaining work on `(3)` is the formalisation of a known
theorem with the corpus's own generic-point machinery, not the solution of an open problem.

## Lean progress — the general component as an ideal

`GaloisForLFunctions/HTGeometry/GeneralComponentIdeal.lean` (wired, axiom-clean):

    generalComponentPoint                       the LIMIT of the corpus's general-component jets
    generalComponentJets_stabilizes             each coordinate is eventually constant, because step
                                                  `n` only updates the jet of order `ord A + n + 1`
    generalComponentPoint_apply_of_le_order      below `ord A` the limit is the base point
    eval₂_generalComponentPoint_eq               evaluation at the limit equals evaluation at any
                                                  sufficiently late stage
    generalComponent                             the vanishing ideal of the limit point
    generalComponent_isPrime                     PRIME, being a kernel into a field
    iterateIdeal_le_generalComponent             the differential ideal sits inside it
    dvd_of_mem_generalComponent_of_order_le      a member of low order is a multiple of `A`

The corpus's bridge built these objects inside one proof and threw them away; this module makes the
component a first-class ideal.  The novelty over the corpus is the LIMIT point: the corpus only had
the truncated jets `differentialPolynomialGeneralComponentJets f A x0 N`, which depend on `N`, so
there was no single ideal to speak of.  The stabilization lemma removes the truncation.

That is the first half of the ranking-independence the peeling needs: primality of the component is
now available (`Q1*Q2` in the component gives `Q1` or `Q2` in it), and so is the low-order converse.
What remains is to see the SAME ideal from the swapped block.

Added to the same module, completing the peeling toolkit in one ranking:

    mem_generalComponent_of_mul_mem            a factor outside the component can be CANCELLED from
                                                 a product lying in it
    not_mem_generalComponent_of_irreducible    a distinct irreducible of no larger order is outside
                                                 the component

These are the two steps Ritt's peeling performs at each stage: the already-divided factors are
distinct irreducibles of the same order (equation (78)), hence outside the component of the current
factor, hence cancellable from the certificate.  Both are now theorems.

The peeling is therefore complete WITHIN ONE RANKING.  What is still missing is only the passage
between the two rankings: the non-membership steps have uniform orders in the `Y`-view, while the
final divisibility needs the `U`-view bound.  In ideal terms the remaining statement is

    Q in generalComponent(A) with ord_U Q <= ord_U A  implies  A | Q,

for the component built in the `Y`-view -- Ritt's ranking-independence, now expressible because the
component is a single ideal rather than a truncation-dependent construction.

## Lean progress — RANKING INDEPENDENCE, via minimality of the general component

Added to `GeneralComponentIdeal.lean` (wired, axiom-clean):

    not_rank_lt_of_dvd                        a nonzero multiple of `A` has no smaller Ritt rank
    generalComponent_le_of_iterateIdeal_le    THE GENERAL COMPONENT IS THE SMALLEST prime differential
                                                ideal containing `A` and avoiding its initial and
                                                separant

This is the theorem that settles the two-ranking problem, and its proof needs nothing new: Ritt
reduction (`characteristicPseudoReduction`, already in the corpus for an arbitrary nonconstant
divisor) sends a member `Q` of the component to a remainder of strictly smaller rank; the remainder
is still in the component, so `dvd_of_mem_generalComponent_of_order_le` makes it a multiple of `A`,
which `not_rank_lt_of_dvd` forbids unless it vanishes; hence `I^a S^b Q` lies in the differential
ideal, and any prime containing that ideal and avoiding `I` and `S` absorbs `Q`.

**Consequence -- ranking independence.**  Let `P_Y` be the component built with the right block as
polynomial variables and `P_U` the one built with the left block.  Each contains the differential
ideal of `A` and each avoids the OTHER's initial and separant, because divisibility by `A` would
raise the corresponding order or degree past the initial's and separant's (the initial has strictly
smaller order in its own ranking, the separant strictly smaller leader degree).  Minimality applied
twice gives `P_Y <= P_U <= P_Y`, i.e. the two rankings define the SAME prime.

That is exactly the missing passage in Ritt's peeling: the non-membership and cancellation steps may
be run in the `Y`-ranking, where equation (78) makes all factors have the same order, and the final
divisibility in the `U`-ranking, where the cross-difference's order is bounded -- both about one
ideal.

Added, completing the layer:

    initial_not_mem_generalComponent    the initial is outside the component
    separant_not_mem_generalComponent   the separant is outside the component
    generalComponent_eq                 RANKING INDEPENDENCE: two general components of the same
                                          polynomial, built from ANY two generic base points over any
                                          two fields, coincide

`generalComponent_eq` is the theorem the peeling was waiting for, and it is now unconditional: the
non-membership of the initial and separant is automatic (divisibility by `A` would raise the order or
the leader degree past them), so minimality applies in both directions with no side conditions beyond
the two base points being generic.

The differential Luroth chain is now complete except for instantiating this layer on the two-block
characteristic: build the two components (right block as variables, then left block), transport the
certificate between them with the descent and ascent lemmas already proved, and run the peeling with
`mem_generalComponent_of_mul_mem` and `not_mem_generalComponent_of_irreducible`.

## Lean progress — the bridge, freed of its multiplier hypothesis

Added to `GeneralComponentIdeal.lean` (wired, axiom-clean):

    dvd_of_mul_mem_iterateIdeal_of_notMem_generalComponent
        a certificate `M * Q in [A]` with `M` OUTSIDE the general component gives `A | Q`,
        with NO constraint on the multiplier's order
    mem_generalComponent_of_mul_mem_of_notMem, mul_notMem_generalComponent
        cancellation and the product rule for staying outside the component

This supersedes the corpus's `irreducible_dvd_of_order_le_of_mul_mem_iterateIdeal`, whose multiplier
had to satisfy `ord M <= ord A` and `not A | M`.  With the component available as a prime ideal the
multiplier's order is irrelevant: it only has to avoid the component, and primality does the
cancellation.  That removes the multiplier-order problem from this card entirely -- it had been one of
the two obstructions to the factorwise argument, and it needed the Bezout lemma to work around.

**The peeling now closes with the tools in the tree.**  For an irreducible factor `A` of the cleared
characteristic:

* `D` lies in the component of `A` -- from the two-block certificate plus the multiplier's avoidance,
  which is `initial_not_mem_generalComponent` / `separant_not_mem_generalComponent` together with
  equation (78) (each factor has right-block order `m`, the initial has smaller order, the separant
  smaller leader degree);
* the already-divided factors are distinct irreducibles of the SAME right-block order, hence outside
  the component (`not_mem_generalComponent_of_irreducible`), hence cancellable
  (`mem_generalComponent_of_mul_mem_of_notMem`), so the running quotient stays in the component;
* the quotient's left-block order drops below the current factor's, because the factors of a given
  top jet absorb all of `C`'s degree there;
* `generalComponent_eq` lets the final divisibility be read in the left-block ranking, where that
  order bound holds.

What remains is bookkeeping: the degree accounting for the quotient, and the induction over the
finitely many left-block orders.

## Lean progress — the peeling's degree accounting

Added to `CrossDifferenceRigidity.lean` (wired, axiom-clean):

    degreeOf_quotient_eq_zero       once the factors carrying a variable are divided out of `D`, the
                                      quotient no longer involves that variable
    degreeOf_inl_quotient_eq_zero   the left-block form: the quotient's jets stay below the level
                                      already peeled

This is the accounting that makes the peeling terminate: at each stage the divided factors already
carry the whole degree of `C` at the current top jet, and `D`'s degree there is dominated by `C`'s, so
the running quotient loses that jet.  With it, the induction over the finitely many left-block orders
has its decreasing measure.

Every ingredient of `(3)` is now a proved theorem; what is left is to write the induction that
threads them.

## Lean progress — the peeling step, as one theorem

Added to `GeneralComponentIdeal.lean` (wired, axiom-clean):

    mul_dvd_of_peeling_step
        if the processed factors multiply to `T` with `D = T * L`, `T` avoids the component of the
        next factor `A`, `D` lies in it, and the running quotient has order at most `A`'s, then
        `T * A` divides `D`

This is the inductive step of Ritt's peeling in the exact form the induction consumes: it both
divides one more factor out and reproduces the invariant.  Its three hypotheses are supplied by
theorems already proved -- `mul_notMem_generalComponent` with
`not_mem_generalComponent_of_irreducible` for `T`, the certificate plus
`dvd_of_mul_mem_iterateIdeal_of_notMem_generalComponent` for `D`, and
`degreeOf_inl_quotient_eq_zero` for the order of the quotient.

The only thing still to write is the loop: an induction over the finitely many left-block orders that
applies this step once per level, with the factorization of `C` as a multiset.  There is no
mathematics left in it.

## Lean progress — the peeling LOOP

Added to `GeneralComponentIdeal.lean` (wired, axiom-clean):

    dvd_of_peeling_loop
        in any unique factorization domain: if from every partial product `T` of factors of `C`
        that already divides `D` one can split off one more non-unit factor and keep dividing `D`,
        then `C | D`

The induction is on the number of irreducible factors still to process, which strictly drops at each
step because the factor split off is a non-unit.  This is the generic loop that Ritt's peeling runs,
stated so that the application only has to supply the STEP -- which is
`mul_dvd_of_peeling_step`, already proved.

With the loop and the step both in place, `(RITT-DVD)` reduces to instantiating the step's three
hypotheses at each stage, all of which are theorems:

    T not in the component of the next factor        mul_notMem_generalComponent +
                                                       not_mem_generalComponent_of_irreducible
    D in the component of the next factor            exists_twoBlock_crossDifference_saturation_of_dvd +
                                                       dvd_of_mul_mem_iterateIdeal_of_notMem_generalComponent
    the running quotient's order is small enough     degreeOf_inl_quotient_eq_zero + generalComponent_eq

## Lean progress — Ritt's peeling, assembled

`dvd_of_peeling_prime` (in `GeneralComponentIdeal.lean`, wired, axiom-clean) is the whole peeling in
one theorem:

    at every stage -- a partial product `T` with `C = T*S` and `D = T*L` -- name the next factor `A`
    of `S` together with a PRIME ideal that detects divisibility by `A` in low order, avoids `T`,
    contains `D`, and bounds the quotient's order; then `C | D`.

Stating the component abstractly as "a prime with the low-order divisibility property" removes the
last structural obstacle: the general component of each factor lives in a DIFFERENT residue field, so
a formulation naming that field could not quantify over the factors.  With the prime abstracted, one
theorem covers all stages.

`(RITT-DVD)` is now exactly: produce, for each factor of the cleared characteristic, the prime and
the four facts.  All four are proved theorems:

    the prime and its low-order divisibility      generalComponent, generalComponent_isPrime,
                                                    dvd_of_mem_generalComponent_of_order_le
    it avoids the partial product                 not_mem_generalComponent_of_irreducible,
                                                    mul_notMem_generalComponent
    it contains the cross-difference              exists_twoBlock_crossDifference_saturation_of_dvd,
                                                    dvd_of_mul_mem_iterateIdeal_of_notMem_generalComponent
    the quotient's order is bounded               degreeOf_inl_quotient_eq_zero, generalComponent_eq

## Lean progress — the generic point, extracted

`exists_generic_point_of_irreducible` (in `GeneralComponentIdeal.lean`, wired, axiom-clean):

    for an irreducible differential polynomial there is a field, a coefficient map and a point at
    which a polynomial vanishes EXACTLY when the irreducible divides it

The corpus built this inside the bridge's proof and discarded it; extracting it as an existence
statement is what makes the component instantiable, and phrasing it existentially (rather than as a
definition) sidesteps the instance problem -- the residue field's `IsDomain` structure depends on the
irreducibility hypothesis, so it cannot be attached to a definition.

With this, the concrete general component of any irreducible factor is available: feed the point to
`generalComponent`, and `generalComponent_isPrime`, `iterateIdeal_le_generalComponent`,
`dvd_of_mem_generalComponent_of_order_le`, `initial_not_mem_generalComponent`,
`separant_not_mem_generalComponent` and `not_mem_generalComponent_of_irreducible` all apply.  That is
every hypothesis of `dvd_of_peeling_prime` except the two-block bookkeeping.

## Lean progress — the per-factor package

`exists_component_prime_of_irreducible` (in `GeneralComponentIdeal.lean`, wired, axiom-clean):

    for an irreducible nonconstant differential polynomial there is a PRIME ideal which
      * contains its differential ideal,
      * detects divisibility by it in low order,
      * avoids its initial, its separant, and every non-associate irreducible of no larger order.

These are exactly the data `dvd_of_peeling_prime` consumes at each stage, so the peeling now runs on
a single existence statement per factor.  Nothing about generic points, residue fields or truncated
jet constructions is visible any more: the general-component layer is closed off behind this
interface.

State of `(3)`: the only remaining work is the two-block instantiation -- choosing the coefficients
`H, K` of the cleared characteristic, matching the left-block order of the running quotient against
each factor's, and feeding the package to the peeling.  Every mathematical ingredient is proved.

### The instantiation, analysed to the last lemma

Running the peeling on the two-block characteristic needs the avoidance facts in the `Y`-view and the
final divisibility in the `U`-view.  Checking each avoidance in the `Y`-view:

    the certificate's initial I      ord_Y I < m = ord_Y A, so `A | I` is impossible          OK
    the certificate's separant S     same order, strictly smaller leader degree                OK
    the clearing denominator d       d lies in F{U}, so ord_Y d = 0 < m                        OK
    the processed factors T          distinct irreducibles of the SAME Y-order (eq. 78)        OK

So `D` lies in the `Y`-view component of every factor, `T` avoids it, and the running quotient stays
in it.  Only the last step -- from `L` in the component and `ord_U L <= ord_U A` to `A | L` -- needs
the `U`-view, i.e. the two-block ranking bridge.

For that bridge the scalar minimality theorem transports, with A's OWN initial and separant as
multipliers (not the characteristic's):

    I_A : ord_U I_A <= ord_U A and ord_Y I_A < ord_Y A, so it avoids the U-view component
    S_A : ord_U S_A <= ord_U A and strictly smaller Y-leader degree, likewise

and the only remaining unknown is the clearing denominator `d'` of the transported certificate.  It
is NOT arbitrary: pseudo-division divides only by the initial, so `d'` is a power of `I_A`, whose
`U`-order is at most `ord_U A` -- hence it avoids the `U`-view component too, and the bridge closes.

    [LAST LEMMA]  the descent `exists_clear_mem_familyIterateIdeal_of_map_mem` must be refined to
                  return a denominator that divides a power of the initial, instead of an arbitrary
                  nonzero element of F{U}.

That is the single remaining technical requirement for `(3)`.  It is a statement about the corpus's
pseudo-division, not about differential algebra: the certificate produced by
`characteristicPseudoReduction` already has its coefficients in the ring localized only at the
initial.

## Lean progress — pseudo-division over a commutative ring (the last lemma's core)

`GaloisForLFunctions/HTGeometry/PseudoDivisionCommRing.lean` (wired, axiom-clean):

    exists_pseudoDivision                univariate pseudo-division over an arbitrary CommRing:
                                           `lc(q)^e * p = q*a + b` with `deg b < deg q`
    exists_mvPolynomial_pseudoDivision   the same at a distinguished variable of a multivariable
                                           ring, with the INITIAL at that variable as multiplier

mathlib has division by a monic polynomial and division over a field, but not pseudo-division over a
ring; the corpus's own pseudo-division also went through a field.  That is why every certificate so
far arrived with an uncontrolled denominator.

This version introduces NO denominators: the multiplier is explicitly a power of the initial.  Applied
with the coefficient ring `F{U}` (a commutative ring, not a field) it gives a two-block reduction
whose multiplier is a power of `A`'s initial -- exactly the `[LAST LEMMA]` recorded above, and with it
the two-block ranking bridge closes, since the initial's left-block order is at most `A`'s.

The remaining work on `(3)` is to iterate this pseudo-division into a full Ritt reduction in the
two-block ring (the ordinary step is now available; the higher-jet step reduces derivatives of `A` the
same way) and then feed `dvd_of_peeling_prime`.
