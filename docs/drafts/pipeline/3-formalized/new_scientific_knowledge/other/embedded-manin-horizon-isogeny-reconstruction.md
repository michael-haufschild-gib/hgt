# The embedded Manin horizon reconstructs a simple varying abelian bulk up to isogeny

- **ID:** embedded-manin-horizon-isogeny-reconstruction
- **Stage:** 3-formalized
- **Type:** THEOREM (paper)
- **Source:** abelian-multiplication-tail-manin-horizon + Manin-kernel rigidity
- **Statement:** The translation stabilizer of an embedded abelian multiplication tail is
  exactly the Manin kernel; for simple abelian varieties not descending to the constants, the
  nonorthogonality class of this horizon symmetry determines the bulk isogeny class.

## Goal

Recover precisely which global information is lost by the abstract no-hair theorem and which is
retained when the tail is kept together with its embedding and ambient translation action.

## Gates

- [x] 0 -> 1 in-progress: embedded stabilizer and reconstruction equivalence isolated
- [x] 1 -> 2 fully-proven: complete proof, `[PROVED HERE]`, Manin-kernel rigidity imported
- [x] 2 -> 3 formalized: Kolchin closure, the `D`-group horizon stabilizer, the concrete
  nonorthogonality relation and its elementary half, Theorem A, Theorem B and the dichotomy
- [ ] 3 -> 4 publication-ready: expert novelty audit and standalone synthesis

## Setup

Let `(K,delta)` be differentially closed of characteristic zero, let `A/K` be an abelian variety,
let `m` satisfy `|m|>1`, and let

`T_A=Tail_m(A)=K<mu_A(a)> subset K<a>`

be the embedded multiplication tail of a differential-generic point `a`.

Define its differential translation stabilizer by

`Stab_A(T_A) = {h in A : f(a+h)=f(a) generically for every f in T_A}.`  (1)

The definition uses the ambient group law and the embedding of `T_A`; it is not an invariant of
the abstract differential field alone.

## Theorem A: exact horizon stabilizer

**[PROVED HERE]**

`Stab_A(T_A)=A^sharp.`                                              (2)

Thus the Manin kernel has a purely asymptotic-dynamical characterization: it is the complete
translation symmetry of the field visible through every depth of one multiplication tower.
Equation (2) is independent of the choice of `m` with `|m|>1`.

### Proof

The Manin-horizon theorem gives `T_A=K<mu_A(a)>` and `ker(mu_A)=A^sharp`.

If `h in A^sharp`, then

`mu_A(a+h)=mu_A(a)+mu_A(h)=mu_A(a)`,

so every element of `T_A` is invariant and `h` belongs to (1).

Conversely, the coordinate functions of `mu_A(a)` and all their derivatives lie in `T_A`.
If `h` stabilizes every tail element, then `mu_A(a+h)=mu_A(a)`.  Since `mu_A` is a group
homomorphism, `mu_A(h)=0`, hence `h in A^sharp`.  This proves (2).

## Theorem B: horizon Torelli theorem up to isogeny

**[PROVED HERE]** Let `A` and `B` be simple abelian varieties over the universal differential
field, neither descending to the constant field.  Then

`Stab_A(T_A)` and `Stab_B(T_B)` are nonorthogonal

if and only if

`A` and `B` are isogenous.                                          (3)

Consequently, the nonorthogonality class of the embedded horizon symmetry reconstructs the
isogeny class of a simple varying abelian bulk.

### Proof

By Theorem A, the two stabilizers are `A^sharp` and `B^sharp`.  For simple abelian varieties not
descending to constants, Manin-kernel rigidity states

`A^sharp nonorthogonal to B^sharp iff A isogenous to B`.

Substitution gives (3).  A published statement of this rigidity appears as Fact 5.6 in
Casale--Freitag--Nagloo: <https://arxiv.org/abs/1811.06583>.

## Corollary: exact abstract/embedded dichotomy

For fixed dimension and multiplier:

- the abstract tail dynamical fields of `A` and `B` are always isomorphic;
- their embedded horizon symmetries are nonorthogonal exactly when the simple varying bulks are
  isogenous.

The boundary field has no hair, but the way it sits in the ambient differential group has enough
hair to recover the bulk up to isogeny.

## Physical/topological reading

This is interpretation only.  The horizon algebra by itself is universal.  Its stabilizer inside
the ambient translation geometry is the differential fundamental symmetry `A^sharp`.  For a
simple varying bulk, the interaction class of that symmetry is a complete isogeny invariant.

This gives a precise version of holographic reconstruction with a sharp qualification: intrinsic
boundary observables do not reconstruct the bulk, but boundary observables plus their ambient
symmetry embedding do so up to isogeny.

## Novelty and significance gate

The inputs `ker(mu_A)=A^sharp` and Manin-kernel nonorthogonality/isogeny rigidity are classical.
The new theorem surface is the dynamical characterization (2) and its combination with rigidity
to obtain the embedded-horizon reconstruction criterion (3).  Targeted searches found no such
stable-tail formulation.  Novelty remains provisional pending expert review.

This supplies a genuine converse within the abelian sector and materially strengthens the HT
horizon theory.  It still does **not** clear the Fields-Medal gate because the decisive rigidity
input is imported and the new deduction is short.

## Lean status

`DeckClosureReconstruction.lean` formalizes the exact ordinary-Galois analogue: a stable core
recovers the topological closure of its total deck group as its fixing subgroup.  The present
Kolchin/Manin-kernel theorem remains paper-level; Krull closure and Kolchin closure are not
identified or conflated.

## RH impact audit

The theorem identifies the minimum extra structure an abelian-tail RH strategy must retain:
the embedded tail and its stabilizer, not merely the abstract boundary field.  Such data can
recover an isogeny class, but no known argument connects that class to zeta-zero location or RH
positivity.  The result sharpens architecture without proving an RH statement.

## Log

- 2026-07-15 -- [PROVED HERE] Tail stabilizer identified with the Manin kernel; simple
  nonconstant embedded horizons shown to reconstruct bulk isogeny class through
  nonorthogonality.

## Lean progress — the tail stabilizer is Kolchin closed, and contains the closure

`GaloisForLFunctions.HTGeometry.MultiplicationTailFixedField` proves the structural half of
"the translation stabilizer of an embedded multiplication tail is exactly the Manin kernel",
unconditionally and axiom-clean (`[propext, Classical.choice, Quot.sound]`):

```text
translationStabilizerSet translation E     the labels whose translation fixes E pointwise
isKolchinClosedOver_translationStabilizerSet
    the stabilizer of any set of field elements is Kolchin closed
kolchinClosureOver_subset_translationStabilizerSet
    the Kolchin closure of a label set stabilizes its own fixed field
kolchinClosureOver_iUnion_subset_translationStabilizerSet_tail
    the Kolchin closure of all the tower labels stabilizes the tail
translationStabilizerSet_tail_eq_kolchinClosureOver
    with the reverse inclusion, the tail stabilizer is exactly that closure
```

The first is the load-bearing one and is not formal bookkeeping: the stabilizer is an intersection
of individual element stabilizers, and Kolchin-closed sets are closed under arbitrary intersections
(`DifferentialKolchinClosure.isKolchinClosedOver_sInter`).  It is what makes the tail stabilizer a
differential algebraic subgroup rather than merely a subgroup, which is the whole point of the
identification with `A^♯`.

Combined with the tail identity `⋂_n L^(S_n) = L^(closure ⋃_n S_n)` of the same module, the only
missing half is the reverse inclusion — that nothing outside the closure stabilizes the tail — which
is the differential Galois correspondence for the multiplication tower.  The card's own Lean status
notes that `DeckClosureReconstruction.lean` formalizes the ordinary-Galois analogue; the Kolchin
analogue is the remaining input, together with the identification of the closure with the Manin
kernel.

## Lean progress — Theorem A from the `D`-group structure, with no additivity hypothesis

`GaloisForLFunctions.HTGeometry.DGroupHorizonStabilizer` proves Theorem A inside the corpus's
commutative-`D`-group framework, unconditionally and axiom-clean:

```text
dGroupSharp P                                     the points with vanishing logarithmic derivative
differentialTranslationStabilizer_ell_eq_dGroupSharp
    for a translation action by differential automorphisms which moves logarithmic coordinates
    along the group law, the stabilizer of the differential field generated by the logarithmic
    coordinates of a point is exactly the sharp subgroup
```

The improvement over `DifferentialHorizonInterface.differentialTranslationStabilizer_differentialAdjoin_eq_kernel`
is that the additivity of the displacement is no longer a hypothesis: it is
`DGroupPresentation.ell_mul`, the statement that the logarithmic derivative of a commutative
algebraic `D`-group is a group homomorphism.  So `Stab_A(T_A) = A^♯` holds by the `D`-group
structure alone, which is exactly the content of the card's Theorem A once `A^♯` is read as the
kernel of the Manin homomorphism.

Two inputs still separate this from the card's own statement: the construction of the Manin
homomorphism of an abelian variety over a differential field as a `DGroupPresentation` (so that
`dGroupSharp` really is the Manin kernel), and — for Theorem B — Manin-kernel rigidity, which rests
on Hrushovski's dichotomy and has no counterpart anywhere in the tree or in mathlib.

## Lean progress — Theorem B, the nonorthogonality relation, and the dichotomy

`GaloisForLFunctions.HTGeometry.ManinHorizonIsogenyReconstruction` completes the card.  The
previous section left `Nonorthogonal` as an abstract parameter of
`DifferentialHorizonInterface.embeddedHorizon_nonorthogonal_iff_isogenous`, so Theorem B was a
substitution into an empty predicate.  It is now a concrete relation with proved structure.

```text
Nonorthogonal S S'      a subgroup of the product lying over both S and S', projecting onto both,
                        with finite kernel in each direction -- an isogeny correspondence
Nonorthogonal.symm      the relation is symmetric (transpose the correspondence)
nonorthogonal_self      it is reflexive on a subgroup (the diagonal)
nonorthogonal_of_monoidHom
                        a homomorphism carrying S into S', onto S', with finite kernel on S,
                        produces a correspondence
DGroupHom P Q           a homomorphism of commutative D-groups: a group homomorphism whose
                        logarithmic coordinates transform by a matrix
DGroupHom.map_dGroupSharp
                        a D-group homomorphism carries sharp points to sharp points
nonorthogonal_dGroupSharp_of_dGroupHom
                        hence an isogeny of D-groups makes the two Manin kernels nonorthogonal
```

The last of these is the *elementary half of Manin-kernel rigidity*, and it is Lean-proved rather
than imported: if `phi` is a `D`-group homomorphism then `ell_Q(phi g) = M . ell_P(g)`, so
`ell_P(g) = 0` forces `ell_Q(phi g) = 0`, and the graph of `phi` restricted to `A^sharp` is the
required correspondence.  Only the converse — nonorthogonality forces isogeny — rests on
Hrushovski's dichotomy, and that is exactly the input the card names as imported.

**Theorem A, in the card's own form.**

```text
multiplicationTail_translationStabilizer_eq_dGroupSharp
    Stab(tail) = dGroupSharp P   for any tail equal to K<ell a>
```

with `differentialTranslationStabilizer_ell_eq_dGroupSharp` supplying the content: additivity of
the displacement is `DGroupPresentation.ell_mul`, the statement that the logarithmic derivative of
a commutative algebraic `D`-group is a group homomorphism, so `(2)` holds by the `D`-group
structure alone.

**Theorem B.**

```text
embeddedManinHorizon_nonorthogonal_iff_isogenous
    Stab_A(T_A) nonorthogonal to Stab_B(T_B)  <->  A isogenous to B
```

from Theorem A applied to each side and the rigidity input carried as the named hypothesis
`hrigidity`, precisely as the paper proof carries Fact 5.6 of Casale--Freitag--Nagloo.

**The corollary, both halves at once.**

```text
manin_horizon_abstract_embedded_dichotomy
    the abstract tail fields are canonically isomorphic  AND
    the embedded horizon symmetries are nonorthogonal exactly when the bulks are isogenous
```

The first component is the no-hair theorem: `differentialQuotientFreeAlgEquiv` builds the
canonical differential isomorphism between two horizon quotients of the same rank with
differentially independent Manin coordinates.  The second is Theorem B.  Together they are the
card's "exact abstract/embedded dichotomy": the boundary field has no hair, the way it sits in the
ambient translation geometry has enough hair to recover the bulk up to isogeny.

**Classical inputs, carried as explicit hypotheses and never as axioms**, following the parent card
`abelian-multiplication-tail-manin-horizon`:

1. the translation action moves logarithmic coordinates along the group law: `hequiv`, `hA`, `hB`;
2. the tail is the differential field generated by the Manin coordinates: `htail`, `htailA`,
   `htailB` (this is the parent card's Theorem A, itself Lean-proved there from its own named
   inputs);
3. the Manin coordinates of a differential-generic point are differentially independent: `hfreeA`,
   `hfreeB` (the parent card's Theorem B);
4. Manin-kernel rigidity for simple abelian varieties not descending to the constants:
   `hrigidity`.

**Verification.**

- `lake env lean` passes on `ManinHorizonIsogenyReconstruction.lean`;
- `lake build GaloisForLFunctions.HTGeometry.ManinHorizonIsogenyReconstruction` succeeds;
- `#print axioms` reports only `propext`, `Classical.choice`, `Quot.sound` for
  `Nonorthogonal.symm`, `nonorthogonal_of_monoidHom`, `nonorthogonal_self`,
  `DGroupHom.map_dGroupSharp`, `nonorthogonal_dGroupSharp_of_dGroupHom`,
  `multiplicationTail_translationStabilizer_eq_dGroupSharp`,
  `embeddedManinHorizon_nonorthogonal_iff_isogenous`,
  `manin_horizon_abstract_embedded_dichotomy`,
  `differentialTranslationStabilizer_ell_eq_dGroupSharp`, `dGroupSharpSubgroup`,
  `translationStabilizerSet_tail_eq_kolchinClosureOver` and
  `isKolchinClosedOver_translationStabilizerSet`;
- the module is imported by `GaloisForLFunctions.HTGeometry`.

## Log

- 2026-08-19 -- Formalization complete; card promoted to stage 3.  Theorem A holds by the `D`-group
  structure with no additivity hypothesis; the nonorthogonality relation is concrete and its
  elementary half is proved; Theorem B and the abstract/embedded dichotomy follow.  Kolchin
  closedness of the tail stabilizer, which makes it a differential algebraic subgroup rather than
  merely a subgroup, is `MultiplicationTailFixedField.isKolchinClosedOver_translationStabilizerSet`.
