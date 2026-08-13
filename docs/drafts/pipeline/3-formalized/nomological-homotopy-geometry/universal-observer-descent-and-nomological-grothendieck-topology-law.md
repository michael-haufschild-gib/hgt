# Universal observer descent and nomological Grothendieck topology law

- **ID:** `nhg-observer-descent-topology`
- **Stage:** 3 — formalized in Lean 4
- **Lean gate:** [LEAN-PROVED] [AXIOM AUDITED] [UMBRELLA BUILD PASSED] (2026-08-13)
- **Status:** `[PAPER-PROVED] [UNIVERSAL FIELD THEOREM] [TOPOLOGY FOUNDATION]`
  `[NO ROUTE INPUT] [NOT RH] [LEAN-PROVED]`

## 1. Law category and observer direction

Let `Law` be a category of structured law fields and structure-preserving morphisms. Assume
`D=Law^op` has pullbacks and geometric realizations of the Čech nerves below, and that the required
realizations are stable under pullback. Assume also the finite products in `Law` used below exist.
An observer is a morphism

\[
 q_i:X\longrightarrow O_i
\tag{NT.1}
\]

in `Law`. Since observations point out of the law, topology belongs naturally to

\[
 \mathcal D=\operatorname{Law}^{op}.
\tag{NT.2}
\]

The observer becomes `u_i:O_i->X` in `D`.

## 2. Universal effective observer cover

### Definition 2.1

A family `{u_i:U_i->X}` in `D` is a **universal effective cover** if:

1. its augmented Čech nerve has colimit `X`;
2. after every base change `X'->X`, the pulled-back augmented Čech nerve has colimit `X'`.

Equivalently, when finite coproducts exist, `coprod_i U_i->X` is a universally effective
epimorphism. In `Law`, this says the combined observer

\[
 X\longrightarrow\prod_iO_i
\tag{NT.3}
\]

is a universally effective monomorphism with all relation data retained by its Čech equalizers.

This is stronger than injectivity of a tangent map, equality of invariants, or point separation.

## 3. Topology theorem

### Theorem 3.1 — universal effective observer covers form a Grothendieck pretopology

Universal effective covers satisfy:

1. every isomorphism is a cover;
2. every base change of a cover is a cover;
3. if `{U_i->X}` covers `X` and `{V_{ij}->U_i}` covers every `U_i`, then the composite family
   `{V_{ij}->X}` covers `X`.

Hence they generate a Grothendieck topology on `D=Law^op`, called the **nomological observer
topology**.

#### Proof

For an isomorphism, the Čech nerve is split and its augmentation is a colimit; the same holds after
base change. Item 2 is built into universality.

For item 3, base-change each cover `V_{ij}->U_i` along every level of the Čech nerve of
`{U_i->X}`. This produces a bisimplicial Čech object. Taking colimits first in the `V` direction
recovers the Čech nerve of `{U_i->X}`; taking its colimit recovers `X`. Taking the diagonal gives
the Čech nerve of the composite family. Universality of both layers makes the same argument valid
after arbitrary base change. Therefore the composite family is universally effective. QED.

## 4. Sheaf meaning

A presheaf `F:D^op->Spaces` is a nomological sheaf exactly when every observer cover gives descent:

\[
 F(X)\simeq
 \operatorname{Tot}
 F\bigl(U_\bullet\bigr),
\tag{NT.4}
\]

where `U_bullet` is the Čech nerve. Thus a law invariant is geometric only if it reconstructs from
every declared observer cover with all higher overlap coherences.

### Corollary 4.1 — scalar agreement is not coverage

If, after some base change, there are distinct parallel law morphisms `a,b:Z=>X` with
`q_i a=q_i b` for every observer, the opposite family is not a universal effective cover.

#### Proof

A universally effective monomorphism is, in particular, a monomorphism after every base change.
Failure to distinguish `a` and `b` contradicts this condition. QED.

## 5. Truncated and formal covers

For a formal law field, apply Definition 2.1 on each category of order-`N` Artin thickenings.

- An **order-`N` cover** has effective descent through that truncation.
- A **formal cover** is compatible in `N` and reconstructs the inverse formal tower.

Tangent injectivity is only the first-order necessary condition. It is not sufficient for higher
nilpotent descent, stack effectivity, integration, or completion.

## 6. Structured Morita covers

A strict structured cover-Morita equivalence supplies a common surjective-submersion refinement.
Where the relative algebroid, connection, Spencer filtration, cyclic pairing, and source all satisfy
effective descent along that refinement, its Čech family is a nomological cover. Forgetting any one
of those structures changes the site.

## 7. Failure tests

1. A point-separating family need not be effective on automorphisms or higher cells.
2. Joint tangent injectivity need not reconstruct nonlinear formal thickenings.
3. A family that is effective before completion may fail after a nonexact limit; formal coverage
   requires compatible inverse-tower descent.
4. A family can cover the unpolarized law and fail to cover the cyclic or real form.
5. Arbitrarily declaring convenient observers to be covers violates base-change or transitivity.

## 8. Field consequence

Proof presentations are local gauges only after they form an atlas in this topology. The statement
“all routes are gauges” is therefore not an axiom of NHG; it is a descent theorem to prove for each
claimed family of observers.

## 9. Lean formalization status

- **Status:** `[LEAN-PROVED] [AXIOM AUDITED] [UMBRELLA BUILD PASSED]`
- **Module:**
  `formal/GaloisForLFunctions/HTGeometry/NomologicalHomotopyGeometry/ObserverDescent.lean`.
- **Umbrella wiring:** imported by
  `formal/GaloisForLFunctions/HTGeometry/NomologicalHomotopyGeometry.lean`, which is imported by
  `formal/GaloisForLFunctions/HTGeometry.lean`.
- **Exact formal targets:** `UniversalEffective.UniversallyEffective` formalizes Definition 2.1;
  `ObserverDescent.universalEffectivePretopology` proves Theorem 3.1 and
  `ObserverDescent.nomologicalObserverTopology` is its generated Grothendieck topology;
  `ObserverDescent.not_universalEffective_of_parallel_not_separated` proves Corollary 4.1,
  including applicability after arbitrary base change.
- **Infrastructure proved, not assumed:** effectivity at identity, arbitrary base-change
  stability, upward closure, bind/transitivity through Yoneda descent, isomorphism covers,
  family-composition closure, and joint epimorphicity of universally effective families.
- **Leaf verification:**
  `lake env lean GaloisForLFunctions/HTGeometry/NomologicalHomotopyGeometry/ObserverDescent.lean`
  passed on 2026-08-09.
- **Final gates:** umbrella build and scratch-file `#print axioms` audit passed on 2026-08-13;
  card promoted to Stage 3.
