# Correlated continuation ambiguity may be the source of quantum phase

- **ID:** `correlated-continuation-ambiguity-law`
- **Stage:** 1-in-progress
- **Type:** FOUNDATIONAL PHYSICS CONJECTURE / QUANTUM-SPACETIME RECONSTRUCTION TARGET
- **Scientific status:** `[HUNCH] [NOT YET SCIENTIFIC KNOWLEDGE] [NATURE: DO NOT WRITE]`
- **Parent:** `dynamical-composition-universal-law.md`
- **Exact finite bridge:**
  `../../../3-formalized/not_new_scientific_knowledge/source-ordered-pair-complex-structure.md`
- **Exact finite selector:**
  `../../../3-formalized/not_new_scientific_knowledge/joint-reversal-no-spectator-selector.md`
- **Statement:** Quantum phase may be the invariant residue of source ambiguities that can be
  reversed only together, not independently.

## Public hunch

> **Quantum reality exists because some choices can only be undone together.**

Technical version:

> **Nonclassical phase is the descent residue of correlated continuation ambiguity.**

This is a proof-independent conjecture. It is not inferred from the ease of the finite theorem and
does not claim that every nonfactorization is interaction.

## Why this hunch exists

The exact finite source pair contains two real open generators:

\[
J^2=S^2=I,\qquad JS=-SJ.
\]

Their ordered product \(\mathcal I=JS\) satisfies \(\mathcal I^2=-I\). The Lean-formalized parity
\(\Pi\) simultaneously reverses \(J\) and \(S\), and its fixed algebra is exactly

\[
\{aI+b\mathcal I\}.
\]

Over \(\mathbb R\), this is the complex scalar algebra. The complex direction therefore survives
the **joint** source reversal even though it is built from two real generators.

The two generators give the standard
\(\mathrm{Cl}_{2,0}\cong M_2(\mathbb R)\) presentation under the convention that positive
generators square to \(+I\).

The first discriminator is now Lean-proved. If both source choices may be removed independently,
the common fixed algebra contracts to real scalar matrices. A second Lean-proved classification
asks whether the admissible reversal leaves a nontrivial fixed idempotent. Either individual
reversal does: its fixed algebra is a split copy of \(\mathbb R\times\mathbb R\). Joint reversal
does not: its fixed algebra is \(\mathbb C\), whose only idempotents are \(0\) and \(1\).

Thus a supplied no-spectator criterion selects the correlated reversal without supplying complex
scalars. The physical theory still has to derive that criterion rather than insert it.

The physical hunch is the higher version:

```text
independently removable continuation choices
  -> no relative phase residue;

choices removable only through correlated completion changes
  -> nontrivial invariant phase;

failure to compare those correlations globally
  -> candidate quantum-spacetime transport obstruction.
```

## Semantic commitments

1. **Ambiguity** means inequivalent source-positive completions of the same present record, not
   subjective ignorance.
2. **Correlated** means the admissible equivalence acts jointly on two completion directions while
   the corresponding separate actions are not admissible physical gauge changes.
3. **Residue** means invariant or derived-invariant data of the completion groupoid; it is not a
   chosen branch.
4. **Quantum phase** requires more than an operator squaring to \(-I\): the programme must derive
   central complex amplitudes, positivity, interference, and the Born rule.
5. **Gravity** is not identified with bare nonfactorization. Any gravitational claim must arise
   only after local correlated ambiguities acquire source-derived causal comparison, soldering,
   and continuum dynamics.

## Relation to continuation-invariant reality

For history \(H\), the parent programme conjectures a source-positive completion moduli object
\(\operatorname{Ext}^{+}(H)\). The present card asks whether its admissible symmetry is itself
physically structured:

```text
product symmetry of independent completion changes
  versus
diagonal/correlated symmetry of jointly admissible changes.
```

Ordinary descent on a fixed site does not choose between those two symmetry types. The source event
must determine which changes are independently admissible. This is the non-circular content.

If the conjecture is correct, quantumness is not inserted as a complex field on a state space.
Complex phase appears when the equivalence relation among ways of continuing reality is correlated.
An event can then change quantumness by changing that correlation structure.

## Direct-parent and collision audit

Weaker territory is occupied:

1. fixed algebras of group actions, crossed products, Clifford algebras, and superselection theory
   are standard mathematics;
2. [reference-frame and superselection theory](https://arxiv.org/abs/quant-ph/0610030) already
   distinguishes correlated/global from uncorrelated/local reference restrictions and uses
   relational encodings to retain degrees erased by independent averaging;
3. gauge theory already defines observables by invariance;
4. [sheaf contextuality](https://arxiv.org/abs/1102.0264) already identifies nonclassicality with
   global-section obstructions;
5. [relational quantum mechanics](https://arxiv.org/abs/2109.09170) already makes facts
   event-relative;
6. process matrices and [causaloids](https://arxiv.org/abs/gr-qc/0608043) already permit non-fixed
   causal structure;
7. [background-independent process models](https://arxiv.org/abs/2106.01038) already impose
   permutation invariance;
8. bare nonfactorization as a universal force law was already killed in this corpus as circular and
   by force-free nonfactorizable counterexamples; and
9. the retired HT realization-stack route already proves that “use a stack,” “retain
   stabilizers,” and “horizontal descent fails” are not novelty claims.

Therefore the finite fixed-algebra result and the slogan alone are not new science.

Possible novelty survives only if one source-derived theorem jointly:

1. distinguishes independent from correlated completion changes without a supplied tensor split;
2. derives a source-positive no-spectator principle that selects the admissible equivalence rather
   than assuming a gauge subgroup or irreducibility axiom;
3. derives the complex scalar algebra and Born-positive quantum composition;
4. makes classicality the exact independently-localizable limit;
5. makes event composition change the correlation groupoid;
6. reconstructs causal comparison and Lorentzian spacetime from the same structure without
   identifying gravity with nonfactorization; and
7. yields a quantitative correction or selection result absent from quantum field theory plus
   general relativity.

## Completed exact finite discriminator

The finite Lean model now proves, over a characteristic-zero field:

1. each individual conjugation is an involutive algebra automorphism;
2. their composite is `sourcePairParity`;
3. joint-reversal invariants are exactly the generated complex plane;
4. invariance under both individual reversals leaves exactly scalar multiples of the identity; and
5. the generated imaginary direction is fixed jointly and odd under each individual reversal.

Over \(\mathbb R\), the added selector module also proves:

1. the fixed algebra of each individual reversal is split and contains a nontrivial idempotent;
2. every idempotent in the joint fixed algebra is \(0\) or \(1\); and
3. joint reversal is therefore the unique idempotent-indecomposable choice among the three
   order-two source reversals.

These are standard finite algebra, recorded in
[`joint-independent-source-reversal-fixed-algebra.md`](../../../3-formalized/not_new_scientific_knowledge/joint-independent-source-reversal-fixed-algebra.md)
and
[`joint-reversal-no-spectator-selector.md`](../../../3-formalized/not_new_scientific_knowledge/joint-reversal-no-spectator-selector.md).
Their value is to close a sharp source-selection seed, not to establish physics.

## No-spectator sharpening

`[HUNCH — UNIVERSAL EXTRAPOLATION FALSIFIED]`

> **Physical equivalence is the maximal source-generated identification whose invariant reports
> contain no untouched classical spectator sector.**

Public form:

> **Reality keeps only differences that cannot be separated.**

In the finite bridge, “spectator sector” has an exact algebraic meaning: a nontrivial fixed
idempotent. This converts the arbitrary instruction “quotient by joint reversal” into the
conditional theorem “joint reversal is the only candidate passing idempotent indecomposability.”

The new open core is not another fixed-algebra calculation. It is to define spectator freedom
from source-positive future interventions, prove that it selects admissible equivalences before
quantum theory or spacetime is supplied, and show that its positive compositional realization
forces rather than merely permits complex quantum mechanics.

### Hostile correction

The finite statement remains exact: in the supplied three-candidate real \(2\times2\) family,
individual reversal fixed algebras are split while the joint fixed algebra has only idempotents
\(0,1\).

The universal physical inference does not survive. Noncentral projections in a quantum factor are
not automatically spectators, while central-idempotent indecomposability does not detect an
independent tensor-factor spectator. Tensoring by a factor can preserve a trivial centre and the
chosen vertical fixed-algebra invariant. Thus “no nontrivial fixed idempotent” is neither necessary
nor sufficient for source-complete physical consequentiality outside the finite bridge.

Spectator freedom, if definable, must be dynamical: every retained component must alter some
source-generated later comparison. It cannot be tested against a future intervention alphabet
chosen in advance, because that returns to predictive-state reconstruction relative to supplied
behavior.

The stronger active mathematical frontier is now source-consequence trirepresentability in
[`consequence-trirepresentability-universal-law.md`](consequence-trirepresentability-universal-law.md).
Correlated reversal remains one finite amplitude shadow, not the selector of physical law.

## New-mathematics target

Construct a source-positive correlated-descent theory with:

1. an event-generated higher groupoid of completion changes;
2. a source-derived spectator criterion deciding which completion changes are gauge and proving
   why nontrivial fixed idempotents are physically removable sectors;
3. an intrinsic independence test deciding when completion changes factor;
4. coefficient objects assigned before taking invariants, without presupposing \(\mathbb C\),
   Hilbert tensor products, spacetime, or gauge group;
5. derived fixed objects retaining isotropy and obstruction sectors;
6. correspondences between history-dependent completion groupoids;
7. a theorem classifying when residual phase is real, complex, or quaternionic;
8. positivity and probability reconstructed from the same source; and
9. a continuum descent theorem separating internal gauge comparison from causal/soldering
   comparison.

## Pre-registered falsifiers

Retire or sharply reduce the conjecture if:

1. the correlated/independent distinction requires a prior tensor factorization or physical
   dynamics;
2. the finite complex fixed algebra is an accidental two-dimensional Clifford effect with no
   source-natural higher analogue;
3. independently admissible completion changes coexist with irreducible complex quantum phase in
   the constructed theory;
4. the construction cannot exclude real or quaternionic quantum theory without adding local
   tomography by hand;
5. positivity or the Born rule must be supplied separately;
6. causal/gravitational comparison has no theorem-level relation to the correlation groupoid;
7. a known parent theory already proves the full conjunction;
8. no finite prediction distinguishes the theory from quantum field theory plus general
   relativity; or
9. the no-spectator rule is only a renamed irreducibility or superselection axiom, rejects known
   physical superselection sectors, or cannot be stated before a fixed observable algebra exists.

## Gates

- [x] 0 → 1 in-progress: hunch, semantic commitments, exact finite seed, parent collisions, and
  falsifiers frozen
- [x] finite discriminator: joint/independent fixed algebras and unique idempotent-indecomposable
  reversal formalized unconditionally
- [ ] 1 → 2 fully-proven: source-derived correlated-descent theorem with dependency-closed proof
- [ ] 2 → 3 formalized: every finite mathematical dependency unconditional in Lean
- [ ] 3 → 4 publication-ready: quantum, spacetime, four-force, and predictive gates passed

## Log

- 2026-07-30 — extracted after the source-pair parity theorem: simultaneous reversal fixes the
  generated complex scalar plane.
- 2026-07-30 — separated the hunch from the killed bare-nonfactorization force law and from standard
  invariant/descent mathematics.
- 2026-07-30 — froze individual-versus-joint reversal as the next exact finite discriminator and
  source-positive correlated descent as the higher open core.
- 2026-07-30 — proved and formalized the individual-versus-joint discriminator; corrected the
  graded presentation from \(\mathrm{Cl}_{1,1}\) to \(\mathrm{Cl}_{2,0}\).
- 2026-07-30 — external priority audit found the correlated/global versus independent/local
  averaging mechanism already in reference-frame and superselection theory.
- 2026-07-30 — extracted the stronger finite selector: joint reversal is uniquely
  idempotent-indecomposable. Physical novelty moved to deriving no-spectator admissibility from
  source-positive continuation rather than assuming it.
- 2026-07-30 — hostile generalization audit killed fixed-idempotent indecomposability as a
  universal spectator criterion; retained the Lean theorem only as a finite conditional bridge.
