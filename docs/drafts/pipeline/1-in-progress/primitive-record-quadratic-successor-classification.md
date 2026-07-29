# Primitive record nonselection and quadratic successor classification

- **ID:** primitive-record-quadratic-successor-classification
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper)
- **Source:** `obstruction-law-reciprocity.md`
- **Statement:** A nonzero primitive obstruction space does not determine its first higher-record
  coalgebra; one-step pointed coalgebras are classified by projective congruence classes of their
  reduced coproduct tensors.

## Goal

Resolve the first exact uniqueness discriminator for source-record bar--cobar succession. Determine
whether the primitive record
\(\operatorname{Prim}(\mathsf R_e)\simeq\mathsf{Ob}_e\) can determine the higher record
\(\mathsf R_e\), and extract the strongest positive invariant when it cannot.

This theorem is intentionally finite and pre-physical. It does not claim to construct an event
source, positivity, a cobar law, spacetime, or a force. Its role is to prevent the universal-law
programme from hiding higher composition inside the word "obstruction".

## Gates

- [x] 0 → 1 in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [ ] 1 → 2 fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [ ] 2 → 3 formalized: exact unconditional Lean theorem, final module audit green
- [ ] 3 → 4 publication-ready: not a standalone Nature claim; integrate only as a boundary theorem

## Setup

Let \(k\) be a field, let \(P\) be a finite-dimensional \(k\)-vector space, and let

\[
C_q=k1\oplus P\oplus kz
\]

for a tensor \(q\in P\otimes P\). Define a coaugmentation \(k\to C_q\), counit
\(\varepsilon(1)=1\), \(\varepsilon(P)=\varepsilon(z)=0\), and comultiplication

\[
\begin{aligned}
\Delta_q(1)&=1\otimes1,\\
\Delta_q(p)&=1\otimes p+p\otimes1 &&(p\in P),\\
\Delta_q(z)&=1\otimes z+z\otimes1+q.
\end{aligned}                                                     \tag{Q1}
\]

Call \(C_q\) a **one-step pointed record coalgebra**. Its first layer is \(P\); \(q\) is the first
higher-record datum.

## Theorem: projective tensor-orbit classification

`[PROVED HERE]`

Let \(q\in P\otimes P\) and \(q'\in P'\otimes P'\) be nonzero.

1. `(Q1)` defines a coassociative counital coalgebra. It is cocommutative exactly when
   \(q\) is fixed by the tensor flip.
2. The primitive subspace of \(C_q\) is exactly \(P\).
3. Coaugmented coalgebras \(C_q\) and \(C_{q'}\) are isomorphic exactly when there are
   \(g\colon P\xrightarrow{\sim}P'\) and \(a\in k^\times\) such that

   \[
   (g\otimes g)q=a q'.                                             \tag{Q2}
   \]

   Therefore their isomorphism classes are the projective diagonal
   \(GL(P)\)-orbits in \((P\otimes P)\setminus\{0\}\).
4. In the cocommutative case, these are projective congruence classes in
   \(\operatorname{Sym}^2(P)\setminus\{0\}\).

### Proof

For coassociativity it suffices to check \(z\). Write
\(q=\sum_i p_i\otimes r_i\). Both iterated coproducts are

\[
\begin{aligned}
1\otimes1\otimes z+1\otimes z\otimes1+z\otimes1\otimes1
1\otimes q+q\otimes1+\sum_i p_i\otimes1\otimes r_i.
\end{aligned}
\]

The counit identities follow directly from \(\varepsilon(P)=0\). The coproducts of \(1\) and
\(P\) are flip-invariant; hence \(C_q\) is cocommutative exactly when \(q=\tau(q)\).

Every counit-zero element has a unique form \(p+bz\). Its reduced coproduct is \(bq\).
Since \(q\ne0\) and \(k\) is a field, it is primitive exactly when \(b=0\). Thus
\(\operatorname{Prim}(C_q)=P\).

Let \(F\colon C_q\to C_{q'}\) be a coaugmented coalgebra isomorphism. Coalgebra maps preserve
primitive elements, so \(F|_P=g\colon P\to P'\) is an isomorphism. Counit preservation and the
one-dimensional quotient by \(k1\oplus P'\) give

\[
F(z)=p_0+a z'
\]

for unique \(p_0\in P'\) and \(a\in k^\times\). Comparing the reduced coproducts of \(F(z)\) and
\((F\otimes F)\Delta_q(z)\) gives `(Q2)`. Conversely, any \(g,a\) satisfying `(Q2)`, together
with any \(p_0\in P'\), defines an isomorphism by \(1\mapsto1\), \(p\mapsto g(p)\), and
\(z\mapsto p_0+a z'\). This proves the classification.

## Corollary: the smallest cocommutative nonselection pair

`[PROVED HERE]`

Take \(k=\mathbb C\), \(P=\mathbb Cx\oplus\mathbb Cy\), and

\[
q_{\mathrm{pair}}=x\otimes y+y\otimes x,\qquad
q_{\mathrm{self}}=y\otimes y.
\]

Both coalgebras have dimension four and exactly the same two-dimensional primitive subspace.
They are not isomorphic: viewed as linear maps \(P^*\to P\),
\(q_{\mathrm{pair}}\) has rank two and \(q_{\mathrm{self}}\) has rank one, while `(Q2)` preserves
rank.

Moreover, every nonzero symmetric \(q\in\operatorname{Sym}^2(\mathbb C^2)\) is congruent,
up to nonzero scalar, to exactly one of these two ranks. Thus there are exactly two nontrivial
four-dimensional one-step cocommutative record coalgebras with a two-dimensional primitive layer.

The finite dual algebras make the missing information concrete:

\[
\begin{aligned}
C_{q_{\mathrm{pair}}}^*
  &\cong \mathbb C[X,Y]/(X^2,Y^2),\\
C_{q_{\mathrm{self}}}^*
  &\cong \mathbb C[X,Y]/(X^2,XY,Y^3).
\end{aligned}
\]

Their maximal ideals have the same dimension, their indecomposable quotients
\(\mathfrak m/\mathfrak m^2\) have the same dimension, and their squares are both
one-dimensional. Their quadratic multiplication forms have different rank. Primitive generators
and dimension counts therefore do not recover composition.

## Hostile audit

### Does this falsify source-record bar--cobar succession?

No. It falsifies only the stronger shortcut

\[
\mathsf{Ob}_e\quad\Longrightarrow\quad\mathsf R_e
\]

when \(\mathsf{Ob}_e\) means the primitive record alone. The active conjecture already requires the
full \(\mathsf R_e\) to be generated independently by the event source. Neither example has yet
been shown source-selected, positive, spectator-free, physically complete, or compatible with
successive events. They therefore do not satisfy clauses 1--6 of the physical falsifier.

### Is the classification new?

No. This is elementary finite coalgebra/local-algebra structure. Classification by the bilinear
form is a small instance of the established theory of commutative algebras with one-dimensional
square. The 2025 classification of Martín Barquero, Martín González, and Sánchez-Ortega explicitly
uses the associated bilinear form and its congruence invariants:
<https://doi.org/10.1007/s00009-025-02812-7>.

Door grade: `[BRIDGE]`. Any novelty lies in a source theorem selecting the entire higher record,
not in `(Q1)`--`(Q2)`.

### Strongest positive survivor

The first higher-record invariant is the projective congruence class

\[
[q]\in \mathbb P(P\otimes P)/GL(P),                                \tag{Q3}
\]

not the primitive obstruction space \(P\). In the smallest cocommutative complex case its first
observable is rank. Operationally, \(P\) lists distinctions that became impossible; \(q\) records
which pairs of those distinctions can jointly generate the next consequential operation.

This changes the open core. A source law cannot merely say that every impossibility becomes a
generator. It must explain, without importing later dynamics, why impossibilities acquire one
specific hierarchy of joint-composition tensors.

## Revised exact discriminator

`[OPEN CORE: SOURCE SELECTION OF HIGHER COEXISTENCE TENSORS]`

For a physical event source \(S\), construct tensors

\[
q_2(S),q_3(S),\ldots
\]

on the primitive complementary record such that:

1. \(q_n(S)\) is defined from source incidence and positivity before successor operations exist;
2. the full hierarchy is invariant under presentation, dilation, gauge, and reference-frame
   changes;
3. it defines an effective conilpotent higher record with no cofree or spectator padding;
4. positive cobar reconstructs the successor operational law;
5. composition of sources maps to composition of the reconstructed laws; and
6. the hierarchy is unique among source-positive realizations.

The first serious uniqueness question is no longer whether primitives determine a coproduct—they
do not—but whether source incidence uniquely determines the projective orbit `(Q3)` and all its
higher analogues.

## Log

- 2026-07-29 — created after the typed obstruction--law conjecture exposed primitive-to-higher-law
  nonuniqueness as its first exact discriminator.
- 2026-07-29 — proved projective tensor-orbit classification and the rank-one/rank-two
  four-dimensional counterpair on paper.
- 2026-07-29 — novelty audit: elementary parent coalgebra/local-algebra mathematics; retained as a
  `[BRIDGE]` boundary theorem and source-selection test.
- 2026-07-29 — first repair found: the involution-selected retained/created polarity plus
  source-oddness excludes the rank-one self tensor and uniquely selects the paired orbit in the
  balanced two-channel truncation; see
  `../3-formalized/not_new_scientific_knowledge/primitive-record-polarity-selector.md`.
