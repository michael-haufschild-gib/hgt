# Recurrence-symmetry Boolean interaction reconstruction law

- **Status:** `[PAPER-PROVED] [LEAN-PROVED]`
  `[EXTERNAL PRIORITY AUDIT OPEN]`
- **Target:** interaction-topology universal quantum recurrence master paper
- **Claim class:** finite exact inverse theorem

## Jump

Fix a supplied finite family of sites \(V\), finite local alphabets
\((A_v)_{v\in V}\), and an energy function
\[
  E:\prod_{v\in V}A_v\longrightarrow\mathbb R.
\]
For a site mask \(M\subseteq V\), partially swap the \(M\)-coordinates of
two configurations \(x,y\), producing \(S_M(x,y)\). Call \(M\) a universal
recurrence symmetry when
\[
  E(S_M^1(x,y))+E(S_M^2(x,y))=E(x)+E(y)
  \qquad\text{for every }x,y.                    \tag{R1}
\]

Conjecture:

1. the universal recurrence masks form a Boolean subalgebra of
   \(\mathcal P(V)\);
2. \(E\) is additively separable across \(M\mid M^c\) exactly when \(M\)
   satisfies `(R1)`;
3. the atoms of this Boolean algebra are the unique finest additive
   interaction blocks of \(E\);
4. the complete pair-resolved long-time recurrence kernel reconstructs this
   algebra and hence those blocks;
5. every scalar SFF moment, Hamming collision cube and independent-history
   product law is a forward shadow of this inverse object.

## Candidate universal interpretation

> The way a quantum system repeats reveals which of its declared parts are
> dynamically indivisible.

Equivalent mathematical headline:

> Recurrence symmetries are the Boolean algebra of additive interaction
> components.

## Proof germ

For a base configuration \(b\), `(R1)` with the pair \((x,b)\) is equivalent
to the rectangular decomposition
\[
 E(x)+E(b)
 =
 E(x_M,b_{M^c})+E(b_M,x_{M^c}).                  \tag{R2}
\]
Thus recurrence symmetry is exactly additive separability across the cut.

If `(R2)` holds for masks \(M\) and \(N\), decompose the coordinates into
the four cells
\[
 M\cap N,\quad M\setminus N,\quad N\setminus M,\quad
 V\setminus(M\cup N).
\]
Applying the two rectangular decompositions successively separates all four
cells, proving `(R2)` for \(M\cap N\), \(M\cup N\), complements and symmetric
differences. Hence the valid masks form a finite Boolean algebra. Every
finite Boolean subalgebra of a powerset is the family of unions of its atoms,
which gives the unique finest additive partition.

## Non-overclaim boundary

The site decomposition \(V\) and its controllable local coordinates are
inputs. The theorem can reconstruct interaction blocks relative to those
declared sites. It cannot derive tensor-product structure, physical space,
or a preferred subsystem ontology from spectral data alone. The exact
no-go is recorded in
`../../../5-failed/space-is-the-connected-part-of-time-conjecture.md`.

## External priority status

Searches found extensive parents for:

- exact and higher-order spectral form factors;
- componentwise permutation moments in rationally independent free systems;
- functional ANOVA and non-additive interaction detection;
- Hamiltonian and quantum-process structure learning.

No located primary source states the exact equivalence between universal
partial-swap recurrence, a Boolean algebra of separable cuts, and recovery of
its atomic interaction partition. This is not yet complete priority
clearance.

## Falsifiers

1. A universal partial-swap mask across which \(E\) is not additively
   separable.
2. Two universal masks whose intersection or union is not universal.
3. Nonunique atomic additive partitions.
4. Pair-resolved recurrence data cannot determine `(R1)`.
5. Existing literature already contains the same recurrence/Boolean-algebra
   inverse theorem.
6. The only proof defines the desired partition into existence without an
   independently measurable recurrence criterion.
7. Reconstruction silently assumes unknown tensor factorization rather than
   the explicitly supplied site controls.

## Formal plan

1. [x] Define dependent partial swaps and universal recurrence masks.
2. [x] Prove partial-swap/basepoint rectangular equivalence.
3. [x] Prove empty/full/complement/intersection/union closure.
4. [x] Define atomic masks and prove unique finest additive partition.
5. [x] Bridge the pair-resolved symmetric phase average to the mask predicate.
6. [x] Target compile and axiom audit.
7. [ ] Complete external priority audit before manuscript use.

## Formal result

`formal/GaloisForLFunctions/HTGeometry/RecurrenceSwapInteractionReconstructionLaw.lean`
unconditionally proves the swap/separability equivalence, Boolean
subalgebra, atom reconstruction, pairwise atom disjointness, coverage and
unique atom assignment for every supplied site, and the operational
phase-kernel equivalence. Target compilation passes. Axiom audit reports
only `propext`, `Classical.choice` and `Quot.sound`.

## Current hostile verdict

The theorem is exact and inverse, but its mathematical ingredients are close
to classical rectangle separability tests and finite Boolean algebra.
Recurrence interpretation alone may not carry Nature-level novelty. It is
therefore a structural corollary of the broader
`recurrence-relation-lattice-universal-law.md`, not yet an independent
headline.
