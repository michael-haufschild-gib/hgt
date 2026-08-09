# Kolchin--Spencer inverse-limit noncompactness and observer-tail law

- **ID:** `nhg-kolchin-spencer-noncompactness`
- **Stage:** 2 — fully proven on paper
- **Status:** `[PAPER-PROVED] [UNIVERSAL FIELD THEOREM] [PRO-SPENCER TOPOLOGY]`
  `[KOLCHIN GROWTH] [NONLOCAL COMPACTNESS] [FINITE OBSERVER TAIL]`
  `[NO ROUTE INPUT] [NOT RH] [NO LEAN WRITTEN OR BUILT]`

## 1. Smooth prolongation tower

Let

\[
 \cdots\longrightarrow V_{n+1}
 \xrightarrow{\pi_{n+1,n}}V_n
 \longrightarrow\cdots\longrightarrow V_0
\tag{KS.1}
\]

be an inverse system of finite-dimensional real vector spaces with surjective transition maps. In a
formally smooth differential-law chart, `V_n` is the tangent space at prolongation order `n` and

\[
 K_{n+1}=\ker\pi_{n+1,n}
\tag{KS.2}
\]

is the new Spencer-symbol freedom appearing at the next order.

Give

\[
 V_\infty=\varprojlim_nV_n
\tag{KS.3}
\]

its inverse-limit locally convex topology.

## 2. Product normal form

### Theorem 2.1

After choosing linear splittings of the maps in `(KS.1)`, there is a topological linear
isomorphism

\[
 \boxed{
 V_\infty\cong V_0\times\prod_{n\geq1}K_n.}
\tag{KS.4}
\]

The isomorphism is not canonical, but the dimensions of the successive kernels and every conclusion
below are canonical.

### Proof

Surjectivity and finite dimensionality give a linear splitting

\[
 V_n\cong V_{n-1}\oplus K_n.
\tag{KS.5}
\]

Iterating gives `V_n congruent V_0 direct_sum K_1 ... direct_sum K_n`, compatibly with truncation.
Passing to the inverse limit replaces the increasing finite direct sum by the product, proving
`(KS.4)`. The product and inverse-limit seminorms agree coordinatewise. QED.

## 3. Exact local-compactness criterion

### Theorem 3.1

The following are equivalent:

1. `V_infinity` is locally compact;
2. `V_infinity` is finite-dimensional;
3. `K_n=0` for all sufficiently large `n`;
4. `sup_n dim V_n<infinity`.

Hence

\[
 \boxed{
 \dim V_n\longrightarrow\infty
 \quad\Longrightarrow\quad
 V_\infty\text{ is not locally compact}.}
\tag{KS.6}
\]

### Proof

Equivalence of 2--4 follows from `(KS.4)` and

\[
 \dim V_n=\dim V_0+\sum_{j=1}^n\dim K_j.
\tag{KS.7}
\]

Finite-dimensional real vector spaces are locally compact. Conversely, suppose infinitely many
`K_n` are nonzero. Every basic neighborhood in the product `(KS.4)` restricts only finitely many
coordinates, so it contains the full line through a nonzero vector in some unrestricted `K_n`.
Its closure cannot be compact because the continuous projection to that line is unbounded. Thus no
neighborhood is relatively compact. QED.

The theorem locates noncompactness in the lifted pro-law space itself, not in any particular
observer orbit or holonomy group.

## 4. Finite observer tail

Let `O` be finite-dimensional and let

\[
 q:V_\infty\longrightarrow O
\tag{KS.8}
\]

be a continuous linear observer that factors through some finite prolongation `V_N`.

### Corollary 4.1

The observer kernel contains the full tail

\[
 \boxed{
 \prod_{n>N}K_n\subseteq\ker q.}
\tag{KS.9}
\]

If infinitely many tail factors are nonzero, this invisible fibre is not locally compact. Therefore
a finite observer can have compact or recurrent dynamics while the lifted source history retains a
nonlocally compact open tail.

The last sentence is a compatibility statement: recurrence on `O` does not itself choose a motion
in the tail or a cost on it.

## 5. Kolchin specialization

Let a differential-algebraic law chart be formally smooth at a sourced point, with finite-order jet
tangent spaces `V_n` and surjective tangent truncations. Suppose its Kolchin dimension function at
that point agrees with the jet dimensions:

\[
 \omega(n)=\dim V_n.
\tag{KS.10}
\]

### Corollary 5.1

If `omega(n)` is unbounded, the sourced formal jet tangent `V_infinity` is not locally compact and
every fixed finite-order observer has an infinite Spencer tail.

If the coordinate family is differentially hypertranscendental, so its jets are algebraically free
in the declared chart, then every new derivative order contributes the maximal permitted kernel
increment. Hypertranscendence therefore produces noncompactness through pro-Spencer depth.

It does not imply noncompact ordinary holonomy, nonprecompact positive observer dynamics, or
divergent physical action.

## 6. Completion alternatives

The algebraic product topology in `(KS.4)` is only one realization. A weighted Hilbert, nuclear
Frechet, Tate, or bornological completion may alter bounded sets and continuous duals. Nevertheless:

1. no Hausdorff locally convex vector topology on the retained full infinite-dimensional space can
   be locally compact;
2. a stronger topology can exclude some product histories rather than compactify them;
3. a weaker completion can erase continuous reporters;
4. proper action requires an independently derived weight/cost on the tail.

Thus completion is another field layer, not a cure for prolongation growth by definition.

## 7. Hostile boundaries

1. Surjective tangent truncations are load-bearing. Singular differential equations can have
   nontrivial inverse-limit obstructions and derived-limit terms.
2. Unbounded coordinate-ring Kolchin dimension need not equal tangent dimension at singular points.
3. Infinite-dimensional nonlocal compactness does not imply hypertranscendence; the converse uses
   the specified formally smooth differential chart.
4. A finite observer need not factor through one jet order unless this is imposed by locality or
   continuity in the inverse-limit topology.
5. Noncompact invisible tail does not select a preferred history, recurrence time, or cost.

## 8. Field consequence

NHG now has an exact topology for the slogan "open lifted history":

\[
 \boxed{
 \text{unbounded formally smooth Kolchin growth}
 \Longrightarrow
 \text{nonlocally compact pro-Spencer source tangent}
 \Longrightarrow
 \text{infinite tail invisible to every finite-order observer}.}
\tag{KS.11}
\]

The implications are typed and one-way. They do not identify hypertranscendence with recurrence or
holonomy.

## 9. Lean formalization status

- **Status:** `[LEAN IMPLEMENTED] [LEAF CHECK PASSED] [FINAL AXIOM/UMBRELLA AUDIT PENDING]`
- **Module:**
  `formal/GaloisForLFunctions/HTGeometry/NomologicalHomotopyGeometry/KolchinSpencerLimit.lean`.
- **Umbrella wiring:** imported by
  `formal/GaloisForLFunctions/HTGeometry/NomologicalHomotopyGeometry.lean`, which is imported by
  `formal/GaloisForLFunctions/HTGeometry.lean`.
- **Exact formal targets:** `inverseLimitNormalForm` proves Theorem 2.1;
  `locallyCompact_inverseLimit_iff_finiteDimensional`,
  `finiteDimensional_inverseLimit_iff_eventually_kernel_eq_bot`, and
  `locallyCompact_inverseLimit_iff_bounded_finrank` prove all equivalences of Theorem 3.1;
  `not_locallyCompact_of_finrank_tendsto_atTop` proves `(KS.6)`;
  `range_tailEmbedding_le_observerKernel` and `tailRange_not_locallyCompact` prove Corollary 4.1;
  `kolchin_unbounded_specialization` proves Corollary 5.1.
- **Infrastructure proved, not assumed:** continuous linear splittings from finite-dimensional
  surjections; explicit recursive inverse-limit reconstruction; agreement of product and
  inverse-limit topologies via a `ContinuousLinearEquiv`; rank-nullity growth; bounded monotone
  dimension stabilization; infinite independent coordinate families; explicit full-tail
  embedding/projection and tail-range normal form; completion-independent Hausdorff topological
  vector-space Riesz obstruction.
- **Leaf verification:**
  `lake env lean GaloisForLFunctions/HTGeometry/NomologicalHomotopyGeometry/KolchinSpencerLimit.lean`
  passed on 2026-08-09.
- **Remaining gates:** final umbrella `lake build`, formal lint, and scratch-file `#print axioms`
  audit. Card remains in Stage 2 pending those repository-wide final gates; it is not moved.
