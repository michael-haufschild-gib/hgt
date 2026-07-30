# Complete-comparison reciprocity forces the \(3\times2\) witness

- **ID:** `complete-comparison-reciprocity-rigidity`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) / FINITE GRAPH-COHOMOLOGY BRIDGE
- **Source:** `../1-in-progress/no-outside-witness-self-unfolding-law.md`
- **Scientific status:** `[PROVED HERE] [STANDARD MATHEMATICS]`
  `[NEW CROSS-SHADOW SYNTHESIS] [NO NEW PHYSICS PROVED]`
- **Statement:** A connected elementary fact with \(n\) pairwise-complete raw accounts has one
  independent loop disagreement exactly when \(n=3\); its reduced comparison map then has source
  rank \(2\), target rank \(3\), and cokernel rank \(1\).

## Goal

Replace the root conjecture's two fitted finite selectors

```text
no residual frame  -> p=q+1;
no third witness   -> q=2
```

by one exact finite source condition:

```text
one connected fact = one irreducible comparison disagreement.
```

This theorem does not prove that nature uses a raw complete graph, that graph cohomology is physical
disagreement, that coefficients are complex, or that all framed deformations are physical. It
proves that if those source meanings are earned, the \(3\times2\) integers are consequences rather
than inputs.

## Theorem

Let \(F\) be a field, let \(n\ge1\), and regard the complete graph \(K_n\) as a
one-dimensional simplicial comparison complex: vertices are raw accounts, every unordered pair is
directly comparable, and no \(2\)-simplex or higher filler is supplied at this layer. Let

\[
\delta:C^0(K_n;F)\longrightarrow C^1(K_n;F)
\]

be the oriented graph coboundary. Put

\[
q:=\dim_F\operatorname{im}\delta,\qquad
p:=\dim_F C^1(K_n;F),\qquad
d:=\dim_F H^1(K_n;F).
\]

Then:

1. \(p=\binom n2\);
2. \(q=n-1\);
3. \(d=p-q=\binom n2-n+1=\frac{(n-1)(n-2)}2\);
4. \(d=1\) if and only if \(n=3\);
5. when \(d=1\),
   \[
   (p,q,d)=(3,2,1),\qquad p=q+1;
   \]
6. consequently the reduced cochain sequence is
   \[
   0\longrightarrow F^2
   \xrightarrow{\bar\delta}
   F^3
   \longrightarrow F
   \longrightarrow0.
   \]

Equivalently, among finite raw pairwise-complete comparison complexes, one connected public mode
and one irreducible loop-disagreement mode force the empty triangle.

## Proof

The unordered edges of \(K_n\) are the two-element subsets of its \(n\) vertices. Hence

\[
p=\#E(K_n)=\binom n2.
\tag{1}
\]

Because \(n\ge1\), \(K_n\) is connected. The kernel of the graph coboundary consists exactly of
functions constant on connected components. Its dimension is therefore one. Rank--nullity gives

\[
q=\operatorname{rank}\delta=n-1.
\tag{2}
\]

A graph has no \(2\)-cochains, so every \(1\)-cochain is a cocycle and

\[
H^1(K_n;F)=C^1(K_n;F)/\operatorname{im}\delta.
\]

Taking dimensions and applying `(1)`--`(2)` gives

\[
d=p-q
=\binom n2-(n-1)
=\frac{n(n-1)}2-(n-1)
=\frac{(n-1)(n-2)}2.
\tag{3}
\]

If \(n=3\), equation `(3)` gives \(d=1\). Conversely, suppose \(d=1\). Put \(m=n-1\).
Equation `(3)` gives

\[
m(m-1)=2.
\tag{4}
\]

For \(m\le1\), the left side is zero. For \(m=2\), it is two. For \(m\ge3\), it is at least six.
Thus \(m=2\) and \(n=3\). Substitution in `(1)`--`(3)` gives

\[
p=3,\qquad q=2,\qquad d=1,\qquad p=q+1.
\]

Quotienting \(C^0\) by its one-dimensional constant kernel makes the coboundary injective, and its
cokernel is \(H^1\). This yields the asserted short exact sequence. ∎

## Role-changing corollary

For the selected empty triangle \(C_3=\partial\Delta^2\), every edge is present but the triangular
filling is a minimal nonface. Hochster's formula puts its full-support reduced \(H^1\) class in

\[
\operatorname{Tor}_{1,\{0,1,2\}}.
\]

Thus the unique comparison disagreement is simultaneously a primitive first-Koszul constraint
class. This is the exact finite shadow of the root conjecture's claim that an obstruction changes
role and becomes a generator in the next operation layer.

The role-changing corollary is standard Hochster/Stanley--Reisner mathematics. The corpus already
formalizes its concrete rank-one \(C_3\) instance in
`formal/GaloisForLFunctions/HTGeometry/HochsterCycleRealization.lean`.

## Relation to the physical \(3\times2\) phase

The theorem supplies the dimensions of one reduced incidence map

\[
\bar\delta:F^2\hookrightarrow F^3.
\]

It does not by itself supply:

- \(F=\mathbb C\);
- the space of all faithful deformations
  \(\operatorname{Hom}_{\mathbb C}(\mathbb C^2,\mathbb C^3)_{\mathrm{reg}}\);
- a positive Gram record \(X^\dagger X\);
- the AIII \(SU(5)/S(U(3)\times U(2))\) phase;
- a Lorentzian continuum, quantum probability, matter, or dynamics.

If those bridges are derived independently, the theorem has a sharp consequence: the existing
no-residual-frame condition \(p=q+1\) and no-third-witness condition \(q=2\) are both outputs of one
source reciprocity equation \(d=1\).

## Hostile boundary

1. A one-vertex CW loop also models \(S^1\). Simple graphs forbid self-comparison and parallel
   channels; physics must derive those restrictions.
2. A clique complex fills every triangle, so \(K_3\) has \(H^1=0\). The theorem explicitly uses
   the raw one-dimensional comparison complex. Higher fillers must be generated later, not silently
   included or excluded.
3. Pairwise completeness may be too strong. If objective facts need not compare every internal
   account directly, many non-complete connected graphs have first Betti number one.
4. Rank-one \(H^1\) is a mathematical count. Identifying it with exactly one physical disagreement
   is conjectural.
5. The result is elementary graph cohomology, not a priority claim and not Nature-level physics.

## Gates

- [x] 0 → 1 in-progress: well-posed finite source model, attacks recorded
- [x] 1 → 2 fully-proven: dependency-closed paper proof, `[PROVED HERE]`
- [ ] 2 → 3 formalized: exact complete-graph rigidity theorem and \(3\times2\) corollary in Lean
- [ ] 3 → 4 publication-ready: not standalone; usable only as a certified lemma in a physical paper

## Log

- 2026-07-30 — extracted complete-comparison rank identity from fact--disagreement reciprocity.
- 2026-07-30 — proved that one loop disagreement forces \(n=3\) and simultaneously yields
  \(p=q+1\), \(q=2\), closing the finite conjunction in the root conjecture.
