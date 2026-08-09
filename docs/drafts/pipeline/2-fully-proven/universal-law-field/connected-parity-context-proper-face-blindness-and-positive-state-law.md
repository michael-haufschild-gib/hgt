# Connected parity context, proper-face blindness, and positive-state law

- **Stage:** 2 — fully proved on paper
- **Status:** [PAPER-PROVED] [SPECULATIVE FIELD SURVIVOR]
  [NOMOLOGICAL CONTEXTUALITY] [INFINITE NATIVE FAMILY]
  [PROPER-FACE BLINDNESS] [POSITIVE GLOBAL EMPIRICAL STATE]
  [NOT RH] [NO LEAN WRITTEN OR BUILT]

## 1. Setup

Let \(G=(V,E)\) be a finite connected simple graph. Each vertex is a classical observer context.
Each edge \(e\) is a binary observable shared by its two endpoint contexts. Fix a parity charge

\[
 b=(b_v)_{v\in V}\in\mathbb F_2^V.
\tag{PC.1}
\]

A deterministic local law at context \(v\) is an assignment

\[
 x_e\in\mathbb F_2
 \qquad(e\ni v)
\]

satisfying

\[
 \sum_{e\ni v}x_e=b_v.
\tag{PC.2}
\]

A global classical law is one edge assignment satisfying (PC.2) at every vertex.

Let

\[
 \partial_G:\mathbb F_2^E\longrightarrow\mathbb F_2^V
\tag{PC.3}
\]

be the unsigned incidence map. Then the global-law equation is

\[
 \partial_Gx=b.
\tag{PC.4}
\]

## 2. Theorem

### Theorem 2.1 — exact contextuality criterion

For connected \(G\),

\[
 \boxed{
 \operatorname{im}\partial_G
 =
 \left\{
 c\in\mathbb F_2^V:
 \sum_{v\in V}c_v=0
 \right\}.}
\tag{PC.5}
\]

Consequently a global classical law exists if and only if

\[
 \boxed{\sum_{v\in V}b_v=0.}
\tag{PC.6}
\]

The obstruction group is canonically one-dimensional:

\[
 \operatorname{coker}\partial_G\cong\mathbb F_2,
\tag{PC.7}
\]

and the obstruction is the total parity charge.

### Theorem 2.2 — proper-face blindness

Assume

\[
 \sum_{v\in V}b_v=1.
\tag{PC.8}
\]

Then the full context system has no global classical law. Nevertheless, for every proper subset
\(W\subsetneq V\), the restricted equations

\[
 \sum_{e\ni v}x_e=b_v
 \qquad(v\in W)
\tag{PC.9}
\]

have a global edge assignment.

Thus every proper observer face is classically consistent, while the total cover is contextual.
No test confined to any proper set of contexts can detect the obstruction.

### Theorem 2.3 — positivity does not classicalize

Assume every vertex has degree at least two. At context \(v\), put the uniform probability
distribution on the \(2^{\deg(v)-1}\) local assignments satisfying (PC.2). These local
distributions agree on every shared edge: each edge marginal is uniform on \(\mathbb F_2\).

Hence they form a compatible positive empirical state on the entire context cover. Under (PC.8),
this positive state has no deterministic global section.

Therefore:

\[
 \boxed{
 \text{compatible positivity}
 \centernot\Longrightarrow
 \text{global classical law}.}
\tag{PC.10}
\]

## 3. Proof

Every edge column of \(\partial_G\) contains exactly two ones, so every vector in its image has even
total parity. Thus the right-hand side of (PC.5) contains the image.

Choose a spanning tree \(T\subset G\). Delete one vertex row from its incidence matrix. The
resulting square \((|V|-1)\times(|V|-1)\) matrix is invertible over \(\mathbb F_2\): orient the
tree away from the deleted root and eliminate leaves successively. Hence

\[
 \operatorname{rank}\partial_G=|V|-1.
\]

The even-parity hyperplane also has dimension \(|V|-1\), proving (PC.5)--(PC.7).

For Theorem 2.2, let \(A_W\) be the row restriction of \(\partial_G\) to \(W\). Suppose a linear
combination of rows in \(A_W\) vanishes. Extend its coefficient vector by zero on \(V\setminus W\).
It lies in

\[
 \ker(\partial_G^T).
\]

For a connected graph, \(\ker(\partial_G^T)\) consists exactly of constant vertex functions.
Because the extended coefficient vector vanishes at some vertex outside \(W\), it is zero.
Therefore \(A_W\) has full row rank and (PC.9) is solvable for every right-hand side.

For Theorem 2.3, fixing one incident edge value leaves
\(2^{\deg(v)-2}\) solutions of (PC.2), independent of whether the fixed value is zero or one.
Thus every edge marginal is uniform. Context intersections are single shared edges, so the local
distributions are compatible. Theorem 2.1 forbids a deterministic global section under (PC.8).

## 4. Native models

### 4.1 Triangle context

Take \(G=C_3\) and any odd charge \(b\). Each of three two-observable contexts is locally
consistent; every pair of contexts extends globally; all three do not. Uniform local parity
distributions give a positive compatible empirical state.

### 4.2 Peres--Mermin context

Take the context graph \(K_{3,3}\): three row contexts and three column contexts, with nine
observables as edges. Assign even charge to five contexts and odd charge to one. This is the parity
skeleton of the Peres--Mermin square. The abstract obstruction is (PC.7); the two-qubit Pauli
realization supplies commuting operator contexts and a genuine quantum positive state.

In sign notation, each observable value appears in exactly two context products. Multiplying all
six context equations gives \(+1\) from the values and \(-1\) from the prescribed context charges,
the familiar contradiction.

## 5. Field interpretation

This theorem gives a non-geometric candidate for the universal “shadow” phenomenon:

1. each observer context is classical;
2. every proper collection of observers admits a common classical completion;
3. the total observer cover has a one-bit obstruction;
4. a global positive nonclassical state still exists.

The missing datum is not local curvature or a forgotten scalar. It is a total-context obstruction
that is identically invisible on every proper face. A universal field based on contexts would treat
proof systems as local commutative worlds and the source as a global noncommutative or
nonclassical state.

## 6. Conjecture loops

1. **Pairwise consistency forces global law — false.** The triangle already refutes it.
2. **Every proper-face completion forces total completion — false.** Theorem 2.2 gives an infinite
   family of counterexamples.
3. **Positivity removes contextuality — false.** Theorem 2.3 gives compatible positive states with
   no deterministic global law.
4. **One more local relation repairs the problem — false in form.** The obstruction is total parity;
   changing it requires changing the global charge class, not refining any proper face.
5. **Contextuality explains all observer loss — open and probably false.** Tangent collapse,
   analytic completion, and cost may exist in one commutative context. The fork survives only if a
   source-native context category transmits those structures.

## 7. Parent boundary

Sheaf-theoretic contextuality and its cohomological obstructions are established:

- Abramsky--Brandenburger, *The Sheaf-Theoretic Structure of Non-Locality and Contextuality*,
  <https://arxiv.org/abs/1102.0264>;
- Abramsky--Mansfield--Barbosa, *The Cohomology of Non-Locality and Contextuality*,
  <https://arxiv.org/abs/1111.3620>;
- Carù, *On the Cohomology of Contextuality*,
  <https://arxiv.org/abs/1701.00656>.

The graph-incidence theorem is elementary. Its role here is a dependency-closed native test of a
new field interpretation, not a priority claim.

## 8. Sharp scope

1. Connectedness is load-bearing for the one-dimensional obstruction.
2. Minimum degree two is used only for the uniform positive-state construction.
3. Contextuality does not by itself produce dynamics, hypertranscendence, completion, or action.
4. The abstract triangle model need not be quantum-realizable; the Peres--Mermin model is.
5. No arithmetic source, proof endpoint, or RH statement is used.

