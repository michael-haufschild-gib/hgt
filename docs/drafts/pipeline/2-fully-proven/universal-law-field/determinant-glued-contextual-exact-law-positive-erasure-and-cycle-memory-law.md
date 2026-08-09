# Determinant-glued contextual exact law, positive erasure, and cycle-memory law

- **Stage:** 2 — fully proved on paper
- **Status:** [PAPER-PROVED] [UNIVERSAL-LAW FIELD]
  [NON-PRODUCT SYNTHESIS] [CONTEXTUAL EFFECTIVITY + DETERMINANT MEMORY]
  [POSITIVE ERASURE] [CYCLE MULTIPLICITY] [NOT RH] [NO LEAN]

## 1. Setup

Let \(G=(V,E)\) be a finite connected simple graph and let

\[
 b=(b_v)_{v\in V}\in\mathbb F_2^V.
\tag{DG.1}
\]

For every incidence \(v\in e\), choose a determinant sign

\[
 \varepsilon_{v,e}\in\{\pm1\}.
\tag{DG.2}
\]

The local law at \(v\) consists of the based acyclic complexes

\[
 C(\varepsilon_{v,e}):
 0\longrightarrow\mathbb C
 \xrightarrow{\varepsilon_{v,e}}\mathbb C
 \longrightarrow0
\tag{DG.3}
\]

subject to the vertex determinant constraint

\[
 \prod_{e\ni v}\varepsilon_{v,e}=(-1)^{b_v}.
\tag{DG.4}
\]

On an edge \(e=\{v,w\}\), gluing requires

\[
 \varepsilon_{v,e}=\varepsilon_{w,e}.
\tag{DG.5}
\]

A **global exact law** is a family satisfying (DG.4)--(DG.5).

## 2. Determinant-gluing theorem

### Theorem 2.1 — one determinant law carries effectivity and hidden memory

The following are equivalent:

1. a global exact law exists;
2. the total charge is even:

   \[
    \sum_{v\in V}b_v=0\quad\text{in }\mathbb F_2;
   \tag{DG.6}
   \]

3. the total determinant anomaly vanishes:

   \[
    \mathfrak a(b):=\prod_{v\in V}(-1)^{b_v}=1.
   \tag{DG.7}
   \]

When these conditions hold, the number of global exact laws is

\[
 \boxed{2^{\,|E|-|V|+1}.}
\tag{DG.8}
\]

Thus the same gluing law has:

- an effectivity obstruction when \(\mathfrak a(b)=-1\);
- a cycle-memory torsor of size \(2^{\beta_1(G)}\) when \(\mathfrak a(b)=1\), where
  \(\beta_1(G)=|E|-|V|+1\).

### Proof

Write

\[
 \varepsilon_{v,e}=(-1)^{x_{v,e}},
 \qquad x_{v,e}\in\mathbb F_2.
\tag{DG.9}
\]

The gluing condition identifies the two half-edge values with one edge value \(x_e\). The vertex
constraint becomes the incidence equation

\[
 \partial_Gx=b.
\tag{DG.10}
\]

For a connected graph, the image of the unoriented incidence map over \(\mathbb F_2\) is the
even-sum hyperplane, proving the equivalence of (1) and (2). Equivalence of (2) and (3) is
immediate.

The incidence map has rank \(|V|-1\). Every nonempty solution fibre is therefore an affine space
of dimension

\[
 |E|-(|V|-1)=|E|-|V|+1,
\tag{DG.11}
\]

which proves (DG.8).

### Direct anomaly identity

Any glued family necessarily satisfies

\[
 \prod_{v\in V}(-1)^{b_v}
 =
 \prod_{v\in V}\prod_{e\ni v}\varepsilon_e
 =
 \prod_{e\in E}\varepsilon_e^2
 =1.
\tag{DG.12}
\]

Hence odd total charge is a literal determinant-gluing anomaly, not an externally attached
obstruction label.

## 3. Proper-face solvability

### Theorem 3.1 — every proper observer face is exact

For every proper vertex subset \(W\subsetneq V\), every prescribed charge
\(b|_W\in\mathbb F_2^W\) admits incidence signs satisfying (DG.4) at all vertices of \(W\), with
gluing imposed on every edge visible to \(W\).

Consequently an odd global charge can be:

- locally exact on every proper observer face;
- positive on every local determinant complex;
- globally non-effective.

### Proof

Restrict the incidence matrix to the rows indexed by \(W\). If a linear combination of these rows
vanishes, extend its coefficients by zero to all of \(V\). Connectedness forces every coefficient
in a relation among all incidence rows to be equal. Since at least one coefficient outside \(W\)
is zero, all coefficients vanish. The restricted row matrix has full row rank, so every right-hand
side is solvable.

## 4. Positive erasure

Every local complex (DG.3) is acyclic and has positive scalar determinant shadow

\[
 P(C(\varepsilon))=
 \varepsilon\overline{\varepsilon}=1.
\tag{DG.13}
\]

### Corollary 4.1

The observer retaining only:

1. local homology;
2. local positive determinant norms;
3. proper-face solvability;

sees exactly the same data for even and odd total charge. It detects neither the anomaly
\(\mathfrak a(b)\) nor the cycle-memory torsor.

The oriented determinant gluing is load-bearing.

## 5. Non-product character

This theorem does not take a contextual model and multiply it by an unrelated torsion model.
The contextual variables are the determinant histories of the exact complexes themselves:

\[
 \text{context assignment}
 =
 \text{determinant gluing datum}.
\tag{DG.14}
\]

The same incidence equation simultaneously controls:

1. global existence;
2. determinant anomaly;
3. hidden cycle multiplicity;
4. positive phase erasure.

This is the first finite calibration in the program where object-level effectivity, stable
determinant memory, and positivity interact through one restriction law.

## 6. Fatal boundaries

1. The signs \(\{\pm1\}\) form only a tiny determinant subgroup. No full Waldhausen
   infinity-category or algebraic \(K\)-theory descent theorem is constructed.
2. The graph and its context cover are constitutive. A source must generate them before target
   inspection.
3. Positive erasure uses scalar norm square. A full hermitian Gram observer may retain more.
4. The anomaly is a finite parity obstruction. It supplies no dynamics, filling cost,
   hypertranscendence, arithmetic source relation, or RH leverage.
5. The theorem is a genuine non-product synthesis but not yet a universal field.

## 7. Distinguishing prediction

If a Waldhausen-lawstack field is viable, more sophisticated source diagrams should exhibit the
same phenomenon with determinant signs replaced by nontrivial \(K_1\), Whitehead, Witt, or higher
\(K\)-classes: the class governing global effectivity should also measure stable proof memory and
its positive erasure.

## 8. Generalization

The sign theorem is the \(A=\{\pm1\}\) unoriented specialization of
abelian-determinant-flux-effectivity-cycle-memory-and-positive-quotient-law.md. The oriented
version works for every abelian determinant group, including \(K_1(R)\), and places global
effectivity obstruction and cycle-memory torsor in one exact sequence.
