# Abelian determinant flux, effectivity, cycle memory, and positive quotient law

- **Stage:** 2 — fully proved on paper
- **Status:** [PAPER-PROVED] [UNIVERSAL-LAW FIELD]
  [DETERMINANT-FLUX GEOMETRY] [ARBITRARY ABELIAN COEFFICIENT]
  [EFFECTIVITY + MEMORY EXACT SEQUENCE] [POSITIVE QUOTIENT] [NOT RH] [NO LEAN]

## 1. Setup

Let \(G=(V,E)\) be a finite connected graph with an arbitrary orientation and let \(A\) be an
abelian group written multiplicatively. Define the determinant-flux boundary

\[
 \partial_A:A^E\longrightarrow A^V
\tag{DF.1}
\]

by

\[
 (\partial_Au)_v
 =
 \prod_{e:\,h(e)=v}u_e
 \prod_{e:\,t(e)=v}u_e^{-1}.
\tag{DF.2}
\]

Define the total-charge map

\[
 \Pi:A^V\longrightarrow A,
 \qquad
 \Pi(b)=\prod_{v\in V}b_v.
\tag{DF.3}
\]

An edge field \(u\in A^E\) is a global realization of a vertex law \(b\in A^V\) when

\[
 \partial_Au=b.
\tag{DF.4}
\]

## 2. Determinant-flux exact sequence

### Theorem 2.1

There is a natural exact sequence of abelian groups

\[
 1\longrightarrow H_1(G;A)
 \longrightarrow A^E
 \xrightarrow{\partial_A}A^V
 \xrightarrow{\Pi}A
 \longrightarrow1.
\tag{DF.5}
\]

Here

\[
 H_1(G;A)=\ker\partial_A
 \cong H_1(G;\mathbb Z)\otimes_{\mathbb Z}A
 \cong A^{\beta_1(G)}
\tag{DF.6}
\]

after choosing a cycle basis, with

\[
 \beta_1(G)=|E|-|V|+1.
\tag{DF.7}
\]

Consequently:

1. \(b\) is globally realizable if and only if

   \[
    \boxed{\Pi(b)=1;}
   \tag{DF.8}
   \]

2. every nonempty realization fibre is a torsor under \(H_1(G;A)\);
3. global effectivity obstruction and hidden cycle memory are the cokernel and kernel of the same
   determinant-flux map.

### Proof

Every edge contributes \(u_e\) once and \(u_e^{-1}\) once, so
\(\Pi\partial_A=1\), proving \(\operatorname{im}\partial_A\subseteq\ker\Pi\).

Choose a spanning tree \(T\) and a root \(r\). Given \(b\in A^V\) with \(\Pi(b)=1\), orient the
tree toward the root. Starting at the leaves, assign the unique outgoing tree-edge value that
realizes the prescribed charge at that vertex, setting all non-tree edge values to \(1\). Remove
the solved leaf and continue. The root equation holds automatically because the product of all
charges is \(1\). Hence \(\ker\Pi\subseteq\operatorname{im}\partial_A\).

The total-charge map is surjective by placing any \(a\in A\) at one vertex and \(1\) elsewhere.
Finally, the cellular chain complex of a graph has no two-cells, so
\(\ker\partial_A=H_1(G;A)\). Since \(H_1(G;\mathbb Z)\cong\mathbb Z^{\beta_1(G)}\), equation
(DF.6) follows.

## 3. Proper-face exactness

### Corollary 3.1

For every proper vertex subset \(W\subsetneq V\), the restricted boundary map

\[
 A^E\longrightarrow A^W
\tag{DF.9}
\]

is surjective.

### Proof

Given \(b_W\in A^W\), choose one vertex \(r\notin W\), put

\[
 b_r=\left(\prod_{v\in W}b_v\right)^{-1},
\tag{DF.10}
\]

and put charge \(1\) on all other vertices outside \(W\). The resulting total charge is \(1\), so
Theorem 2.1 supplies an edge realization. Restriction realizes \(b_W\).

Thus a nontrivial total anomaly can remain invisible on every proper observer face.

## 4. Exact-complex realization

Let \(R\) be a unital ring. Every invertible matrix \(U\in GL_n(R)\) defines a based acyclic
complex

\[
 C(U):0\longrightarrow R^n\xrightarrow{U}R^n\longrightarrow0
\tag{DF.11}
\]

and a stable determinant-history class

\[
 [U]\in K_1(R).
\tag{DF.12}
\]

Taking \(A=K_1(R)\), an oriented edge carries \(C(U_e)\); reversing orientation carries the inverse
class. Vertex gluing multiplies incident determinant histories exactly as in (DF.2).

### Corollary 4.1

The exact sequence (DF.5) becomes a source-independent algebraic template:

\[
 1\to H_1(G;K_1(R))
 \to K_1(R)^E
 \to K_1(R)^V
 \to K_1(R)
 \to1.
\tag{DF.13}
\]

The total \(K_1\)-charge obstructs global exact-law gluing; graph cycles retain the ambiguity of
successful gluings.

## 5. Positive coefficient quotient

Let

\[
 p:A\longrightarrow P
\tag{DF.14}
\]

be any homomorphism to another abelian group, interpreted as a positive or scalar observer.
Applying \(p\) coefficientwise gives a morphism of determinant-flux sequences.

### Theorem 5.1 — positive anomaly erasure criterion

For a vertex law \(b\),

\[
 \Pi(p(b))=p(\Pi(b)).
\tag{DF.15}
\]

Hence the \(P\)-observer declares the total anomaly trivial exactly when

\[
 \Pi(b)\in\ker p.
\tag{DF.16}
\]

It can therefore see a globally effective positive shadow even when the oriented \(A\)-law is
globally non-effective.

For \(A=\mathbb C^\times\), \(P=\mathbb R_{>0}\), and

\[
 p(z)=|z|^2,
\tag{DF.17}
\]

every unitary anomaly lies in \(\ker p=U(1)\).

## 6. Three native geometries from one chain complex

The coefficient chain complex

\[
 A^E\xrightarrow{\partial_A}A^V\xrightarrow{\Pi}A
\tag{DF.18}
\]

simultaneously produces:

1. **effectivity geometry:** the global anomaly \(\Pi(b)\);
2. **memory topology:** the cycle group \(H_1(G;A)\);
3. **observer relativity:** coefficient quotients \(A\to P\) that erase selected anomalies and
   cycle classes.

This is stronger than a scalar obstruction classification. It predicts the full realization
torsor whenever the anomaly vanishes and types exactly what a positive observer loses.

## 7. Hostile scope

1. The theorem is classical graph homology with a determinant-law interpretation.
2. A source must produce \(G\), \(A\), the edge complexes, and the coefficient quotient before
   endpoint specialization.
3. Nonabelian \(K_1\)-level representatives, higher \(K\)-groups, higher-dimensional observer
   complexes, and coherence under refinement are not constructed.
4. Positive coefficient quotients need not model every positive operator observer.
5. The theorem yields no arithmetic source class or RH leverage until a literal source diagram is
   realized.

## 8. Next conjecture

Replace the graph by a source-generated observer cell complex \(X\) and \(A\) by a connective
law-memory spectrum \(\mathbf K_{\mathrm{law}}\). The proposed total law field is then the
hypercohomology/descent object whose:

- negative effectivity layers obstruct global realization;
- degree-zero layer records determinant charge;
- positive homotopy layers record hidden proof memory;
- hermitian comparison records positive erasure.

This conjecture must first survive a two-dimensional finite example where a higher obstruction
and a nontrivial memory group arise from one cellular differential.
