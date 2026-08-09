# Nomological Gauss--Codazzi relative observer-fibre law

- **Stage:** 2 — fully proved on paper
- **Status:** [PAPER-PROVED] [ROUTE-INDEPENDENT] [FIELD-STRUCTURAL]
  [LINEARIZED POLARIZED CHART] [NOT RH] [NO LEAN WRITTEN OR BUILT]

## 1. Setup

Let \(M\) be a smooth manifold. Let \(E\to M\) be a finite-rank real vector bundle with a
nondegenerate symmetric bilinear form \(g\) and a \(g\)-compatible connection \(\nabla^E\). Let
\(K\subset E\) be a nondegenerate subbundle and put \(H=K^\perp\), so

\[
 E=K\oplus H.
\tag{NGC.1}
\]

Write \(P_K,P_H\) for the orthogonal projections. Define induced connections

\[
 \nabla^K=P_K\nabla^E|_K,
 \qquad
 \nabla^H=P_H\nabla^E|_H,
\tag{NGC.2}
\]

and second fundamental one-forms

\[
 \mathsf A_Xk=P_H\nabla^E_Xk,
 \qquad
 \mathsf B_Xh=P_K\nabla^E_Xh.
\tag{NGC.3}
\]

Thus \(\mathsf A\in\Omega^1(M;\operatorname{Hom}(K,H))\) and
\(\mathsf B\in\Omega^1(M;\operatorname{Hom}(H,K))\).

In an NHG chart, \(K\) is the linearized relative law-fibre of a regular observer and \(H\) is its
polarized observed sector.

## 2. Theorem

### Theorem 2.1 — observer Gauss--Codazzi--Ricci decomposition

Relative to (NGC.1), the connection and curvature have block forms

\[
 \nabla^E=
 \begin{pmatrix}
  \nabla^K&\mathsf B\\
  \mathsf A&\nabla^H
 \end{pmatrix},
\tag{NGC.4}
\]

and

\[
 R^E=
 \begin{pmatrix}
  R^K+\mathsf B\wedge\mathsf A & d_\nabla\mathsf B\\
  d_\nabla\mathsf A & R^H+\mathsf A\wedge\mathsf B
 \end{pmatrix}.
\tag{NGC.5}
\]

Metric compatibility gives

\[
 g(\mathsf B_Xh,k)+g(h,\mathsf A_Xk)=0.
\tag{NGC.6}
\]

In a positive Hermitian realization, (NGC.6) is \(\mathsf A=-\mathsf B^\dagger\).

### Corollary 2.2 — apparent curvature from observer coupling

If \(R^E=0\), then

\[
 d_\nabla\mathsf A=d_\nabla\mathsf B=0,
 \qquad
 R^K=-\mathsf B\wedge\mathsf A,
 \qquad
 R^H=-\mathsf A\wedge\mathsf B.
\tag{NGC.7}
\]

Hence a flat total law connection can induce nonzero observed curvature, but only through nonzero
second fundamental coupling to the relative law-fibre.

### Corollary 2.3 — exact parallel-observer criterion

The following are equivalent:

1. \(K\) is parallel under \(\nabla^E\);
2. \(H\) is parallel under \(\nabla^E\);
3. \(\mathsf A=0\);
4. \(\mathsf B=0\);
5. the splitting (NGC.1) is preserved by parallel transport.

On this locus the holonomy of \(\nabla^E\) is block diagonal and observer history has no local
transverse leakage.

### Corollary 2.4 — \(Q\)-compatibility

Assume \(E\) is graded, \(Q\) is a cyclic degree-one endomorphism with \(Q^2=0\), \(K\) is
\(Q\)-invariant, and \([\nabla^E,Q]=0\). Then \(H=K^\perp\) is \(Q\)-invariant and
\(\mathsf A,\mathsf B\) intertwine the induced \(Q\)-complexes. Every block in (NGC.5) is therefore
a morphism of the corresponding \(Q\)-complexes.

### Corollary 2.5 — gauge covariance

Every orthogonal bundle gauge preserving \(K\) and \(H\) conjugates \(R^K,R^H\) and transforms
\(\mathsf A,\mathsf B\) tensorially. Vanishing, rank, holonomy reduction, and the conjugacy class of
the full block curvature are independent of the adapted frame.

## 3. Proof

For \(k\in\Gamma K\) and \(h\in\Gamma H\), decompose \(\nabla^E_Xk\) and
\(\nabla^E_Xh\) with \(P_K+P_H=1\). This is (NGC.4).

Square the matrix-valued covariant derivative. The diagonal blocks are

\[
 (\nabla^K)^2+\mathsf B\wedge\mathsf A,
 \qquad
 (\nabla^H)^2+\mathsf A\wedge\mathsf B,
\]

and the off-diagonal blocks are the induced covariant exterior derivatives of
\(\mathsf B\) and \(\mathsf A\). This proves (NGC.5).

Differentiate \(g(h,k)=0\). Metric compatibility gives (NGC.6). Thus
\(\mathsf A=0\Longleftrightarrow\mathsf B=0\). By (NGC.3), simultaneous vanishing is equivalent
to preservation of both summands by the connection, hence by parallel transport. This proves
Corollaries 2.2 and 2.3.

For Corollary 2.4, cyclicity gives, for \(h\in H,k\in K\),

\[
 g(Qh,k)=\pm g(h,Qk)=0.
\]

Thus \(QH\subset H\). Expanding \([\nabla^E,Q]=0\) in blocks proves that the off-diagonal forms
intertwine the induced complexes. Gauge covariance follows directly from conjugation of the block
connection.

## 4. Coordinate-free consequence

The curvature of an observer is not an arbitrary comparison square. It is the relative geometry of
its law-fibre inside one total connection. Locally, the complete first-order data are

\[
 (K,Q_K,\nabla^K,R^K,\mathsf B),
\tag{NGC.8}
\]

with \(\mathsf A\) fixed by the polar pairing. Tangent loss is carried by \(K\), hidden local
transport by \(R^K\), and observed/hidden exchange by \(\mathsf B\). Formula (NGC.5) forces their
coherence.

This is the exact linearized field theorem behind the NHG relative-law-fibre primitive. The
nonlinear filtered \(L_\infty\)-algebroid extension remains open.

## 5. Sharp scope

1. Nondegeneracy of \(K\) is load-bearing for the orthogonal splitting.
2. Without a selected polarization or nondegenerate cyclic restriction, no canonical complement
   is asserted.
3. The theorem does not identify internal minimal \(L_\infty\) operations with connection
   curvature.
4. Flatness does not eliminate global block-diagonal monodromy.
5. The theorem is finite-rank and local. Pro-Spencer and completion phenomena require an inverse
   system of such charts.
6. No dynamical field equation, action, arithmetic realization, or endpoint statement is claimed.

