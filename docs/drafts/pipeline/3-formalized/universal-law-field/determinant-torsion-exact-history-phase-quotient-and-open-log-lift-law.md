# Determinant torsion, exact history, phase quotient, and open logarithmic lift law

- **ID:** ULF-TORS-1
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean-certified)
- **Lean module:** `GaloisForLFunctions.HTGeometry.ConstitutiveDeterminantTorsion`
- **Status:** [LEAN-CERTIFIED] [UNIVERSAL-LAW FIELD]
  [COBORDISM/TORSION FORK] [EXACTNESS DOES NOT ERASE HISTORY]
  [POSITIVE PHASE QUOTIENT] [CLOSED OBSERVATION/OPEN LIFT] [NOT RH] [NO PROJECT AXIOMS]

## 1. Setup

Let \(k\) be a field. For \(u\in k^\times\), define the based two-term complex

\[
 C(u):\qquad 0\longrightarrow k e_1
 \xrightarrow{d_u}k e_0\longrightarrow0,
 \qquad d_u(e_1)=u e_0.
\tag{DT.1}
\]

Its **determinant history** is the comparison scalar

\[
 \tau(C(u)):=u,
\tag{DT.2}
\]

between the declared source bases under the exact differential. For a finite orthogonal sum of
such complexes, define

\[
 \tau\!\left(\bigoplus_{j=1}^r C(u_j)\right):=\prod_{j=1}^r u_j.
\tag{DT.3}
\]

This is the elementary determinant-line model of based Reidemeister torsion. The source bases are
part of the law datum.

## 2. Exact-history theorem

### Theorem 2.1 — homology forgets a multiplicative history field

For every \(u\in k^\times\):

1. \(C(u)\) is acyclic;
2. all \(C(u)\) have identical homology, namely zero;
3. determinant history is multiplicative under direct sum as in (DT.3);
4. a based chain isomorphism \(C(u)\to C(v)\) that preserves the declared basis vectors exists if
   and only if \(u=v\).

Thus the homology observer collapses the full \(k^\times\)-family of distinct based exact law
histories to one point.

### Corollary 2.2 — positive scalarization is a phase quotient

Take \(k=\mathbb C\) and define the positive history shadow

\[
 P(C):=\tau(C)\overline{\tau(C)}\in\mathbb R_{>0}.
\tag{DT.4}
\]

Then every unitary history \(C(e^{i\theta})\) has the same positive shadow \(P=1\), while its
oriented determinant history remains \(e^{i\theta}\). More generally, \(P\) is exactly the quotient
of \(\mathbb C^\times\) by its \(U(1)\)-phase action.

### Theorem 2.3 — closed exact observation can have open lifted history

For an integer \(N\neq0\), let

\[
 u_N(t)=e^{2\pi iNt},\qquad 0\leq t\leq1.
\tag{DT.5}
\]

The family \(C(u_N(t))\) satisfies:

1. its homology observation is constantly zero;
2. its positive shadow is constantly one;
3. its determinant history is a closed loop in \(\mathbb C^\times\);
4. its logarithmic lift
   \(\widetilde\ell_N(t)=2\pi iNt\in\mathbb C\) is open and ends at \(2\pi iN\);
5. the winding number is recovered by
   
   \[
    N=\frac{1}{2\pi i}\int_0^1u_N(t)^{-1}\dot u_N(t)\,dt.
   \tag{DT.6}
   \]

Hence exactness, positive return, and determinant return do not imply closed lifted law history.

## 3. Proof

Since \(u\neq0\), \(d_u\) is an isomorphism, so \(C(u)\) is acyclic. Equations (DT.2)--(DT.3)
are determinants of a diagonal block map. A basis-preserving chain map has identity maps in both
degrees, so the chain condition is \(u=v\). Equation (DT.4) is the ordinary polar quotient. For
(DT.5), \(u_N(0)=u_N(1)=1\), whereas the chosen logarithm changes by \(2\pi iN\); direct
integration gives (DT.6).

## 4. Native three-way coupling

One primitive family couples three phenomena without curvature language:

1. **exactness:** every complex has zero homology;
2. **positivity:** \(P=|\tau|^2\) forgets determinant phase;
3. **history:** a closed determinant loop can have nonzero logarithmic winding.

This is not a relabelled matching-map theorem. Matching asks whether local faces reconstruct a
total law. Determinant torsion asks what exactification itself erases about the path by which a law
became exact.

## 5. Fatal boundaries

1. If arbitrary independent basis changes in degrees zero and one are declared gauge, every
   \(u\) can be changed to every \(v\); the invariant disappears. A source marking, determinant
   orientation, or restricted gauge group is load-bearing.
2. Zero homology alone never produces torsion. A determinant-line comparison must be supplied by
   the exact law history.
3. Positive scalarization need not erase phase when the positive observer retains a full Gram
   matrix or a marked complex structure. Equation (DT.4) concerns the scalar norm-square observer.
4. The theorem supplies no canonical law cobordism category, source basis, dynamics, complexity,
   hypertranscendence, or physical action.
5. This elementary theorem is evidence for a torsion/cobordism ontology, not acceptance of it as
   the universal field.

## 6. Distinguishing prediction

If determinant-history geometry is fundamental, there should exist families of proof systems that
are indistinguishable by every homological/exactness endpoint but are separated by a
source-invariant determinant or higher \(K\)-theory class. Failure to find such source markings
outside constructed based complexes kills this fork.
