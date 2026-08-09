# Cyclic bulk-boundary character, fusion recurrence, and open lift law

- **Stage:** 2 — fully proved on paper
- **Status:** [PAPER-PROVED] [UNIVERSAL-LAW FIELD]
  [BULK/BOUNDARY FORK] [SCALAR-INDISTINGUISHABLE BOUNDARIES]
  [FUSION RECURRENCE/OPEN LIFT] [NOT TQFT CLAIM] [NOT RH] [NO LEAN]

## 1. Setup

Let

\[
 G=C_3=\langle g\mid g^3=1\rangle,
 \qquad A=\mathbb C[G],
 \qquad \omega=e^{2\pi i/3}.
\tag{BB.1}
\]

For \(j\in\mathbb Z/3\mathbb Z\), let \(M_j\) be the one-dimensional \(A\)-module on which

\[
 g\cdot v=\omega^jv.
\tag{BB.2}
\]

Interpret \(A\) as a finite bulk law algebra and the \(M_j\) as boundary conditions. This is a
finite algebraic calibration; no extended field theory is asserted.

## 2. Boundary-indistinguishability theorem

### Theorem 2.1

The three boundary modules satisfy:

1. \(M_0,M_1,M_2\) are pairwise nonisomorphic;
2. \(\dim_\mathbb C M_j=1\) for every \(j\);
3. \(\dim_\mathbb C\operatorname{End}_A(M_j)=1\) for every \(j\);
4. the positive scalar character shadow is constant:

   \[
    |\chi_j(g)|^2=|\omega^j|^2=1;
   \tag{BB.3}
   \]

5. the marked bulk character separates them:

   \[
    \chi_j(g)=\omega^j.
   \tag{BB.4}
   \]

Hence boundary dimension, endomorphism dimension, and positive character norm cannot reconstruct
the boundary condition. A bulk phase observable can.

### Proof

One-dimensional representations of \(C_3\) are classified by the three possible eigenvalues of
\(g\). Schur's lemma gives one-dimensional endomorphism algebras. Equations (BB.3)--(BB.4) are
immediate.

## 3. Fusion recurrence and open history

Use the Hopf comultiplication \(\Delta(g)=g\otimes g\). Then

\[
 M_i\otimes M_j\cong M_{i+j\pmod3}.
\tag{BB.5}
\]

Let the defect \(D=M_1\) act by fusion.

### Theorem 3.1

Starting from \(M_0\), repeated fusion gives

\[
 D^{\otimes n}\otimes M_0\cong M_{n\pmod3}.
\tag{BB.6}
\]

The boundary observer is exactly periodic with period three. The marked fusion count
\(n\in\mathbb Z\) is an open lift, and the projection

\[
 \mathbb Z\longrightarrow\mathbb Z/3\mathbb Z
\tag{BB.7}
\]

forgets the number of completed fusion cycles.

The bulk character evolves as \(\omega^n\), so it closes with the boundary. A logarithmic lift
\(2\pi i n/3\) retains the open history.

### Proof

Equation (BB.5) follows because \(g\) acts on \(M_i\otimes M_j\) by
\(\omega^i\omega^j=\omega^{i+j}\). Iteration proves (BB.6). The remaining claims are the quotient
and its standard logarithmic lift.

## 4. Three-way coupling

The same finite algebra couples:

1. multiple boundary realizations with identical scalar positive data;
2. a bulk observable that separates them;
3. recurrent boundary fusion with open marked history.

This differs from PLG: all three boundary conditions exist. It differs from filling geometry:
the hidden datum is a bulk character and fusion grade, not minimum proof area. It differs from
dynamic equivalence: the quotient by fusion period is induced by a monoidal action.

## 5. Fatal boundaries

1. The bulk algebra, Hopf structure, and marked generator \(g\) are constitutive. Without a
   source-native origin, this model is fitted.
2. Equal dimension and character norm are weak scalar coincidences, not equality of all possible
   boundary observables.
3. A full bulk-boundary field would need locality, gluing, dualizability, and coherent defect
   composition. None is proved here.
4. Fusion recurrence is finite group arithmetic, not quantum recurrence or physical time.
5. The model supplies no anomaly class: it is a bulk-separation and fusion calibration.

## 6. Distinguishing prediction

If a bulk/boundary law field is fundamental, there should exist source-generated boundary proof
systems indistinguishable by their intrinsic scalar invariants but separated by the action of a
common bulk center or defect-fusion category. No such common action means this fork dies.

