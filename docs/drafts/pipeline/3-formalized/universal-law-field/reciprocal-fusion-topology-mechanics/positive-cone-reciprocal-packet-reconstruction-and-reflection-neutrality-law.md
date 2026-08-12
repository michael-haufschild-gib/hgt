# Positive-cone reciprocal packet reconstruction and reflection neutrality law

- **ID:** ULF-RFTM-3A
- **Stage:** 2 — fully proven on paper
- **Type:** THEOREM / GLOBAL FORMATION CHART / FUNCTIONAL-EQUATION ACTION
- **Status:** `[PAPER-PROVED] [LEAN-PROVED] [DEPENDENCY-CLOSED] [BRIDGE] [GLOBAL RECONSTRUCTION]`
  `[REFLECTION INFORMATION-NEUTRAL] [NOT PROPERNESS] [NOT RH]`

## 1. Mathematical delta

The common-kernel packet theorem proves that a functional-equation involution is information-neutral
after stochastic formation.  ULF-RFTM-2 proves that direct/reflected quadratic congruence retains
noncommutative ordering history that scalar traces erase.  The missing compatibility statement is
global rather than infinitesimal:

> Does the functional-equation exchange act on the entire positive reciprocal packet without
> losing either the formation coordinate or the internal relative-law coordinate?

The answer is yes.  Every ordered pair of positive-definite matrices is exactly one reciprocal
formation packet.  Its geometric midpoint recovers the formation coordinate; its oriented
displacement recovers the relative law.  Exchanging packet legs fixes formation and inverts only
the relative law.  Thus functional-equation exchange is a globally reconstructible involution, not
an annihilator or selector.

## 2. Setup

Let \(\mathcal P_n\) be the cone of positive-definite Hermitian \(n\times n\) matrices.  For
\(R,Q\in\mathcal P_n\), define direct/reflected formation

\[
 \Phi(R,Q)=(\Phi_+(R,Q),\Phi_-(R,Q))
 :=(RQR,RQ^{-1}R).
 \tag{PCR.1}
\]

For \(X,Y\in\mathcal P_n\), let \(X\#Y\) be the unique positive-definite solution \(S\) of

\[
 SX^{-1}S=Y.
 \tag{PCR.2}
\]

Explicitly, with \(H=X^{1/2}\),

\[
 X\#Y=H\bigl(H^{-1}YH^{-1}\bigr)^{1/2}H.
 \tag{PCR.3}
\]

Define recovery

\[
 \Psi(X,Y)=(R_{X,Y},Q_{X,Y}),
 \qquad
 R_{X,Y}=(X\#Y)^{1/2},
 \qquad
 Q_{X,Y}=R_{X,Y}^{-1}XR_{X,Y}^{-1}.
 \tag{PCR.4}
\]

Let packet exchange and parameter reflection be

\[
 \tau(X,Y)=(Y,X),
 \qquad
 \rho(R,Q)=(R,Q^{-1}).
 \tag{PCR.5}
\]

## 3. Positive Riccati lemma

### Lemma 3.1 — existence and uniqueness

For every \(X,Y\in\mathcal P_n\), `(PCR.3)` is positive definite and is the unique
positive-definite solution of `(PCR.2)`.

### Proof

Put \(H=X^{1/2}\), \(C=H^{-1}YH^{-1}\), and \(K=C^{1/2}\).  Positive congruence gives
\(C,K\in\mathcal P_n\).  Since \(H^2=X\),

\[
 (HKH)X^{-1}(HKH)
 =HKH(H^{-1}H^{-1})HKH
 =HK^2H
 =HCH=Y.
\]

Now let \(Z\in\mathcal P_n\) satisfy \(ZX^{-1}Z=Y\), and put
\(W=H^{-1}ZH^{-1}\in\mathcal P_n\).  Then

\[
 W^2=H^{-1}(ZX^{-1}Z)H^{-1}=H^{-1}YH^{-1}=C.
\]

The positive-definite square root of \(C\) is unique, so \(W=K\), hence \(Z=HKH=X\#Y\).
QED.

### Lemma 3.2 — midpoint symmetry

\[
 X\#Y=Y\#X.
 \tag{PCR.6}
\]

### Proof

Let \(S=X\#Y\).  From \(SX^{-1}S=Y\), inversion gives
\(Y^{-1}=S^{-1}XS^{-1}\), hence \(SY^{-1}S=X\).  The same positive matrix \(S\) solves the
swapped Riccati equation; Lemma 3.1 gives `(PCR.6)`. QED.

## 4. Global reciprocal reconstruction

### Theorem 4.1 — midpoint recovery and exact inverse chart

For all \(R,Q\in\mathcal P_n\),

\[
 \boxed{(RQR)\#(RQ^{-1}R)=R^2.}
 \tag{PCR.7}
\]

For all \(X,Y\in\mathcal P_n\), the recovered \(R=R_{X,Y}\) and \(Q=Q_{X,Y}\) are positive
definite and satisfy

\[
 \boxed{RQR=X,\qquad RQ^{-1}R=Y.}
 \tag{PCR.8}
\]

Moreover recovery returns the original parameters:

\[
 \boxed{\Psi(\Phi(R,Q))=(R,Q).}
 \tag{PCR.9}
\]

Consequently \(\Phi\) and \(\Psi\) are mutually inverse bijections of
\(\mathcal P_n\times\mathcal P_n\).

### Proof

Set \(X=RQR\) and \(Y=RQ^{-1}R\).  Since

\[
 X^{-1}=R^{-1}Q^{-1}R^{-1},
\]

one has

\[
 R^2X^{-1}R^2=RQ^{-1}R=Y.
\]

The matrix \(R^2\) is positive definite, so Lemma 3.1 gives `(PCR.7)`.

Conversely, let \(S=X\#Y\), \(R=S^{1/2}\), and \(Q=R^{-1}XR^{-1}\).  Positive congruence
gives \(R,Q\in\mathcal P_n\), and cancellation gives \(RQR=X\).  Inverting the definition of
\(Q\) yields

\[
 Q^{-1}=RX^{-1}R.
\]

Since \(R^2=S\), the Riccati equation gives

\[
 RQ^{-1}R=R^2X^{-1}R^2=SX^{-1}S=Y.
\]

This proves `(PCR.8)`.  Applied to a formed packet, `(PCR.7)` and uniqueness of the positive square
root recover \(R\); then

\[
 R^{-1}(RQR)R^{-1}=Q,
\]

which proves `(PCR.9)` and mutual inversion. QED.

## 5. Functional-equation exchange

### Theorem 5.1 — reflection lifts through recovery without information loss

The two involutions in `(PCR.5)` are conjugate through formation and recovery:

\[
 \boxed{\tau\circ\Phi=\Phi\circ\rho,}
 \qquad
 \boxed{\Psi\circ\tau=\rho\circ\Psi.}
 \tag{PCR.10}
\]

Equivalently, for every positive packet,

\[
 \boxed{R_{Y,X}=R_{X,Y},\qquad Q_{Y,X}=Q_{X,Y}^{-1}.}
 \tag{PCR.11}
\]

Thus packet exchange preserves all recoverable information: it fixes the formation coordinate and
reverses the oriented relative-law coordinate.  In particular it is an involutive bijection, not a
quotient, coarse graining, or vanishing operation.

### Proof

The first identity in `(PCR.10)` is direct:

\[
 \Phi(R,Q^{-1})=(RQ^{-1}R,RQR)=\tau\Phi(R,Q).
\]

For the recovery identity, Lemma 3.2 gives
\(Y\#X=X\#Y\), hence \(R_{Y,X}=R_{X,Y}=:R\).  Put \(S=R^2=X\#Y\).  The Riccati equation gives

\[
 R^{-1}YR^{-1}=RX^{-1}R.
\]

But \(Q_{X,Y}=R^{-1}XR^{-1}\), so inversion gives
\(Q_{X,Y}^{-1}=RX^{-1}R\).  Therefore \(Q_{Y,X}=Q_{X,Y}^{-1}\), proving `(PCR.11)` and the
second identity in `(PCR.10)`. QED.

### Corollary 5.2 — compatibility with common-kernel information neutrality

Suppose an observer law is extended by a parameter-independent Markov recovery kernel as in
ULF-PFM-2.  If its functional-equation action realizes packet exchange \(\tau\), then:

1. stochastic formation preserves directed KL and Jeffreys information exactly;
2. positive-cone recovery preserves the complete ordered packet exactly;
3. functional-equation exchange fixes \(R\) and sends \(Q\) to \(Q^{-1}\).

Hence neither recovery layer can select the reflection center: both are information-neutral.  A
selector must impose a further properness, bounded-work, or annihilation law on \(Q\) or on an
independent formation history.

## 6. Hostile audit and exact boundary

1. **Not a new geometric mean.**  The Riccati characterization, symmetry, congruence invariance,
   and positive-cone midpoint geometry are established matrix analysis.  See Lawson--Lim,
   *The expanding universe of the geometric mean* (2024), and the matrix-geometric-mean survey of
   Iannazzo (2024).  The 2026 Koufany--Lim symmetric-cone work extends related decomposition and
   midpoint constructions beyond matrices.  This card is a `[BRIDGE]` at the ingredient level.
2. **Actual field delta.**  The theorem closes a missing compatibility law among three already
   independent ULF mechanisms: reciprocal quadratic formation, common-kernel information
   neutrality, and functional-equation reflection.  It proves they form one exact global chart.
3. **No scalar sufficiency.**  Trace, determinant, distance, or unordered packet data need not
   recover \(Q\).  Exact neutrality uses the full ordered packet.
4. **No selection.**  Since \(Q\mapsto Q^{-1}\) is bijective, reflection alone cannot force
   \(Q=I\).  This is the positive-cone analogue of ULF-PFM-2's conserved Jeffreys work.
5. **No indefinite extension claimed.**  On an indefinite cone, positive Riccati uniqueness can
   fail or require a different component.  The proof is specifically positive-definite.
6. **No properness claimed here.**  The amplified midpoint orbit and its boundedness criterion
   remain ULF-RFTM-3B.  They require a separate cofinal/topological theorem.

## 7. Literature boundary

- J. D. Lawson and Y. Lim, *The expanding universe of the geometric mean*, Acta Sci. Math.
  90 (2024), 327--347, <https://doi.org/10.1007/s44146-024-00133-x>.
- B. Iannazzo, *Computational aspects of the geometric mean of two matrices: a survey*, Acta Sci.
  Math. (2024), <https://doi.org/10.1007/s44146-024-00155-5>.
- K. Koufany and Y. Lim, *Mostow-Type Decompositions and Geometric Means for Symmetric Cones*,
  arXiv:2607.27714.

None of these sources supplies or needs the HGT formation/common-recovery/functional-equation
interpretation.  Conversely, this card makes no priority claim for their matrix identities.

## 8. Gates

- [x] 0 -> 1: exact global reconstruction conjecture and hostile limits
- [x] 1 -> 2: dependency-closed proof of Riccati uniqueness, mutual reconstruction, and reflection
  equivariance
- [x] 2 -> 3: exact Lean theorem package, axiom audit, scoped forbidden scan, and umbrella build
- [ ] 3 -> 4: independent expert audit and integration with amplified properness

## Log

- 2026-08-12 — split ULF-RFTM-3 into reconstruction/reflection theorem and separate amplified
  properness conjecture; closed all finite-dimensional positive-cone proof obligations.
- 2026-08-12 — formalized Riccati uniqueness, global reconstruction, midpoint symmetry, exchanged
  recovery, and reflection-information-neutrality capstone; direct checks and 11,844-job ULF
  umbrella build passed; axiom audit reports only standard quotient/classical axioms.
