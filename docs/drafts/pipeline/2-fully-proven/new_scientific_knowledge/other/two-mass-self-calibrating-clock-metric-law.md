# Two-mass self-calibrating clock metric law

- **ID:** `two-mass-self-calibrating-clock-metric-law`
- **Stage:** 2-fully-proven
- **Type:** THEOREM / CONTINUUM GRAVITY / CLOCKS / INVERSE PROPAGATORS / CALIBRATION
- **Parent:** `../../1-in-progress/continuum-chronometric-equivalence-theorem.md`
- **Status:** operator and principal-symbol reconstruction paper-proved and formalized
  unconditionally in Lean; physical recovery of complete dressed Green operators remains open.

## Headline

> **Two different clocks can measure spacetime without a calibrated ruler.**

Sharper operational form:

> **Two distinct clock masses exactly cancel unknown source and detector gain, exposing the full
> spacetime metric.**

This gives the second clock species a necessary role absent from idealized inverse problems that
assume absolutely calibrated Green-function amplitude.

## Setup

Let

\[
  P_\mu=P_0+\mu I                                                       \tag{1}
\]

be a normally hyperbolic scalar operator on a four-dimensional globally hyperbolic region. Its
principal symbol is

\[
  \sigma_2(P_\mu)(x,\xi)=g^{-1}_x(\xi,\xi),                              \tag{2}
\]

independent of the calibrated squared mass \(\mu\).

Let \(G_\mu\) be a retarded or advanced Green operator in a fixed support class, so

\[
  P_\mu G_\mu=I,\qquad G_\mu P_\mu=I                                    \tag{3}
\]

on their standard test-function domains.

The laboratory does not observe \(G_\mu\) directly. Let \(A=M_a\) and \(B=M_b\) be unknown
invertible smooth multiplication operators describing receiver and source gain. Assume the same
endpoint gains act on two clock species. The complete measured response is

\[
  \widehat G_\mu=A\,G_\mu\,B.                                           \tag{4}
\]

No absolute calibration of \(a\) or \(b\) is assumed.

## Theorem 1 — the measured inverse operator

The inverse of the measured response is

\[
  Q_\mu:=\widehat G_\mu^{-1}
  =
  B^{-1}P_\mu A^{-1}.                                                    \tag{5}
\]

### Proof

Associativity, `(3)`, and the two-sided inverse laws for \(A,B\) give

\[
\begin{aligned}
  Q_\mu\widehat G_\mu
  &=B^{-1}P_\mu A^{-1}A G_\mu B
    =B^{-1}P_\mu G_\mu B=I,\\
  \widehat G_\mu Q_\mu
  &=A G_\mu B B^{-1}P_\mu A^{-1}
    =A G_\mu P_\mu A^{-1}=I.
\end{aligned}
\]

Thus `(5)` is the unique two-sided inverse. \(\square\)

## Theorem 2 — two masses isolate calibration

For two distinct calibrated squared masses \(\mu_1\neq\mu_2\),

\[
  \boxed{
  Q_{\mu_1}-Q_{\mu_2}
  =
  (\mu_1-\mu_2)B^{-1}A^{-1}.}                                           \tag{6}
\]

Hence the previously unknown pointwise calibration product

\[
  \kappa=(ab)^{-1}
\]

is reconstructed exactly:

\[
  \boxed{
  M_\kappa=
  \frac{Q_{\mu_1}-Q_{\mu_2}}{\mu_1-\mu_2}.}                              \tag{7}
\]

### Proof

Subtract `(5)` for the two species:

\[
\begin{aligned}
  Q_{\mu_1}-Q_{\mu_2}
  &=
  B^{-1}(P_0+\mu_1I)A^{-1}
  -
  B^{-1}(P_0+\mu_2I)A^{-1}\\
  &=
  (\mu_1-\mu_2)B^{-1}A^{-1}.
\end{aligned}
\]

The differential part cancels before any inversion or integration. Division by the nonzero
calibrated mass difference proves `(7)`. \(\square\)

## Theorem 3 — full metric reconstruction

Composition on the left and right by multiplication operators scales the principal symbol
pointwise. Therefore

\[
  \sigma_2(Q_\mu)
  =
  \kappa\,g^{-1}.                                                        \tag{8}
\]

Combining `(6)` and `(8)` gives the full inverse metric, not only its conformal class:

\[
  \boxed{
  g^{-1}
  =
  \frac{\mu_1-\mu_2}
       {Q_{\mu_1}-Q_{\mu_2}}\,
  \sigma_2(Q_{\mu_i}).}                                                  \tag{9}
\]

In `(9)`, the quotient by \(Q_{\mu_1}-Q_{\mu_2}\) means pointwise division by the nonvanishing
zeroth-order multiplication coefficient identified in `(6)`.

### Proof

The order-two term of \(B^{-1}P_\mu A^{-1}\) is

\[
  b^{-1}a^{-1}g^{\alpha\beta}\partial_\alpha\partial_\beta.
\]

Derivatives of \(a^{-1}\) enter only order one and order zero. Thus `(8)` holds. Equation `(7)`
recovers \(\kappa\neq0\), and pointwise division of `(8)` by \(\kappa\) proves `(9)`.
\(\square\)

## Exact identifiability statement

At each event and covector, put

\[
  D=(\mu_1-\mu_2)\kappa,\qquad S=\kappa g^{-1}(\xi,\xi).
\]

For \(\mu_1\neq\mu_2\) and \(\kappa\neq0\), the map

\[
  (\kappa,g^{-1}(\xi,\xi))\longmapsto(D,S)
\]

is injective, with inverse

\[
  \kappa=\frac D{\mu_1-\mu_2},
  \qquad
  g^{-1}(\xi,\xi)=
  \frac{(\mu_1-\mu_2)S}{D}.                                             \tag{10}
\]

Polarization over covectors then reconstructs every component of \(g^{-1}\).

## Why one species is insufficient under unknown gain

For one species, measured principal symbol gives only

\[
  \sigma_2(Q_\mu)=\kappa g^{-1}.
\]

The transformation

\[
  \kappa\mapsto c\kappa,\qquad g^{-1}\mapsto c^{-1}g^{-1}
\]

leaves this datum unchanged. A second mass provides the zeroth-order difference `(6)`, fixing
\(\kappa\) independently of the metric.

This is not a claim that one species is insufficient when its amplitude is absolutely calibrated,
or when other calibration data are available. It is the exact removal of the common unknown-gain
ambiguity by two mass labels.

## Physical and novelty boundary

Required hypotheses are load-bearing:

1. both species have the same normally hyperbolic principal part;
2. their distinct pole masses are independently calibrated;
3. source and receiver gains are nonzero multiplication operators and are species-independent, or
   their relative species calibration is known;
4. complete measured Green operators are available on a common support domain;
5. cross-species mixing has been removed or jointly inverted.

If either endpoint gain varies independently by species, two masses do not identify a common
\(\kappa\). If nonminimal couplings differ, \(P_{\mu_1}-P_{\mu_2}\) need not be a pure mass
multiple. These are exact failure modes, not technicalities.

Published detector protocols can, at leading perturbative order and with known trajectories,
recover both real and imaginary parts of a Wightman two-point function
(<https://arxiv.org/abs/1807.00013>). Published nonlinear Einstein--scalar inverse results recover
causal-diamond conformal geometry from controlled sources
(<https://arxiv.org/abs/1406.4776>). Search found no theorem using two distinct relativistic clock
masses to remove a shared unknown source/receiver calibration and then divide the recovered
principal symbol to obtain the full Lorentzian metric. This is a provisional priority statement,
not proof that no collision exists.

The theorem does not yet prove that a backreacting finite laboratory implements complete
\(\widehat G_{\mu_i}\). It closes the exact calibration and conformal-scale obstruction once those
responses are reconstructed.
