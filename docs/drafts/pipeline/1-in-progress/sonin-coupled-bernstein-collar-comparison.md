# Sonin-coupled Bernstein collar comparison

## Claim

Let \(m=(m_j)_{j\ge 0}\) be the endpoint-normalized prime--Gamma
moment sequence, and let
\[
  \Pi_n=\sum_{j=0}^n \binom{n}{j}^2
    \bigl((-1)^{n-j}\Delta^{n-j}m_j\bigr)^2
\]
be its degree-\(n\) Bernstein square energy.

For a nondegenerate aperture \(a\), let \(C_a\) be the actual all-prime
coupled Sonin column, put \(T_a=C_a^*C_a\),
\(M_a=\operatorname{Tr}(T_a)>0\), and define the normalized spectral
moment sequence
\[
  q_a(k)=\frac{\operatorname{Tr}(T_a^{k+1})}{M_a^{k+1}}.
\]
Write
\[
  Q_{a,n,j}=\binom{n}{j}(-1)^{n-j}\Delta^{n-j}q_a(j),
  \qquad
  D_{a,n}=\sum_{j=0}^n
    \left(\binom{n}{j}(-1)^{n-j}\Delta^{n-j}m_j-Q_{a,n,j}\right)^2.
\]

Then the following comparison is the target theorem:
\[
  \boxed{\Pi_n\le 2+2D_{a,n}\quad\text{and}\quad
         D_{a,n}\le 2\Pi_n+2.}
\]
Consequently,
\[
  \forall\varepsilon>0\ \exists C_\varepsilon>0\ \forall n,
  \quad \Pi_n\le C_\varepsilon(1+\varepsilon)^n
\]
if and only if the same estimate holds for \(D_{a,n}\). Equivalently,
the collar statement \(R_A=1\) is reduced to zero exponential density of
the concrete coupled-Sonin Bernstein mismatch.

## Status

**In progress.**

- `[PROVED ON PAPER]` The spectral sequence \(q_a\) is a Hausdorff
  moment sequence: it is the moment sequence of the spectral probability
  measure of the density operator \(T_a/M_a\), supported in \([0,1]\).
- `[PROVED ON PAPER]` Its Bernstein coefficients are nonnegative, sum to
  one, and therefore have square energy at most one.
- `[PROVED ON PAPER]` The two displayed inequalities follow coefficientwise
  from \((x+y)^2\le 2x^2+2y^2\).
- `[OPEN CORE]` Prove subexponential growth of \(D_{a,n}\) from the coupled
  Sonin source itself. No collar, RH, or endpoint susceptibility assumption
  may be used in this step.
- `[FORMALIZATION]` Formalize the Hausdorff source law and the two-sided
  Bernstein energy comparison in Lean.

## Proof

Because \(T_a\ge0\) is trace class and
\(M_a=\operatorname{Tr}(T_a)>0\), the operator
\(\rho_a=T_a/M_a\) is a density operator. Its spectrum is contained in
\([0,1]\): every eigenvalue is nonnegative and no eigenvalue exceeds their
sum. The probability measure
\[
  \nu_a=\sum_\lambda \lambda\,\delta_\lambda
\]
therefore satisfies
\[
  q_a(k)=\int_{[0,1]}x^k\,d\nu_a(x).
\]
For every \(0\le j\le n\),
\[
  Q_{a,n,j}
  =\int_{[0,1]}\binom nj x^j(1-x)^{n-j}\,d\nu_a(x)\ge0,
\]
and the Bernstein partition of unity gives
\(\sum_{j=0}^n Q_{a,n,j}=1\). Hence
\(\sum_jQ_{a,n,j}^2\le1\).

If \(P_{n,j}\) denotes the endpoint coefficient in the definition of
\(\Pi_n\), then \(P_{n,j}=(P_{n,j}-Q_{a,n,j})+Q_{a,n,j}\). Summing
\((u+v)^2\le2u^2+2v^2\) gives
\(\Pi_n\le2D_{a,n}+2\). Conversely,
\(P_{n,j}-Q_{a,n,j}=P_{n,j}+(-Q_{a,n,j})\), so
\(D_{a,n}\le2\Pi_n+2\).

The pointwise two-sided estimates preserve subexponential growth. The
constant sequence \(2\) is absorbed into the admissible constant for every
base \(1+\varepsilon>1\).

## Novelty gate

`[BRIDGE]` The Hilbert-space fact that density-operator moments are
Hausdorff moments is standard and is not claimed as new mathematics.

`[CANDIDATE NEW INSIGHT]` The exact two-sided Bernstein-energy comparison
uses the actual coupled all-prime Sonin operator and identifies a concrete,
quantitative source discrepancy that is equivalent to the collar estimate.
This is stronger than a one-way condition implying RH, but it does not prove
the open discrepancy bound.

The claim must not be promoted to new scientific knowledge until the
literature audit rules out an equivalent source-mismatch formulation and the
open core is materially advanced.

## Significance gate

The comparison is significant as a reduction only if the coupled operator
provides independent control of \(D_{a,n}\). Without such control it is a
precise localization of the obstruction, not a proof of \(R_A=1\).

## Dependencies

- `formal/GaloisForLFunctions/RHTower/SoninCoupledPrimeArchGramTransfer.lean`
- `formal/GaloisForLFunctions/RHTower/PrimeArchBernsteinPurityDivergence.lean`
- `formal/GaloisForLFunctions/RHTower/PrimeArchHausdorffBernsteinKMSRH.lean`
