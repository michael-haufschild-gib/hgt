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

- `[FORMALIZED]` The spectral sequence \(q_a\) satisfies the complete
  Hausdorff hierarchy.  Every complementary finite difference is an
  explicit Hilbert--Schmidt square of the actual coupled Sonin master effect.
- `[FORMALIZED]` Its Bernstein coefficients are nonnegative, sum to one,
  and therefore have square energy at most one.
- `[FORMALIZED]` The two displayed inequalities and the exact unit-collar
  equivalence hold without a residual Hausdorff hypothesis.
- `[FORMALIZED]` The mismatch is the Bernstein purity of the logarithmic
  derivative coefficients of the normalized endpoint/Sonin relative
  determinant defect.
- `[OPEN CORE]` Prove subexponential growth of \(D_{a,n}\) from the coupled
  Sonin source itself. No collar, RH, or endpoint susceptibility assumption
  may be used in this step.

## Normalized determinant refinement

Let
\[
  \ell_m(k)=\frac{m_k}{k+1},\qquad
  \ell_a(k)=\frac{q_a(k)}{k+1}.
\]
The second sequence is the coefficient sequence of the positive logarithmic
exponent of the trace-normalized degree-one Fredholm determinant germ
\[
  \Delta_a(z)=\det{}_1\!\left(I-\frac{z}{M_a}T_a\right).
\]
Define the relative logarithmic-derivative coefficient sequence
\[
  r_a(k)=(k+1)(\ell_m(k)-\ell_a(k))=m_k-q_a(k).
\]
Linearity of the moment functional gives the exact identity
\[
  \boxed{D_{a,n}=\sum_{j=0}^n
    \operatorname{Bern}_{n,j}(r_a)^2.}
\]
Consequently the unit collar is equivalent to a subexponential Bernstein
purity envelope for the logarithmic derivative of this concrete normalized
relative determinant defect.

The germ \(\Delta_a\) is a product of exponentials and never vanishes.
Therefore multiplying an endpoint determinant by \(\Delta_a\) cannot change
its zero divisor.  A successful determinant argument must control the
relative logarithmic derivative above; zero cancellation by the positive
density determinant is unavailable.

## Literature calibration and the Connes determinant boundary

Connes--Consani--Moscovici's semilocal prolate construction proves stability
of the Sonin spaces and develops the semilocal prolate operator, but does not
state a Bernstein-purity collar estimate or the relative logarithmic-derivative
identity above:

- <https://arxiv.org/abs/2310.18423>

Their later spectral-triple construction uses a different determinant.  It is
the phase-bearing regularized determinant of a rank-one perturbation of the
scaling operator; its zeros are the real spectrum of that self-adjoint
operator.  The paper proposes convergence of suitably normalized determinants
to the Riemann \(\Xi\) function and explicitly lists the operator/determinant
convergence as a missing step:

- <https://arxiv.org/abs/2511.22755>

Thus the nonvanishing positive-density germ \(\Delta_a\) cannot substitute for
the Connes--Consani--Moscovici determinant.  Its correct role is the Hausdorff
reference term in the relative logarithmic derivative.  The phase-bearing
rank-one determinant is the candidate that must supply the endpoint comparison.

`[CONJECTURE]` Let \(\mathcal D_{\lambda,N}\) be the normalized regularized
determinants of the rank-one perturbed scaling operators.  A proof of a
cutoff-uniform Hardy/Gutzmer bound, after the Bernstein Möbius pullback, for
\[
  \partial_z\log \mathcal D_{\lambda,N}(z)
  -\partial_z\log \Delta_a(z)
\]
that survives the cofinal \((\lambda,N)\)-limit would imply the required
subexponential envelope for \(D_{a,n}\), hence the unit collar.  Compact-open
convergence alone is insufficient for this step; the bound must be uniform in
the pulled two-torus norm that recovers Bernstein purity.

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

`[FORMALIZED BRIDGE]` The Hilbert-space fact that density-operator moments
are Hausdorff moments is standard and is not claimed as new mathematics.

`[CANDIDATE NEW INSIGHT]` The exact two-sided comparison and determinant-defect
identity use the actual coupled all-prime Sonin operator and identify a
concrete relative logarithmic derivative whose Bernstein purity is equivalent
to the collar estimate.  This is stronger than a one-way condition implying
RH, but it does not prove the open discrepancy bound.

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
- `formal/GaloisForLFunctions/HTGeometry/QuantumReplicaHausdorff.lean`
- `formal/GaloisForLFunctions/RHTower/SoninCoupledQuantumHausdorff.lean`
- `formal/GaloisForLFunctions/RHTower/SoninCoupledBernsteinCollarQuantumDischarge.lean`
- `formal/GaloisForLFunctions/RHTower/SoninCoupledNormalizedDeterminantCollar.lean`
