# Backreaction-subtracted two-clock gravity law

- **ID:** `backreaction-subtracted-two-clock-gravity-law`
- **Stage:** 2-fully-proven
- **Type:** THEOREM / CAUSAL RESPONSE / CLOCK PROBE / METRIC RECOVERY
- **Novelty labels:** Schur inversion `[REDISCOVERED]`; coupling-contrast/two-mass composition
  `[CANDIDATE-NEW]`
- **Lean:** `formal/GaloisForLFunctions/HTGeometry/ClockPropagatorSelfCalibration.lean`

## Headline

> **Two clocks can subtract their own disturbance and leave spacetime behind.**

Technical form:

> The coupling-off minus coupling-on inverse response of a local clock probe is exactly the hidden
> retarded target propagator, up to common endpoint factors. Repeating the experiment for two
> distinct clock masses removes those factors and recovers the metric.

## Setup

Work in one fixed retarded or advanced support category for a Green-hyperbolic two-channel
system. Write its operator in block form

\[
  T_\mu=
  \begin{pmatrix}
    P_\mu & R\\
    S & Q
  \end{pmatrix},
  \qquad
  P_\mu=P_0+\mu I.
                                                              \tag{1}
\]

Here \(P_\mu\) is the hidden clock-field operator, \(Q\) is the calibrated probe operator, and
\(R,S\) are compactly supported source/receiver couplings. Let

\[
  G_\mu=P_\mu^{-1},\qquad
  K_\mu=Q-SG_\mu R,\qquad
  H_\mu=K_\mu^{-1}.                                           \tag{2}
\]

All inverses are two-sided on their stated support domains. \(H_\mu\) is the exact probe-to-probe
block of \(T_\mu^{-1}\). No Born expansion or weak-coupling truncation is made.

The measured free and coupled probe responses have common unknown receiver/source gains
\(A,B\):

\[
  \widehat H_{\rm off}=A Q^{-1}B,\qquad
  \widehat H_{\mu,\rm on}=A H_\mu B.                          \tag{3}
\]

## Theorem 1: exact finite-coupling block response

The exact two-sided inverse of `(1)` is

\[
  T_\mu^{-1}=
  \begin{pmatrix}
    G_\mu+G_\mu R H_\mu S G_\mu & -G_\mu R H_\mu\\
    -H_\mu S G_\mu & H_\mu
  \end{pmatrix}.                                               \tag{4}
\]

### Proof

Put \(G=G_\mu\), \(H=H_\mu\), and \(K=Q-SGR\). The hypotheses are

\[
  PG=GP=I,\qquad KH=HK=I.                                     \tag{5}
\]

Multiplying `(1)` by the right side of `(4)` gives the four blocks

\[
\begin{aligned}
  &P(G+GRHSG)+R(-HSG)=I,\\
  &P(-GRH)+RH=0,\\
  &S(G+GRHSG)+Q(-HSG)=SG-(QH-SGRH)SG=0,\\
  &S(-GRH)+QH=(Q-SGR)H=I.
\end{aligned}                                                  \tag{6}
\]

Multiplication in the opposite order gives

\[
\begin{aligned}
  &(G+GRHSG)P+(-GRH)S=I,\\
  &(G+GRHSG)R+(-GRH)Q=GR-GR(HQ-HSGR)=0,\\
  &(-HSG)P+HS=0,\\
  &(-HSG)R+HQ=H(Q-SGR)=I.
\end{aligned}                                                  \tag{7}
\]

Thus `(4)` is a two-sided inverse. In particular, its probe block is exactly \(H_\mu\).
\(\square\)

## Theorem 2: exact backreaction subtraction

Define the measured inverse-response contrast

\[
  \mathcal D_\mu
  :=
  \widehat H_{\rm off}^{-1}
  -
  \widehat H_{\mu,\rm on}^{-1}.                              \tag{8}
\]

Then

\[
  \boxed{
  \mathcal D_\mu
  =
  B^{-1}S\,G_\mu\,R A^{-1}.}                                 \tag{9}
\]

### Proof

Endpoint inversion reverses the gains:

\[
  \widehat H_{\rm off}^{-1}=B^{-1}QA^{-1},\qquad
  \widehat H_{\mu,\rm on}^{-1}
  =B^{-1}(Q-SG_\mu R)A^{-1}.                                 \tag{10}
\]

Subtracting the second equality from the first cancels \(Q\) exactly and gives `(9)`.
\(\square\)

Equation `(9)` includes every repeated target--probe exchange already resummed into \(H_\mu\).
The subtraction is therefore exact for the linear coupled system, at finite coupling. It is not a
claim that nonlinear gravitational backreaction has disappeared.

## Corollary: two masses recover the metric

Set

\[
  U=B^{-1}S,\qquad V=RA^{-1}.
\]

Then `(9)` is precisely an endpoint-dressed hidden Green operator:

\[
  \mathcal D_\mu=U G_\mu V.                                  \tag{11}
\]

Assume \(U,V\) are invertible on the observed source/receiver subspaces and are common across two
distinct calibrated squared masses \(\mu_1\ne\mu_2\). Its measured inverse is

\[
  \mathcal D_\mu^{-1}=V^{-1}(P_0+\mu I)U^{-1}.                \tag{12}
\]

Therefore

\[
  \boxed{
  \mathcal D_{\mu_1}^{-1}-\mathcal D_{\mu_2}^{-1}
  =
  (\mu_1-\mu_2)V^{-1}U^{-1}.}                                \tag{13}
\]

The mass difference reconstructs the endpoint-calibration product. The principal symbol of either
side of `(12)` is that product times \(g^{-1}\); division by `(13)` recovers the full inverse
metric. Polarization recovers all off-diagonal metric components. Equality of the resulting
complete source/metric graphs is equivalent to equality of an arbitrary nonlinear continuum
gravity law by the already proved self-calibrating continuum rigidity theorem.

## Operational bridge

Bär's Green-hyperbolic support theorem gives uniqueness of retarded/advanced Green operators in
the fixed support class:
<https://arxiv.org/abs/1310.0738>. Fewster and Verch construct an exact local QFT measurement
scheme for two scalar fields coupled in a compact spacetime region and identify the coupled
probe response through the exact Green operator of the block system:
<https://arxiv.org/abs/1810.06512>.

A complete family of compact probe drives and separating clock readouts determines the bilinear
kernel of \(\widehat H\). Continuous Ramsey phase germs remove the \(2\pi\) branch ambiguity.
Equations `(8)`--`(13)` then turn clock-only probe data into the hidden clock propagators required
by the two-mass metric theorem.

## Hostile novelty audit

1. Block inversion, Schur complements, Dyson resummation, and self-energy subtraction are standard
   and are not claimed new.
2. Exact local QFT probe measurement for coupled linear scalar fields is due to Fewster--Verch.
3. Inverse propagators differing by a mass term is standard field-theory algebra.
4. Candidate novelty is the dependency-closed operational composition:
   coupling-on/off inverse contrast produces a common-dressed hidden causal propagator; two masses
   self-calibrate that dressing; the calibrated principal symbol recovers the metric; complete
   source/observation graphs recover the nonlinear continuum law.
5. No searched primary source states this complete two-stage reconstruction or its
   hypertranscendental null test. This is a priority-audit result, not proof of global novelty.

## Load-bearing hypotheses and kill conditions

1. Target and probe form a linear Green-hyperbolic block system on one common support domain.
2. Complete complex probe responses, not only intensities or poles, are available.
3. Coupling-on and coupling-off runs share endpoint gains.
4. Coupling maps are invertible, or at least separating, on the recovered subspace.
5. Two target species share \(P_0,R,S,A,B\) and differ only by calibrated \(\mu I\).
6. Gauge constraints and conservation laws permit a separating source/readout family.
7. The theorem includes target--probe backreaction exactly but not metric backreaction from the
   apparatus. If that nonlinear backreaction cannot be independently scaled, modelled, or
   reconstructed, the universal gravity claim remains open.

## Hypertranscendence falsifier

Within the common local single-metric model, `(13)` is a zeroth-order endpoint product. If the
endpoint/coupling model is differentially algebraic, a derivative-supported, off-diagonal,
nonlocal, or hypertranscendental two-clock inverse residual falsifies at least one of locality,
single-metric propagation, common coupling, common calibration, or minimal mass shift.

## Status

Paper proof of exact algebra is complete. Remaining physical core:

1. recover complete \(\widehat H_\mu\) from finite compact clock interventions with quantified
   stability;
2. replace invertible compact couplings by a realistic separating family;
3. incorporate conservation-constrained gauge-invariant sources;
4. control genuine nonlinear gravitational backreaction of probe apparatus;
5. prove the clock-only nonlinear causal-diamond reconstruction theorem.
