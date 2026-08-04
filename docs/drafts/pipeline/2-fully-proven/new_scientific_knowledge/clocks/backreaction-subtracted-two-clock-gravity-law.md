# Backreaction-subtracted two-clock gravity law

- **ID:** `backreaction-subtracted-two-clock-gravity-law`
- **Stage:** 2-fully-proven
- **Type:** THEOREM / CAUSAL RESPONSE / CLOCK PROBE / METRIC RECOVERY
- **Novelty labels:** Schur inversion `[REDISCOVERED]`; coupling-contrast/two-mass composition
  `[CANDIDATE-NEW]`
- **Lean modules:**
  `formal/GaloisForLFunctions/HTGeometry/ClockPropagatorSelfCalibration.lean`,
  `formal/GaloisForLFunctions/HTGeometry/ClockPrincipalSymbolCalibration.lean`,
  `formal/GaloisForLFunctions/HTGeometry/ClockLocalityDistributionKernel.lean`,
  `formal/GaloisForLFunctions/HTGeometry/ClockBackreactionTwoMass.lean`,
  `formal/GaloisForLFunctions/HTGeometry/ClockResponseIdentifiability.lean`,
  `formal/GaloisForLFunctions/HTGeometry/ClockResponseStability.lean`,
  `formal/GaloisForLFunctions/HTGeometry/ClockConservationConstrainedDrives.lean`,
  `formal/GaloisForLFunctions/HTGeometry/ClockApparatusBackreaction.lean`,
  `formal/GaloisForLFunctions/HTGeometry/ChronometricCausalDiamond.lean`

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

### Lean status of the corollary

`formal/GaloisForLFunctions/HTGeometry/ClockBackreactionTwoMass.lean` composes the chain
`(11)`--`(13)` into one theorem, so the corollary is proved rather than assembled by the reader:

- `measuredClockInverse_eq_endpointDressedInverse` — the measured inverse of a species *is* the
  endpoint-dressed mass-shifted operator, so `(12)` is a definitional identity once the dressings
  are named;
- `measuredClockInverse_isTwoSided_backreactionSubtracted` — that element is the two-sided inverse
  of the coupling-off/coupling-on contrast `(8)` of the same species, at finite coupling;
- **`backreactionSubtracted_twoMass_calibration`** — both species' contrasts are inverted, and the
  difference of the inverses, divided by the calibrated mass difference, is exactly the
  endpoint-calibration product `V⁻¹U⁻¹` of `(13)`.

Axioms: `[propext, Classical.choice, Quot.sound]`.

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

### Lean status of the operational bridge

The identifiability half of the bridge — that a complete family of probe drives and a separating
family of clock readouts determines the measured response operator, and with invertible endpoints
the hidden one — is formalized in
`formal/GaloisForLFunctions/HTGeometry/ClockResponseIdentifiability.lean`:

- `SeparatingReadouts`, `eq_of_separatingReadouts`, `separatingReadouts_dual` — a readout family
  separates responses when only the zero response is invisible to all of it; the full continuous
  dual always does, by Hahn--Banach;
- **`responseOperator_eq_of_data`** — two response operators agreeing on every (drive, readout)
  pair are equal, provided the drives span a dense subspace;
- **`hiddenResponse_eq_of_data`** — the same for the hidden response behind unknown endpoint gains:
  an injective receiver and a surjective source suffice, with no calibration of either.

- **`hiddenResponse_eq_of_family_data`** — invertible couplings are not needed: a *family* of
  couplings that jointly separates responses, with drives whose images span a dense subspace, does
  the same job. This is load-bearing hypothesis 4 of this card in its realistic form.

The quantitative half is `formal/GaloisForLFunctions/HTGeometry/ClockResponseStability.lean`:

- `NormingReadouts`, `NormingDrives` — the two families control, respectively, the norm of a
  response and the operator norm; `normingReadouts_dualBall` and `normingDrives_unitBall` prove the
  canonical families do so with constant `1`, so the hypotheses are inhabited;
- **`responseOperator_norm_sub_le_of_data`** — data agreeing to within `ε` force
  `‖T - S‖ ≤ C_drive C_readout ε`;
- `norm_le_of_dressed_norm` — a receiver bounded below and a bounded right inverse of the source
  convert a bound on the dressed operator into one on the undressed operator;
- **`hiddenResponse_norm_sub_le_of_data`** — hence
  `‖T - S‖ ≤ c⁻¹‖right‖ C_drive C_readout ε` for the hidden response.

So the reconstruction is not merely unique: it is Lipschitz in the data, with an explicit constant
built from the apparatus. What is still open is physical — that a finite compact intervention set is
norming, and that noise stays inside `ε`. Axioms: `[propext, Classical.choice, Quot.sound]`.

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
   stability — both halves are now proved (`hiddenResponse_eq_of_data`,
   `hiddenResponse_norm_sub_le_of_data`); what remains is physical, that a finite compact
   intervention set is norming and that noise stays inside the tolerance;
2. replace invertible compact couplings by a realistic separating family — proved
   (`hiddenResponse_eq_of_family_data`);
3. incorporate conservation-constrained gauge-invariant sources — proved that the constraint costs
   nothing (`responseOperator_eq_of_conservationBalanced_data`): with a clock coframe the
   conservation-balanced sources exhaust the source space
   (`conservationBalancedClockSourceWithSignal_bijective`), so the constrained drives span exactly
   what the unconstrained ones span;
4. control genuine nonlinear gravitational backreaction of probe apparatus — the exact algebra of
   this is now proved (`formal/GaloisForLFunctions/HTGeometry/ClockApparatusBackreaction.lean`):
   `measuredClockInverse_difference_geometry_independent` — the calibration channel does not mention
   the geometric operator, so **any** species-common perturbation of the geometry, the apparatus's
   own backreaction included, leaves the reconstructed calibration untouched;
   `ScalarSecondOrderOperator.twoMassPrincipalSymbol_reconstruction_perturbed` — the symbol channel
   returns the symbol of the operator actually present, that is, the backreacted geometry, shifted
   from the undisturbed one by exactly the symbol of the perturbation (`principalSymbol_add`), so
   backreaction is *measured*, not an error; `measuredClockInverse_difference_species_geometry` and
   `exists_measuredClockInverse_difference_ne` — a *species-dependent* perturbation, by contrast,
   enters the residual as its dressed difference, and that failure is not vacuous. What remains
   physical is whether a given apparatus perturbs the two species identically;
5. prove the clock-only nonlinear causal-diamond reconstruction theorem — the *kinematic* half is
   formalized in `formal/GaloisForLFunctions/HTGeometry/ChronometricCausalDiamond.lean`:
   `SmoothPseudoMetric.eqOn_of_properTime_eqOn` localizes proper-time determination to an arbitrary
   region (the argument is pointwise in the event, so it claims nothing outside);
   `coneFuture`, `conePast`, `coneDiamond` are the coordinate diamond, and
   `mem_coneDiamond_segment` shows the timelike segment joining the tips lies inside it, so the
   region a clock can traverse is not empty; **`eqOn_coneDiamond_of_properTime`** — clocks agreeing
   at every event of the diamond determine the metric at every event of the diamond. What is still
   open is the *dynamical* half: that clock-only sources realize the required variations inside the
   diamond, which is where the nonlinear interaction analysis lives.

## Gates

- [x] 0 → 1: exact coupling contrast and two-mass reconstruction chain stated
- [x] 1 → 2: all eight Schur inverse equations, backreaction subtraction, dressed inverse,
  calibration cancellation, and metric-symbol recovery proved on paper
- [x] 2 → 3: noncommutative block algebra, exact two-sided inverse bridge, literal local
  second-order principal-symbol recovery, diagonal distribution kernels, continuum polarization,
  and nonlinear graph rigidity formalized unconditionally and axiom-audited
- [ ] 3 → 4: finite experimental recovery, gauge/control, stability, and priority audit

## Log

- 2026-08-01 — added exact Lean bridge proving that the coupling-off/on contrast has the
  oppositely dressed hidden operator as a two-sided inverse; connected it to literal two-mass
  principal-symbol and distribution-kernel infrastructure.
