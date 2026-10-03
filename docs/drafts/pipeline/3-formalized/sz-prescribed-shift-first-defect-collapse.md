# Actual prescribed-shift parity limits and first-defect collapse

- **ID:** sz-prescribed-shift-first-defect-collapse
- **Stage:** 3-formalized
- **Route:** SZ
- **Type:** THEOREM (Lean)
- **Date:** 2026-10-02
- **Statement:** Both actual V2 parity energies tend to1/4 under common scale c_a exp(-2a); their projective first defect tends to0.
- **Lean status:** Three final leaf audits and all twelve public axiom checks passed.

## Exact positive results

For actual prescribed shift c_a=norm(B_interval,a)+1, actual V2 parameter1,
and t_a=c_a exp(-2a), on the entire positive-aperture atTop filter:

    t_a*(E_a+O_a) -> 1/2,
    t_a*(E_a-O_a) -> 0,
    t_a*E_a -> 1/4,  t_a*O_a -> 1/4,
    suzukiDefectAngle(E_a,O_a) -> 0.

Both apertures independently tending to infinity also gives

    W_ab(I)/(Eraw_b(I)*Eraw_a(I)) -> 0.

These are statements about the literal actual completed covariance and raw
characteristic, with no unproved source or metric hypotheses. The last law
controls the anchor mode only. It does not establish full signed shell
cancellation or identify the entire limiting carrier.

## Dependency-closed paper proof [PROVED HERE]

Let p(x)=exp(x), m(x)=exp(-x), cut off to [-a,a], and let f be the actual
physical raw deficiency at1. The audited actual V2 profile gives

delta_a=norm(f-p/c_a)->0. Its previous squared-error root implies this by
nonnegativity. Literal integration and reflection give

    norm(p)^2=sinh(2a), norm(p),norm(m)<=exp(a), <m,p>=2a.

The exact actual source-response pairing and actual reflection identities give

    S_a=E_a+O_a=Re<p,f>, D_a=E_a-O_a=Re<m,f>.

The audited upper shift bound c_a<=C exp(a), C=norm(kappa)+47, and
Cauchy--Schwarz then imply simultaneously

    abs(t_a S_a-exp(-2a)sinh(2a)) <= C delta_a,
    abs(t_a D_a-2a exp(-2a)) <= C delta_a.

Exact exponential algebra gives
exp(-2a)sinh(2a)=(1-exp(-4a))/2->1/2, while 2a exp(-2a)->0.
Thus t_a S_a->1/2 and t_a D_a->0. Adding/subtracting gives both parity
limits1/4. The actual scale is strictly positive. The existing common-scale
projective consumer therefore yields defect0, with nonzero limiting sum1/2.

The existing exact first-mode Wronskian identity is minus one quarter of the
complexified defect increment. Product-filter convergence gives its limit0
with both apertures independent. No full-current estimate is inferred.

## Corpus and search evidence

Source-uniform inverse/profile inputs: P3:sz-uniform-source-covariance-profile.
Exact source/energy inputs: SuzukiTaV2ActualDefectJet,
CCMRestrictedWeilPolarSourceCancellation, SuzukiMatchedOddMetricTransport.
Projective consumer: SuzukiMovableDefectAnchor. Anchor identity:
CCMSuzukiCrossApertureProjectiveWronskian.

Search1189532: partial, pending coverage, source_only; no proof ideas or
ingredient sets. Candidate interfaces were inspected in source and checked
in Lean. Existing SuzukiNegativeShiftEscape selects shifts for generic
solutions and does not supply this prescribed norm-shift conclusion.
No global absence or novelty claim follows from partial retrieval.

## Exact Lean exports and audits

- SuzukiTaV2PrescribedEnergySource: final66261 passed; exact diagonal Gram,
  negative source norm, both energy source identities, simultaneous scaled
  source-error inequalities.
- SuzukiTaV2PrescribedParityLimit: final2082 passed; actual profile norm limit,
  scaled sum/difference, parity limits and
  `tendsto_suzukiTaV2_prescribed_firstDefect_zero`.
- SuzukiTaV2PrescribedXiSeparation: final13420 passed;
  `tendsto_suzukiTaV2_prescribed_anchorWronskian_zero` and
  `not_exists_suzukiTaV2_prescribed_cofinal_xi_limit`.

Every final command used `lake --old env lean <leaf> -o <leaf.olean>`.
All three leaves are wired once. No full or umbrella build, numerical
experiment, heartbeat increase, new axiom, or subagent. Explicit complex
scalar casts and function-composition unfolding resolved implementation
failures without changing the paper argument. Axiom/lint ledger follows.

## No-go and next hard problem

P5:sz-prescribed-shift-direct-xi-identification records the strict Xi
separation with these nontrivial positive survivors. This does not retire SZ
or falsify RH. P3:sz-prescribed-shift-full-carrier-collapse now proves the stronger
actual carrier classification via mixed exponential pairings and Vitali
identification: the whole upper-half-plane limit is0. Full signed shell/metric cancellation, shift selection
and removal, canonical normalization, Xi identification and RH remain open.

## Final audit ledger

Axiom audit60205 passed for all twelve public theorems. Every dependency list
contains only propext, Classical.choice and Quot.sound. The parity, first-defect,
independent-aperture Wronskian and cofinal-Xi-no-go root signatures were checked
and have no hypothesis binders.

Global lint64122 exits1 on eleven unrelated modules unreachable from their
umbrella: CCMApertureChainProfile, CCMApertureTranslationChains,
CCMExponentialRampPrimeMoment, CCMExponentialRampSourceDissipation,
CCMExponentialRampTerminalEntropy, CCMRetainedChainKernelLower,
MoebiusMollifiedCriticalMoment, MoebiusMollifiedErrorThreeLines,
ThetaCuspCurvatureDefectGrowthSeamOrientation, ThetaMovingShellFirstOrderPhase,
ZetaZeroDensityPowerSaving. No current leaf is among these failures. The global
gate is not green. These unrelated modules were not modified.
