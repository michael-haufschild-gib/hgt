# Exact finite-clock translation moment of the literal HB source

- **ID:** HB-FIXED-ONSET-TRANSLATION-MOMENT
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** At every unchanged complex rate and every source-independent nonnegative clock step, the full original scalar source has a determined resonant translation mass; its retained derivative-contact pulse has zero translation mass, and the two actual wave images retain the original source mass.

## Exact source identity

Let chi=Real.smoothTransition, v∈C and h≥0. Both v and the original time coordinate remain fixed. Define

    Delta_h^v f(u) = f(u+h)-exp(vh)f(u),
    M_h^v(f) = integral_{-h}^1 exp(-vu) Delta_h^v f(u) du,
    S_{A,B}(u) = [A chi(u)+B chi'(u)]exp(vu).

The proved identities are

    exp(-vu) Delta_h^v S_{A,B}(u)
      = exp(vh){A[chi(u+h)-chi(u)]+B[chi'(u+h)-chi'(u)]},
    M_h^v(S_{A,B}) = h exp(vh) A.

These are actual finite integrals. The compact temporal support of the difference follows from the original transition endpoints. There is no evaluation of a divergent transform at v, no numerical experiment and no frequency renormalization. A and B may be arbitrary complex spatial coefficients. The theorem adds no source regularity, equation, covariance, extinction or RH premise.

For the original onset S_v=chi exp(vu), M_h^v(S_v)=h exp(vh). In particular Delta_1^v S_v is never the zero function, including at rates belonging to critical-line occurrences. Raw fixed-onset covariance therefore differs from covariance of centered spectral packets.

## Proof

Cancel the two exponential factors algebraically. For the chi term, translation changes its integral over [-h,1] to the integral over [0,1+h]. The common [0,1] interval cancels. The remaining integral on [-h,0] is zero, and that on [1,1+h] is h.

For chi', the fundamental theorem of calculus gives one on both intervals: chi(1+h)-chi(0)=1 and chi(1)-chi(-h)=1. Their difference is zero. Continuity of chi and chi' supplies every finite-integral admission. Multiplying by the constant coefficients gives the exact formula, also at h=0. At h=1 the onset moment is exp(v), which never vanishes; a zero difference function would have zero moment, a contradiction.

## Literal source and wave-image specializations

At fixed tortoise coordinate x and original angular point z, use ingoing time u=t+x and set v=2 physicalRate(q,branch). The actual source is

    F(t,x,z)=A(x,z) chi(u)exp(vu),

where A is exactly `originalForcing` with both `fullSquarePotential` and `fullGradientEnergy/2` retained. Hence

    M_h^v(u ↦ F(u-x,x,z)) = h exp(vh) A(x,z).

The complete original onset pulse has the form

    P(t,x,z)=B(x,z) chi'(u)exp(vu),
    B=-2 sourceSeedFieldFirst · fullAngularField
      +2 alpha radialLiftFirst · fullSquarePotential.

Both angular profiles remain present. Consequently M_h^v(P)=0.

The established actual source equation is

    alpha L U-L V = alpha F-P,

with U=`timeLiftField`, V=`timeAngularSeedField`, alpha=`parameter`, and L=`timeFieldWave`, retaining actual time, tortoise and angular derivatives. Substitution into the same two-coefficient source theorem proves

    M_h^v(alpha L U-L V) = h exp(vh) alpha A(x,z).

No presumed Green response, angular eigenprofile replacement or adjoint boundary cancellation enters this proof.

## Lean declarations

Module: `GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMFixedClockSourceTranslation`.
Namespace: `RHTower.D4BMSourceClockTranslation`.

- `sourceAndContact_clockDifference`
- `sourceAndContact_clockMoment`
- `timeOnset_clockMoment`
- `timeOnset_unitClockDifference_ne_zero`
- `timeOriginalForcing_clockMoment`
- `fullSourceOnsetPulse_clockMoment`
- `waveImages_clockMoment`

The definitions `clockDifference`, `clockMoment` and `sourceAndContact` specify actual functions and finite integrals.

## Scope and surviving extinction problem

This closes a source-level temporal balance, not the complete nonlinear action. It proves neither nonvanishing nor vanishing of the actual radial/angular left-QNM moment. The complete SS/SV/VV correction fields, spin-two action projection, metric-dependent pairing and horizon/cusp/characteristic/source-contact flux must still be assembled. No scalar temporal test is identified with that physical functional by definition.

The [active extinction card](../1-in-progress/hb-fixed-clock-source-translation.md) records the full corrected mixed coefficient, all nine independent radiative channel pairings, the exact Green-boundary interface and the signed estimate that would imply extinction through existing clock-defect transduction. None is assumed in this module. RH remains unproved.

The positive result exposed by the failed zero-contact guess is an exact source mass invariant under arbitrary addition of the derivative-contact channel. No HB route is retired.

## Verification

- Foreground `lake env lean /tmp/hb-fixed-clock-translation.lean`: PASS, no warnings.
- Exact `lake build GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMFixedClockSourceTranslation`: PASS, 47 seconds, two jobs and no warnings. A temporary one-leaf Lake package reused the twelve existing dependency cache search roots; only the new leaf was registered for compilation. Its source was byte-identical to the installed canonical source. The canonical olean/ilean were produced by this build and imported successfully in the subsequent audit.
- New-only `#print axioms` through foreground `lake env lean /tmp/hb-clock-axioms.lean`: all seven public theorems use only `propext`, `Classical.choice`, `Quot.sound`.
- `scripts/formal_tools.py index`: PASS; public entries verified in `LEAN_API.md`.
- `scripts/formal_tools.py lint`: PASS, with existing large-file warnings elsewhere.
- Owned-file whitespace and unique import checks: PASS.
- One new RHTower umbrella import; no umbrella/full build.
- No owned Lean/Lake process remained after verification. Temporary scratch and audit files removed after recording results.

Source SHA-256: `11ce72bfe2eae71ce1610be20b54f9f6c14459494c7f12d5828d386565aa812a`.
