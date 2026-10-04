# SZ: signed ramp flux and its surviving phase

- **ID:** SZ-RAMP-SIGNED-FLUX
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean); leaf and all public axiom audits passed
- **Source:** CCMPrimeDeficitFluxBalance, CCMPrimeDeficitWeilFlux,
  WeilLagFunctionOmega, ChebyshevDeficitPrimitiveOneSidedRH.
- **Target:** The literal normalized deficit and full ramp action have both
  signs cofinally, separated from zero by a fixed positive threshold.

## Why this addresses the current attempt

The complete centered-age identity is A+D=AgeForce+Entropy. Eventual
dominance of either side would force one sign of A. Deciding this candidate
requires the signed action, not another absolute energy bound. This does
not decide uniform boundedness of A or canonical-head Weil positivity.

## Dependency-closed paper proof

Write I=e^(-T/2)P(T), S for the actual deficit flux state, and O=S-I.
The corpus proves S'=O-S/2 and O=Phi+r for T>0, where Phi is the full
Weil lag and |r(T)|<=C e^(-T/2).

Under RH the full multiplicity-copy lag series has coefficients
w_q=1/(1/4+gamma_q^2)>0, with summable mass. Define

    a_q = w_q/(1/2+i gamma_q),
    H(T) = sum_q a_q exp(i gamma_q T),
    B(T) = Re H(T)-Phi(T).

Both a_q and i gamma_q a_q are absolutely summable (bounded by a
constant times w_q). Termwise differentiation gives H'+H/2=Phi.
The integrating factor therefore gives

    |S(T)-Re H(T)| <= (C0+C*T)e^(-T/2),  T>=1.

Hence I-B tends to zero. B is a continuous almost-periodic real function
with Bohr mean zero. The source-proved zero-height gap gives w_q<1,
so Re H(0)=(1/2)sum w_q^2 <= (1/2)sum w_q and B(0)<0.
Zero-mean uniqueness forces B to take a positive value too. Almost periods
recur cofinally, giving fixed positive and negative thresholds for B and I.
The ramp transient T e^(-T/2) tends to zero, preserving both thresholds.

If RH fails, either eventual finite one-sided bound on I extends over its
compact initial interval and invokes the existing one-sided RH theorem,
a contradiction. This discharges RH in the final oscillation statement.

The complex transfer coefficient for I is
(1/2-i gamma)/(1/2+i gamma), of modulus one. Filtering retains every
frequency and multiplicity; it does not destroy the phase needed by SZ.

## Audits and scope

- Corpus searches: signed-lag and imaginary-boundary queries were partial
  and mostly source-only. The Bohr derivative search completed with full
  inventory at generation1221048; compiler coverage remained mostly
  pending/stale. Source inspection, not search rank, determines applicability.
- No numerical experiments, RH hypothesis in the final target, added axioms,
  full builds, or subagents.
- Leaf47925 and axiom/API97972 exited0. All9 public declarations use only propext, Classical.choice and Quot.sound. The narrow no-go and positive survivor are closed.
- Canonical-head Gamma--prime--polar sign remains OPEN.

## Log

- 2026-10-04: selected after centered-age identities alone supplied no sign.
  Completed scratch34264 passed. Final leaf47925 passed after removing two tactic warnings.

## Lean declarations and audit

Module: `formal/GaloisForLFunctions/RHTower/CCMPrimeDeficitBohrFlux.lean`.

The final premise-free statements are
`ccmPrimeDeficitIncoming_omega_pm` and
`ccmActualTimeExponentialRampAction_omega_pm`. The six other proof/definition
components construct the complete stable state and its signed model;
`norm_ccmPrimeDeficitBohrIncoming_coeff` proves the exact coefficient
modulus law. Intermediate model/limit theorems explicitly assume RH;
the final oscillation theorems discharge that assumption by cases.

Final foreground leaf check (exit0, no diagnostics):

    lake --old env lean GaloisForLFunctions/RHTower/CCMPrimeDeficitBohrFlux.lean -o .lake/build/lib/lean/GaloisForLFunctions/RHTower/CCMPrimeDeficitBohrFlux.olean

Exactly one umbrella import, no umbrella/full build. No numerical
experiment, heartbeat override, added axiom, subagent, or commit.
The nine public declarations include three definitions and six theorems.

Lint37688 exited1; diagnostics were truncated by the tool, so89207 reran
with both output streams captured and exited1. It reported16 unrelated
unreachable modules, none in this new leaf:

- `GaloisForLFunctions.RHTower.CCMApertureChainProfile`
- `GaloisForLFunctions.RHTower.CCMApertureTranslationChains`
- `GaloisForLFunctions.RHTower.CCMExponentialRampPrimeMoment`
- `GaloisForLFunctions.RHTower.CCMExponentialRampSourceDissipation`
- `GaloisForLFunctions.RHTower.CCMExponentialRampTerminalEntropy`
- `GaloisForLFunctions.RHTower.CCMRetainedChainKernelLower`
- `GaloisForLFunctions.RHTower.MertensProductDiamondPintz`
- `GaloisForLFunctions.RHTower.MoebiusMollifiedCriticalMoment`
- `GaloisForLFunctions.RHTower.MoebiusMollifiedErrorThreeLines`
- `GaloisForLFunctions.RHTower.RoutePCausalBiasTransfer`
- `GaloisForLFunctions.RHTower.RoutePFinitePrimeCovariance`
- `GaloisForLFunctions.RHTower.RoutePPrimeCovarianceBudget`
- `GaloisForLFunctions.RHTower.ThetaCuspC5IntrinsicGreenRecovery`
- `GaloisForLFunctions.RHTower.ThetaMovingShellFirstOrderPhase`
- `GaloisForLFunctions.RHTower.ZetaZeroDensityPowerSaving`
- `GaloisForLFunctions.HTGeometry.CompactMonoidMeasureAlgebra`

Final axiom/API audit97972 exited0. All9 declarations reported only
`propext`, `Classical.choice`, `Quot.sound`; no custom axiom or sorryAx.
The preceding99392 run already printed the same9 axiom results, then
failed two ancillary unqualified Filter API checks. Qualifying those
names fixed the audit; production proofs were unchanged.

Cleanup: all9 exact owned temporary files removed after every owned
process terminated. Audited leaf olean retained. Unique umbrella import
and targeted whitespace checks passed. RH remains unresolved; goal active.
