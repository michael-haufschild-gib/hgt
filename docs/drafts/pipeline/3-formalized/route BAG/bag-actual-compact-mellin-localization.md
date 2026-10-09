# BAG actual compact Mellin localization and Euler coefficients

- **Stage:** 3-formalized

2026-10-06,01ax. Dependency-closed paper proof and Lean production closure.
CompactMellinLocalization343lines/API21. Complete scratch30497/log06 PASS;
production56153/log01 emptyPASS; all21 imported public declaration axioms
10859/log01 standard3 only; index75708 PASS; HTGeometry importonce16680;
scoped diffcheckPASS. Lint30292/log01 terminal1:362warnings,18 unrelated
unreachable modules, no ownedleaf finding. Global lint not clean. Exact
unreachable modules: RHTower.KuznetsovExplicitIdentity;
Sieve.TwistedSelbergCoefficient,Factorization,Forms,GcdLog,GcdLogForms,Summability;
ThetaCarrierResetDilation; ThetaCuspRatioKineticBlockCoefficients10,4,6,8;
ThetaCuspRatioKineticDegree; HTGeometry.KMSGibbsDensityExecutionEntropy,
ResetBilateralDilation,ResetHasseExecutionDefect,ResetMarkovExecution,
ResetPathSingularity. Logs /tmp/bag-compact-mellin-localization-*01ax.log.

Construct fixed physical chi, smooth and compactly supported in(1/8,8)^2,
identically1 on an OPEN neighborhood of the complete stationary box[1/4,4]^2.
Construct fixed compact smooth parameter eta, identically1 near[1,2]^2.
The literal joint coefficient is
 A(sigma,x)=eta(sigma)*chi(x)*exp(sigma0*log(x0)+sigma1*log(x1)).
Its exact agreement with the weighted physical cutoff holds for EVERY
parameter in[1,2]^2, at EVERY physical point. On tsupport chi, both coordinates
are strictly positive, giving joint smoothness by the log/exp chain rule.
Outside tsupport chi, the complete coefficient is locally zero; this proves
smoothness across both axes without differentiating a singular log there.
Its joint support lies in tsupport eta times tsupport chi, hence is compact.

The actual first Euler coefficients are
 B_i(sigma,x)=-xi*D_(0,e_i) A(sigma,x),
 C_i(sigma,x)=-xi*A(sigma,x).
Native derivative support and compactness show B_i,C_i are jointly smooth
and compact, supported inside the same positive physical region. The proved
compact-parameter fractional multiplier theorem gives ONE bound independent
of parameter and input for each of A,B_i,C_i. It includes admitted fractional
energy and the exact physical Fourier-energy/mass bound. Joint compactness
also gives the separate uniform nonnegative L2 mass estimate.

For G_(sigma,f)(u)=A(sigma,exp(-u))*f(exp(-u)), the full first derivative is
 D_i G(u)=B_i(sigma,exp(-u))*f(exp(-u))
          +C_i(sigma,exp(-u))*D_i f(exp(-u)).
The actual derivative of the log node, both product terms and the joint
parameter/physical derivative are retained. For sigma in[1,2]^2, G agrees
exactly with exp(-sigma dot u)*chi(exp(-u))*f(exp(-u)). The existing positive-
line logarithmic Schwartz theorem applied to the proved compact physical
localization gives an exact Schwartz realization of G; the same Euler law
is attached to that Schwartz object. This membership asserts no uniform
Schwartz seminorm bound.

Route contribution: constructs the actual coefficient family and first
Euler identities required to turn the closed fractional chart/multiplier
bounds into uniform log H^(1+theta) energy. That full energy assembly and
actual exterior attachment remain open, as do Mellin line tails,
lower-growth arithmetic envelope, moving-test cancellation/full sharp-action
bridge, growing moments/cofactors and deterministic common-height return.
RH remains open. No positive-cone/full-original-action identification.

## Lean certificate (2026-10-08 promotion audit)

Every claim of this card was re-read against the public statements below; each statement
is unconditional (structural domain subtypes only, no analytic or arithmetic premise).

| Module | Public theorems |
|-|-|
| `GaloisForLFunctions.HTGeometry.CompactMellinLocalization` | `mellinLocalizationCutoff_spec`, `compactMellinCoefficient_smooth`, `hasCompactSupport_compactMellinCoefficient`, `compactMellinCoefficient_eq`, `compactMellinEuler_coefficients`, `compactMellinEuler_support`, `compactMellinJetCoefficient_spec`, `compactMellinJetCoefficient_uniform_fractional_energy`, `compactLocalizedMellinProfile_eq`, `compactLocalizedMellinProfile_euler`, `compactMellinJetCoefficient_support`, `compactMellinJetCoefficient_uniform_mass`, `compactLocalizedMellinSchwartz_apply`, `compactLocalizedMellinSchwartz_euler` |

- `lake env lean <module source>`: every module above compiles with no errors (2026-10-08).
- Axiom audit: every declaration of these modules (643 declarations across the 83 BAG modules)
  depends only on `propext`, `Classical.choice`, `Quot.sound`; no `sorryAx`.
- Each module is imported exactly once in its area umbrella (`RHTower.lean` / `HTGeometry.lean`).
- Open targets recorded on this card (route-level obligations, RH) are not claimed.

## Log (promotion)

- 2026-10-08 — promotion audit passed; moved from `2-fully-proven/route BAG` to `3-formalized/route BAG`.
