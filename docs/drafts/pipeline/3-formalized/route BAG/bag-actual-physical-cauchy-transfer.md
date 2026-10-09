# BAG actual physical and localized Mellin Cauchy transfer

- **Stage:** 3-formalized

2026-10-06,01ax. Dependency-closed paper proof and production closure.
ChiCubicSelectedPhysicalConvergence225lines/API2, public167/200.
Scratch71682/log02terminal0 bothpublics standard3. Production97119/log01
emptyPASS withlake --old env lean andexplicit leaf olean. Both imported
axioms73599/log01standard3. Index68204/log01PASS/API2; RHTimportonce23599;
scoped diffcheckPASS. No admissions, new axioms or resource increases.
Authoritative lint93037/log01terminal1:362warnings21unrelatedunreachable,
noownedfinding. Global lint is NOT clean. Exact errors:
- error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.KuznetsovUniformBounds
- error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.Sieve.TwistedSelbergCoefficient
- error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.Sieve.TwistedSelbergFactorization
- error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.Sieve.TwistedSelbergForms
- error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.Sieve.TwistedSelbergGcdLog
- error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.Sieve.TwistedSelbergGcdLogForms
- error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.Sieve.TwistedSelbergRatioForms
- error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.Sieve.TwistedSelbergSummability
- error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.VerticalProgressionClassLimits
- error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.VerticalProgressionFarey
- error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.VerticalProgressionOffResonance
- error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.VerticalProgressionRatioFibers
- error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.VerticalProgressionRatioForm
- error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.VerticalProgressionResonantBounds
- error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.VerticalProgressionResonantCount
- error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.VerticalProgressionResonantSmall
- error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.RHTower: GaloisForLFunctions.RHTower.VerticalProgressionSecondMomentExpansion
- error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.HTGeometry: GaloisForLFunctions.HTGeometry.ComplexMeasurePairing
- error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.HTGeometry: GaloisForLFunctions.HTGeometry.MultiplicativeConvolutionDomain
- error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.HTGeometry: GaloisForLFunctions.HTGeometry.PermutationAveragedFirstFailure
- error: owned module unreachable from theorem-area umbrella GaloisForLFunctions.HTGeometry: GaloisForLFunctions.HTGeometry.PositiveIntervalConvolutionDomain

Logs /tmp/bag-physical-cauchy-*01ax.log andscratch01–02retained.

First theorem: for EVERY0<=s<3/2 andepsilon>0 there isR such that ANY two
real parametersN,M>=R give weighted Fourier energy of the exact difference
f_N-f_M at mostepsilon. Heref_N is the literal selected normalized original
physical cone, with cutoffwidthN^(1/4), relativewidthN^(-3/4), heightwindow
[1,2] andnormalization(logN)^3/N. No stationary profile or Schwartz limit
is assumed. The public statement quantifies the actual family itself.

Second theorem: for EVERY0<theta<1/2 andepsilon>0, oneR gives the same
Cauchy bound at order1+theta after applying the complete localized Mellin
operator to f_N-f_M, uniformly over ALLq in[1,2]^2. The operator constant
is the previously proved parameter-uniform actual localization constant.
There is no analytic uniformity premise and no change to the physical cutoff.

Proof. The corpus already proves strong weightedL2 convergence of the
selected reciprocal kernel K_N toward the sharp reciprocal kernel Ksharp,
including admission of every error integral. Use Ksharp only as a common
comparison center. Pointwise,
|K_N-K_M|²<=2(|K_N-Ksharp|²+|K_M-Ksharp|²).
Both complete weighted error integrals tend to zero for every0<=s<3/2.

The exact ordinary Fourier identity is
Fourier(f_N)(xi)=kappa*K_N(kappa*xi0,kappa*xi1), kappa=2*pi,
with the literal curved reciprocal parameter(1/kappa)/N retained. The
frequency weight grows underkappa>=1. Squared amplitude contributeskappa²;
two exact one-dimensional dilation formulas cancel both factors. Exact
Euclidean/product volume transport turns the resulting integral into the
already admitted reciprocal errors. Choosing both errors small proves the
actual physical Cauchy bound. No equality involving a non-admitted totalized
error integral is used.

For localization, apply the existing complete H^(1+theta) operator bound to
the Schwartz inputf_N-f_M and the physical Cauchy bound at the same order.
Its constant is independent ofq. This pays the first term in
local(q_N,f_N)-local(q0,f_M)=local(q_N,f_N-f_M)
 +local(q_N,f_M)-local(q0,f_M).

Hard frontier: fixed-input Mellin parameter continuity must pay the second
term. Then compare the literal moving test to one fixed late Schwartz test
using the closed complete arithmetic pairing operator and signed fixed-test
law, retaining both2*pi frequency Jacobians. The complete actual exterior
pairing already vanishes. Full original sharp-action bridge, growing
moments/cofactors/common-height return and RH remain open.

## Lean certificate (2026-10-08 promotion audit)

Every claim of this card was re-read against the public statements below; each statement
is unconditional (structural domain subtypes only, no analytic or arithmetic premise).

| Module | Public theorems |
|-|-|
| `GaloisForLFunctions.RHTower.ChiCubicSelectedPhysicalConvergence` | `bagCubicSelectedNormalizedCone_energy_cauchy`, `bagCubicSelectedNormalizedCone_uniform_local_mellin_cauchy` |

- `lake env lean <module source>`: every module above compiles with no errors (2026-10-08).
- Axiom audit: every declaration of these modules (643 declarations across the 83 BAG modules)
  depends only on `propext`, `Classical.choice`, `Quot.sound`; no `sorryAx`.
- Each module is imported exactly once in its area umbrella (`RHTower.lean` / `HTGeometry.lean`).
- Open targets recorded on this card (route-level obligations, RH) are not claimed.

## Log (promotion)

- 2026-10-08 — promotion audit passed; moved from `2-fully-proven/route BAG` to `3-formalized/route BAG`.
