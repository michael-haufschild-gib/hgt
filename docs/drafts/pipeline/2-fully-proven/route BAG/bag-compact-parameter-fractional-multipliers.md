# BAG compact parameter fractional multipliers

2026-10-06,01ax. Dependency-closed paper proof and Lean production closure.
HTGeometry.FractionalCompactMultiplier269lines/API3. Complete scratch64419/
log05 PASS/all3 axiomprints standard3; production26654/log01 emptyPASS;
all3 imported production axiomprints29266/log01 standard3 only; index17064
PASS/API3; HTGeometry importonce at16679; scoped diffcheckPASS.
Lint49753/log01 terminal1:362warnings,15 unrelated unreachable modules,
no ownedleaf finding. Global lint not clean. Unreachable:
KuznetsovEisensteinTransform; Sieve.TwistedSelbergCoefficient,Factorization,
Forms,GcdLog,Summability; ThetaCarrierResetDilation;
ThetaCuspRatioKineticCoefficients10,6,8; HTGeometry.KMSGibbsDensityExecutionEntropy,
ResetBilateralDilation,ResetHasseExecutionDefect,ResetMarkovExecution,
ResetPathSingularity. Logs /tmp/bag-fractional-compact-multiplier-*01ax.log.

For every0<s<1, compact C1 coefficient A on a finite-dimensional real
Euclidean space, and directionv, one constant bounds the full directional
fractional energy of A*f by fractional energy of f plus L2 mass for every
continuous f. No integrability or coefficient-norm budget is assumed.
For a jointly compact C1 coefficient A(parameter,x), the same conclusion
has ONE constant for EVERY parameter value. The Schwartz corollary gives
finite energy with a uniform bound by actual weighted Fourier energy and
physical L2 mass.

Proof. Expand the complete difference as
 A(x)*(f(x)-f(y))+(A(x)-A(y))*f(y).
The squared norm is at most twice each squared term. Compact C1 data derive
both a global coefficient bound M and a Lipschitz constant L. The first
term is bounded by2*M^2 times input difference energy. For y=x+h*v, the
increment term is bounded by an explicit scalar remainder:
 L^2*|v|^2*h^(1-2s) on(0,1], and4*M^2*h^(-1-2s) on(1,infinity).
Both are admitted by native rpow integrability for0<s<1. Nonnegative
integration and translation invariance reduce the complete remainder to
an admitted scalar integral times input mass. No energy finiteness is used
before this estimate. Joint compactness supplies the same M,L for every
parameter slice; equal-parameter product distance is exactly physical
distance. DirectionalGagliardoFourier then gives the spectral corollary and
finiteness for Schwartz inputs.

Route contribution: closes the missing fractional multiplier mechanism,
including uniformity for joint compact data. Actual Mellin parameter/cutoff
coefficients must still be constructed and shown jointly compact smooth;
first Euler derivative transfer, actual exterior attachment and full Mellin
line tails remain open. Further BAG hard problems: lower-growth completed
arithmetic envelope, moving-test cancellation/full original sharp-action
bridge, growing moments/cofactors and deterministic common-height return.
RH remains open; generic uniform multiplication is not the full transfer.
