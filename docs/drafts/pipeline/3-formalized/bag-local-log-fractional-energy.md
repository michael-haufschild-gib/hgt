# BAG compact logarithmic fractional energy

2026-10-06, 01ax. Dependency-closed paper proof and complete scratch audits.
Scalar scratch73895/log08 PASS; planar scratch81332/log01 PASS.
Final production60539/log02 emptyPASS. All three production public axiom
prints35000/log01 PASS, standard3 only(propext,Classical.choice,Quot.sound).
LocalLogFractionalEnergy518lines/API3; final index94569PASS, API3 confirmed,
importonce at HTGeometry:16678. Scoped diffcheckPASS. Final lint22415/log02
terminal1:362warnings,12 unrelated unreachable modules, no ownedleaf finding.
Global lint not clean. Unreachable: KuznetsovEisensteinTransform;
Sieve.TwistedSelbergCoefficient,Factorization,Forms,GcdLog,Summability;
ThetaCuspRatioKineticClockReduced;ThetaCuspRatioKineticContraction;
HTGeometry.ResetBilateralDilation,ResetHasseExecutionDefect,ResetMarkovExecution,
ResetPathSingularity. Prior scalar-only lint93688/log01 had14 unrelated errors.

For every0<s<1 and fixed0<a,b, one C>0 works for every continuous complex
function f supported in[a,b]:
 E_s(f(exp(-u))) <= C*(E_s(f)+integral |f|^2).
All energies are nonnegative Lebesgue integrals, so no unproved admission
is implicit. Physical E_s uses negative translations; the log energy uses
positive translations. The exact directional Gagliardo/Fourier theorem
then proves finiteness and a bound by physical L2 mass plus weighted
Fourier energy for every supported Schwartz function.

The planar theorem applies uniformly to every continuous f supported in
[a,b]^2. For the first log axis, with the other log coordinate integrated,
its full fractional energy is bounded by C times the physical first-axis
fractional energy plus physical mass, integrated in the other physical
coordinate. Exchanging coordinates gives the identical second-axis result.
There is no assumed slice-energy, Jacobian, interchange, or norm budget.

Proof. Nonnegative one-dimensional Jacobian change of variables, first
x=exp(-u), then y=x*exp(-h), gives the exact two-point kernel
 |f(x)-f(y)|^2*(-log(y/x))^(-1-2s)/(xy), 0<y<x.
Forh<=1, any nonzero difference has at least one point in[a,b], forcing
both points into[A,B]=[a/exp(1),exp(1)*b]. The elementary log inequality
-log(y/x)>=(x-y)/x>=(x-y)/B and xy>=A^2 imply domination by
(B^(1+2s)/A^2)*|f(x)-f(y)|^2*(x-y)^(-1-2s).
Enlarge to all ordered physical pairs, use y=x-h, and apply nonnegative
Tonelli. This gives the physical negative-direction fractional energy.
Forh>1, the squared difference is at most twice each squared value.
Translation invariance and the admitted rpow tail reduce this part to
pullback mass, which is at most1/a times physical mass. The exact near/far
partition closes the full estimate; no prior finiteness is used.

For two coordinates, apply the scalar theorem to each physical slice.
Its complete physical fractional-energy-plus-mass function vanishes when
the transverse coordinate is outside[a,b]. The second nonnegative log
substitution therefore costs at most1/a. This pays the transverse Jacobian
without requiring a slice-integrability premise or a uniform Schwartz bound.

Route contribution: closes the scalar and unweighted planar fractional
log-chart mechanism needed by BAG's actual moving physical kernels.
Still open: uniform compact weighted multiplication, first Euler derivative
transfer for1<s<3/2, actual exterior attachment, Mellin line tails,
lower-growth arithmetic envelope, moving-test cancellation, full sharp-action
bridge, growing moments/cofactors and deterministic common-height return.
No RH proof and no identification of positive cone pairing with full action.
