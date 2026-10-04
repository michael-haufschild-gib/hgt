# RN: uniform small-node center Schur residuals

Status: formalized in Lean; unconditional actual-source theorem.
Route: RN. Date: 2026-10-03. Conjecture RN-P-7v succeeded.

## Exact theorem

RHTower.ThetaJoint.exists_actual_ports_pos_triangle proves

    exists epsilon > 0, forall z y : Real,
      0 < z -> z < y -> y < epsilon ->
        0 < ThetaConfluent.sourceResidual z y
        and 0 < ThetaCoordinate.coordinateResidual z y.

Both residuals retain the literal two-node inverse-Gram coefficients of
thetaTailFirstMomentKernel and thetaCuspFullSource. One epsilon covers
every relative approach of the two positive nodes to zero or to each other.
There is no added source, kernel, sign, or RH premise.

## Dependency-closed proof

Write k for the actual source, H for the actual tail kernel,
J=H(0,0), P=k(0)^2, q=c(0), I=integral(t*k_prime^2), and
S=integral(t*k_second^2).

1. For arbitrary Schwartz f,g, establish the actual shifted correlation
   C(f,g;x,y) and weighted kernel K(f,g;x,y). The moving-tail identity

       C(x,y)=C(0,y-x)-integral_0^x f(t)g(y-x+t)dt

   proves joint continuity. Exact left/right differentiation replaces the
   corresponding Schwartz factor by its derivative, adding C for K.
   K(k,k)=H is the literal shift-tail formula.

2. Integration by parts gives the actual origin entries
   H_x=0, H_xx=-2I, H_xy=beta=2I-P, H_xyy=0,
   H_xxyy=2S, H_xyyy=qP-2S.

3. Set T(x,y)=H(x,y)-H(0,x)H(0,y)/J. Its double compact derivative average Q
   satisfies x*y*Q(x,y)=T(x,y) on all real nodes, including both axes.
   Compact weighted averages give continuous partial derivatives and

       Q(0,0)=beta, Q_x(0,0)=Q_y(0,0)=0,
       Q_yx(0,0)=S/2-I^2/J,
       Q_yy(0,0)=(qP-2S)/3.

4. For E=Q/(k(x)k(y)), the exact normalized Hessian is

       E_y(0,0)=0,
       E_yy(0,0)=-2*coordinateEnergy/(3P)<0,
       E_yx(0,0)+E_yy(0,0)=-jointCoordinateCompensation/P<0.

   Both strict source-energy signs were proved in RN-P-7u and its preceding
   coordinate-current certificate. The I^2/J correction is retained.
   Continuity preserves both signs on a joint neighborhood. Integrating first
   along the diagonal makes E_y(z,z)<0; integrating vertically then gives
   E_y(z,y)<0 and E(z,y)<E(z,z). The actual two-point determinant gives
   E(z,z)>0, so the literal coordinate residual equals
   y*k(y)*(1-E(z,y)/E(z,z))>0.

5. Taking x down to zero in the proved diagonal tail comparison gives
   qJ<=P. Since beta=2I-P>0, 2I-qJ>0. The actual source deficit

       g(y)=1-k(0)*H(0,y)/(J*k(y))

   has g(0)=g'(0)=0 and g''(0)=(2I-qJ)/J>0. Local convexity gives
   g(z)>0 and y*g(z)<=z*g(y).

6. The normalized actual projection coefficient d1 satisfies the exact
   identities B_z(y)=k(y)*(y-z*d1) and
   A_z(y)=k(y)*(g(y)-d1*g(z)). The coordinate sign and convex chord inequality
   give the source sign. Intersect the two neighborhoods.

No numerical experiment or approximation is used.

## Lean and audit

Seven leaves, namespace RHTower.ThetaJoint:

- ThetaTailJointCorrelation
- ThetaTailJointCenterJets
- ThetaTailSchurAxisExtension
- ThetaTailNormalizedSchurHessian
- ThetaTailCenterSourceConvexity
- ThetaTailSmallNodeCoordinate
- ThetaTailSmallNodePorts

All targeted lake --old builds passed. All seven final direct
lake env lean GaloisForLFunctions/RHTower/<leaf>.lean audits passed with
empty diagnostics. All seven leaves are wired in the RHTower umbrella;
no umbrella or full build was run.

All 109 public theorem axiom queries passed in /tmp via lake env lean.
Every query returned exactly propext, Classical.choice and Quot.sound.
The capstone's printed type has no extra premises.

scripts/formal_tools.py lint reports twelve unreachable modules outside these
seven leaves: CCMApertureChainProfile, CCMApertureTranslationChains,
CCMExponentialRampPrimeMoment, CCMExponentialRampSourceDissipation,
CCMExponentialRampTerminalEntropy, CCMRetainedChainKernelLower,
MertensProductDiamondPintz, MoebiusMollifiedCriticalMoment,
MoebiusMollifiedErrorThreeLines, ThetaMovingShellFirstOrderPhase,
ZetaZeroDensityPowerSaving, and HTGeometry.CompactMonoidMeasureAlgebra.
It reports no owned-leaf violation.

No added axiom, admitted declaration, heartbeat increase, subagent, numerical
experiment, commit, or push was used.

## Hard frontier remaining

Global finite-pair upper compensation, general anchors, arbitrary-rank
positivity, and transfer to the literal arithmetic RH operator remain open.
The result does not prove RH. The continuing full-pair conjecture and the
complete coarea weighted-current comparison are recorded in
../../1-in-progress/rn-center-schur-coordinate-row-flow.md.

