# RN: Gaussian coarea and the actual center Schur cross term

Status: paper proof and all three Lean leaves complete; targeted builds, final direct-file
audits, and all34 public theorem axiom checks passed on 2026-10-02.
This is an intermediate actual finite-pair inequality, not RH, full finite-pair
coordinate residual positivity, or a principal three-node determinant theorem.

Target, for the literal theta source k and full-tail first-moment kernel H:

    H(0,x) H(0,y) < H(0,0) H(x,y),  x,y>0.

It makes the actual coefficient of the positive old node in the center-anchored
two-node inverse-Gram projection strictly positive. The remaining coordinate
port requires an upper bound on that coefficient, not merely this lower bound.

## Corpus inputs

The actual p=-(log k)' satisfies p(0)=0, p'=c>0, c'>0 on the
positive ray, and c''>0. These are already unconditional. The common-translation
representation of H and Schwartz integrability are already formalized.
The current global confluent coordinate theorem controls only the derivative
of the desired finite-pair comparison at the center.

## Paper proof

Let U=-log k. For x,y>=0 and u>0 define

    L=sqrt((x+y)^2+4u), t=(L-x-y)/2,
    s=x+t, r=y+t,
    V(x,y,u)=U(s)+U(r)-U(x)-U(y).

Then t>0, t(t+x+y)=u, du=(x+y+2t)dt, and

    R(x,y)=H(x,y)/(k(x)k(y))=integral_0^infinity exp(-V(x,y,u)) du.

The exact mixed derivative is

    V_xy = -u [L(c(s)+c(r))-2(p(s)+p(r))]/L^3 < 0.

Indeed strict convexity of c gives 2p(v)<v(c(0)+c(v)) for v>0;
c(s),c(r)>=c(0) then give strict positivity of the displayed bracket.
Integrating V_xy over [0,x]x[0,y] yields

    D=V(0,x,u)+V(0,y,u)-V(0,0,u)-V(x,y,u)>0.

Put w(u)=exp(-V(0,0,u)) and A_x(u)=exp(V(0,0,u)-V(0,x,u)).
Both A_x and A_y strictly decrease in u. For this, at x>=0 let
s=(sqrt(x^2+4u)-x)/2, r=(sqrt(x^2+4u)+x)/2. Then

    V_u(0,x,u)=(p(s)+p(r))/(s+r),
    derivative_x V_u(0,x,u)
      =[(s+r)(r c(r)-s c(s))-(r-s)(p(s)+p(r))]/(s+r)^3 >0

for x>0. The numerator is positive because p(s)+p(r)<(s+r)c(r)
and r c(r)-s c(s)>(r-s)c(r). Thus V_u(0,x,u)>V_u(0,0,u).
All V(x,y,0)=0, so 0<A_x<=1. The products below are integrable
by domination by w and the already integrable actual kernel density.

Strict submodularity gives pointwise

    exp(-V(x,y,u)) > w(u) A_x(u) A_y(u).

The same-direction covariance inequality, proved by integrating
w(s)w(t)(A_x(s)-A_x(t))(A_y(s)-A_y(t))>=0, gives

    (integral w)(integral w A_x A_y)
      >= (integral w A_x)(integral w A_y).

Combine these with the exact coarea identities and integral w=R(0,0)>0.
Multiplication by positive source factors proves the target.

## Scope and next hard step

This proof retains an actual integral and its positive covariance; no pointwise
sign of the original Schur derivative integrand is asserted. It does not prove
E_y<0 for E=(R(x,y)-R(0,x)R(0,y)/R(0,0))/(xy). The strict coefficient
upper bound, and eventually arbitrary-rank compensation and arithmetic transfer,
remain open. Do not claim the kernel is totally positive: local mixed logarithmic
derivatives need not have the same sign as this center-anchored cross minor.

## Formal certificate

Namespace: `RHTower.ThetaGaussianCoarea`.

- `ThetaTailGaussianCoarea.lean`: exact coarea identity and actual density integrability.
- `ThetaTailGaussianSubmodular.lean`: strict potential submodularity, decreasing bounded
  center amplitudes, and strict product-density comparison.
- `ThetaTailCenterSchurCross.lean`: `center_schur_cross_pos` and
  `positive_node_coefficient_pos`, retaining the complete positive covariance.

Each leaf passed its targeted `lake --old build GaloisForLFunctions.RHTower.<leaf>`
and final `lake env lean GaloisForLFunctions/RHTower/<leaf>.lean` check.
A separate /tmp scratch file queried all34 public theorem axioms: only
`propext`, `Classical.choice`, and `Quot.sound`. No proof diagnostics remain.
All three leaves are wired into RHTower. No full or umbrella build was run.

Repository lint reports no violation in these leaves. Its11 unrelated reachability
errors at this audit were:
- `CCMApertureChainProfile`
- `CCMApertureTranslationChains`
- `CCMExponentialRampPrimeMoment`
- `CCMExponentialRampSourceDissipation`
- `CCMExponentialRampTerminalEntropy`
- `CCMRetainedChainKernelLower`
- `MoebiusMollifiedCriticalMoment`
- `MoebiusMollifiedErrorThreeLines`
- `RoutePNativeNegativeCoprimeWork`
- `ThetaMovingShellFirstOrderPhase`
- `ZetaZeroDensityPowerSaving`


## Arbitrary-anchor extension (2026-10-02)

The source-dependent amplitude and covariance proofs now apply above every
nonnegative anchor a: H(a,x)H(a,y)<H(a,a)H(x,y) for a<x and a<y.
The center capstones remain as specializations. Both modified leaves and all29
of their public theorem axiom checks passed the new audit. The current certificate
is `rn-gaussian-coarea-arbitrary-anchor.md`; the upper coordinate-port bound
remains open.
