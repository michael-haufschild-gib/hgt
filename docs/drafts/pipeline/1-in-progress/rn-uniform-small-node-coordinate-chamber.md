# RN: uniform small-node coordinate chamber

Status: raw joint kernel derivatives built; two-axis extension and normalized
Hessian identification under Lean audit.
Previous compensation sign D>0 is audited, not an assumption.

Target: one epsilon>0 such that every 0<z<y<epsilon has both actual
center-anchored Schur residuals positive. Existing fixed-y then z->0
theorems do not supply this uniform triangular region.

## Literal kernel calculus

For Schwartz f,g, use

    C[f,g](x,y)=integral_(t>0) f(x+t)g(y+t),
    K[f,g](x,y)=integral_(t>0) (x+y+2t)f(x+t)g(y+t).

K[k,k]=H exactly. Their partial derivatives replace f or g by its
Schwartz derivative, with the additional C term for K. Joint continuity
can be proved from the moving-tail identity

    C[f,g](x,y)=corr[f,g](y-x)-integral_0^x f(t)g(t+y-x)dt.

This uses the corpus's actual correlation derivative and Mathlib's continuous
parametric interval integral, retaining the moving boundary. No guessed joint
smoothness premise may be inserted into the actual theorem.

At the origin integration by parts gives the exact raw kernel entries
H_x=0, H_xx=-2I, H_xy=beta, H_xyy=0, H_xxyy=2S,
H_xyyy=qP-2S. Definitions are those in the completed joint-center certificate.

## Removing the two axes

T(x,y)=H(x,y)-H(0,x)H(0,y)/J vanishes on both axes. Define its smooth
divided extension Q by the double unit-interval average of T_xy. Then
Q=T/(xy) off the axes, and E=Q/(k(x)k(y)). The center values satisfy

    E_y(0,0)=0,
    E_yy(0,0)=-2*coordinateEnergy/(3P)<0,
    E_yx(0,0)+E_yy(0,0)=-D/P<0.

Continuity preserves both inequalities near the origin. Radial integration
of z*(E_yx+E_yy)+(y-z)*E_yy makes E_y(z,y)<0 for 0<=z<=y small.
Vertical integration gives E(z,y)<E(z,z), proving the actual coordinate port.
The source port follows on a smaller neighborhood from strict increase of
(R(0,0)-R(0,y))/y, whose derivative at zero is (2I-qJ)/(2P)>0.

Equivalent, simpler local propagation proof: first differentiate E_y(t,t).
Its derivative is E_yx+E_yy<0, and its value at zero is zero. Thus
E_y(z,z)<0 for z>0. Then E_yy<0 propagates this inequality vertically
from (z,z) to (z,y), and E_y<0 gives E(z,y)<E(z,z). The corpus's
ClockBivariateChart and Mathlib FDeriv.Partial supply the chain rule from
continuous partial derivatives; no unproved joint differentiability premise
is needed.

Source-port simplification: it is enough to show local convexity of
g(y)=1-R(0,y)/C. Here g(0)=g'(0)=0 and
g''(0)=(2I-qJ)/J>0. Then g(y)>=y*g(z)/z for 0<z<y;
the already strict coordinate coefficient d1<y/z and g(z)>0 give
A(z,y)/k(y)=g(y)-d1*g(z)>0. This avoids a second removable quotient
construction for the source port. The normalized-row second derivative is
obtained from the now available actual firstLeft/secondLeft source jets.

## RN-P-7v current audit checkpoint

New ThetaTailJointCorrelation and ThetaTailJointCenterJets leaves have passed
targeted lake --old builds. They establish joint continuity, literal partial
derivatives, and all six raw origin entries above. Both are wired in RHTower.
ThetaTailSchurAxisExtension has now also passed its targeted build: exact
x*y*Q(x,y)=T(x,y) on all real nodes, continuous partial derivative families,
and origin Q, Q_y, Q_x, Q_yx, Q_yy values are formalized. Two unused simp
arguments were removed and that cleanup passed its dependent build.
All finished leaves are umbrella-wired.
Final direct-file and axiom audits are still pending in this checkpoint.
ThetaTailNormalizedSchurHessian passed its targeted build after replacing an
expensive inferred neighborhood expression by explicit Tendsto statements.
It proves the exact normalized Hessian formulas and their strict negativity
on a joint neighborhood. No heartbeat limit was raised.
The diagonal-then-vertical propagation receiver passed a separate scratch
audit. ThetaTailSmallNodeCoordinate and ThetaTailCenterSourceConvexity have
now passed targeted builds. They establish a uniform coordinate-positive
triangle and the source-deficit chord inequality. The combined
ThetaTailSmallNodePorts theorem passed elaboration apart from a redundant
ring in its projection identity; that tactic is removed and recheck is running.
All final direct-file checks and axiom checks remain pending.

Corpus check found ThetaTailConfluentCoordinateGlobal: it proves the
confluent coordinate residual at every fixed y>0 and eventual actual ports
as z tends to zero. It does not provide the joint triangular region.
Searches were partial/source-heavy; exact applicability is being checked in
Lean. The qJ<=P source comparison can be obtained by taking x down to zero
in ThetaTailTwoPoint.diagonal_tail_lt_source_square, followed by the already
strict centerEntry>0. This is a qualitative source sign, not a numeric bound.

## Scope

Formalize these actual identities and signs without abstract kernel assumptions.
Finite-pair propagation outside the small region, general anchors, arbitrary
rank and arithmetic RH transfer remain open. No RH theorem is claimed here.
