# RN: finite-center-pair coordinate row flow

Status: next source-specific conjecture after the global confluent transfer.
The full finite-pair coordinate-port sign remains open; Schur cross lower signs are proved below.

Corpus basis: ThetaTailFirstMomentKernel, ThetaTailOrderedRowMonotonicity,
ThetaTailConfluentCoordinatePort, ThetaTailConfluentCenterLimits, and the
new canonical-current/transport leaves. The deep finite-pair search was
partial (semantic timeout and reranking deadline; coverage pending).
Existing normalized-row and mixed-row hits were inspected. A hit on the
new unbuilt global residual file is source text, not validation evidence.

Put K=k(0), R(x,y)=H(x,y)/(k(x)k(y)), h(y)=R(0,y), C=R(0,0), and

    G(z,y)=R(z,y)−h(z)h(y)/C,
    E(z,y)=G(z,y)/(zy),                 z,y>0,
    N(y)=H_x(0,y)/(yKk(y)).

Actual two-node determinant positivity gives E(z,z)>0. Retaining the
literal inverse-Gram coefficients gives the exact algebraic identity

    B_z(y)=y k(y)[1−E(z,y)/E(z,z)].

Therefore the coordinate residual is positive precisely when
E(z,y)<E(z,z). Conjecture: E_y(z,y)<0 for 0<z≤y. This is stronger than
the required comparison, and a failure would not refute RH or B_z>0.
The completed confluent argument supplies the boundary E(0,y)=N(y),
with N'(y)<0 by the audited global transport identification.

## Exact paper flow and the remaining sign

The literal common-shift integral H(x,y)=∫₀∞(x+y+2t)k(x+t)k(y+t)dt
gives H_x+H_y=−(x+y)k(x)k(y). Consequently

    h'=p h−y(1+N),
    (∂z+∂y)E=(p(z)+p(y)−1/z−1/y)E+F(z,y),
    F=[(1+N(z))h(y)/C−1]/y+[(1+N(y))h(z)/C−1]/z.

For Γ=E_y the prospective first-zero barrier has forcing

    (c(y)+1/y²)E
      +(1+N(z))h'(y)/(Cy)
      +[1−(1+N(z))h(y)/C]/y²
      +N'(y)h(z)/(Cz).

The boundary Γ(0,y)=N'(y)<0 alone does not determine that forcing.
The next hard task is an actual compensated sign law for this complete
expression, retaining E and the full negative-current integral producing
N'. Do not replace it with signs of isolated summands, arbitrary source
coefficients, or uniform convexity of normalized kernel rows (already
obstructed in the corpus).

Sharper next conjecture: at any actual contact Γ(z,y)=0 with 0<z<y,
the displayed forcing is strictly negative. Every characteristic y−z=d>0
starts from the now controlled boundary Γ(0,d)=N'(d)<0. A proved contact
law would exclude its first zero, hence give Γ<0 throughout the open
ordered chamber. Continuity at y=z would then give E(z,y)<E(z,z) for
every y>z. No strict diagonal derivative or uniform coalescent radius is
needed. The contact condition must be retained as the actual integral
identity when proving the source compensation; the PDE alone is only a
receiver for that missing mathematical law.

The common-shift differential identities above are paper deductions from
the literal integral, with Schwartz differentiation and boundary decay;
they are not yet a separate Lean flow theorem. A finite-pair proof would
still leave general anchors, arbitrary rank, and the arithmetic RH transfer.

## Gaussian coarea successor (2026-10-02)

The unconditional contact forcing sign is not adopted: a large-spacing expansion
suggests it can be positive while E_y remains negative. This is a diagnostic
paper observation, not an audited asymptotic theorem. The contact identity must
remain in any first-contact proof.

Direct double-integral symmetrization of the E_y comparison also exposes a
strictly negative diagonal contribution. It cannot be closed by declaring the
original symmetrized integrand nonnegative. Three-translate Wronskian control
was examined, but no implication from its source sign to the full inverse-Gram
compensation has yet been established.

A different exact change of variables, u=t(t+x+y), yields a dependency-closed
paper proof of

    H(0,x)H(0,y) < H(0,0)H(x,y), x,y>0.

The proof retains the actual kernel, strict submodularity of its coarea
potential, and a nonnegative covariance of two decreasing center amplitudes.
See `../3-formalized/theta/rn-gaussian-coarea-center-schur.md` for the proof and
audit certificate. All three leaves (`ThetaTailGaussianCoarea`,
`ThetaTailGaussianSubmodular`, `ThetaTailCenterSchurCross`) passed targeted
builds, final direct-file checks, and all34 public standard-axiom audits.

This is a global finite-pair lower bound on the actual positive-node projection
coefficient. The coordinate port still needs its strict upper bound. The new
positive covariance must be retained when differentiating the center Schur
comparison; dropping it would remove part of the compensation problem.


## Next coupled-current attack

Use the audited definitions V, density and amplitude. With C=R(0,0), let
mu have probability density exp(-V(0,0,u))/C and put

    F_xy=exp(V(0,0,u)-V(x,y,u)),
    B_xy=F_xy-A_x A_y > 0.

The exact paper decomposition is

    G(x,y)/C = expectation_mu(B_xy) + covariance_mu(A_x,A_y).

Both terms are positive/nonnegative, but their y-derivatives require compensation.
The original hard target E_y<0 becomes the coupled inequality

    y*d_y[expectation(B_xy)+covariance(A_x,A_y)]
      < expectation(B_xy)+covariance(A_x,A_y), 0<x<y.

Do not delete the covariance derivative or assume it has favorable sign. The
base potential Q(u)=2U(sqrt(u))-2U(0) has
Q''(u)=(sqrt(u)*c(sqrt(u))-p(sqrt(u)))/(2*sqrt(u)^3)>0.
A corpus search found `HTGeometry.OneDimBrascampLieb.double_integral_kernel`
and `variance_le_integral_deriv_sq_div_curvature` in OneDimBrascampLieb.lean,
and `HTGeometry.integral_Ioi_mul_halfLineSteinScore_with_boundary` in
HalfLineSteinRobertson.lean. The full-line theorem's hypotheses do not apply
by zero extension: the actual half-line density is nonzero at0. Retain its
endpoint term. The source and derivative integrability premises must be proved
for the actual amplitudes before applying a generic receiver.

The same search found the explicit remainder obstruction in
OneDimBrascampLiebCorrection.lean: subtracting a first Popescu correction
from a variance upper bound requires vanishing of the retained nonnegative
resolvent remainder. That subtraction is NOT an available upper bound.
Search metadata was partial (reranking incomplete), full inventory coverage,
compiler metadata mostly pending/stale; source statements above were inspected.
No new variance or coordinate-port upper theorem is claimed here.


## Joint-center diagnostic (2026-10-02; paper calculation only)

Testing E_y<0 along y=x requires more than the audited fixed-y coalescent
limit. Put P=k(0)^2, I=ThetaConfluent.derivativeMass,
J=H(0,0), S=ThetaCoordinate.secondMass, q=c(0). Expanding the actual
kernel and its full center Schur subtraction on paper gives

    E(x,y)=beta/P - coordinateEnergy/(3P)*(x^2+y^2)
             +(S/2-I^2/J)/P*x*y + higher order,
    E_y(x,x)/x -> [-S/6+2qI-2qP/3-I^2/J]/P.

The x*y term must retain the I^2/J inverse-Gram correction. Thus the
strong monotonicity conjecture requires at least

    S/6-2qI+2qP/3+I^2/J >= 0.

The compensation sign is now strictly positive in Lean: see
`../3-formalized/theta/rn-joint-center-coordinate-compensation.md`.
The joint kernel derivatives, smooth axis-divided Schur extension, and exact
normalized Hessian identification are now formalized in ThetaTailJointCorrelation,
ThetaTailJointCenterJets, ThetaTailSchurAxisExtension and
ThetaTailNormalizedSchurHessian. Targeted builds and their final direct-file
audits passed. The full Taylor-remainder assertion is unnecessary: continuous
Hessian signs and integration along the diagonal and then vertically give the
uniform triangle. The actual source identities H_xy=beta, H_xx=-2I,
H_xyyy=qP-2S and H_xxyy=2S are all proved directly from Schwartz correlations.
No numerical test was used, and no failure of the stronger conjecture is claimed.

## Finite-pair successor after the uniform center triangle

The local gap is closed by
ThetaTailSmallNodePorts.exists_actual_ports_pos_triangle. All seven final
direct-file audits and all109 public standard-axiom queries passed. Certificate:
../3-formalized/theta/rn-uniform-small-node-coordinate-chamber.md. Do not spend the next research step on compact
uniformity receivers or improving an epsilon. The hard target remains the
full source-specific finite-pair compensation.

The coarea conjecture can be written without deleting the covariance. Keep
Q(u)=V(0,0,u), probability density exp(-Q)/C,
F_xy=exp(Q-V(x,y,u)), A_x=exp(Q-V(0,x,u)), and put

    L_xy(u)=[1+y*partial_y V(x,y,u)] F_xy(u).

Then the exact prospective derivative identity is

    -x*y^2*E_y(x,y)/C
      = expectation(L_xy)-expectation(A_x)*expectation(L_0y).

Conjecture: this complete signed quantity is positive for every 0<x<y.
This is the same genuine upper-comparison obligation in a form suited to
source transport. Establish actual integrability/differentiation when proving
it; the identity is paper-only at this checkpoint. Potential submodularity
alone gives F_xy>A_x*A_y while making partial_y V(x,y,u) smaller than
partial_y V(0,y,u), so it does not compare the weighted currents L.
Retain both effects. The existing secant-feedback theorem has the adverse
orientation secant(0,z,0)<feedback(0,z); it cannot supply a missing feedback
upper bound. Corpus searches checked these statements and found no global
upper producer. No new global sign is claimed.


## Arbitrary-anchor lower sign closed (2026-10-02)

The coarea amplitude proof now retains the nonnegative anchor-curvature term
and proves H(a,x)H(a,y)<H(a,a)H(x,y) for every 0<=a<x and a<y.
The larger-node projection coefficient is therefore positive at every such
anchor. `ThetaTailGaussianSubmodular` and `ThetaTailCenterSchurCross` passed
both targeted builds, final direct-file checks, and all29 public standard-axiom
queries. Certificate: `../3-formalized/theta/rn-gaussian-coarea-arbitrary-anchor.md`.
This is a lower sign; no full coordinate-port upper bound is supplied.

## RN-P-7w: complete current transport diagnostic (2026-10-03)

Status: research in progress; no new global inequality or Lean theorem claimed.
The completed local theorem does not supply global three-node positivity, so
Cauchy–Schwarz for the center Schur kernel would assume a still-open input.

Retain W(x,y)=R(x,y)-y*R_y(x,y). The target is exactly

    C*W(x,y)-h(x)*W(0,y)>0, 0<x<y.

The coarea weighted interaction and covariance must be controlled together.
For a paper diagnostic at mass u=0, put

    m(x,y)=(p(x)+p(y))/(x+y), q=c(0).

For positive endpoints, V_u(x,y,0)=m(x,y). Hence the coefficient of u in
L_xy-A_x*L_0y is

    kappa(x,y)=-q+m(0,x)+m(0,y)-m(x,y)
                 +y*(m_y(x,y)-m_y(0,y)).

Extend m(0,x)=p(x)/x smoothly to q at x=0 using the actual even source.
Then direct differentiation gives

    kappa_x(0,y)=(3*p(y)-y*c(y)-2*q*y)/y^2.

This isolates a source-dependent sign; submodularity alone does not pay it.
Writing K(y)=3*p(y)-y*c(y)-2*q*y and using the actual corpus definition of
ThetaRadial.radialDefect gives the exact paper relation

    K(y)-y*K'(y)=ThetaRadial.radialDefect y,
    (K(y)/y)'=-ThetaRadial.radialDefect y/y^2.

The corpus proves that radialDefect is negative near zero and positive
eventually. This does not by itself determine K everywhere or the integrated
current sign. No unproved far-tail expansion or pointwise-current no-go has
been promoted to a theorem. Next attack: a source-potential transport of the
complete signed current, retaining its covariance and endpoint contribution,
rather than assigning separate favorable signs to those terms.

Searches: the broad deep query was non-partial but returned mostly unrelated
weighted-covariance statements. The Theta-filtered query was partial, with
complete source inventory and predominantly pending/stale compiler metadata;
it recovered the actual massRate derivative and anchored Schur lower theorem,
not the missing upper sign. Proposed ingredient sets were not accepted as
proofs. Sources inspected include ThetaTailGaussianSubmodular,
ThetaTailCenterSchurCross, ThetaCoordinateCrossCurrent,
ThetaCuspCurvatureLogConvex and ThetaRadialSourceCurvature.

## RN-P-7x: global finite-pair positive primitive — 2026-10-03

The literal primitive O_x(t)=H(0,x)H(t,t)-J H(t,t+x) is positive and exceeds
x*t*J*k(t)*k(t+x) for all positive x,t. Both statements, the exact coupled
(a,B) ODEs, and their analytic tail limits are directly Lean-audited; all25
public theorem axiom closures use only the standard three axioms. See P3
`theta/rn-finite-pair-positive-transport-primitive.md` and successor P1
`rn-finite-pair-positive-transport-primitive.md`.

This supplies a global finite-pair object with a definite sign. It does not
yet settle coordinate compensation. The successor retains a and B together,
proves their exact improper-integral transport, then targets the full current.
The conjecture N=a+s_x B>0 has genuinely signed forcing; positivity of N
alone would also leave a second unproved current coefficient. Do not promote
that conjecture to a closure criterion or drop the signed packet a.
