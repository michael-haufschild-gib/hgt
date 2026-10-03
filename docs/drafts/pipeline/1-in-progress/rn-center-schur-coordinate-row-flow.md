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
The joint Taylor remainder and its exact identification with E remain
unformalized. The expansion is still a paper diagnostic, not a formal
kernel-derivative theorem or a counterexample. The source identities used are H_xy=beta,
H_xx=-2I, H_xyyy=qP-2S, and H_xxyy=2S at the center; the last equality
and the multivariate expansion need their own exact proof before use.
No numerical test was used, and no failure of the stronger conjecture is claimed.


## Arbitrary-anchor lower sign closed (2026-10-02)

The coarea amplitude proof now retains the nonnegative anchor-curvature term
and proves H(a,x)H(a,y)<H(a,a)H(x,y) for every 0<=a<x and a<y.
The larger-node projection coefficient is therefore positive at every such
anchor. `ThetaTailGaussianSubmodular` and `ThetaTailCenterSchurCross` passed
both targeted builds, final direct-file checks, and all29 public standard-axiom
queries. Certificate: `../3-formalized/theta/rn-gaussian-coarea-arbitrary-anchor.md`.
This is a lower sign; no full coordinate-port upper bound is supplied.
