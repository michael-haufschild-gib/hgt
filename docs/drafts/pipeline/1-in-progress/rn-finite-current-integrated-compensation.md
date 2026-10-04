# RN-P-7ac: finite-current integrated compensation

2026-10-04. Open conjecture. Parent: ../3-formalized/theta/rn-finite-pair-current-center-variation.md.
No RH proof, pointwise sign, integral sign, or limit interchange is assumed.

## Actual hard target

For 0<x<=y, retain the literal weight
  w(x,y,t)=k(t+x)*k(t+y)/(k(x)*k(y)),
the transported moment C=a_x+s_y*B_x, and the complete canonical current
  Ican=C_y-lambda*C_t-lambda_t*C,
  lambda=(p(t+y)-p(y))/(p(t+x)+p(t+y)).
The target is the strictly negative weighted improper integral of Ican,
with integrability and the zero boundary flux proved from the actual source.
This would produce normalized Schur row decrease for finite pairs; general
anchors, higher rank, and arithmetic RH transfer remain separate obligations.

The RN-P-7ab positive-current germ passed all final source and axiom audits.
A global pointwise negative-current proof is impossible. The whole signed
integral is the surviving problem. The already audited matched packet N>0,
negative matched coefficient, exact coupled a/B equations, and complete
source projective descent remain usable input.

## New conjecture to test by proof

The cumulative weighted current may satisfy
  integral_0^T w(x,y,t)*Ican(x,y,t) dt < 0
for every T>0 and 0<x<=y. This would pay every positive source-time region
from the actual earlier negative mass. It is stronger than the desired total
sign and is not yet proved. Do not insert it as a premise. Work with the
literal finite-prefix primitive and source equations to seek a positive
energy/square decomposition, retaining endpoint and inverse-Gram terms.
If it fails, extract the exact signed compensation that survives.

## Center boundary diagnostic, paper only

Write q=c(0), alpha=I/J, gamma=alpha-q/2>0. Existing center-source deficit
convexity proves gamma>0. For fixed t>0, RN-P-7ab proves Ican(x,x,t)/x->L(t).
The two limits x->0 and t->0 are not uniform: at t comparable to x,
  lambda~t/(2*(t+x)), lambda_t~x/(2*(t+x)^2), C~x*gamma.
Thus -lambda_t*C/x has a candidate negative boundary mass -gamma/2.
A proposed measure limit is
  w(x,x,t)*Ican(x,x,t)/x dt
      -> (k(t)^2/k(0)^2)*L(t) dt - gamma/2*delta_0.
This is a conjectural diagnostic, not an audited distributional theorem.

The audited normalized-Schur Hessian sum is -D/k(0)^2 with D>0. Formally
matching it suggests the compensation identity
  integral_0^infinity (k(t)^2/k(0)^2)*L(t) dt - gamma/2
      = -D/k(0)^2.
Neither dominated convergence nor integrability of L is supplied by this
observation. An exact finite-primitive proof should establish the identity
and all limits before using it. The global finite-pair prefix target above,
not rediscovering the already known Hessian sign, is the main new frontier.

## Corpus audit

Search10104 (deep finite-pair/current/flux) was non-partial, inventory65155,
with older-generation/semantic-coverage warnings and mostly source-only
compiler metadata. Generic Schur candidates were inapplicable. Targeted
search74269 (centerCurrentProfile OR logarithmicFlux) was also non-partial
with the same inventory/freshness limitations. Applicable source inputs:
ThetaConfluentCoordinateEnergy.logarithmicFlux_hasDerivAt and its positive
joint energy; ThetaTailNormalizedSchurHessian exact joint-center sign.
At search time, new RN-P-7ab source-only hits described unaudited work and were
not independent evidence. Their later final audits are recorded in the P3
certificate. No existing finite-pair integrated sign was retrieved.

## Exact center-flux algebra to audit next

The corpus kernel expression for b=centerPrimitiveVariation has the paper tail
form b=(I_t-alpha*H(t,t))/k(t)^2, hence
  b'=2*p*b+t*(2*alpha-p^2).
In the literal center profile, the projective term is
  (q/2)*(t*c/p)'.
Repeated product differentiation, without any numerical evaluation, gives
  k^2*L = F' + k^2*[-t*(p^2-c)^2/6
                    +(2*q-alpha)*t*p^2+(alpha-q)*p],
where
  F=k^2*[q*t*c/(2*p)-b*p^2/2+(t*v-c)/12
         +t*p*c/6+t*p^3/6+p^2/12+(q-alpha)*t*p].
The center limit is F(0+)=5*q*k(0)^2/12. If its tail vanishes, the exact Ward
integrals of the polynomial part yield
  integral k^2*L = k(0)^2*(alpha/2-q/4)-D.
This derives the proposed boundary capacity gamma/2 with the full positive
joint compensation D retained. The derivative identity, b tail identity,
endpoint limits and improper transfer are paper obligations, not yet Lean
claims. To advance beyond the known Hessian, seek a finite-pair analogue of
this flux with a positive energy decomposition and actual Gram correction.

Prefix search97074 finished non-partial: inventory65160, older-generation and
semantic-coverage warnings; compiler mostly pending/source-only. Candidate
normalizedSchurHessian_sum_origin and anchored_schur_cross_pos are already
known inputs, while the proposed unrelated Haar-prefix/Schur-weight ingredient
set does not apply to the literal finite-pair current. All listed source
arguments were inspected; none supplies the finite-pair prefix or total sign.

## Boundary-layer conjecture with a dependency-closed paper route

The proposed negative atom has a sharper source-specific precursor. For each
fixed r>=0, the exact two-scale limit should be
  Ican(x,x,r*x) -> -gamma/(2*(1+r)^2), as x->0+.
Thus its mass in the scaled variable r is exactly -gamma/2. A theorem about
this pointwise scaled profile would not itself justify weak convergence or
interchange with the r integral; those remain separate analytic obligations.

The corpus supplies the global identity
  H(u,v)=H(0,u)*H(0,v)/J+u*v*dividedSchur(u,v)
away from the axes and a continuous axis extension with value 2I-P at(0,0).
Together with H(0,a*x)=J-I*a^2*x^2+o(x^2) and
k(a*x)=k(0)*(1-q*a^2*x^2/2)+o(x^2), it gives
  a_x(r*x)/x -> gamma-q*r,
  B_x(r*x)/x -> r,
  C(x,x,r*x)/x -> gamma.
No uniform Taylor remainder is needed because each r is fixed.
Smooth secant averages give s_x(r*x)->q and both secant derivative averages
->0. Meanwhile
  lambda -> r/(2*(r+1)),
  x*lambda_t -> 1/(2*(r+1)^2).
Consequently x*A -> -1/(2*(r+1)^2) and
x*D_current -> -q/(2*(r+1)^2). Combining the two actual packet limits cancels
r and yields the claimed strictly negative profile. This is the next precise
boundary theorem to audit; the arbitrary finite-pair total sign is still the
main open mathematical problem.

Boundary transfer implementation: ThetaFinitePairBoundaryPackets has six public
statements and passed a clean export in sequence19053. It includes the complete
joint directional kernel limit and both actual packet limits, for every fixed
real r. ThetaFinitePairBoundaryCurrent has the three intended capstones: the
matched-moment coefficient gamma, the exact negative current profile, and
its eventual negativity at fixed nonnegative scaling. Its first check required
only fixing the continuity evaluation point and reducing a lambda application;
recheck52982 is running. The boundary layer is not yet reported as audited.

An auxiliary source-shape search55794 returned partial inventory65174 with
older-generation and semantic-coverage warnings; predominantly source-only
compiler metadata. Its Wronskian/connection ingredient set belongs to a different
source and is inapplicable. No new Schur sign was inferred. The actual finite-pair
integrated compensation remains the target; source-only shape statements must
retain a proved connection to the actual projection equations before promotion.

## Next analytic attack: recover the boundary mass from the actual finite current

For fixed T>0, a stronger finite-prefix limit would be
  lim_(x->0+) integral_0^T w(x,x,t)*Ican(x,x,t)/x dt
    = integral_0^T (k(t)^2/k(0)^2)*L(t) dt - gamma/2.
This is not yet proved by the fixed-r profile. It can be attacked without
assuming uniform convergence of Ican/x. Put j=t*c-p, w0=k^2/k(0)^2,
  F0=w0*j/2,
  Frel_x=(w(x,x,t)*lambda(x,x,t)*C(x,x,t)-F0)/x,
  Grel_x=(w(x,x,t)*(C_y(x,x,t)-(p(t+x)-p(x))*C(x,x,t))-F0')/x.
The exact current identity gives w*Ican/x=Grel_x-(Frel_x)'. For every x>0,
Frel_x(0)=0. For each t>0 the proposed limiting flux is
  F1=w0*[C1/2-p*j-q*j/(2*p)],
  C1=alpha-(c+p^2)/2+t*v/2+c*b.
Its right boundary limit is gamma/2. Thus the missing boundary contribution
is explicit, not a guessed dominated-convergence term.

Required source regularity can be built from compact x-averages of the actual
packet numerators. Both vanish at x=0; their first x-averages remove division
by x. Continuous second/third kernel jets give continuous parameter derivatives
of the regularized a and B. The actual Grel then has a continuous extension on
compact source-time intervals. For the flux, use p(t+x)>=q*(t+x), j=O(t^3),
and C=j+x*Ctilde with bounded continuous Ctilde. This controls C/p(t+x)
uniformly on a compact positive quadrant, so Frel admits an integrable bound.
These are proof obligations to build, not assumptions to add to a capstone.
The final sign for arbitrary finite x,y and the improper tail still need a
source-specific positive energy decomposition; the prefix limit alone is not
an RH proof or a global Schur sign.

A sharper finite-prefix proof avoids even a uniform flux bound. Define the
source-derived packet extensions explicitly by
  areg(x,t) = integral_0^1 [-p(t+u*x)*k(t+u*x)
                  -firstLeft(u*x,0)*k(t)/J] du / k(t+x),
  Breg(x,t) = integral_0^1 [firstLeft(u*x,0)*H(t,t)/J
                  -firstLeft(t+u*x,t)] du / (k(t)*k(t+x)).
The compact FTC in x identifies them with a and B for x!=0; at x=0 they
are -p and t. Their first x derivatives are compact averages of the actual
second kernel jets, so both the extensions and these derivatives are jointly
continuous. Thus no unproved joint Taylor remainder is needed.

Set Creg=areg+smoothSecant(x,t)*Breg and
  Greg=w(x,x,t)*[smoothSecantNodeJet(x,t)*Breg
                   -(p(t+x)-p(x))*Creg].
Its x derivative is jointly continuous using only second kernel jets and
source curvature c''. Hence
  Grelreg(x,t)=integral_0^1 partial_x Greg(u*x,t)du
is jointly continuous and equals (Greg(x,t)-Greg(0,t))/x for x!=0.
The compact integral of Grelreg tends to the integral of Grelreg(0,t)
by the corpus's parametric-interval continuity theorem. For each fixed T>0,
ordinary parameter differentiability gives Frel_x(T)->F1(T).
The exact finite FTC identity
  integral_0^T w*Ican/x = integral_0^T Grelreg - Frel_x(T)
then proves the boundary-sensitive limit without domination of Ican/x.
To identify its value with integral w0*L-gamma/2, prove
F1'=Grelreg(0,t)-w0*L for t>0 and F1(0+)=gamma/2. The packet ODE gives
b'=2pb+t(2alpha-p^2), closing the derivative identity. Analytic transfer of
this dependency-closed paper route remains to be built and audited in Lean.

Boundary-layer closure: both leaves and all9 public standard-axiom queries
passed final sequence8949 with empty source diagnostics. The exact fixed-r
negative profile and positive matched coefficient are now formalized;
certificate ../3-formalized/theta/rn-finite-pair-boundary-layer.md.
The earlier pending-check notes are historical. The actual finite-prefix limit
and global weighted sign above remain the current hard frontier.

## Compact primitive simplification

No uniform bound for Ican/x, nor a second compact average of Greg_x, is
necessary. Once packet extensions have jointly continuous node jets, apply the
corpus parametric derivative theorem directly to integral_0^T Greg(x,t) dt.
For T>0, the endpoint flux W*lambda*C is ordinarily differentiable in x at0.
Their difference has zero value at0 (the exact G0=F0' cancellation), equals
the actual current prefix for every x>0, and has derivative
  integral_0^T G1(t)dt-F1(T).
Here
  G1=w0*[t*c''/3+v*b/2-(c-q)*j-p*C1-2*p*(t*v/2-p*j)].
This proves the actual prefix limit before rewriting it as the interior-profile
integral minus gamma/2. The latter needs the b ODE and exact endpoint limit.

Search60346 (deep parametric interval integral/continuous derivative/divided
difference) finished partial: complete inventory65184, compiler predominantly
pending/source-only, semantic coverage unavailable; only filter_and_judge
unfinished. All20 candidates and20 source arguments were inspected. Applicable
inputs are ClockParametricDerivative.hasDerivAt_parametric_intervalIntegral and
the mathlib compact parametric integral continuity theorem. Generic algebraic
divided differences supply no packet-specific regularity or sign. API scratch
initially caught wrong namespace for integral_pow; corrected scratch60392
passed. PacketExtension and RegularizedBulk are being implemented; neither is
yet audited or an established new theorem.

The exact short-prefix survivor is now the target theorem
  eventually T->0+, eventually x->0+,
    integral_0^T W(x,t)*Ican(x,x,t) dt < 0.
It follows from the actual prefix variation above and its T-boundary
  integral_0^T G1-F1(T) -> -gamma/2 < 0.
This order of quantifiers is essential: the node threshold may depend on T.
No uniform finite-pair or improper-tail sign is inferred.

Search12203 (secondLeft/diagonal/hasDerivAt, Theta-filtered) finished partial,
complete inventory65195, text/source retrieval unfinished, older-generation
snapshot and semantic-coverage warnings, predominantly pending/source-only
compiler metadata. All returned candidate statements and source arguments
were inspected. The proposed ingredient set supplies only a left derivative,
not the diagonal derivative required for b'. The exact moving-tail correlation
identity instead gives
  d/dt secondLeft(t,t)=2*(p+t*c-t*p^2)*k^2
by compact FTC; the actual source second derivative is (p^2-c)*k. Together with
H(t,t)'=-2t*k^2 this proves b'=2pb+t*(2alpha-p^2), the remaining algebraic link
from integral G1-F1(T) to integral w0*L-gamma/2. This link is paper-proved,
not yet formalized.

## Global finite-pair attack after prefix transfer

The four RN-P-7ad leaves now export successfully and are wired. Their final
source/axiom audits run sequentially. They prove the actual finite-prefix
limit integral w0*L-gamma/2 and eventual short-prefix negativity. The b ODE,
F1 derivative identity and compact endpoint transfer are included. No improper
tail limit or global finite-pair sign follows automatically.

Search1220 (rank-one projection/coordinate derivative/normalized row/covariance)
was non-partial, inventory65203, older-generation and semantic-coverage
warnings, predominantly pending/source-only compiler metadata. All candidates
and source arguments were inspected. The proposed matrix-Schur exponential
path ingredient set is not identified with this theta kernel and cannot be
used as a producer. Actual applicable source is the existing Gaussian coarea
decomposition in ThetaTailGaussianCoarea, ThetaTailGaussianSubmodular and
ThetaTailCenterSchurCross; their exact bodies were read.

Let V be the actual coarea potential, mu(u)=exp(-V(0,0,u)),
A_x(u)=exp(V(0,0,u)-V(0,x,u)), and
delta=V(0,x,u)+V(0,y,u)-V(x,y,u)-V(0,0,u)>0.
The normalized center Schur numerator splits exactly into
  integral mu*A_x*A_y*(exp(delta)-1) + Z*Cov_mu(A_x,A_y),
where Z=integral mu and Cov is for the normalized measure mu/Z.
Both terms are positive by the audited potential/covariance comparison.
The global derivative requires their coupled variation after division by x*y.

Tested paper conjecture: B_y=A_y-y*partial_y A_y decreases in coarea mass.
That would give the desired covariance sign independently. It fails at the
mass boundary: for every y>0,
  partial_u B_y(0+)=q+c(y)-2*p(y)/y > 0.
The strict sign is exactly the actual curvature trapezoid; A_x itself decreases
with initial derivative -(p(x)/x-q)<0. Thus their two-mass covariance kernel
has the adverse sign near0. This is a paper obstruction, not yet a new Lean
no-go certificate. Strongest positive survivor: the exact strictly positive
score defect and its positive curvature quadrature
  q+c(y)-2*p(y)/y = (1/y)*integral_0^y s*(y-s)*c''(s) ds.
Its compensation by the potential term, and the full integrated sign, remain
the hard target. Do not assert separate derivative signs from positivity of
the original two coarea terms.

## RN-P-7ad final closure

Final sequence48501 exited0: all four direct source audits and all53 public
axiom queries pass with exactly propext, Classical.choice, Quot.sound. Imports
are wired. Certificate: ../3-formalized/theta/rn-finite-current-prefix-compensation.md.
Earlier pending-prefix notes are historical. Global finite-pair compensation
remains open. Search7631 returned partial inventory65228, older snapshot and
semantic coverage limitations; all four candidate statements and four source
arguments were inspected. Actual massRate/shift derivative APIs apply to the
coarea score attack, but provide no integrated derivative sign.

## RN-P-7ae: retain the coarea score obstruction and curvature survivor

Candidate separate covariance differentiation is false on paper. Before
retiring it, formalize the literal score B_y=A_y*(1+y*V_y(0,y,u)), its actual
mass derivative, and derivative limit q+c(y)-2p(y)/y>0 along u=z^2->0+.
An exact primitive for the positive curvature quadrature is
s*(y-s)*c'(s)-(y-2*s)*c(s)-2*p(s).
Its endpoint difference is y*(q+c(y))-2*p(y). This avoids a generic convexity
premise and retains the actual source's positive fourth jet. A positive mass
score derivative together with decreasing A_x obstructs the covariance sign.
The next full target must compare the coupled score integrals; positivity of
the original coarea Schur decomposition alone is insufficient.

Search36421 (covariance/variance/Poincare/derivative/integral/compensation,
Theta filter) returned partial inventory65238, semantic coverage unmeasured,
source metadata predominantly pending/source-only. All20 candidate statements,
20 source arguments and the proposed ingredient set were inspected. The
returned Selberg/XiZeroCopy and D4BM covariance identities concern different
measures/operators; none supplies the required actual coarea compensation.

The exact coupled target, with V the actual coarea potential and
Q_xy(u)=density(x,y,u)*(1+y*leftDerivative(y,x,u)), is
  integral Q_xy > (integral density(0,x)/Z)*integral Q_0y,
for 0<x<=y, Z=integral density(0,0). If justified under the integral, this is
precisely negativity of the normalized center Schur row derivative. It must
not be replaced by separate signs of its two coarea terms.
A possible direct compensation representation is the centered primitive
  K_x(u)=integral_0^u mu*(A_x-mean_mu A_x)>0.
Integration by parts would turn Z*Cov(A_x,B_y) into -integral K_x*B_y'.
This is paper algebra; the primitive, endpoints, integrability, and the
source-specific comparison paying this term have not been formalized.

RN-P-7ae closed: ThetaGaussianCoareaScore exports successfully (5123),
final direct source audit and9 public axiom queries pass (29877), exactly
propext/Classical.choice/Quot.sound. Import wired. P3 positive score-defect
certificate and P5 separate-score no-go created; frontier updated. The actual
score derivative limit, positive curvature quadrature, non-antitonicity and
adverse covariance pair are established. No integrated covariance sign or
global finite-pair sign is claimed. Serena symbol editing rejected the ignored
Lean path, so the observed source was patched directly.

## Next actual compensation attack: half-line boundary retained

Search77468 (coarea centered primitive, ThetaTail) returned partial inventory
65240, older snapshot and unmeasured semantic coverage. All20 candidates and
20 source-argument statements were inspected. Existing coarea covariance and
center Hessian apply only in their audited regimes; no global score producer.
Search53915 (translation/order-three/Wronskian) returned non-partial inventory
65242 with old-snapshot/semantic warnings. Its20 candidates and20 source
arguments do not establish an inverse-Gram implication. The older row-flow
card already records this gap; do not spend another turn re-proving a source
Wronskian without a paper proof of the needed transfer.
Search70696 (halfLineSteinScore/variance/curvature/boundary) returned partial
inventory65240, source-text stage unfinished, old-snapshot/semantic warnings.
Both candidate statements and both source arguments were inspected. The
HalfLineSteinRobertson boundary identity applies only after actual derivative,
integrability and endpoint obligations are discharged. Its zero-boundary
specialization cannot simply erase the actual density at zero.

A direct paper correction to the full-line Brascamp-Lieb kernel is available.
For positive half-line density rho, mass Z, rate M=-rho'/rho and tail T(v),
the exact kernel is
  integral_0^v integral_v^infinity (M(w)-M(u))*rho(u)*rho(w) dw du
    = Z*rho(v)-rho(0)*T(v).
This follows by FTC from integral_0^v M*rho=rho(0)-rho(v) and
integral_v^infinity M*rho=rho(v), retaining the endpoint. For actual coarea
rho=density(0,0), rho(0)=1. The correction is not optional. This identity is
paper algebra with endpoint/integrability obligations still to discharge for
the actual source; no new Lean kernel or variance theorem is claimed.

Research decision: the hard next theorem is still the complete coupled score
integral sign. A generic half-line variance bound or another source Wronskian
alone would not settle it. Seek an actual source comparison paying both the
potential variation and the adverse covariance derivative, retaining the
centered primitive K_x and all boundary terms. Prove that comparison on paper
before promoting auxiliary estimates as frontier progress.

## RN-P-7af conjecture: integrated adverse covariance

Previous turn was verified progress (RN7ad/7ae source and axiom closure).
The next candidate concerns the entire coarea measure, not another two-mass
witness. Let mu have density density(0,0)/Z. Along the actual diagonal,
  Cov_mu(A_x,B_x)=Var_mu(A_x)-(x/2)*(Var_mu(A_x))'.
For u=t^2, the expected exact second-node amplitude defect is
  (1-A_x(u))/x^2 -> a(u)=(c(t)+p(t)/t-2q)/4.
The corpus's curvature monotonicity makes a strictly increasing. If the
necessary full-half-line domination is proved, then
  Var_mu(A_x)/x^4 -> Var_mu(a)>0,
  Cov_mu(A_x,B_x)/x^4 -> -Var_mu(a)<0.
This would refute an integrated favorable-covariance shortcut in the actual
ordered diagonal regime, retaining its exact positive variance survivor.
These limits and the covariance sign are new conjectures, not Lean results.

Domination mechanism on paper: with r-s=x, rs=u, r+s=length,
V_y(0,x,u)=(r*p(r)-s*p(s))/(r+s)-p(x).
For x>0,u>0, actual increasing c and p(0)=0 give
  0<V_y(0,x,u)<=x*c(r)<=x*c(t+x).
Since A_x<=1, for 0<x<=1 both (1-A_x)/x^2 and V_y*A_x/x
are bounded by constants times c(t+1). The audited c'<2c bounds the
latter by an exponential in t; actual source Gaussian/superexponential decay
should make its square integrable against 2t*k(t)^2 dt. Verify every
inequality and analytic transfer, not just the formal variance expansion.

RN7af implementation: ThetaGaussianAmplitudeQuadratic now exports successfully
(sequence68182). It proves the two exact quadratic defect limits and uniform
bounds |D_x(t)|<=c(t+1), |E_x(t)|<=2c(t+1) for 0<x<=1,t>0, plus strict increase
of the limiting profile. Final source/axiom audit remains pending until the
full integrated covariance result is assembled. The global covariance limit
will use direct dominated convergence of D_x, E_x and their product; no
parameter derivative of an improper integral is needed.
Search25041 returned partial inventory65251 and no global contact producer;
all20 candidate/source statements inspected. Search9421 returned partial
inventory65253, old snapshot and unmeasured semantics; all20 candidates and20
source statements inspected. Direct source inspection located the existing
HedenmalmThetaAllShiftedTails all-exponential-moment theorem, which closes the
needed tail-envelope input; its API scratch passed. New CovarianceMeasure
leaf is written and queued after its API checks, not yet validated.

Search7787 (coupled coarea / centered primitive / covariance / potential
compensation) finished with partial inventory65264, semantic retrieval
unfinished and coverage unmeasured. All20 candidate and20 source-argument
statements inspected. Generic finite covariance bounds and unrelated physical
energy identities do not discharge the actual source comparison. The search
also indexed our unverified quadraticVariance_pos source; this is not proof
evidence and was not used as an external producer.
Measure proof repairs: qualified the all-shift Hedenmalm theorem to avoid the
older unit-strip theorem of the same name; explicitly reduced pointwise
function operations; rewrote the exponential product before polynomial
normalization. Sequence72528 now checks/exports Measure then Limit in order.
The Limit leaf includes exact chart transport back to density(0,0), the raw
covariance formula, and direct product dominated convergence. No integrated
result is promoted until this chain and the final source/axiom audit pass.

Sequence72528 has successfully exported CovarianceMeasure (703512-byte olean;
only an informational ring suggestion). Actual whole-half-line exponential
and curvature-square domination, profile-square integrability and strictly
positive quadratic variance now check. The sequence has advanced to Limit.
The covariance limit, chart identities and final audits remain pending.

## RN-P-7ag candidate: global diagonal compensation

Attack the full coupled sign on every positive diagonal node, beyond the
audited small-node chamber. Set Z=H00/k0^2, r=Hxx/kx^2,
g=H0x/(k0*kx), n=H_left(0,x)/(x*k0*kx), D=r-g^2/Z.
The common-translation Ward derivative gives
  r'=2*p*r-2*x,
  g'=p*g-x*(1+n),
  D-x*D'/2=(1-x*p)*D+x^2*(1-g*(1+n)/Z).
The desired global diagonal sign is positivity of this last expression.
This is a paper reduction, not a new Lean sign theorem. A first attempted
proof using r<x/p fails: the derivative of H(0,x) is the RIGHT-node
derivative, whereas n uses the LEFT-node derivative. Replacing one with the
other incorrectly erases the negative feedback term. Keep it explicitly.
The corpus already proves the raw diagonal tail bound and decreasing
confluent normalized mixed row. Neither alone pays the coupled expression.
Search74397 checks novelty/applicable producers; source inspection grounded
the translation identity in hasDerivAt_thetaTailFirstMomentKernel_commonShift.
No route is retired and no extra conditional receiver is being formalized.
Search74397 finished with partial=false, inventory65272, semantic coverage
unmeasured and predominantly pending/source-only compiler metadata. All20
candidates and20 source statements plus the proposed ingredient set were
inspected. The actual normalizedSchur_diag_pos and confluent determinant
limit apply; the proposed spectral-stage Schur norm bound concerns another
object and supplies no global diagonal derivative sign.

## RN-P-7af final closure

Final sequence3029 exit0: all three actual source audits and36 public axiom
queries pass, every closure exactly propext/Classical.choice/Quot.sound.
No errors or warnings remain; informational ring suggestions only. The exact
original coarea covariance has the negative variance/x^4 limit and is negative
for all sufficiently small positive diagonal nodes. All three imports wired.
P3 certificate rn-integrated-coarea-covariance-variance and P5 favorable-
integrated-covariance no-go now record both the obstruction and its exact
positive variance survivor. Frontier updated. Lint22123 has18 unrelated
unreachable modules, no own-leaf/forbidden-declaration error; working log has
the exact names. RH remains open and goal ACTIVE. The next hard target is
RN-P-7ag's full coupled diagonal expression, then the whole finite-pair
chamber; do not return to the now refuted favorable-covariance shortcut.

## RN-P-7ag continuation: retain the centered forcing

New turn: previous RN7af closure is verified progress, not an RH proof.
Revalidated source/card before continuing. For rho=k^2, let
F=1-g*(1+n)/Z and z=x*p(x)-1. The exact diagonal equation is
  (D*rho)'=-2*x*F*rho,
whereas (x^2*rho)'=-2*x*z*rho. Thus both forcings have zero total
integral against x*rho dx, subject to the actual already available tail
limits, and D/x^2 is the ratio of their tail integrals.
Candidate producer: F is strictly concave as a function of z (equivalently
F'/z' strictly decreases, since z'=p+x*c>0). A centered concave forcing
comparison could make this tail ratio strictly decrease. This is a new
source-specific conjecture to prove or learn from, not an assumed premise
or a Lean result. It retains the signed Ward feedback and does not replace
the full target by separate score ordering. Search7933 is checking the
current normalized-Schur derivative/compensation corpus before new code.

Search7933 finished partial=false, inventory65281, semantic unmeasured;
all20 candidate and20 source-argument statements inspected. Existing diagonal
positivity, raw-row decrease and finite transport equations apply. The proposed
D4BM tail-bound ingredient concerns a different object. Search24629 finished
partial=true, inventory65281, semantic unmeasured; all20+20 statements inspected.
It supplies generic concavity criteria and the earlier finite-pair Sturm
crossing, not the actual diagonal forcing comparison. No conditional RH hit
or source-only search declaration is accepted as a producer.

Dependency-closed paper subtheorem now selected for formalization: F strictly
increases on x>0 and has exactly one positive zero. Ward gives
g'=p*g-x*(1+n). Existing g'<0, g>0, p>0 imply 1+n>0. Both g and n strictly
decrease, so g*(1+n) strictly decreases. At zero,
F -> -centerEntry/k0^2<0. Moreover -centerEntry/k0^2<F<1, giving integrability
against 2*x*k(x)^2. For E=Hxx-H0x^2/H00, E'=-2*x*k(x)^2*F,
E(0)=0, E(infinity)=0: E is nonnegative and bounded above by Hxx, whose
actual tail tends to zero. FTC therefore gives integral 2*x*k(x)^2*F=0.
Strict increase and zero mass force a positive value; continuity gives the
unique crossing. This is a global coupled-forcing classification, not the
still-open sign of D-x*D'/2. Clock concavity remains the next producer to solve.

The same paper proof gives a unique positive maximum of the literal Schur
energy E on the whole nonnegative ray: E'=-2*x*k(x)^2*F is positive before
the crossing and negative afterward. This is stronger than mere existence
of a crossing, but does not control E/(x^2*k(x)^2). Both statements are being
formalized in ThetaDiagonalWardForcing and ThetaDiagonalWardCrossing.
First check59392 found only elaboration issues in Forcing (identity-function
simplification, explicit set membership, and whitespace before `mass` to
avoid matroid notation). Repairs are checking/exporting in77741; Crossing
has not yet been checked. Search65550 examines the actual row/clock-curvature
producer. No new theorem has passed a final audit yet.

Forcing export28526 exit0 (only an informational ring hint). The exact Ward
sum, normalized-row derivative, positivity of 1+n, global strict increase of
F, its negative initial limit and strict two-sided bounds now check. Crossing
export15140 is running. Search65550 finished partial=true, inventory65290,
semantic coverage unmeasured, predominantly source-only compiler metadata;
all20 candidate and20 source-argument statements inspected, no proposed
ingredient set. Its mixed-row residual identity is already in use; unrelated
row/curvature hits do not prove this clock comparison.

Paper comparison mechanism sharpened: for the positive measure w dx,
both F and z are centered. At any cut, the line joining the two conditional
means (mean z, mean F) passes through the origin. If the actual graph F(z)
is strictly concave, Jensen on each side plus strict concavity places the
cut point above that line. This yields F(x)-z(x)*D(x)/x^2>0, precisely the
target. This validates the proposed mechanism; actual clock concavity is
still unproved. Raw translated-row convexity cannot substitute: the corpus
proves opposite midpoint gaps in ThetaTailNormalizedRowCurvature. No claim
is made that that obstruction refutes the centered-anchor clock conjecture.

Next actual-source conjecture (RN-P-7ah): with j=1+n, Q=p+x*c=z'>0,
prove Q*(g*j)''-Q'*(g*j)'>0 on x>0. This is exactly strict clock
concavity of F, with all factors fixed by the literal source. Do not assume
separate convexity of g and j: the product identity retains the favorable
cross term 2*Q*g'*j', since both derivatives are strictly negative.
Using the audited Ward equation g'=p*g-x*j, its expanded target is

  Q*g*j'' + ((2*Q*p-Q')*g-3*Q*x*j)*j'
    + (Q*(c+p^2)-Q'*p)*g*j
    + (x*Q'-Q*(1+x*p))*j^2 > 0,

where Q'=2*c+x*c'. This is an exact paper algebra reduction, not an
established sign. The source-specific second derivative j'' and its coupled
transport payment are the next hard producer. Ordinary row monotonicity
does not settle it; no derivative sign is inserted as a Lean premise.

The j'' object is already analytically available, rather than a missing
smoothness assumption. Write M(x)=ThetaJoint.firstLeft 0 x. The corpus has
M'=ThetaJoint.mixed 0 x and M''=ThetaJoint.mixedRight 0 x, with continuous
joint jets in ThetaTailJointCenterJets. For d=x*k(0)*k(x), L=1/x-p(x),

  j''=[M''-2*L*M'+(L^2+1/x^2+c)*M]/d.

Thus the remaining problem is a signed actual-source inequality among
three admitted mixed jets, not derivative existence or integral admission.
The pointwise canonical-current obstruction must remain in view when
seeking an integration-by-parts payment for this complete expression.

## RN-P-7ag final closure

Forcing28526 and Crossing89292 direct source checks/exports exited0, using
`lake --old env lean` on the actual files. Neither source changed afterward.
All29 public #print axioms queries23335 exited0, each exactly
propext/Classical.choice/Quot.sound; the full manifest comparison found29
expected,29 audited, none missing/extra/nonstandard. Both imports are wired.
Forcing has an informational ring hint; Crossing and the axiom log have no
diagnostics. Lint46380 has24 unrelated unreachable modules, all recorded in
the working log, and no own-leaf/forbidden-declaration error. No full or
umbrella build, numerical experiment, added premise/axiom, heartbeat increase
or subagent. P3 rn-diagonal-ward-single-crossing and frontier updated.

This solves the actual forcing crossing and raw Schur-energy peak. It does
not solve full normalized diagonal compensation, the general finite-pair
chamber or RH. Goal remains ACTIVE. Next hard attack is RN-P-7ah's complete
clock-curvature expression, with the explicit mixed-jet formula above.

## RN-P-7ah continuation: actual source clock geometry

Previous turn is verified progress (29 audited Ward/crossing theorems), not
closure of normalized compensation. Revalidated actual crossing source and
this card before continuing. Search83823 finished partial=false, inventory
65309; search11212 partial=false, inventory65311. Both have unmeasured
semantic coverage and predominantly source-only compiler metadata. All20
candidate and20 source statements plus proposed ingredients inspected in
each. Joint mixed jets apply; proposed Schur symmetry/diagonal identities
do not establish the coupled curvature sign.

New dependency-closed paper source sign exposed by the clock attack:
A=x*c-p, M=3*x*c^2-3*p*c-x*p*c', R=c*c'-p*c'' are already strictly
positive on x>0. Define C=x*M-A^2. The exact derivative identities give

  C'=M+x^2*R+2*x*c'*A>0, C(0)=0,
  C=2*x^2*c^2-x*p*c-p^2-x^2*p*c'>0.

For r(x)=p(x)/x and Q=p+x*c, this says

  Q*r''-Q'*r'=-2*C/x^3<0.

Thus the actual boundary coarea rate p(x)/x is strictly concave in the
same clock z=x*p-1 used by the coupled target. This is a source sign, not
a numerical bound or an imposed curvature premise. It also supplies the
positive first-mass coefficient of the amplitude's clock-convexity defect.
The whole-mass and mixed-row comparison remain to prove. Search for prior
clock geometry is running before formalizing this exact new source law.

Search83853 completed partial=false, inventory65311, semantic unmeasured;
all20 candidate and20 source-argument statements plus proposed ingredients
inspected. It returns the earlier potential margin and its derivative;
future-pulse clock bounds concern another object. No existing theorem in
these hits proves C>0 or the new Ward-clock chord law. The new leaf
ThetaDiagonalClockGeometry is written with the reserve derivative and
global strict lower/upper tangent inequalities for p/x as a function of
x*p-1. API check1601 is running; no new source theorem is audited yet.

API1601 exited0. Leaf check/export92376 is running.

The next whole-mass comparison has a concrete division-free form. For
u>0, set a=shift(0,x,u), b=x+a, r=a+b, S=p(a)+p(b),
N=r*(b*c(b)-a*c(a))-x*S and
T=a*c(a)+b*c(b)+a^2*c'(a)+b^2*c'(b).
The literal coarea rate m(x,u)=S/r has, at fixed u,

  m_x=N/r^3,
  m_xx=(T-S)/r^3-3*x*N/r^5.

Candidate full-mass producer is
  (3*x*Q+r^2*Q')*N-Q*r^2*(T-S)>0.
At u=0 it reduces exactly to 2*x^2*C>0, now covered by the new paper
source reserve. For u>0 its sign is still unproved. If proved, integrating
the rate in u would make the coarea potential concave in the Ward clock,
and its exponential amplitude convex in that clock. This addresses g;
the complete product g*(1+n), including the mixed-row feedback, still must
be paid. This is an attack on the same coupled target, not a substitute
completion criterion or a new assumed Lean premise.

The reserve calculation forces a stronger geometric conjecture, now proved
on paper: B=x*M-2*A^2 has B'=M+x^2*R>0 and B(0)=0. Thus
  B=x^2*c^2+x*p*c-2*p^2-x^2*p*c'>0,
  ( (p/x)'/p )'=-B/(x^3*p^2)<0.
The actual slope ratio is strictly concave already in source potential U,
where U'=p. This is a geometric strengthening, not an optimized numeric
bound: it changes the comparison clock from x*p-1 to U and is closer to
the coarea potential transport. C=B+A^2 is the Ward-clock reserve.
Search for this stronger potential-clock law is running before new code.

Search62410 completed partial=false, inventory65315, semantic unmeasured;
all20 candidate and20 source statements and proposed ingredients inspected.
The index includes our still-unverified clock leaf, which is not independent
proof evidence. Existing position/potential curvature differs from p/x in
potential. Unrelated causal-clock sources supply no sign. The stronger B
law, its exact potential-slope derivative, and all positive-pair potential
chords have been added to the same leaf. Check92376 failed elaboration only
(identity/Pi applications, derivative-function instance mismatch, one unused
simp argument); repaired and extended check47756 is running. No new formal
result is promoted until source/axiom audits pass.

The full coarea rate target can be strengthened consistently with B:
  (3*x*p(x)+r^2*c(x))*N-p(x)*r^2*(T-S)>0.
At u=0 this is exactly x^2*B>0. This would make m(x,u) concave in source
potential, and hence in the Ward clock using the corpus's positive slope
elasticity margin. Its positive-u sign has not been proved. Algebraic
expansion into endpoint slope/curvature secants exposes competing terms;
individual monotonicity and the boundary law do not justify dropping them.

Useful exact decomposition for the next positive-mass attack:
  N=r*(A(b)-A(a))+2*u*(p(b)/b-p(a)/a).
Both differences are positive by admitted source laws. Their derivatives
retain endpoint accelerations; positivity of N alone does not prove that
N/(r^3*p(x)) decreases. This is the precise additional comparison needed
for potential concavity of m. The new potential chord bounds constrain
the second difference while retaining the first difference and its weight.

Check47756 found only two superfluous terminal ring tactics and two unused
one_mul simp arguments; removed. Direct actual-source check/export3895 is
running. The final public axiom manifest contains20 theorems.

## RN-P-7ah source-clock closure

Final direct actual-source check/export3895 exited0 with no diagnostics;
no source edit followed. All20 public axiom queries26415 exited0, exact
closure propext/Classical.choice/Quot.sound for every theorem. Manifest
comparison found20 expected/20 audited, none missing/extra/nonstandard.
ThetaDiagonalClockGeometry is wired; P3 rn-source-clock-concavity and the
frontier are updated. Lint36597 has18 unrelated unreachable modules and no
own-leaf/forbidden-declaration error; all18 saved in the working log.
No full/umbrella build, numerical experiment, added premise or axiom,
heartbeat increase or subagent. Targeted whitespace check passed.

The new mathematical progress is global source concavity in two clocks,
including the stronger potential clock. Complete Ward-forcing concavity
has not been proved. Continue attacking its two-endpoint/mixed-row payment
using these source chords; the actual mass-rate numerator and mixed-jet
formula above identify the remaining terms. RH remains open; goal ACTIVE.
