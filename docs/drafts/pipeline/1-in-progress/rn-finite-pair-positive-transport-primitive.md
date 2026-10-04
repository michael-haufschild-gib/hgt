# RN-P-7x: finite-pair positive transport primitive

Status: primitive sign and strict linear comparison formalized and directly audited.
Integrated current sign open; global pointwise negativity is refuted below.
Certificate: ../3-formalized/theta/rn-finite-pair-positive-transport-primitive.md.
Route RN; successor to rn-center-schur-coordinate-row-flow.md.

Let k be the actual source, H its literal first-moment kernel, J=H(0,0),
h=H(0,x), x>0. Define

    f_x(t)=J*(x+2t)*k(t)*k(x+t)-h*2t*k(t)^2,
    O_x(t)=integral_0^t f_x(s) ds.

The whole half-line integral of f_x is exactly zero. Its sign is the sign of
J*r_x(t)-h, where r_x(t)=(x+2t)*k(x+t)/(2t*k(t)). The actual source has
strictly increasing logarithmic decay slope p, so k(x+t)/k(t) strictly
decreases; the positive factor 1+x/(2t) also strictly decreases. Thus r_x
strictly decreases for t>0. At any t>0, either f_x(t)>=0 and every earlier
positive point has positive density, or f_x(t)<0 and every later point has
negative density. Finite-prefix integration in the first case and the exact
zero total mass in the second prove O_x(t)>0.

Exact survivor:

    O_x(t)=h*H(t,t)-J*H(t,t+x)>0.

Hence the actual common-shift tail ratio H(t,t+x)/H(t,t) lies strictly below
H(0,x)/J for every x,t>0. This is an integrated statement, retaining both
signed densities. No rank-three positivity premise is used.

For the finite-pair canonical transport, use normalized b_x(t)=k(x+t)/k(x),
eta=R(0,x)/R(0,0), rho=b_0*b_x, q_x=1-eta*b_0/b_x and the corresponding
normalized primitive O=integral rho*(x+2t*q_x). Put a=q_x/x, B=O/(x*rho).
The formalized system is

    a'=(p(x+t)-p(t))*(a-1/x),
    B'=1+2t*a+(p(t)+p(x+t))*B, B>0.

The now formalized improper transport rewrites the full axis-divided center Schur row as

    E(x,y)=integral rho*(b_y/b_0)*[a+(p(t+y)-p(t))*B/y] dt.

Its canonical speed is (p(t+y)-p(y))/(p(x+t)+p(t+y)). The resulting current
must retain both a and B; neither arbitrary coefficient substitution nor
discarding a term is allowed. Actual integrability and vanishing flux are
proved in ThetaTailFinitePairTransport. The x->0 diagnostic
a->-p(t), B->t recovers the already audited confluent canonical moment.
The transport identity is closed; the integrated current sign is still open.
The proposed global pointwise negative current is now refuted by the actual
center variation; see the final section below.

## Stronger positive survivor: B>t (formalized, 2026-10-03)

The literal native fourth-jet inequality c''<2c^2 on the positive ray follows
from thetaCuspFullReflectedLogFourthJet_lt_two_mul_curvature_sq and the exact
native/full-reflected identities in ThetaCuspCompletedInverseCurvatureTransport.
Thus M=2pc-c' has M(0)=0 and M'=2c^2+2pc'-c''>0, so M>0.

For x>0,t>=0 define

    F=x*(p(t+x)^2-p(t)^2-c(t+x)-c(t))+2*(p(t+x)-p(t)).

As a function of x, F starts at zero and has derivative
p(t+x)^2-p(t)^2+c(t+x)-c(t)+x*M(t+x)>0. Hence F>0.
The modified density ratio

    r2_x(t)=(1+x*(p(t)+p(t+x))/2)*k(t+x)/k(t)

has derivative -F*k(t+x)/(2*k(t))<0. The corrected primitive

    O2_x(t)=O_x(t)-x*t*J*k(t)*k(t+x)

satisfies O2(0)=0, O2(infinity)=0, and
O2'=2t*k(t)^2*(J*r2_x(t)-h). The same one-crossing argument proves
O2_x(t)>0, equivalently B_x(t)>t. The tail limit uses actual Schwartz decay.
No source coefficient or inverse-Gram sign is postulated.

The remaining signed packet a cannot be discarded. A sharper candidate is
N=a+s*B>0, s=(p(t+x)-p(t))/x. Its exact prospective ODE is

    N'=s*(x+2t)*N+(s'-2*j*s)*B,
    j=(t*p(t+x)-(t+x)*p(t))/x.

The forcing s'-2*j*s is minus s^2 times the previously audited signed Sturm
weight. ThetaFinitePairSturmCrossing now proves that it is positive before
exactly one positive zero and negative afterward. This source-specific
classification now gives an audited Lean proof of N>0, including its tail
endpoint (P3 theta/rn-finite-pair-packet-positivity.md). N>0 is not supplied
by B>t alone.

## Full-current successor: keep both packet coordinates

Write s_y=(p(t+y)-p(t))/y, delta_x=p(t+x)-p(t),
Sigma_x=p(t)+p(t+x), and lambda=(p(t+y)-p(y))/(p(t+x)+p(t+y)).
For the proposed exact transported moment C=a+s_y*B, direct differentiation
gives current C_y-lambda*C_t-lambda_t*C as

    A*a+D*B+lambda*(delta_x/x-s_y),
    A=-lambda*delta_x-2*t*lambda*s_y-lambda_t,
    D=partial_y(s_y)-lambda*(partial_t(s_y)+Sigma_x*s_y)-lambda_t*s_y.

The constant term is negative for 0<x<y by strict convexity of p. Replacing
a by N-s_x*B leaves a second coefficient D-A*s_x; no favorable sign of that
coefficient has been established. Therefore the now-proved N>0 does not
yet close the full current. Keep its magnitude and the actual a/B relation.

The corpus's strict normalized-row decrease gives, on paper,

    a+B*k(t)^2/H(t,t)
      = (1-H(t,t+x)*k(t)/(H(t,t)*k(t+x)))/x > 0.

This retains the actual diagonal tail. It is not a global current proof;
substituting it still leaves a source-dependent coefficient and the endpoint
region. Do not replace the diagonal tail by an unproved curvature bound.

## Improper-transport proof: directly audited 2026-10-04

Let r_y(t)=k(t+y)/k(t), U=r_y*O_x, and
G=(p(t+y)-p(t))*r_y*O_x. Then U'=r_y*f_x-G. The ratio r_y is positive and
bounded on the positive ray, so U tends to zero. The product r_y*f_x is an
exact linear combination of Schwartz products. The function
V(t)=integral_0^t r_y*f_x-U(t) has derivative G>=0 and a finite limit.
Thus the actual monotone-derivative improper-integral theorem supplies
integrability of G and integral G=integral r_y*f_x, without assuming that
integration by parts is admissible. Adding the raw packet term gives the
finite-pair Schur transport identity. ThetaTailFinitePairTransport built and
passed its direct actual-source `lake env lean` audit with empty diagnostics.
All required integrability and boundary limits are proved internally.

## Second compensation identity: paper successor, 2026-10-04

Let w=k(t+x)*k(t+y)/(k(x)*k(y)), D=B-t>0, delta_y=p(t+y)-p(t),
Sigma_x=p(t)+p(t+x). For t>0 the exact coupled ODE gives

    w*(a+delta_y*B/y)
      = (w*D/(2t))' + w*(C0+Q*D),
    C0=t*delta_y/y-Sigma_x/2,
    Q=delta_y*(1/y+1/(2t))+1/(2t^2)>0.

This is a paper algebra identity. Its second improper integration and positive
Q*D integrability have not been formalized. At zero, B(0)=0 and B'(0)=1
give D/t->0. At infinity, w*B is proportional to the already vanishing
balance flux, so w*D/t->0. The same monotone-primitive argument is a plausible
way to prove the missing integrability, retaining C0 instead of dropping it.

A source-only conjecture for this representation, now proved globally in
ThetaTailCorrectionCurrent (nine public theorems, direct audit 2026-10-04), is

    partial_y Q-(p(t+y)-p(y))*Q < 0.

Its exact numerator after multiplication by 2*t^2*y^2 is

    t*y*(2t+y)*c(t+y)-2*t^2*delta_y
      -(p(t+y)-p(y))*(t*y*(2t+y)*delta_y+y^2).

The t->0 limit of the proposed sign expression is
(y*c(y)-p(y))/y^2-(2*p(y)*c(y)-c'(y))/4. Positivity of the newly audited
Schrodinger slope alone does not determine this difference. The literal
corpus ThetaCuspCurvatureLogConvex additionally supplies c'<2c and logarithmic
convexity of c. The complete two-interval comparison and proof are recorded in
rn-positive-correction-current.md and its P3 certificate.
The proved negative Q current still requires the explicit C0 contribution
to be paid by the actual D term. This is a successor attack on compensation,
not a proof of the coordinate current or a reason to discard its signed part.

## Riccati form retaining the matched compensation

For x,t>0 set m=-a/B and ell=k(t)^2/H(t,t). The actual coupled ODEs give
  m'=2*t*m^2-2*p(t)*m+(s_x-m)/B,
while the diagonal tail equation gives ell'=2*t*ell^2-2*p(t)*ell.
The audited matched-packet positivity supplies m<s_x;
the existing ordered-row identity supplies m<ell. These two comparisons keep
actual coefficient dependence and can be used together, but neither alone
has closed the coordinate current.

For r=s_y and lambda=(p(t+y)-p(y))/(p(t+x)+p(t+y)), the full canonical current
divided by positive B is exactly
  r_y-lambda*r_t-(lambda*Sigma_x+lambda_t)*r
    +(lambda*x*s_x+2*t*lambda*r+lambda_t)*m
    +lambda*(s_x-r)/B.
This is a paper algebra identity, not a new sign claim. For y>=x the final
term is nonpositive; the coefficient multiplying m must also be handled.
In the constant-curvature Gaussian calibration all terms cancel exactly.
A next comparison must retain the 1/B term and actual Riccati evolution;
replacing m by an arbitrary number below s_x loses essential information.

## Retired conjecture: the actual canonical Riccati barrier

The new packet and speed leaves now pass their direct source-file audits.
For x>0,y>=x,t>0 let r=s_y, s=s_x, P=-A>0 and
  D=r_y-lambda*r_t-(lambda*Sigma_x+lambda_t)*r,
  E=lambda*(s-r), m=-a/B.
The former exact full-current conjecture was
  P*m+D+E/B<0,
equivalently m<-(D+E/B)/P. The actual m satisfies
  m'=2*t*m²-2*p(t)*m+(s-m)/B.
The proved signs m<s, A<0 and E<=0 close the region where
(D-A*s)*B+E<=0. The remaining positive-cost region requires a quantitative
comparison with the actual N/B, not just N>0 or an unconstrained coefficient.
Keep B's actual coupled ODE and endpoint data throughout this attack. No
conditional restatement of this inequality counts as a source producer.

RN-P-7ab now refutes this barrier in the strictly ordered chamber x<y.
The literal finiteCanonicalCurrent is positive somewhere with t>0 and 0<x<y;
its equality to the actual differential transport current is audited. The
source-derived moment comparison alpha<=q/2+c''(0)/(6q) and exact positive
center variation are retained as new positive knowledge. All four leaves and
25 public standard-axiom audits passed. Certificate:
../3-formalized/theta/rn-finite-pair-current-center-variation.md.
No RH or integrated-Schur counterexample is asserted. The surviving hard
target is rn-finite-current-integrated-compensation.md, including its boundary
flux and every positive source-time contribution.
