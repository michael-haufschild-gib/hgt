# RN-P-7ag: global diagonal Ward forcing and Schur-energy peak

2026-10-04. Formalized in ThetaDiagonalWardForcing and
ThetaDiagonalWardCrossing. Parent:
../../1-in-progress/rn-finite-current-integrated-compensation.md.

For the actual theta source k, logarithmic slope p and first-moment kernel H,
define, on x>0,

  Z=H(0,0)/k(0)^2,
  g(x)=H(0,x)/(k(0)*k(x)),
  n(x)=partial_left H(0,x)/(x*k(0)*k(x)),
  F(x)=1-g(x)*(1+n(x))/Z,
  E(x)=H(x,x)-H(0,x)^2/H(0,0),
  w(x)=2*x*k(x)^2.

F is strictly increasing on the entire positive ray, with

  -centerEntry/k(0)^2 < F(x) < 1,
  F(x) -> -centerEntry/k(0)^2 < 0 as x->0+,
  integral_0^infinity w(x)*F(x) dx = 0.

There is exactly one positive zero r of F. F is strictly negative before r
and strictly positive after r. Consequently E has a unique global maximum
on the nonnegative ray, at r: E(x)<E(r) for every x>=0 with x!=r.
The forcing's value assigned at zero by totalized division is immaterial;
the continuity and crossing statements concern x>0.

## Dependency-closed paper proof

The actual common-translation Ward derivative, compared with the two joint
kernel partial derivatives, gives

  H_left(x,y)+H_left(y,x)=-(x+y)*k(x)*k(y),
  g'=p*g-x*(1+n),
  E'=-w*F.

The corpus already proves strict negative g' and n', with g,p>0.
The g equation forces 1+n>0. Thus g*(1+n) strictly decreases and F strictly
increases. The literal center mixed jet gives its negative initial limit.
The decreasing-row bounds give the strict two-sided bounds above, and hence
integrability of w*F using actual Schwartz source admission.

The positive two-node determinant gives E(x)>0 for x>0. At zero E=0, and
0<=E(x)<=H(x,x). The admitted diagonal kernel tail tends to zero, so E also
tends to zero at infinity. The improper fundamental theorem of calculus
therefore gives integral w*F=0, retaining the inverse-Gram correction.

If F were never positive, -w*F would be nonnegative with zero integral.
Continuity on the open half-line and positivity of w would make F identically
zero there, contradicting strict increase. The negative initial limit,
continuity and strict increase give the unique positive zero. The exact
derivative of E makes E strictly increase up to it and strictly decrease
afterward, establishing the unique peak.

## Validation

Direct source checks/exports use `lake --old env lean` on each actual leaf:
Forcing28526 and Crossing89292 both exited0. Forcing has an informational
ring suggestion; Crossing has no diagnostics. Both imports are wired into
RHTower.lean. No full or umbrella build was run.

All29 public theorem axiom queries in23335 exited0, each with exactly
propext, Classical.choice and Quot.sound. The audit output was compared with
the full public-theorem manifest:29 expected,29 audited, none missing or extra.
Lint46380 exited1 with24 unrelated unreachable modules and no own-leaf or
forbidden-declaration error; the working log records every error. No numerical
experiment, added axiom, unproved source premise, heartbeat increase or
subagent was used.

## Remaining hard problem

Put D=E/k(x)^2 and z=x*p(x)-1. Full diagonal compensation requires

  F(x)-z(x)*D(x)/x^2 > 0,

equivalently strict decrease of D(x)/x^2. The unique peak of E does not prove
this differently normalized sign. A proposed actual-source producer is
strict concavity of F in the clock z. RN-P-7ah retains the complete product
curvature of g*(1+n), including its favorable mixed derivative term.
That sign, the global finite-pair chamber, general anchors, arbitrary rank
and arithmetic RH transfer remain open. No RH proof or falsification follows.
