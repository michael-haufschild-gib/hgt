# C70: global third-slope sign through forward trapping

Route TT, open, 2026-10-04. C69 proved actual normalized third-minor
derivative eventually positive. Hard target: strict negativity of its
flow derivative wherever the polynomial slope vanishes inside the
actual source cone. This would forbid forward exit from the nonpositive
region, contradicting the actual positive tail. No sign premise may
remain in the actual capstone. No such sign law is presently proved.

Corpus basis: ThetaCuspRatioDefectSign.acceleration_neg and
ThetaCuspRatioDefectMonotonicity give an exact successful lower-order
model. C65 cone contains negative third-slope points, so mere pointwise
cone positivity is false. C69 closes only the actual tail. Deep searches
/tmp/tt_c70_slope_escape_search.json (partialfalse, gen1224781) and
/tmp/tt_c70_third_minor_global_search.json (partialfalse, gen1224836)
found no applicable global sign law; suggested generic flow/unique-zero
lemmas do not discharge the sign. Narrow corpus search confirms exact
thirdSlope, its seam/zero-speed signs, and lower-order acceleration law.

First attack: test the dynamic barrier at the compactified critical
face before committing to a global separator. Let Q=h19*S and H be
the full compactified field. At h0, HQ=108Q, so the residual
R=108Q-HQ vanishes identically. Its first nonzero transverse coefficient
on r=12t governs the sign of HQ on nearby Q0 sheets. The first h
coefficient of P on r=12t depends only on the first h coefficient of
the regularized tenth moment, because regularized moments8/10 vanish
there. Derive that coefficient exactly in Lean from C65 moment source;
no external coefficient calculation or numerical tests. Scratch
/tmp/TTC70CriticalFirst.lean prepared. No barrier result claimed.

## Critical first-jet learning; refined source constraint
The exact critical tenth-moment first jet normalized in Lean (audit2
exit0, standard3) to -4265518180073472*r. Identifying it with
-(7/6)*6^12*1679616*r and deriving P_h=(7/6)C*r is under audit.
This predicts Q_h=756C*r and cancellation of the first residual
(108Q-HQ)_h on r=12t. A first-order dynamic sign test cannot close
the proposed barrier; higher structure is necessary.

New conjecture aimed directly at that cancellation: actual
q > b(h)=1/12-7h/72 globally (h=1/k). This sharp source inequality
would give E<(7/6)h*r and remove the leading negative mode; no global
S sign follows without another polynomial proof. Do not call it proved.

Algebraic proof plan (unverified): write V=u²,T=9-V and
G=36(q-1/12)+3h+4h²/3-5Tq+(2/3)Vqh-(2/9)Vqh²
 +(2/3)V(1+h/3)q²T-(7/108)Vh²(1+h/3)
 +(7/108)Vh(1+h/3)qT.
Then δ=q-b(h) satisfies δ'=(k/u)G and G(h,V,b) = T*D(h,V),
D=4h²/27+31h/72-5/12+V*(1+h/3)*b/18.
D has both signs in the coarse cone; a one-dimensional everywhere
negative residual proof therefore is not available.

Proposed two-dimensional trap: if δ≤0 and D≤0, neither variable can
cross its zero boundary upward. At δ0, G=T D≤0. At D0 with δ≤0,
H D<0: for h≤2/3, D<0 already; for 2/3≤h<4/5 use q≤b,
b≤1/54, h-bT≥1/2 and D_h>1/2 to get
H D ≤ -(2/9)V(3+h)*(6h(h-bT)D_h-Tb)<0.
The exact drift Hh=-(4/3)h²(3+h)V*(1-qT/h), HV=12VT.
All inequalities/identities require Lean certification; bounds serve
this structural trapping proof, no numerical optimization.

Initial δ>0: clear positive denominator and use
B=u*(1+7T/72-kT/12)-3J. At0, B0=0 and
B'(0)=12+(279/8)k0-(135/4)k0²>0 from the already proved seam k range.
A first crossing of δ below0 would enter D≤0, then remain trapped.
For large x, G_q>0 and D<0 force any negative δ to grow in magnitude,
contradicting boundedness/δ→0. Equality excluded by strict boundary
flow. This would prove the sharp global source inequality, not RH.

C70 scratch status: CriticalFirst audit4 (root=/tmp) exit0, both
criticalMoment10First_eq and criticalMinorFirst_eq standard3.
CriticalBarrierAlgebra audit3 exit0: G_boundary, G_split,
fieldD_neg_at_zero, A_pos_tail standard3. Thus the proposed forcing
trap's exact polynomial sign IS verified. Cache valid.
CriticalBarrierDynamics audit1: dCriticalError passed standard3;
dCriticalForce only function pointwise-power/multiplication simp
errors; force-negative proof needed typed positive denominator.
Fixed script, next audit pending. Failed Dynamics cache removed.
TwoFunctionTrap scratch prepared/first audit active: generic compact
negative-component exclusion using last/first zeros, scalar fencing
for force and one-sided slope limits. This is implementation plumbing
for the actual sharp global inequality, not claimed frontier theorem.
No C70 production leaves/wiring yet. C69 fully integrated/clean.

C70 progress: CriticalBarrierDynamics audit2 exit0, dCriticalError,
dCriticalForce, criticalForceSpeed_neg all standard3. Exact actual ODE
and inward sign of forcing at its zero boundary are verified.
TwoFunctionTrap audit2 exit0 standard3: compact negative-component
argument succeeds (first/last zeros, derivative endpoint signs, scalar
fencing for force). SeamTail audits1/2 proved the sharp tail strictly
positive standard3; initial numerator proof needed Pi.mul/sub simp,
then removal of a redundant simp. SeamTail audit3 now active.
Global scratch prepared, strict scratch prepared. The latter uses
existing public DeBruijn.deriv_deriv_nonneg_of_isLocalMin: a zero
critical error is a local minimum, forcing both error speed and force
to vanish, but the differentiated exact speed split gives strictly
negative second derivative. This excludes equality after global
nonnegativity. Search /tmp/tt_c70_second_derivative_search.json,
partialfalse generation1225247, found this applicable corpus lemma;
source read and existing olean confirmed. Other generic source hits
not needed. No global sharp-source capstone verified yet.

C70 SeamTail audit3 exit0: both criticalError_seam_pos and
criticalError_eventually_pos standard3, no added source premises.
Global audit2 active only after predecessor terminal success.
Premature Global audit1 had exited immediately missing dependency;
no duplicate build remains and its cache was removed. Generic
TwoFunctionTrap audit2 complete. Strict global scratch prepared,
not audited. All searches terminal. Next is global application then
strictness by existing second-derivative local-minimum corpus lemma.

C70 GLOBAL NONSTRICT SOURCE BARRIER VERIFIED: Global audit3 exit0,
criticalError_nonneg and boundaryRatio_ge_critical_barrier standard3.
Thus for every actual x>0, q>=1/12-7/(72k), with no free source or
RH premise. The first failed global attempt was an untyped filter
membership; typed eventual positivity repaired it. Strictness audit1
now active. Six completed scratch leaves have production copies
prepared but not yet production-audited/wired; strict seventh awaits
its audit. The generic trap has now been applied to the actual source;
this is a global trajectory constraint, not a conditional receiver.

C70 strict scratch audit2 exit0, all three actual capstones standard3:
criticalError_pos, boundaryRatio_gt_critical_barrier,
expandingMode_critical_upper. Only audit1 error was a convert-generated
instance equality; rfl discharged it before the function/scalar goals.
Seven production leaves prepared; sequential direct leaf audits active.
No global third-slope claim. No failed scratch cache retained.

Next C71 test: determine slope on/above the new affine critical barrier.
The exact compact variables satisfy t=r*q, so the barrier is
 t=r*(1/12-7h/72). The next transverse coefficient of P and Q, rather
than another numerical bound, decides whether this cone can prove S>0.
A structurally suggested replacement is q-(9-u²)*q²>b(h): it cancels
the next source-defect feedback. This is a conjecture, not established.
Search /tmp/tt_c71_affine_slope_search.json returned source incidence
and unrelated generic barriers; no applicable higher source constraint.
Use exact source ODE and polynomial jets to prove or reject it.

C70 COMPLETE: strict actual barrier q>1/12-7/(72k) for every x>0.
Seven production leaves passed sequential direct lake env lean audits;
15 imported type/axiom checks exit0, standard3 only. RHTower umbrella
wired; index exit0. Lint exit1 solely 12 unrelated missing umbrella
imports (same kind as earlier); no owned C70 finding. P3 card:
tt-global-critical-source-barrier.md. Frontier map updated. Scratch
sources/caches and audit driver cleaned after successful migration;
logs retained. Global third-slope, full quadratic, transported fourth
gap, join and all-rank closure remain OPEN. C71 affine-boundary
second jet / nonlinear source-defect attack active, not yet proved.

C71 COMPLETE: unconditional exists_affineCone_negative_slope falsifies
coarse-cone plus strict C70 affine barrier as a pointwise criterion.
Positive survivor quadraticSlope_sign classifies both signs by the
exact threshold 144a=r² along t=r*b(h)+a*h²; equality remains open.
Seven production leaves passed direct serial leaf audits; eleven
imported capstones standard3, audit exit0. RHTower umbrella wired;
index exit0. P5 tt-third-slope-affine-cone contains dependency-closed
paper proof; frontier map updated. C72 nonlinear actual invariant
q−Tq²>b is now the active conjecture, with inward forcing sign open.
Global actual slope/fullquadratic/fourthgap/join/allrank/RH remain OPEN.
