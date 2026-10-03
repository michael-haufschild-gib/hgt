# RN-P-7l: actual confluent coordinate-source residual

Status: global confluent coordinate comparison formalized and audited.
For every y>0, B_*(y)>0 and both actual finite-pair ports are positive
for sufficiently small z>0. This file retains the derivation history;
certificate: P3 `theta/rn-global-confluent-coordinate-residual.md`.
Active successor: `rn-center-schur-coordinate-row-flow.md`, where finite
old-node spacing and its complete compensation remain open.

Write k for the actual source, H for the actual full-tail kernel,
K=k(0), I=∫₀∞t k'(t)²dt and β=2I−K²>0. In the confluent old basis
(k,k'), the Gram is diag(H(0,0),β), the source endpoint vector is (K,0),
and the coordinate-source endpoint vector is (0,K).

For fixed y>0 the literal coordinate residual therefore has candidate limit

    B_*(y)=y k(y)−K H_x(0,y)/β.

The exact common-shift identity gives
`H_x(0,y)+H_y(0,y)=−y K k(y)`. For the normalized row
`L(y)=H(0,y)/(K k(y))` and p=−(log k)', this becomes

    B_*(y)/k(y) = [2I y+K²(L'(y)−p(y)L(y))]/β.

The already proved L'<0 does not decide this expression: its negative
contribution must be compared with the positive linear term. The actual
projection has been retained. No inverse-coefficient sign has been assumed.

The center leading linear terms cancel. A further exact paper expansion,
using J₂=∫₀∞t k''(t)²dt and q=p'(0), gives

    B_*(y)/k(y) = [J₂−3q I+q K²] y³/(3β)+o(y³).

Indeed `H_xy(0,0)=β`,
`H_xyyy(0,0)=q K²−2J₂`, and `k(y)=K(1−q y²/2)+o(y²)`.
Schwartz differentiation and half-line integration by parts justify these
identities; k'(0)=0 removes the other endpoint terms. Their mixed-kernel Lean
proofs are now audited in `ThetaTailConfluentCoordinateJets`. The sign
`J₂−3q I+q K²>0` is proved without premises
in `ThetaConfluentCoordinateEnergy.coordinateEnergy_pos`. A finite pointwise
center log jet alone was not used to determine this integral sign.

Original global conjecture, now proved: B_*(y)>0 for every y>0. The target was this exact
source integral law; do not replace it by row monotonicity or independent
coefficient positivity. If it fails, audit the actual compensation barrier
and retain a nontrivial positive survivor before retiring that extension.

The corpus search for theta tail coordinate residuals and confluent source
derivatives had partial coverage and returned no matching producer. The
source Ward tail and differentiability results were applicable; unrelated
conditional RH transfer hits do not close this sign problem.

## Positive mixed-derivative current

A new exact integration-by-parts reduction identifies the sign of the
uncompensated mixed row. For y>0, put

    C_y(t)=t[p(t+y)−p(t)]/y−p(t),
    w(t)=k(t)²/K²,
    R_y(t)=K k(t+y)/(k(t)k(y)).

The boundary derivative of `t k(t)k(t+y)` integrates to zero. Subtracting
it from the literal x-derivative integrand gives

    H_x(0,y)/(y K k(y)) = ∫₀∞ C_y(t) w(t) R_y(t) dt.       (2)

Strict convexity of p gives `(p(t+y)−p(t))/y>p'(t)` for t,y>0;
RN-P-7k's positive current gives `t p'(t)−p(t)>0`. Hence C_y(t)>0
throughout the positive half-line, so H_x(0,y)>0. This sign has a complete
paper proof from the inspected corpus; Lean pending.

The remaining compensated sign is now the exact integral comparison

    ∫ C_y w R_y < ∫ C_0 w,       C_0(t)=t p'(t)−p(t).    (3)

This is equivalent to B_*(y)>0, because the right integral is β/K².
Convexity increases C_y while source log-concavity decreases R_y; neither
fact alone decides their product. Pointwise domination is unavailable near
t=0: C_0 vanishes cubically, whereas for fixed y>0, C_y has positive linear
coefficient p(y)/y−q. Thus the actual weighted integral must be controlled.
The first y-variation of its integral cancels by another boundary derivative;
the first remaining center sign is the cubic invariant already recorded.

## RN-P-7m: Gaussian-cancelling current for the cubic coordinate sign

Let E=J₂−3qI+qK². Formal half-line integration by parts suggests

    4E=∫₀∞ G_q(t) k(t)² dt,
    G_q=p p'+3t(p')²−t p p''−6qt p'+2qp.             (4)

To derive (4), use ∫t k' k'''=−J₂ and
`2J₂=∫t[(p')²+p²p'−p p'']k²`, then integrate the derivative
of `t p p' k²`; finally `2I=∫(p+t p')k²` and `∫p k²=K²/2`.
This derivation still needs an integrability and boundary audit for the
logarithmic flux `t p³ k² = −t k'³/k`. Schwartz regularity alone does not
control division by k. Thus (4) is not yet an established improper-integral
identity. Its raw polynomial remainder is integrable by Schwartz regularity:
`G_q k²=P−(t k'³/k)'`, where
`P=3t k''²−t k'k'''+k'k''−6qt k'²+6qt kk''−2qkk'`, and
`∫P=4E`. Actual source tail bounds must discharge the extra flux obligation.

Resolved conjecture: the actual G_q(t)>0 for every t>0. This is a sufficient producer
for the first nonzero center coordinate-residual sign, not yet a proof of
global B_*(y)>0. It cancels identically for a Gaussian decay p=qt.
For actual p=qt+a t³+b t⁵+O(t⁷), a=−L4(0)/6>0 and b=−L6(0)/120<0,
G_q=(24a²−12qb)t⁵+O(t⁷), so the actual center sign is strict positive.
The corpus tail limits p/S→2, p'/S→4, p''/S→8 imply
G_q/(t S²)→32, hence eventual positivity. The intervening source interval
was the hard part; the following global proof resolves it without inferring
an interior sign from endpoint signs.

### Global sign proof from the corpus projective reserve

The inspected `ThetaCuspCurvatureProjectiveGlobal.projectiveEnergy_pos`
provides the missing global mechanism. Write c=p', q=c(0), R=c''/c and
P=c'c''−cc'''>0. Thus R'=−P/c²<0. Set

    T=c'−pR,
    W=c²−q²−pc',
    F=p(c+2q)−qt(2c+q).

All three vanish at zero. Their exact derivatives are

    T'=pP/c²>0,
    W'=cT>0,
    F'=W+2(p−qt)c'>0.

Here p>0, c>0, c'>0, and p−qt>0 follow from the actual source curvature
signs and center parity. Consequently

    G_q=tW+F+2t(c−q)²>0                 (t>0).

This closes the global pointwise current sign without a compact interval
estimate. `ThetaConfluentCoordinateCurrent.coordinateCurrent_pos` formalizes
it. The improper logarithmic flux audit below supplies the remaining step to E>0.

### Flux audit without assuming logarithmic integrability

The corpus first-atom relative source and slope limits imply p/S→2. Its
curvature limit gives c/S→4, while 1/S→0. Therefore r=c/p²→0. The raw source
identity k''=(p²−c)k yields, eventually,

    t k'³/k = (t k'k'')/(1−r) → 0.

The numerator tends to zero by the weighted Schwartz-product theorem;
the denominator tends to one. This proves the missing boundary limit
without asserting that a quotient of Schwartz functions is Schwartz.
To infer E>0, define A(b)=∫₀ᵇ P−b k'(b)³/k(b). Then A(0)=0,
A'(b)=G_q(b)k(b)²>0 for b>0, and A(b)→∫₀∞P=4E. Thus
4E≥A(1)>0. This argument requires only the already justified integrability
of polynomial Schwartz products P; integrability of G_q k² follows later
if needed. `ThetaConfluentCoordinateEnergy` now formalizes this argument.
Both leaves passed targeted `lake --old build` and final direct
`lake env lean <leaf>` audits; all eleven public theorems have only
propext, Classical.choice and Quot.sound. Both are wired into RHTower.
See P3 `theta/rn-confluent-coordinate-energy.md` for the complete certificate.

### Exact transfer after the energy audit

For T(y)=H_x(0,y), the Schwartz correlations give
T(0)=0, T'(0)=β, T''(0)=0, T'''(0)=qK²−2J₂.
Indeed the last identity uses ∫kk'''=qK²,
∫k'k''=0 and ∫t k'k'''=−J₂. Hence B_* has its first two derivatives
zero at the center and B_*'''(0)=2KE/β>0. The proved limit is
`B_*(y)/y³→KE/(3β)>0`, followed by the literal finite old-pair coordinate
projection limit. This supplies an actual open chamber with both residual
ports positive. It does not establish the global compensation barrier,
arbitrary-rank positivity, or transfer to the arithmetic off-diagonal kernel.

### RN-P-7n completed formal audit

The mixed-row derivative and third-quotient APIs in CenterLimits have passed
their targeted dependency build. `ThetaTailConfluentCoordinatePort` retains
the exact inverse-Gram residual and its confluent limit. The new
`ThetaTailConfluentCoordinateJets` implementation proves the three center
mixed-row derivatives by Schwartz correlation differentiation and half-line
integration by parts, then uses E>0 to prove an actual ordered chamber
`∀ᶠ y→0+, ∀ᶠ z→0+, z<y ∧ A_z(y)>0 ∧ B_z(y)>0`.
All four changed leaves passed targeted `lake --old build` and final direct
`lake env lean <leaf>` checks. All 26 public theorems use only propext,
Classical.choice and Quot.sound. Both new leaves are wired into RHTower.
Lint reports twelve unrelated unreachable modules; no owned proof violation.
The chamber has nested quantifiers, not a uniform two-variable neighborhood.
No global chamber propagation is claimed. See P3
`theta/rn-confluent-coordinate-chamber.md` for the exact certificate.

### Global canonical-current conjecture

For C=C_y and w_y=k(t)k(t+y)/(Kk(y)), set
λ=[p(t+y)−p(y)]/[p(t)+p(t+y)]. Formal differentiation and subtraction of
the vanishing t-flux give N'=∫Jw_y, where

    J=∂yC−λ∂tC−(∂tλ)C.

The minus sign on ∂tλ corrects an earlier working-log error. Write
a=p(t), b=p(t+y), r=p(y), u=c(t), v=c(t+y). Direct algebra gives

    y²(a+b)²J = y(2t+y)[a(a+r)v+b(b−r)u]
                −(b²−a²)[t(a+b)+y(b−r)].

Conjecture: this is strictly negative for every t,y>0. Together with an
audited differentiated integral and boundary flux, this would make N
strictly decreasing and prove the global comparison (3). Neither the
three-point inequality nor that integral audit is yet proved.

The endpoint coefficient is supported by the existing chord reserve:
J/t→−c(y)/y−p(y)/y²+2q c(y)/p(y) as t→0+. Put m=p(y)/y.
The reserve gives m>q(2c+q)/(c+2q), which implies
m²+mc−2qc>0; at the lower endpoint the numerator reduces to
q²(c−q)²/(c+2q)². Thus this endpoint sign is negative. This is a paper
deduction from audited source inequalities, not a proof of global J<0.

### RN-P-7o: all-spacing canonical boundary

The current global sign remains open after testing projective ratio descent.
The next exact formal target is stronger than a joint small-spacing germ:
for every y>0, J(t,y)<0 for all sufficiently small t>0. Let Q be minus
the division-free numerator above, and let

    E_y=p(y)²+y p(y)c(y)−2q y²c(y).

Then Q(0,y)=0 and Q_t(0,y)=p(y)E_y. The chord reserve gives the exact
positive identity, with A=c(y)+2q, B=q y(2c(y)+q), F=p(y)A−B>0:

    A²E_y=F[A p(y)+B+y c(y)A]+q²y²(c(y)−q)²>0.

Thus Q_t(0,y)>0 globally in y. Formalizing the literal differential
current and this boundary sign supplies a proved initial condition for
its interior continuation, not a proof of that continuation.

This boundary is now formalized in `ThetaCoordinateCanonicalBoundary`.
`canonicalCurrent_eq_margin` checks the full derivative formula, and
`eventually_canonicalCurrent_neg` proves the negative left boundary for
every y>0. The targeted `lake --old build`, final direct `lake env lean`
and all six public theorem axiom audits passed. Only propext,
Classical.choice and Quot.sound occur. The module is wired into RHTower.
Certificate: P3 `theta/rn-canonical-coordinate-boundary.md`.

An equivalent interior formulation retains the actual normalized source
potential V(t,y)=U(t)+U(t+y)−U(0)−U(y), where U'=p. Along a level of V,
dt/dy=−λ. Put L=2t+y, A=p(t)+p(t+y), and g=p(t+y)−p(t).
Then C/A=(Lg/(yA)−1)/2, and direct differentiation gives

    d/dy [Lg/(yA)] at fixed V = −2Q/(y²A³).

Thus the hard sign is exact decrease of this ratio along each positive
source-potential level. This is a paper reformulation, not a producer or
a substitute for the weighted-integral and boundary audits.

### RN-P-7q: global canonical producer and finite-primitive transfer

The interior now has a dependency-closed paper proof. Actual curvature
log-convexity makes tc/p strictly increasing and pays the cross term in
Q=Q_base+y[p(t+y)−p(t)−p(y)]Q_cross. The projective reserve
V=cc'−pc''>0 makes c concave in U=−log k. The new K-current
K=3tc²−3pc−tpc', K'=tV+4c'(tc−p)>0, makes t/p convex in U.
The two strict trapezoids pay Q_base>0. Consequently J<0 globally.
ThetaCoordinateCanonicalGlobal is written; complete Lean audit pending.

The following transfer has a paper proof without presupposing integrability
of Jw. Fix y>0, write K0=k(0), w=k(t)k(t+y)/(K0 k(y)), M=Cw, and F=λM.
The literal raw numerator is

    L=(t+y)k'(t)k(t+y)−tk(t)k'(t+y),  M=L/(yK0k(y)).

The centerMixedRow integrand minus L is (tk(t)k(t+y))'. Weighted
Schwartz decay and t=0 give zero boundary contribution. Thus
N(y)=T(y)/(yK0k(y))=∫M. Differentiation is justified by writing L as
three half-line Schwartz correlations (including t-weighted factors):

    L_y=k'(t)k(t+y)+(t+y)k'(t)k'(t+y)−tk(t)k''(t+y),
    M_y=[L_y−(1/y+k'(y)/k(y))L]/(yK0k(y)).

This is integrable by the same Schwartz correlation API. The canonical
speed obeys 0≤λ≤1 for t≥0: p is increasing, p(0)=0, and
p(t+y)−p(y)≤p(t)+p(t+y). Since L→0, F→0. At t=0, C=λ=0.
The exact source scores give w_t=−[p(t)+p(t+y)]w and
w_y=−[p(t+y)−p(y)]w, so F_t=M_y−Jw.
For G_y(b)=∫₀ᵇM_y−F(b), one has G_y(0)=0 and G_y'=Jw<0 on b>0.
Its limit is N'(y). Strict decrease gives N'(y)≤G_y(1)<0.
The existing mixed-row center derivative T'(0)=β and T(0)=0 give
N(0+)=β/K0². Hence N(y)<β/K0² for every y>0, and

    B_*(y)=yk(y)[1−K0²N(y)/β]>0.

Combined with the audited literal projection limit and source residual
limit, this will give both actual ports positive at every fixed y>0 for
all sufficiently small old-node spacings z>0. The finite z threshold may
depend on y. Finite-pair propagation, arbitrary rank and arithmetic RH
transfer are still separate problems. This paragraph is a paper proof;
no claim of a completed Lean integral-transfer theorem is made yet.

### RN-P-7r: complete global confluent audit

ThetaCoordinateCanonicalFlux and ThetaTailConfluentCoordinateGlobal both
passed targeted --old builds and final direct lake env lean checks without
own diagnostics. All 19 public theorem axiom audits contain only propext,
Classical.choice and Quot.sound. Together with the canonical-current
chain, six leaves and 43 public theorems are audited; five new modules
are wired. The actual global B_* sign and all-spacing coalescent two-port
chamber are now Lean theorems, not paper conjectures.

Repository lint reports 11 unrelated unreachable modules and no owned
proof violation. Certificate: P3 theta/rn-global-confluent-coordinate-residual.md.
The live mathematical task is the finite-pair contact forcing in
rn-center-schur-coordinate-row-flow.md, followed by arbitrary-rank and RH
transfer obligations. The RH goal remains active.
