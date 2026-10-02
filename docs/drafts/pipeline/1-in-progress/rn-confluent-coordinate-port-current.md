# RN-P-7l: actual confluent coordinate-source residual

Status: coordinate sign open; global cubic current and strict center energy
formalized and audited. This follows RN-P-7k's source
residual proof rather than assuming the coordinate port has the same sign.

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
proofs remain open. The sign `J₂−3q I+q K²>0` is now proved without premises
in `ThetaConfluentCoordinateEnergy.coordinateEnergy_pos`. A finite pointwise
center log jet alone was not used to determine this integral sign.

Next conjecture: B_*(y)>0 for every y>0. Prove or falsify this exact
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

### Next exact transfer after the energy audit

For T(y)=H_x(0,y), the Schwartz correlations give
T(0)=0, T'(0)=β, T''(0)=0, T'''(0)=qK²−2J₂.
Indeed the last identity uses ∫kk'''=qK²,
∫k'k''=0 and ∫t k'k'''=−J₂. Hence B_* has its first two derivatives
zero at the center and B_*'''(0)=2KE/β>0. The exact next target is
`B_*(y)/y³→KE/(3β)>0`, followed by the literal finite old-pair coordinate
projection limit. This supplies an actual open chamber with both residual
ports positive. It does not establish the global compensation barrier,
arbitrary-rank positivity, or transfer to the arithmetic off-diagonal kernel.
