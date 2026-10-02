# RN-P-7m: positive center coordinate energy

Status: formalized in `ThetaConfluentCoordinateCurrent.lean` and
`ThetaConfluentCoordinateEnergy.lean`. Both targeted `lake --old build`
checks and both final direct `lake env lean <leaf>` audits passed with no
leaf diagnostics. All eleven public theorem axiom checks contain only
propext, Classical.choice and Quot.sound. Both leaves are wired into RHTower.
Repository lint still fails on the same ten unrelated unreachable modules.

For the literal theta source k, put p=−(log k)', c=p', q=c(0),
I=∫₀∞t k'² and J₂=∫₀∞t k''². The theorem is

    E=J₂−3qI+qk(0)²>0.

This is the first nonzero center coefficient of the confluent coordinate
residual. It is not global coordinate-port positivity or RH.

## Corpus inputs

The source is positive, even and Schwartz. The complete curvature satisfies
c>0 and c'>0 for t>0. `ThetaCuspCurvatureProjectiveGlobal.projectiveEnergy_pos`
proves P=c'c''−cc'''>0, so R=c''/c is strictly decreasing.
`ThetaCuspNativeOddSchurFarTail` proves k/f→1 and k'/(fS)→−2 for first
atom f and scale S. `ThetaCuspExactCompletedC5SeamFarTail` gives c/S→4
and 1/S→0. These are actual-source facts, not assumptions on a generic source.

## Global current

p(0)=c'(0)=0. Increasing c gives p−qt>0. Define

    T=c'−pR,
    W=c²−q²−pc',
    F=p(c+2q)−qt(2c+q).

They vanish at zero and satisfy T'=pP/c²>0, W'=cT>0,
F'=W+2(p−qt)c'>0. Thus T,W,F>0 on the positive axis. The exact identity

    G=pc+3tc²−tpc'−6qtc+2qp
     =tW+F+2t(c−q)²

proves G>0 globally. No source interval is replaced by a numerical bound.

## Boundary and integral audit

Define f_flux=t k'³/k and the polynomial Schwartz remainder

    P_raw=3t k''²−t k'k'''+k'k''−6qt k'²+6qt kk''−2qkk'.

Differentiation, using k'=−pk, k''=(p²−c)k and
k'''=(−p³+3pc−c')k, gives f_flux'=P_raw−Gk².
Every term of P_raw is an integrable polynomial Schwartz product.
Integration by parts gives

    ∫k'k''=0,  ∫t k'k'''=−J₂,
    ∫t kk''=k(0)²/2−I,  ∫kk'=−k(0)²/2,

hence ∫P_raw=4E. The derivative vanishes at zero by source parity.
The weighted Schwartz products give all polynomial boundary limits.

The quotient flux needs a separate argument. The actual tail limits give
p/S→2, hence r=c/p²→0. Eventually

    f_flux=(t k'k'')/(1−r)→0.

No assertion that 1/k preserves Schwartz regularity is used.

Finally A(b)=∫₀ᵇP_raw−f_flux(b) satisfies A(0)=0 and
A'(b)=G(b)k(b)²>0 for b>0, while A(b)→4E. Thus 4E≥A(1)>0.
This avoids assuming improper integrability of Gk² before proving the sign.

## Remaining RN gates

Formalize the actual mixed-row jets and B_*(y)/y³→k(0)E/(3β)>0;
then prove the finite old-pair coordinate projection limit. Global
compensation, arbitrary-rank positivity and the retained arithmetic
RH transfer remain separate obligations. Equality of kernel diagonals
alone does not identify their off-diagonal entries.
