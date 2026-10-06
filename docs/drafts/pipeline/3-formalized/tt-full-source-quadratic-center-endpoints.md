# Route TT: complete source quadratic and exact center endpoints

Status: FORMALIZED. Dependency-closed paper proof, scratch and production audits
complete. Seven direct leaves and31 imported capstones use standard axioms only.
Endpoint determinant SIGN OPEN; RH remains open.

## Hard target

At the canonical fourth load, prove positivity of the actual normalized source
quadratic. The exact normalized-gap derivative then adds a nonnegative transport
square. C88 separately targets global positivity of its last derivative entry.
This card proves an exact two-endpoint reduction, not either endpoint sign or RH.

## Complete source identity

Write p=Q0=k-1/6 and H=m1*m3-m2². A and B are the complete native cofactors
through m7 (order fourteen); D is the complete third minor. All native moments
are identified with the actual source, with no truncated moment or source premise.
Set L0=A+3C p²H, L1=2C pH Q1 and S(P)=p Lie(P)-6P Lie(p).
The normalized derivative quadratic has positive denominator p⁷ and numerator

    S(L0)+p L1+x S(L1)+2 eta S(B)+eta² S(D).

The term p L1 retains the derivative of the literal center x. Native amplitude
cancels exactly. C92 production: ThetaCuspRatioQuadraticSource and QuadraticSlope;
ten imported capstones standard axioms only.

## All-order squared-drift representation

Use shear J=U Z and V=U². The proved chart derivation is 6U times the original
source Lie derivative. For integer source jets I_n, define

    W0=6K-1,
    W(n+1)=squareLie(Wn)-6nK(9-V)Wn+V(1-12K)Wn.

Induction proves square(Wn)=U^n shear(I_n). The full binomial reflection identifies
every moment, with no order cutoff. Complete weighted A,B,D,H have factors
6^28 U^22, 6^26 U^20, 6^24 U^18 and 6^12 U^8 respectively.

For square(P)=c U^m shear(Q), define

    T_m(P)=W0*(V squareLie(P)-6mVK(9-V)P)-6VP squareLie(W0).

Its square substitution is 36c U^(m+3) shear(S(Q)). The loaded coefficients are

    L0w=Aw+3C6^14 V^7 W0² Hw,
    L1w=2C6^13 V^7 W0 Hw W1.

With X=center/U, the complete weighted quadratic is

    T_22(L0w)+6VW0L1w+X T_23(L1w)
      +72V eta T_20(Bw)+1296V² eta² T_18(Dw).

It equals 6^30 U^25 times the unweighted numerator. C93 production:
ThetaCuspRatioWeightedSquareJets, WeightedCofactors, WeightedQuadratic;
eleven imported capstones standard axioms only.

## Actual center and exact endpoint determinants

The corpus's actual retained-center inequality proves, for every x>0,

    0<X=x/u <= Xmax=(k-2/3-J/u)/4.

Consequently lambda=X/Xmax lies in(0,1]. The actual weighted quadratic is exactly
(1-lambda) Q0+lambda Qmax. Its normalizer against the original derivative
quadratic is 6^30*u^25*(k-1/6)^7, strictly positive.

Only the first diagonal coefficient depends on center. With complete entries
A0,Amax,Bw,Dw, exact polynomial square completions give

    Dw*Qendpoint=(Dw*eta+Bw)²+(Aendpoint*Dw-Bw²).

Thus a sufficient companion to C88 is positivity of TWO complete endpoint
determinants at actual squared source coordinates. This endpoint relaxation is
not asserted necessary for the actual quadratic sign. No endpoint sign is assumed.
C94 scratch: ActualWeightedQuadratic and CenterEndpoints, ten capstones standard
axioms only. Production reaudits complete: ThetaCuspRatioActualWeightedQuadratic
and ThetaCuspRatioCenterEndpoints, wired into RHTower.lean.

## Open work

Prove the two endpoint determinant signs, or falsify the endpoint relaxation and
retain actual center selection plus the nonnegative transport gain. Finish C88
interior derivative controls and C77 production dependency closure. Compact gap,
correction-flux decay/join, integrated positivity, all-rank closure and RH remain
open. The previously proved uniform-direction gap tail does not settle these gaps.

Working log: docs/drafts/pipeline/1-in-progress/tt-kinetic-contraction-source.md.
