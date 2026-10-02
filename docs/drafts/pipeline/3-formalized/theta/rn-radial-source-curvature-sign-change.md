# RN-P-7i: actual radial source curvature changes sign

Status: formalized in `ThetaRadialSourceCurvature.lean`, wired into
`RHTower.lean`. Targeted `lake --old build` and final `lake env lean
GaloisForLFunctions/RHTower/ThetaRadialSourceCurvature.lean` passed.
All eight public theorems use only propext, Classical.choice and Quot.sound.

## Actual center sign

The corpus's exact center raw jets satisfy `f_j=m F_j(X)`, with positive
modular mass m and actual `X>191/10`. Its sixth logarithmic numerator is

    C(X)=-F₀²F₆+15F₀F₂F₄-30F₂³.

Expanding `-C(191/10+y)` gives strictly positive coefficients for y≥0;
the symbolic ring/positivity proof passes. The Bell identity gives

    -k(0)³ L⁽⁶⁾(0)=m³ C(X)<0,

where L=log k. Hence `L⁽⁶⁾(0)>0`, unconditionally for the literal source.

## Negative local radial curvature

Put `T(x)=-x²L'''(x)+3xL''(x)-3L'(x)`. Continuity keeps L⁽⁶⁾ positive
on a neighborhood of zero. Evenness gives L⁽⁵⁾(0)=L'''(0)=L'(0)=0.
On a sufficiently short positive interval, the exact derivative chain is

    (L⁽⁵⁾)'=L⁽⁶⁾>0,
    (L'''-xL'''')'=-xL⁽⁵⁾<0,
    T'=x(L'''-xL'''')<0.

All three functions vanish at zero, so T<0 throughout this interval.

## Actual four-point inequality fails

Let `D(x)=2L(x)+L(2x)-L(0)-2L(sqrt(3)x)`. Its derivatives of orders
zero through five vanish at zero, and `D⁽⁶⁾(0)=12L⁽⁶⁾(0)>0`.
Continuity and six successive strict monotonicity arguments give D(x)>0
for every sufficiently small x>0. Exponentiation yields

    k(x)² k(2x) > k(0) k(sqrt(3)x)².

This is the strict reverse of RN-P-7i's proposed producer at t=z=x.
It does not decide the integrated normalized-kernel comparison or the
actual compensated Schur barrier.

## Positive survivor: a true source transition

The existing literal tail limits are `-L''/S→4`, `-L'''/S→8`, where
`S(x)=pi exp(2x)>0`. Therefore

    [-L'''/S - (3/x)(-L''/S)] → 8.

For positive large x, multiplication by x²S gives
`-x²L'''+3xL''>0`. The remaining term `-3L'=3p` is nonnegative on the
positive ray. Consequently T>0 eventually. Together with its negative
local sign, continuity gives at least one positive zero of T.

The survivor retains exact source geometry: a negative central region and
a positive cofinal region separated by a genuine radial-curvature zero.
It is stronger than a generic counterexample to a convexity implication.
No numerical source evaluation, RH premise, or assumed higher-log sign
enters the proof.

## Consequence for the RN loop

The pointwise four-point producer is false. Keep the actual integrated
comparison, whose sign could still receive positive contributions away
from the center. Proving projection compensation and arbitrary-rank
positivity remains the goal; this obstruction does not falsify RH.
