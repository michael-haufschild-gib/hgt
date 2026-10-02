# RN-P-7i: center source four-point inequality for actual projection

Status: falsified for the actual source. `ThetaRadialSourceCurvature` proves
the strict reverse near the equispaced center. See
`5-failed/theta-radial-four-point-projection.md` for the obstruction and
its positive radial sign-change survivor. The original reduction follows
as a record of the attempted producer.

## Hard target

For literal theta source k, prove or falsify, for t,z>0,

    k(t) k(t+z) k(z) < k(0) k(sqrt(t²+tz+z²))².       (F)

The corpus inputs are the common-tail integral, strict two-node determinant,
and strict decrease of source-normalized kernel rows on their ordered ray.
The signed-energy result RN-P-7h proves that actual feedback is positive,
so dropping it cannot prove the first-axis barrier. Target (F) attacks the
actual projection coefficients instead.

## Exact connection to the actual kernel

Write r(x)=-log(k(x)/k(0)), and L(x,y)=H(x,y)/(k(x)k(y)). In L(0,z),
substitute u=t(t+z); in L(z,z), substitute u=(z+v)²-z². The Jacobians are
exactly the respective first-moment weights. Under these substitutions,
(F) says the first exponential integrand is strictly smaller than the second:

    r(t)+r(t+z)+r(z) > 2r(sqrt(t²+tz+z²)).

Thus (F) would imply L(0,z)<L(z,z). The already proved ordered-row law gives
L(0,z)<L(0,0). These two strict inequalities make both coefficients of the
actual source representer M⁻¹(k(0),k(z)) positive.

For any y>z, strict decrease of both normalized rows then gives

    [k(0),k(z)] M⁻¹ [H(0,y),H(z,y)]ᵀ / k(y) < 1,

because the same quantity equals 1 at y=z. Hence the actual source residual
A is positive for every center-anchored ordered triple. This would remove
the first-axis boundary there, but would not settle arbitrary positive
anchors, the coordinate residual, or arbitrary rank.

## Why the known convexity is insufficient

Let R(u)=r(sqrt u). The four-point functional annihilates every polynomial
of degree at most two in u: quadratic and quartic terms in r cancel exactly.
Its cubic value is `3t²z²(t+z)²>0`. A nonnegative third derivative of R would
therefore be a promising producer; ordinary convexity of p is insufficient.

More precisely, put a=t², b=z², c=(t+z)², m=t²+tz+z². The functional is
R(a)+R(b)+R(c)-2R(m)-R(0). Its third-derivative Peano weight is
`((a-s)₊²+(b-s)₊²+(c-s)₊²-2(m-s)₊²)/2`, positive on `(0,c)`:
split at min(a,b), max(a,b), and m; on the middle interval the weight is
concave with positive endpoint values. This is a paper implication, not an
assumed source sign. The actual radial third derivative remains to be proved
or the four-point conjecture falsified analytically.

## Search audit

Deep searches for normalized center projection and row curvature returned
the existing normalized-row derivative and the exact representer equations,
with partial semantic coverage and source-only compiler metadata. They did
not supply the required comparison. Lexical `theta log sixth` returned
actual sixth log-jet and reflected Hankel formulas. The reflected sixth
polynomial is not a sign theorem for the sixth logarithmic derivative, so
it is not being silently substituted for the missing producer.

## Explicit differential producer to attack

For x>0,

    R'''(x²) = [x² p''(x)-3x p'(x)+3p(x)]/(8x⁵).

Therefore the next concrete source target is positivity of
`T(x)=x²p''(x)-3x p'(x)+3p(x)` on `(0,∞)`, rather than another unspecified
curvature hypothesis. Its derivative is
`T'(x)=x²p'''(x)-x p''(x)`. Fourth-log negativity alone gives p'''>0, but
not the needed comparison with p''/x. Global negativity of the sixth log
jet would be sufficient through evenness and integration; it has not been
established by the retrieved reflected-sixth theorem. Investigate T directly
using literal source jets and modular reflection, with no numerical test or
assumed global log-jet sign.

Two exact paper representations sharpen this sign question. For r=-log(k/k(0)),
evenness and Taylor's integral remainder give

    T(x) = (1/8) ∫₀ˣ (x²-u²)² r⁽⁶⁾(u) du
         = (1/2) ∫₀ˣ (3u²-x²) r⁽⁴⁾(u) du.

The first follows by combining the integral remainders for r', r'', r''':
`x²(x-u)²/2 - x(x-u)³/2 + (x-u)⁴/8 = (x²-u²)²/8`.
The second follows by integrating `T'=x²r⁽⁴⁾-xr'''` and using r'''(0)=0.
Thus individual sixth-jet negativity is stronger than necessary: the
actual weighted sixth-jet integral, or the signed fourth-jet covariance,
is enough. The proved r⁽⁴⁾>0 alone does not settle that signed integral.
This is the concrete analytic sign to attack with the literal theta source.

## Center audit in progress

The actual equispaced logarithmic defect is
`D(x)=2L(x)+L(2x)-L(0)-2L(sqrt(3)*x)`, L=log k.
Evenness and chain differentiation give D(0)=D'(0)=...=D^(5)(0)=0 and
`D^(6)(0)=12L^(6)(0)`. Thus an actual positive sixth log jet would give
the strict reverse of (F) at all sufficiently small t=z>0. This test uses
the corpus's exact modular center jets, not a numerical source evaluation.
The same sign would force T<0 nearby, through the derivative chain
`L5'=L6`, `(L3-xL4)'=-xL5`, and `T'=x(L3-xL4)`.
