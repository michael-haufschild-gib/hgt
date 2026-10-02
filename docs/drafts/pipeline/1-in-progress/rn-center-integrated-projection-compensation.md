# RN-P-7j: integrated center projection compensation

Status: exact paper decomposition; actual sign open. RN-P-7i's strict
reverse central regime is now formalized and audited. RN-P-7k bypasses
this stronger coefficient-sign condition when proving actual source-residual
positivity near a coalescing old pair. This is a retained optional producer,
not the current missing premise of that local result.

Let r(x)=-log(k(x)/k(0)), `L(x,y)=H(x,y)/(k(x)k(y))`, z>0. For u≥0 set

    t_z(u)=(sqrt(z²+4u)-z)/2,
    B_z(u)=2[r(sqrt(z²+u))-r(z)],
    Δ_z(u)=r(t_z(u))+r(t_z(u)+z)+r(z)-2r(sqrt(z²+u)).

The exact quadratic substitutions in the two tail integrals give

    N(z):=L(z,z)-L(0,z)
         =∫₀∞ exp(-B_z(u)) [1-exp(-Δ_z(u))] du.       (1)

The positive and negative parts of this integrand, not a pointwise source
inequality, must be compared. The actual first representer coefficient is

    d₁ = k(0)k(z)² N(z)/det M.

Thus N has exactly its sign. The second coefficient is already positive
by strict decrease of the ordered normalized row at zero.

## Concrete conjecture

Determine the sign of N(z) for the literal source on the whole positive
ray. If N≥0, the actual source representer has nonnegative coefficients;
the ordered-row theorem then forces A>0 for every new node y>z. A negative
N would falsify this coefficient shortcut, not the actual compensated
barrier or RH. Retain the full projection equations in either case.

## Local structure of the integrand

Exact differentiation at u=0 gives Δ_z(0)=Δ'_z(0)=0 and

    Δ''_z(0)=[z p'(z)-3p(z)+2z p'(0)]/(2z³).

This numerator is zero for every quadratic-plus-quartic r. Its first
nonzero small-z term comes from the sixth log jet; the now tested center
sign forces a negative local integrand for small z. The far-source region
can still contribute positively. Equation (1) preserves both contributions.

## Scope and remaining RH obligations

This is an actual two-node projection problem on route RN. Even its
resolution would leave general positive anchors, the coordinate residual,
arbitrary-rank full-tail positivity, and the retained signed transfer to
the RH gate. The prospective full-tail kernel must not be identified with
the arithmetic cut kernel merely because their diagonals agree; the
working log already records that distinction.

## First necessary integrated sign at the center

Write q=p'(0), J=H(0,0), and I=∫₀∞ t k'(t)² dt. Differentiating the
actual tail integrals twice at zero (Schwartz domination supplies the
paper justification) gives

    lim_(z→0) N(z)/z² = [2I+qJ-2k(0)²]/[2k(0)²].

Indeed H(0,z) has zero first derivative and second derivative -2I, while
J(z)'=-2z k(z)² and k'(0)=0, k''(0)=-q k(0).
The numerator also has the exact integration-by-parts form

    2I+qJ-2k(0)²
      =∫₀∞ [t p'(t)-3p(t)+2qt] k(t)² dt.

This identifies the actual nonlocal invariant needed to test N≥0 near
zero. The sign is open; the local sixth-jet sign alone does not decide it.
Do not replace the whole weighted integral by the sign near its endpoint.
