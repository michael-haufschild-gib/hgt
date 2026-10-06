# TT — Complete terminal source, principal slope and quadratic remainder

- Stage: formalized in Lean4.
- Route: TT, native source identities needed for the interior surplus sign.
- Parent: `tt-surplus-even-coefficient-orientation.md`.

On U=3 put Y=3K+1 and T=J-Y-1. The complete native Lie field becomes
`12*(Y*(Y+T+1)*∂Y+T*∂T)` and the normalized jet step becomes
`Y*(Y+T+1)*∂Y+T*∂T+5/4-Y`.

Define `B_0^a=1`, `B_(n+1)^a=T*(B_n^a)' +(T+a)*B_n^a`.
Every native jet, divided by12^n, satisfies

    T*P_n=2Y*T*B_n^(9/4)+3Y*B_n^(5/4)-3(T+Y)*(5/4)^n.

This is a polynomial identity, including T=0, with the full source seed
retained. Native reflected moments scale by12^n and satisfy the exact
cleared Cauchy convolution of these complete jets, for every order n.

The complete jets also have the exact affine form
`P_n=Y*A_n(T)-3*(5/4)^n`, with `A_0=2` and
`A_(n+1)=T*A_n'+(T+9/4)*A_n+3*(5/4)^n`. This identity is now formalized
against the original native jets. No terminal variable is divided out.
The univariate realization has degree at most n and leading coefficient2.
For n≥1 its next coefficient is `n²+(7/2)n+3`; for n≥2 its third is

    n(n-1)(n-2)(n-3)/4+(31/12)n(n-1)(n-2)
      +(105/16)n(n-1)+(15/4)n.

Both formulas are proved by induction from the ENTIRE recurrence. Their
small-order exceptions are retained; the polynomial continuations at n=0
and n=1 are not substituted for actual nonexistent coefficients.

For every positive even order, the COMPLETE reflected source is
`R_n=Y²*H_n(T)-6Y*K_n(T)`. Alternating binomial cancellation gives both
principal reflected rows, with the exceptional orders2/4 retained. The
cross-polynomial coefficients and degree bounds are also source-derived.

The inverse-clock determinant polynomial N satisfies
`N(h)=h^21*M(Y/h,T/h)` for the exact pulled native third minor M, with

    N_0=0,
    N_1=-4608*12^18*Y^4*(T+Y)^2*T^14.

The complete two coordinate derivatives are homogenized before taking the
native Lie derivative. Mixed first-variation symmetry reduces their head
pairing to the proved rank-two determinant identity. No lower source term
is discarded. The resulting polynomial regularization R satisfies

    R(h)=h^22*S(Y/h,T/h),
    R_0=221184*12^18*Y^5*(T+Y)^2*T^15,

where S is exactly `pull integerThirdSlope`. The nonzero-clock condition
only defines this coordinate evaluation; the coefficient identities have
no sign/source premise. This closes the native degree20/22 minor/slope
identification, not the full source value sign.

The exact square-chart incidence is

    reducedSlope(9,(Y-1)/3,(T+Y+1)/3)=pull(integerThirdSlope)(Y,T)/3.

It transports the ENTIRE regularization, including all lower terms. For
any original square-source polynomial P, the actual observable minus
P(9,k,1/3) has superpolynomial decay in k. Denominator clearing transfers
the existing compact-coordinate flatness without assuming k bounded.

There is also an exact quadratic remainder theorem. In the free algebra
`W²=-W/3-e`, the constant remainder of `W²*(W-1)^15` is

    e/6^15 * deficitShape(1-36e).

Conjugate selection and the source-derived odd-part identity prove this
also at the double root; no discriminant is divided out. The displayed
reduced principal polynomial, scaled by73728*12^18, is strictly positive
on0<e≤1/36 and has sixth coefficient
`-(8192/3)*189994*12^18`. This is the exact positive-value survivor of the
ordinary-coefficient obstruction. The complete finite family now lifts to C[T][h]. Its exact quadratic image
under W²=(h-4h²)/3-e+(7h-1)W/3 and T=W-1-h, read at W=3zh and divided
by3, has h0 coefficient IDENTICALLY the displayed principal surplus
polynomial, for every complex z. Thus its e6 coefficient at h0 is the
negative value above, retaining every lower source term. The complete unscaled source incidence and all-coefficient transport are
now proved: G_z(h,e)=h^22*Q_k,z(e/h²), k=(1/h-1)/3. Thus its nth
coefficient is h^22*(1/h²)^n times the original nth coefficient, and its
sixth coefficient is h^10*Q6. Bivariate variable swap makes that slice a
polynomial in h. Its negative value at h0 proves eventual strict negativity
of flat-terminal Q6, for every fixed complex reading z. Universal quadratic reduction identifies Q6 as a fixed original-source
polynomial, so the flat-transfer theorem now proves the ACTUAL normalized
Q6 limit and eventual strict negativity. Eighth-to-seventh absorption leaves
Q6 unchanged for every complex mass. Hence ordinary coefficientwise
nonnegative representations of the actual absorbed source eventually fail.

The same absorption of the principal polynomial is strictly positive on
0<e<=1/36, with an exact mixed surplus/deficit decomposition. It is the
h0 fiber of the complete graded absorbed family with mass(1-h)^2/36;
the original maximal mass scales to exactly this polynomial. The entire
finite-clock absorbed polynomial now also satisfies the lossless identity
G_abs(h,e)=h^22*Absorb(Q_k,z,M_k)(e/h²), with M_k=9*(a+b²/4). This closes
the obstruction together with its positive survivor; full compensated
interior source value and RH remain open. Exact proof and scope:
`../5-failed/tt-ordinary-absorbed-surplus-coefficients.md`.

## Lean and validation

All modules below are in `formal/GaloisForLFunctions/RHTower/`, with prefix
`ThetaCuspRatio` and suffix `.lean`:

- TerminalKineticJets
- TerminalReflections
- TerminalPrincipalAlgebra
- TerminalAffineJets
- TerminalAmplitudePolynomial
- TerminalAmplitudeReverse
- TerminalReflectedLeading
- TerminalReflectedSecond
- TerminalReflectedAffine
- TerminalCrossHeads
- TerminalHomogeneousReflections
- TerminalHomogeneousMinor
- TerminalReflectedDerivatives
- TerminalMinorDerivatives
- TerminalHomogeneousSlope
- TerminalQuadraticPrincipal
- TerminalFlatTransfer
- TerminalSquareIncidence
- TerminalGradedFamily
- TerminalQuadraticChange
- TerminalGradedRemainder
- TerminalGradedSource
- TerminalQuadraticScale
- TerminalGradedSpecialization
- TerminalSurplusRescale
- TerminalGradedCoefficient
- TerminalCoefficientSlice
- TerminalUniversalSurplus
- TerminalActualCoefficient
- TerminalAbsorbedPrincipal
- TerminalAbsorbedTransport

All31 production leaves passed direct `lake --old env lean -o ... <module>`
audits without warnings. All are wired into RHTower; no umbrella/full build
or raised limits. The original11 imported capstones and new50 imported
capstones use only `propext`, `Classical.choice`, `Quot.sound`. All50 new imported production checks passed in
`/tmp/tt_terminal_extended_axioms.lean`; superseded scratch sources/caches
were removed, audit logs retained. Nine additional imported capstones for
the last three leaves passed in `/tmp/tt_terminal_quadratic_flat_axioms.lean`,
with every axiom set a subset of the same standard three. Thus all59 new
imported capstones passed; their superseded scratch sources/caches were
removed after audit. Logs retained.

The thirteen new graded/source leaves passed production audits without warnings.
Their first52-capstone imported-production audit passed:
`/tmp/tt_terminal_graded_production_axioms.lean`. Every axiom set is a subset
of the standard three (generic quadratic change/scaling use two). Four further imported capstones passed in
`/tmp/tt_terminal_absorbed_transport_production_axioms.lean`, also standard3.
All thirteen superseded scratch sources/caches cleaned after imported audit;
logs retained.

Latest formal lint `/tmp/tt_terminal_absorbed_transport_lint.log` exits1:
four unrelated unreachable modules (KuznetsovEisensteinGrowth,
Sieve.TwistedSelbergCoefficient, Sieve.TwistedSelbergFactorization,
HTGeometry.ResetPathSingularity), plus
large-file warnings. No terminal-module error; not a globally green gate.

Still open: full compensated interior surplus VALUE, subsequent source
quadratic, fourth gap, join/all-rank closure and RH. Universal coefficient
specialization, actual Q6 sign and the absorbed principal survivor are closed.
