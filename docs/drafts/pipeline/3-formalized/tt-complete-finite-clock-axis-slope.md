# TT: complete finite-clock axis slope

- **ID:** TT-C74
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** docs/reports/rh-current-frontier-map.md, Route TT; C73 nonlinear-cone programme.
- **Statement:** The complete compact third slope satisfies Q(h,0,0)>0 for every real 0<h≤1.

## Frontier contribution

C73 asks for positivity under the exact nonlinear barrier and the strict
coarse source cone. The finite-clock axis is a necessary boundary test:
letting r→0 and t=q*r remains feasible when b(h)<q<A(h)/(6+4h), where
A(h)=1−2h/3−4h²/9 and b(h)=1/12−7h/72. The difference
A−(6+4h)b=1/2−5h/12−h²/18 is positive throughout 0≤h≤4/5.
Thus a negative finite-clock axis slope would obstruct the cone claim.
This theorem excludes that mechanism on the whole admissible interval.
It is a complete polynomial sign law, not a clock sample or a tail jet.
Global interior positivity, the full source quadratic, fourth Schur gap,
join/all-rank closure and RH remain OPEN.

## Complete paper proof [PROVED HERE]

Let A=(6^24)*24^9*720>0 and let p be the degree15 polynomial
`axisMinorShape`, whose sixteen rational coefficients are given in
ThetaCuspRatioAxisCompleteMinor. The exact five axis moment identities,
substituted into the complete third determinant, give

    P(h,0,0)=A*h²*p(h).

The axis field is h'=-36h²−12h³. Substitution into the full slope operator,
including its clock normalization, gives

    Q(h,0,0)=A*h³*q(h),
    q(h)=(-36−12h)*((6−h)*(2p(h)+h*p'(h))+(17h−66)*p(h)).

All coefficients of q are positive except those of h6,h7,h8. The exact
polynomial equals

    1944+1692h+(4077/2)h²+(8781/4)h³+(24335/24)h⁴
    +h⁵*[c+(1−h)*(4619/288+(454729/5184)*(1+h)
                                      +(51673/1152)*(1+h+h²))]
    +(41155/6912)h⁹+(6670877/559872)h¹⁰+(793001/186624)h¹¹
    +(1400219/1679616)h¹²+(2572699/15116544)h¹³
    +(210335/5038848)h¹⁴+(296285/45349632)h¹⁵
    +(169193/408146688)h¹⁶,

where c=3491/16−4619/288−454729/5184−51673/1152>0.
For 0≤h≤1 every displayed term is nonnegative, and the constant is
strictly positive. Therefore q(h)>0. Multiplication by A*h³ proves the
claim for 0<h≤1. Every identity and rational sign is checked by Lean;
no numerical sampling or external algebra computation enters the proof.

## Lean and audit

Namespace `HTGeometry.ThetaRatioInfinity`; production leaves:

- `ThetaCuspRatioAxisCompleteMoments`: full moment normalization identities.
- `ThetaCuspRatioAxisCompleteMinor`: `axisMinor_normalized`.
- `ThetaCuspRatioAxisCompleteSlope`: `axisSlope_normalized`,
  `axisSlopeShape_re`, `axisSlopeShape_pos`, `axis_scaledSlope_pos`.

All three final direct `lake --old env lean` leaf audits exited0.
Umbrella wired without building it. Seven imported capstones passed the standard foundational axiom audit
(propext, Classical.choice, Quot.sound only). Index exited0. Final lint
status is recorded in the working log.

## Next hard problem

Prove the complete transverse sign of Q (equivalently its drift quotient,
since V is independent of t) on the exact C73 domain, then the sign on
its exact algebraic E=0 boundary. Retain E=t−h²t²−r*b(h), V=9−rh²,
and positive source speed. No global sign follows merely from this axis
certificate or from the previously proved uniform clock tail.
