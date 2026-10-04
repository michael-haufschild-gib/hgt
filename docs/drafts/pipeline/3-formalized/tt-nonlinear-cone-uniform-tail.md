# Uniform third-slope positivity on the nonlinear source cone near infinity

- Parent: C73, Route TT, global actual normalized third-minor slope.
- Stage: 3-formalized; seven production leaves and fourteen imported capstones audited.
- Exact target: there is epsilon>0 such that all 0<h<epsilon, 0≤r≤361/25,
  t>0, positive compact source speed and t−h²t²>r*b(h) have Q(h,r,t)>0.
- Global interior, full source quadratic, fourth Schur gap, join, all rank,
  and RH remain open. This strengthens the fixed-r cubic-sheet result;
  it does not assume flatness or a particular actual source trajectory.

## Corpus and proof

Use the audited cubic contact in P3 `tt-third-slope-nonlinear-boundary`,
complete source field in `ThetaCuspRatioInfinityFlow`, and the strict cone
in `ThetaCuspRatioInfinityCone`. Searches and coverage are recorded in
P1 `tt-third-slope-nonlinear-cone`; the new argument uses their exact
identities, not an external mathematical computation.

Put b=1/12−7h/72 and
B=r*b+r²h²/144−7r²h³/432. Make the exact shift t=B+s.
Polynomial division first in s and three times in h gives joint polynomial
functions A(h,r,s), L(h,r) with

    Q(h,r,B+s)=s*A(h,r,s)+h³*L(h,r),
    A(0,r,s)=7776C,
    L(0,r)=63C*(122880/7−r²), C>0.

For the first identity, divide the shifted polynomial by the coordinate s;
the remainder is its restriction to s=0. Its first three h coefficients
vanish for every r, by the proved cubic-contact theorem. Coordinate
quotients commute with restriction to the h line, so the univariate third
quotient is the restriction of a joint polynomial in h and r. This also
proves its continuity in both variables. At h=0 the entire shifted
polynomial is 7776C*s; cancellation by s gives the displayed transverse
quotient, including s=0.

The nonlinear constraint implies s>0 exactly, rather than asymptotically.
For h≤4/5 and r≥0 let a=r*b≥0. Then t−h²t²>a implies t>a≥0 and

    t>a+h²t²≥a+h²a²
     =B+49r²h⁴/5184≥B.

For 0≤h≤1/4 and 0≤r≤15 the source speed has exact form

    F=r*(1−2h/3−4h²/9)−(2/9)*(3+2h)*(9−rh²)*t.

Here 9−rh²≥8, its t coefficient is at least5, and its first term is at
most r. Thus F>0 and t>0 imply t<4. Also B≥0 on this h interval, so
0<s<4. These coarse bounds only place parameters in a compact set;
no optimized numerical estimate is part of the research claim.

On the compact face r∈[0,15], s∈[0,4], A(0,r,s)>0 and L(0,r)>0.
Joint continuity and compactness give one neighborhood of h=0 on which
both coefficients stay positive for every point of this face. Taking
0<h in that neighborhood yields Q=s*A+h³*L>0 uniformly. The actual
kinetic interval is contained in r∈[0,15], finishing the exact target.

## Seam information and remaining hard problem

The independent square-chart identity gives S(V,K,Z)=V*R(V,K,Z) with a
polynomial R. Its seam value is alpha(K)+Z*beta(K)>0 throughout
5/4≤K≤19/15, 0≤Z≤1/3, by the existing seam tangent certificate.
That quotient is the correct interior positivity target: S itself
vanishes at V=0. The new uniform infinity result and this seam information
still do not prove the sign on the intervening nonlinear cone.

## Audit status

Ten prerequisite cubic-contact production leaves and twenty capstones
have final exit0/standard-three-axiom audits. Scratch SeamFactor and
SeamValue exited0 with standard three axioms; CoordinateDivision also
passed. NormalForm pass4 and ConeTail/ConeTailIncidence pass7 exited0 with only
the standard three axioms. Seven production leaves passed final direct `lake --old env lean` audits.
Fourteen imported capstones passed the separate axiom audit with exactly
`propext`, `Classical.choice`, `Quot.sound`; no added axiom or admitted
proof. Umbrella imports are wired without a full/umbrella build. Index
refresh exited0. Lint exited1 with eighteen unrelated umbrella omissions
and no C73 finding. Superseded C73 scratch sources/caches cleaned; logs
and manifests retained.
Manifest: `/tmp/tt_c73_tail_production_modules.txt`; final logs:
`/tmp/tt_c73_final_*.log`, `/tmp/tt_c73_tail_production_axioms.log`.

## Exact compactified seam factor

The polynomial Q itself admits Q=(9−rh²)*R with a polynomial R.
No degree estimate is needed. By structural polynomial induction, any
square-coordinate polynomial P has some denominator-cleared expression
h^n P(9−rh²,1/h,(1−th)/3)=Pbar(h,r,t). Apply this to the square-chart
quotient of the proved seam factor. Together with h¹⁹ S=Q, it gives
(9−rh²) | h^n Q as a polynomial identity. To promote identities known
for h≠0 to polynomial identities, multiply their difference by h, use
polynomial extensionality at all points, then cancel the nonzero
coordinate polynomial. Finally

    (1/9)*(9−rh²)+(rh/9)*h=1

makes the seam factor coprime to h. Coprime divisibility cancels h^n
and gives (9−rh²)|Q. Scratch ScaledDriftFactor pass2 exited0, standard3.
This retains the exact seam geometry in the remaining interior sign
problem; no sign certificate for R on the whole nonlinear cone is claimed.
