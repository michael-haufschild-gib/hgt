# CLG/TTF compact D1 source-cone audit

- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Target:** Prove native reflected rank-three D1 positive on the remaining literal theta orbit, without an assumed source inequality.
- **Full RH chain:** Completed theta source → Xi Bezoutian → every finite two-channel Weil packet positive semidefinite → RH. Native D1 addresses only a necessary finite-rank source sign; clustered/general packet incidence and cofinal no-escape remain afterward.

## Current evidence

- `PolynomialODEJetRankThreeCompactExpansion` proves the full real polynomial identity, with all 540 monomials retained.
- `ThetaCuspModularCompactTube` places the actual orbit for `0≤x≤137/2000` in `-1≤S≤0`, `17≤A≤20`, `0≤W≤6/5`.
- `ThetaCuspFullReflectionEighthProjectiveRefinedParabolicClockCone` gives sharper coupled orbit information in scale and projective coordinates.
- Neither enclosing the source nor expanding its polynomial proves its sign. A rectangular-box sign requires an independent audit before attempting its formalization.

## Work plan

1. Audit the exact polynomial on the coarse box and refined source cone; computation may guide the argument only.
2. Develop a dependency-closed symbolic sign proof or exact obstruction with nontrivial positive salvage.
3. Verify in `/tmp` using `lake env lean`, formalize the surviving theorem, wire its umbrella, run a targeted final module build and axiom/lint audit.
4. Update the frontier as current state. Add route-independent constraints only when a proved result warrants them.

No numerical output, external certificate, assumed sign, or new axiom may supply a Lean premise. No RH proof is claimed by this card.

## Symbolic proof under formal verification

The existing differential estimate `W(x)≤14x` gives `W≤1` on the whole missing interval. Set `u=-S` and `t=A-17`, so `0≤u,W≤1` and `0≤t≤3`. Expand the *complete* polynomial as `sum_j p_j(u,W)t^j`. For each negative monomial, use `u^i W^k≤1`; retain the constant and discard only nonnegative monomials in a lower bound. The proposed exact bounds are `p_0≥10^9`, `p_3≥10^6`, `p_4≥-14000`, and `p_j≥0` for the other degrees. Then `10^6 t^3-14000 t^4≥958000 t^3≥0`, leaving a strict constant reserve.

Every expansion and rational comparison must be derived by Lean's symbolic ring/order proofs from the existing polynomial. Exploratory coefficient arithmetic is not evidence of formal closure. The original wider `W≤6/5` box is not needed and is not being declared false.
