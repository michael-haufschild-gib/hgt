# S6F normalized projective chamber search

## Question

Can exact normalized source coordinates isolate a small physical chamber where rank-three
projective drift is positive, while also finding counterexamples to overbroad chamber claims?

This run is diagnostic only. No polynomial coefficient, ODE value, or certificate here is
admissible in Lean.

## Computation

Literal source-positive drift was transformed from `(U,B,Q)` to

`X=R^2`, `v=U/R`, `z=-Z`, `v=z*y`,

with physical relation

`Q = (X * (1-z^2 + 2/3*(z-v)^2) - 6) / 16`.

Exact symbolic elimination gives

`projective drift / R = z * C(X,z,y)`.

Search tested tensor-Bernstein coefficients of `C` on
`191/10 <= X <= 20`, `0 <= y <= 1`, and several rational caps on `z`. Five cap transforms ran
in parallel. A 2,000,000-point vectorized hostile search attacked full physical simplex.
Independent verifier reconstructed scale elimination at exact rational state, recomputed all
Bernstein coefficients by separate conversion, checked coefficient hash, and checked an exact
rational negative full-simplex state.

## Outcome

- Normalized drift: degree 40, 1,120 terms.
- Factored certificate: total degree 66, 1,120 terms.
- At `z <= 3/10`: all 10,584 exact rational tensor-Bernstein coefficients are strictly positive.
  Minimum is positive and full coefficient hash is
  `9f4aa5b24a730e219a2fdec6f25224a3730af47c06864a1f546ba2c31d2ea602`.
- At `z <= 1/3`: six Bernstein coefficients are negative, so this certificate no longer closes.
- Full physical simplex is false: exact rational state
  `X=199989/10000`, `z=465/1000`, `y=999/1000` has `Q>0` and `C<0`.
- Independent ODE diagnostic ended at `z=0.292770279951584...` for `x=137/2000`, suggesting
  `3/10` is viable physical cap.

## Interpretation and consequence

Whole-simplex projective-drift shortcut is killed. Surviving route is sharply localized:

1. prove actual theta trajectory satisfies `z<3/10` on missing interval;
2. independently derive compact computation-free positivity proof for `C` on that chamber;
3. combine with existing projective derivative bridge.

Step 1 is now closed without computational input in Lean module
`ThetaCuspFullReflectionEighthProjectiveClockChamber`: sharper theta-series majorant gives exact
seam-scale bound, modular-gap monotonicity gives derivative bound, and mean-value theorem gives
`-Z(x)<3/10` for `0<x<137/2000`.

Step 2 remains open. 10,584 computed coefficients must not be copied into Lean; next attack is a
human-size algebraic decomposition, nested low-degree Bernstein proof generated and justified
from exact source polynomial inside Lean, or stronger invariant-cone argument.

Files: `results.json`, `run-output.txt`, `verify-output.txt`, scripts, environment record, hashes.
