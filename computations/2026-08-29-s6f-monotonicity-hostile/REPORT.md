# S6F coordinate-monotonicity reduction attack

## Question

Can positive three-variable S6F chamber certificate be reduced to a corner value by exact
coordinate monotonicity, yielding human-size route to computation-free proof?

Diagnostic only. No derivative certificate or coefficient here is admissible in Lean.

## Computation

Using exact normalized certificate `C` from sibling S6F chamber run, substitute

`X = 191/10 + (9/10)S`, `z = (3/10)T`, with `S,T,y in [0,1]`.

Compute exact tensor-Bernstein coefficients for `dC/dS`, `-dC/dT`, and `-dC/dy` in parallel.
Then restrict to worst `X,z` boundary `(S,T)=(0,1)` and compute exact univariate Bernstein
certificate in `y`. Independent verifier repeats conversion with separate implementation and
checks coefficient hashes.

## Outcome

- `dC/dS` has all 9,828 Bernstein coefficients strictly positive: `C` increases with `X`.
- `-dC/dT` has no negative coefficients and 392 zeros: `C` is nonincreasing with `z`.
- `-dC/dy` has 8,541 negative coefficients: direct monotonicity in `y` is killed.
- Therefore chamber positivity reduces to boundary polynomial
  `P(y)=C(191/10,3/10,y)` on `0<=y<=1`.
- `P` has degree 27 and exactly 28 Bernstein coefficients; all are strictly positive.
- Endpoint `P(1)` equals positive exact rational shown in `results.json`.
- Independent exact verifier passed.

## Interpretation

Naive full corner-minimum proof is false because `y` monotonicity fails. Strong survivor is much
smaller than original 10,584-coefficient certificate: two coordinate monotonicity statements plus
one degree-27 univariate positivity statement. This is best current paper/Lean target for S6F
finite gate.

Computed Bernstein lists remain forbidden as Lean input. Next work must independently derive
compact positive decompositions for two derivative signs and boundary polynomial, or prove them by
source-intrinsic inequalities. If that succeeds, existing computation-free clock theorem places
actual orbit inside chamber and existing projective derivative bridge closes missing compact S6F
sign.
