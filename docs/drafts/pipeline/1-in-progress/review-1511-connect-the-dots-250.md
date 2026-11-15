# Connections across the open obstacles of review 1511

- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Target:** 250 significant, unconditional, Lean-verified contributions to O1–O16 in `docs/reports/review-1511/obstacles-summary.md` §2.2.
- **Accepted contributions:** 0. Existing results, numerical refinements, conditional receivers and renamed statements do not count.
- **Evidence:** local corpus searches, exact source statements and kernel compilation. No external literature checks. Further axiom checks skipped at user request.

## Active conjecture: O3, angular twists of the cubic probe

The finite-order probe estimates extend to each fixed sextic infinity type without changing their exponents. This would give the first half-plane left of 1 for the Grössencharacter rungs and lower the cubic correction boundary below 2/3.

**Connection:** the arbitrary multiplicative twist in the theta-to-Gauss conversion, the normalized cubic Gauss-sum description of rung coefficients, and the existing detector bounds.

**Required proof:** construct the angularly twisted analytic probe; verify every estimate used by the finite-order seed; prove nonvanishing for the actual `grossenLFunction`. Unit norm alone does not justify transferring a cancellation estimate.

**Known obstruction:** `HeckeFamily.Character` contains a periodic residue character and no infinity type. No theorem about its `LFunction` alone proves the conjecture.

## Completion gate

Each accepted entry must identify the obstacle moved, the distinct mathematical connection, a dependency-closed proof, exact Lean declarations, umbrella import and final `lake --old env lean` audit. Working log: `logs/review-1511-connect-the-dots-250.md`.

## Active conjecture: O11, positive arithmetic twins are passive

The reciprocal quadratic twins in `SelbergClass.PositiveFiniteEulerTwins` also satisfy the global Schur passivity and continuous-spectrum unitarity of the modular horizon. For a prime `p` and `1/2 < σ < 1`, take `r=p^σ`, `u=p^(1−σ)`, `A=r+u`. The completed multiplier is `p^s+A+p^(1−s)`; its scattering quotient is `schurNum p (−A) v / schurDen p (−A) v`, `v=p^(−2w)`. Since `(r−1)(u−1)>0`, `A<p+1`, so the existing Schur criterion applies.

**Arithmetic survivor:** the genuine Euler logarithmic coefficient at `p²` is `(1−r²−u²)/2<0`, although all ordinary coefficients are positive. This gives a specific count obstruction that survives strengthening the physical countermodel by ordinary coefficient positivity.

**Internal duplicate rejected:** the sign pattern of the original positive-trace prime-two deformation follows from `PositiveFiniteEulerCoefficients`; the strict Euler-growth obstruction is already `PositiveFiniteEulerBound.not_fullClass`. Neither counts as a contribution.

**Stronger conjecture:** ordinary coefficient integrality also survives. At a prime `p>4`, choose `A=p`; the two reciprocal root radii are `(p±√(p²−4p))/2`, both greater than one and distinct. The ordinary coefficients then lie in `{0,1,1+p,1+2p}`. Audit this exact family after the positive passive construction; count it as a strengthening of the same contribution.
