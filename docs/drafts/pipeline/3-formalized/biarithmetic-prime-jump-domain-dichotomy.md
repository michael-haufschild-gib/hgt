# Prime-log jump weights and the exact finite-energy domain

- **ID:** biarithmetic-prime-jump-domain-dichotomy
- **Stage:** 3-formalized
- **Type:** THEOREM (paper and Lean; classical calibration)
- **Parent:** [Biarithmetic Geometry](../1-in-progress/biarithmetic-geometry-foundations.md), infinite-rank coercivity.
- **Statement:** For ordinary real `L²(R)` translations at the increasing prime logarithms and any nonnegative weights `w_n`, the positive jump series of a vector `f` is summable iff the weights are summable or `f=0`. Thus its domain is all of `L²` or exactly `{0}`, with the exact criterion given by weight summability.

## Dependency-closed paper proof

Let `τ_t f(x)=f(x+t)`, let `p_n` list the primes increasingly, and put
`Q_w(f)=Σ_n w_n ||τ_(log p_n)f-f||²`, allowing infinite values.

For every `f∈L²`, its translation coefficient `<f,τ_t f>` tends to zero as `t→+∞`.
To prove this, choose compactly supported `g` with `||f-g||<δ`. Distant translates of `g`
have disjoint support, so `<g,τ_t g>=0` for sufficiently large `t`. Cauchy–Schwarz and the
translation isometry give the uniform error bound

`|<f,τ_t f>-<g,τ_t g>|≤(||f||+||g||)||f-g||`.

Taking `δ` arbitrarily small proves the limit. Since `log p_n→+∞`,

`||τ_(log p_n)f-f||² = 2||f||²-2<f,τ_(log p_n)f> → 2||f||²`.

If the weights are summable, the triangle inequality gives
`0≤Q_w(f)≤4(Σ_n w_n)||f||²`, proving that every vector is in the domain. The zero vector
is in the domain for every weight sequence. Conversely, for `f≠0`, the jump square is at
least `||f||²` eventually. Summability of the jump series then implies summability of the
weight tail, and hence of the full weight sequence. This proves both directions.

## Strongest positive survivor

The exact domain classification includes the bounded-form regime and its explicit operator
bound `4Σw_n`. Infinite total weight on these unbounded shifts collapses the domain; it does
not produce a stronger densely defined positive form. The mechanism is vanishing of regular
translation coefficients, so it is sensitive to the chosen representation.

## Scope and novelty audit

This concerns positive, unrenormalized jump sums in the ordinary Lebesgue regular
representation. It does not classify the actual signed Weil form, a renormalized expression,
or a Bohr representation with pure point spectrum. The latter need not have translation
coefficients tending to zero. It also does not contradict infinite mass at small jumps,
such as the corpus's prime Lévy measure supported at `1/p→0`.

The result is classical in the setting of Lévy forms. Schilling's
[Chapter 7](https://arxiv.org/pdf/1603.00251) uses the Lévy integrability condition, which forces
finite jump mass away from zero. The programme contribution is the exact domain audit for
the proposed prime-log weighting mechanism, not a new general Lévy theorem or a K4 claim.

## Verification

- [x] Explicit source representation and weights; no imported coercivity premise.
- [x] Dependency-closed paper proof, including the positive bounded-form regime.
- [x] Classical calibration identified; no general novelty claim.
- [x] Lean proof of vanishing translation coefficients.
- [x] Lean proof of the full domain equivalence and bound.
- [x] Direct repository leaf check.
- [x] Main-declaration transitive axiom audit.

Module: `GaloisForLFunctions/BiarithmeticGeometry/PrimeLogJumpDomain.lean`.

All three principal declarations report only `propext`, `Classical.choice`, and `Quot.sound`. The direct repository check passed and the umbrella import is wired.
