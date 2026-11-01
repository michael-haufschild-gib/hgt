# Coherent prime tails and the quadratic logarithmic threshold

- **ID:** critical-rigidity-coherent-prime-tail-threshold
- **Stage:** 1-in-progress
- **Disposition:** Paused with the parent programme. No further research authorized.
- **Type:** CANDIDATE
- **Question:** Is the quadratic logarithmic conductor cost in the relative prime residual optimal?

## Candidate witness

Use prime coefficients `a_p=sqrt(p−1)/p`, zero elsewhere. Their exact adjunction mass is `B_Q=Σ_(p≤Q)log p/p`. A prime-power dilation jump of this packet's `p` component equals `1_(p∤n)`. All actual Mangoldt-weighted jumps are therefore nonnegative.

Let `1≤P≤Q`, `A=floor(N/P)`, and restrict rows to `A<n≤N`. Every prime `p>P` lies beyond the complementary quotient `N/n`. Its full tower contributes

`T_(P,Q)(n)=Σ_(P<p≤Q) log p/(p−1) · 1_(p∤n)`.

The proposed pointwise bound is `completedTail_Q(N/n,n)≥T_(P,Q)(n)≥0`. The receiving constant mode of `T` is exactly `B_Q−B_P`.

## Quantitative target

The sharp annular sampling theorem suggests

`Σ_(n≤N) completedTail_Q(N/n,n)²/n`
` ≥ [Σ_(A<n≤N)1/n − Q(Q−1)/(A+1)] (B_Q−B_P)²`.

Take `Q=P²` and a horizon satisfying `N≥P⁶`. The bracket is `log P−O(1)` and the constant mode is `log P+O(1)`, using the proved prime Mertens estimate. This predicts a cubic logarithmic lower bound for the tail square.

The scalar residual costs at most `C(1+log Q)M`, while the excitation gap bounds `M` by a constant times `B_Q`. Hence the scalar cost is only quadratic logarithmic on this witness. The inequality `(s−t)²≥t²/2−s²` would transfer the cubic lower bound to the actual residual. Dividing by `L=B_Q` predicts an intrinsic `(log Q)²/log N` relative cost.

## Proof obligations and positive survivor

Verify the prime jump formula, source positivity, exact constant row, annular packet representation, and scalar comparison in Lean. Check corpus novelty before claiming sharpness. If successful, the positive survivor is a matching source-relative upper and lower scale, with an explicit arithmetic extremizer; no complete-Weil route is retired by this prime-residual obstruction.

## Stronger source-specific lower bound

Centered divisibility has interval discrepancy at most one. With `B=B_Q−B_P` and `A'=Σ_(P<p≤Q)log p/(p−1)`, finite Abel summation gives

`Σ_(n≤N) completedTail_Q(N/n,n)²/n ≥ H B²−2BA'/(floor(N/P)+1)`,

where `H=Σ_(floor(N/P)<n≤N)1/n`. This removes the quadratic conductor loss from the coherent witness. Its dependency-closed proof and Lean draft are in `2-fully-proven/coherent-prime-tail-incidence-bound.md` and `PrimeIncidenceHarmonicWindows.lean`; verification remains pending.

For `Q=P²,N≥P`, `H≥log P−log 2`, `B=log P+O(1)`, and `A'=log P+O(1)`. The boundary cost is quadratic logarithmic, while the retained term is cubic logarithmic. Formalizing this specialization and its scalar-residual transfer is now the sharpness target; the earlier polynomial horizon condition is unnecessary if the incidence bound passes.
