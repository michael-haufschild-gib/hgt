# Square-root prime heads diagonalize conductor finite parts

- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** [Q1/O1](three-frontier-questions-full-solutions.md);
  [prime boundary](prime-conductor-heads-and-tails-have-opposite-torsion-limits.md).

Let `v_m,N(n)=c_m(n)/sqrt(phi(m)n log N)` and let `P_N^(K)` be the
literal prime matrix restricted to dilation ratios at most `K`.
For all positive conductors, conjecture

`<v_m,N,P_N^(floor(sqrt N)) v_l,N>−(3/4)1_(m=l)log N`
`→−1_(m=l)[gamma+log m+tameDifferent(m)]`.

More generally, at `K=floor(N^theta)`, `0<theta≤1`, the predicted leading
term is `theta(2−theta)1_(m=l)log N` and the finite part is

`(1−2theta)I(m,l)/sqrt(phi(m)phi(l))`
`−1_(m=l)[log m+tameDifferent(m)+2(1−theta)gamma]`.

The square-root head is the unique interior scale with zero mixed torsion
coefficient. This is a statement about the actual truncated form on fixed
conductor pairs; it asserts no norm quasimode law or growing-packet estimate.

## Proposed proof

Write `G_ml(Y)=sum_(n≤Y)u_m(n)u_l(n)/n`, `u_m=c_m/sqrt(phi(m))`,
and `B_ml=gamma·1_(m=l)−I(m,l)/sqrt(phi(m)phi(l))`.
Split each dilated product into its undilated product and the completed
prime-row correction. Finite-period absolute summability of the correction
allows dominated convergence with the moving cutoff; its limit is
`I(m,l)/sqrt(phi(m)phi(l))−1_(m=l)[log m+tameDifferent(m)]`.

The undilated part is
`2 sum_(k≤K)Lambda(k)G_ml(floor(N/k))/(k log N)`.
The harmonic Gram remainder and logarithmic roundoff contribute
`O_(m,l)(psi(K)/(N log N))=o(1)` for `K≤N`.
The remaining terms are
`2delta[A(K)−B(K)/log N]+2B_ml A(K)/log N`, where
`A(K)=sum_(k≤K)Lambda(k)/k` and `B(K)=sum_(k≤K)Lambda(k)log(k)/k`.
Mertens gives `A(K)=log K−gamma+o(1)`; Abel summation gives
`B(K)=(log K)^2/2+o(log K)`. Substitution yields the stated finite parts.

The moving-cutoff domination and weighted Mertens limit still need Lean
formalization. The full Gamma, pole, and successor-shell comparison remains open.
