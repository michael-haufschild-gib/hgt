# Square-root prime heads diagonalize conductor finite parts

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** [Q1/O1](../1-in-progress/three-frontier-questions-full-solutions.md);
  [prime boundary](prime-conductor-heads-and-tails-have-opposite-torsion-limits.md).

Let `v_m,N(n)=c_m(n)/sqrt(phi(m)n log N)` and let `P_N^(K)` be the
literal prime matrix restricted to dilation ratios at most `K`.
For all positive conductors,

`<v_m,N,P_N^(floor(sqrt N)) v_l,N>−(3/4)1_(m=l)log N`
`→−1_(m=l)[gamma+log m+tameDifferent(m)]`.

More generally, at `K=floor(N^theta)`, `0<theta≤1`, the leading
term is `theta(2−theta)1_(m=l)log N` and the finite part is

`(1−2theta)I(m,l)/sqrt(phi(m)phi(l))`
`−1_(m=l)[log m+tameDifferent(m)+2(1−theta)gamma]`.

The square-root head is the unique interior scale with zero mixed torsion
coefficient. This is a statement about the actual truncated form on fixed
conductor pairs; it asserts no norm quasimode law or growing-packet estimate.

The corresponding scalar-identity renormalization has finite part
`lambda_m delta_ml+(1−theta²)B_ml`, where
`lambda_m=gamma+log m+tameDifferent(m)`.
Thus only the full cutoff removes the extra harmonic Gram term.
The finite part of the band between powers `alpha` and `beta`,
after removing its diagonal main term, is `2(beta−alpha)B_ml`.

## Proof

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

The [weighted Mertens limit](prime-head-logarithmic-moment.md)
and [moving-cutoff correction](growing-prime-heads-preserve-the-centered-torsion-correction.md)
are formalized inputs.

## Lean

`SuccessorShellArithmetic/Conductor/PrimeConductorPowerHeads.lean`:
`tendsto_primeConductorPowerHead_finitePart`,
`tendsto_primeConductorSqrtHead_finitePart`,
`tendsto_primeConductorPowerHead_renormalized`, and
`tendsto_primeConductorPowerBand_finitePart`.
Final direct `lake --old env lean` check passed. Every transitive axiom set
is exactly `propext`, `Classical.choice`, and `Quot.sound`. Umbrella import present.

The full Gamma, pole, and successor-shell comparison remains open.
