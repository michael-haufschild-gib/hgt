# Growing prime heads preserve the centered torsion correction

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** [Power-cutoff conductor heads](square-root-prime-heads-diagonalize-conductor-finite-parts.md).

Let `u_m=c_m/sqrt(phi(m))`, `G_ml(Y)=sum_(n≤Y)u_m(n)u_l(n)/n`,
and let `H_K,N` be the literal prime head with dilation ratios `k<K`.
Every exhausting cutoff `K(N)→∞` satisfies

`H_K(N),N − 2 sum_(k<K(N)) Lambda(k)G_ml(floor(N/k))/(k log N)`
`→ I(m,l)/sqrt(phi(m)phi(l))−delta_ml[log m+tameDifferent(m)]`.

No monotonicity or upper bound on `K` is needed. In particular the
centered correction has the same limit at fixed-power and full cutoffs.

## Proof

Only prime divisors of a conductor change its Ramanujan mode. The proved
summable row majorants bound the centered mixed product uniformly in its
base index. Harmonic summation costs at most `H_N/log N≤2` eventually.
For each fixed dilation, the harmonic mean tends to its complete-period
mean. Dominated convergence therefore commutes the moving head and the
harmonic limit. The completed period sum is the positive torsion correction.

## Lean

`SuccessorShellArithmetic/Conductor/PrimeConductorGrowingCorrection.lean`:
`tendsto_primeConductorGrowingHead_correction`.
Final direct `lake --old env lean` check passed; transitive axioms are
exactly `propext`, `Classical.choice`, and `Quot.sound`. Umbrella import present.
