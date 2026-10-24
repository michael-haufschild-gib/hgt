# The actual Möbius long-modulus remainder is a quadrature error

- **ID:** pm-long-modulus-quadrature
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Source:** `../1-in-progress/pm-signed-damping-covariance.md`
- **Statement:** The long-modulus sawtooth and full harmonic tail equal one integrable quadrature error; the complementary square-root head has bounded pronic energy.

## Scope

Formalize the completed paper proofs requested by the user. These results
retain the cancellation needed by PM but do not bound the complete remainder
and do not prove RH. No additional admission premise is introduced.

## Paper proof

Fix ε>0. Put b(d)=μ(d)d^(-ε),
B_D(x)=sum_(D<d<=floor(x)) b(d), and
F_(n,D)(u)=B_D(n/u) for u>0, zero otherwise.

For every d>D, d>=1, its contribution to F is b(d) times the indicator of
(0,n/d]. The sum of the integrals of absolute values is
n sum_(d>D) |b(d)|/d <= n sum_(d>=1) d^(-1-ε), which is finite.
Termwise integration therefore proves that F is integrable and

    integral F = n sum_(d>D) b(d)/d.

For positive integers j, the condition d<=floor(n/j) is equivalent to dj<=n.
Interchanging the finite sums gives

    sum_(j>=1) F(j) = sum_(D<d<=n) b(d) floor(n/d).

Subtracting proves the quadrature identity for the joint long and tail
remainder. Splitting the exact centered divisor prefix at D retains the
short sawtooth and this remainder, with the entire mean tail included.

For 0<ε<1 and D=floor(sqrt n), the short sawtooth is bounded in absolute
value by sum_(d<=D) d^(-ε), hence by
(1+1/(1-ε)) n^((1-ε)/2). Squaring and dividing by n(n+1), the sum through any
horizon is at most (1+1/(1-ε))²(1+1/ε), using the existing power-sum bound.
All domain assumptions concern only positive damping and natural cutoffs.

## Gates

- [x] Dependency-closed paper proofs.
- [ ] Exact identities and short-modulus bound formalized.
- [ ] Foreground leaf audit with `lake --old env lean`.
- [ ] Transitive axiom audit.
- [ ] Umbrella import added without compiling the umbrella.

No external novelty claim or check. The short-modulus estimate uses the
existing corpus mechanism; the quadrature identity is not counted as a
solution of the outstanding signed covariance inequality.

## Significance gate

The subsequent user instruction requires a theorem or discharged premise
that significantly advances a hard PM obstacle. This exact rewrite alone
does not meet that gate. Its paper proof is retained, but its standalone
formalization is deferred; no admission theorem or new cancellation estimate
is claimed. The preliminary Lean API probe was terminated before producing
diagnostics, and no Lean module or umbrella import was added.
