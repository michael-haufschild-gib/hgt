# Shifted Stieltjes Hankel Strictness From Infinite Support

- **ID:** shifted-stieltjes-hankel-strictness-infinite-support
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) / proof-route guardrail
- **Source:** `wild-analogy-web-catalog.md` Clean Finding 61,
  `source-aware-q0-alone-reciprocal-positivity.md`,
  `shifted-reciprocal-moments-determine-divisor.md`
- **Statement:** Once a shifted reciprocal tower is genuinely represented by a
  positive measure with infinite support on `R_{>0}`, every finite shifted Hankel
  block is positive definite. Singular finite Schur branches are finite-support
  or numerical-truncation artifacts, not a softer source route.

## Goal

Remove a small loophole in the boundary-Weyl route. The completed object may
eventually need to be a closed semibounded form rather than a bounded operator,
but finite singular Hankel or Schur-complement branches should not be treated as
extra source structure. For an infinite positive Stieltjes support, the finite
blocks are strict; the zero margin appears only in the limit as degree grows.

## Theorem

Let `mu` be a positive finite Borel measure on `R_{>0}`. Fix `r>=0`, and assume
the moments

`m_n^(r)=int x^(n+r) dmu(x)`

exist for `0<=n<=2d`. Define the shifted Hankel block

`H_r(d) = [m_(i+j)^(r)]_(0<=i,j<=d)`.

If `supp(mu)` contains at least `d+1` points, then `H_r(d)` is positive
definite.

Equivalently, if `H_r(d)` is singular, then `supp(mu)` has at most `d` points.
In that singular case the moment sequence satisfies a finite linear recurrence,
and the generating function `sum_(n>=0) m_n^(r) z^n` is rational whenever all
moments exist.

In particular, if `supp(mu)` is infinite, then every finite block `H_r(d)` is
positive definite for every `d` for which the moments exist.

## Proof

For any polynomial `p` of degree at most `d`,

`c* H_r(d) c = int x^r |p(x)|^2 dmu(x)`,

where `p(x)=sum_(i=0)^d c_i x^i`.

Since `x^r>0` on `R_{>0}`, this integral can vanish only if `p` vanishes
`mu`-almost everywhere on `supp(mu)`. A nonzero polynomial of degree at most `d`
has at most `d` zeros. Therefore, if `supp(mu)` contains at least `d+1` points,
the only vector with quadratic value zero is `c=0`. Thus `H_r(d)` is positive
definite.

The contrapositive gives the singular-block statement: if `H_r(d)` is singular,
there is a nonzero polynomial `p` of degree at most `d` vanishing on the support,
so the support lies in the finite zero set of `p` and has at most `d` points.

If `supp(mu)={x_1,...,x_N}` is finite, write

`m_n^(r)=sum_(j=1)^N w_j x_j^(n+r)`.

The characteristic polynomial `P(X)=prod_j (X-x_j)` gives the corresponding
linear recurrence for the moments. Summing the geometric series gives

`sum_(n>=0) m_n^(r) z^n = sum_j w_j x_j^r/(1-x_j z)`,

so the generating function is rational.

## Consequence for the RH Route

Under RH, the reciprocal nontrivial-zero divisor gives an infinite positive
support on `R_{>0}` with finite shifted moments `T_k` for `k>=1`. Hence the
shifted blocks

`[T_(i+j+1)]` and `[T_(i+j+2)]`

are positive definite at every finite degree, not merely positive semidefinite.

This is not an RH proof. It is a downstream strictness check: after a source
theorem has already produced a positive infinite-support Stieltjes
representation, finite singular Schur complements disappear. Generalized
inverse and range-inclusion branches belong to finite flat extensions,
finite-support controls, or numerical truncations.

The real proof burden remains unchanged: source-build the positive shifted
reciprocal tower or the equivalent boundary/index form from Euler/Gamma/FE data
without reading the zero divisor. This card only says that, once such a positive
infinite-support tower exists, finite flatness is not part of the actual
landscape.

## Theatre Test

For any argument using a singular finite Hankel block, Moore-Penrose Schur
complement, or flat extension:

1. Is the representing positive measure finite-support or infinite-support?
2. If infinite-support is claimed, why is a finite block singular?
3. If the singularity comes from truncation, what source statement survives
   after the truncation is removed?
4. If the singular branch is essential, has the argument silently replaced the
   infinite reciprocal divisor by a finite atomic model?

## Source Boundary

The theorem is elementary Stieltjes moment algebra. Its significance is
proof-route hygiene: it prevents finite flat-extension machinery from being
mistaken for a new source selector in the rank-one boundary-Weyl route.

## Gates

- [x] 0 -> 1 in-progress: singular Schur loophole isolated from the catalog note.
- [x] 1 -> 2 fully-proven: finite support / strictness proof written.
- [ ] 2 -> 3 formalized: optional finite-dimensional moment Gram theorem.

## Log

- 2026-06-24 -- Codex: promoted Clean Finding 61 into a focused guardrail card
  after the boundary/Uvarov duplicate audit.
