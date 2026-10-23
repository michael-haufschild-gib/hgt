# Möbius cancellation in a determinant operator

- **ID:** twin-prime-determinant-operator
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** [consumed-mark determinant endpoint](twin-prime-consumed-mark-determinant.md)
- **Statement:** The actual two-sign determinant matrix contracts every pair of boundary vectors by an arbitrary fixed power of the logarithm.

## Exact first test

Fix `0<delta<1/4`, `C>0`, and a fixed finite family of the prime
bands from the source card. Put `rho=1/2`, `Z=exp((log X)^(24/100))`,
and let `omega` count prime divisors in those bands. Write
`R_Z(a)=1` if every prime divisor of `a` exceeds `Z`, and zero otherwise.
Take positive real dyadic lengths `M,N,Q,H` satisfying

`X <= MN <= 2X`, `X <= QH <= 2X`,
`X^delta <= M,N,Q,H <= X^(1-delta)`.

Rows are odd squarefree integers `q in (Q,2Q]`; columns are odd integers
`n in (N,2N]`. For `|v|<=X^C` and `X<=t<=2X`, define

`K_(v,t)(q,n) = sum_(M<m<=2M, H<h<=2H,
  mn-qh=-2, X<mn<=t, gcd(q,h)=1)
  mu(m) R_Z(m) m^(iv) mu(h) rho^omega(h)`.

The sum is over positive odd integers `m,h`. This loses no nonzero
term of the original coefficient once `Z>2`: `R_Z(m)` removes even
`m`, and the determinant equation then forces `h` odd. Norms below are the usual finite
complex Euclidean norms, without cardinality normalization.

**Candidate:** for every `A>0`,

`sup_(|v|<=X^C, X<=t<=2X) ||K_(v,t)||_(ell2 -> ell2)
  <<_(A,delta,C,bands) sqrt(MH)/(log X)^A`.

The implied constant and threshold may depend on the displayed fixed
parameters, but not on `X,M,N,Q,H,v,t`. This is an actual-arithmetic
claim. Arbitrary bounded replacements for either Möbius factor are
excluded: replacing both by one retains the positive counting main term.
The statement is still a conjecture, with no Lean declaration.

## Why this is a distinct test

The row multiplier `epsilon_q mu(q)W_X(q)` and column multiplier
`c_V(n)R_Z(n)n^(iv)` can be left outside this matrix. Their Euclidean
norms are at most a fixed-band constant times `sqrt(Q)` and
`sqrt(N)log(2X)`, respectively: `W_X` is bounded for fixed bands and
`0<=c_V(n)<=log n`. Thus the conjecture would give a fixed-endpoint
dyadic determinant sum of size

`sqrt(QN) sqrt(MH) (log X)^(1-A) << X (log X)^(1-A)`.

This checks the normalization. It does not yet prove the endpoint on
the source card: individual endpoints `t_q`, factor blocks outside the
stated four-long-variable range, and removal of the marking weights
must all be addressed. No maximal estimate follows merely by putting
a supremum outside the norm. Endpoint separation is a separate step.

## Competing mechanisms and preliminary attacks

1. **Independent-sign contraction.** The signed matrix could have much
   smaller norm than its positive support matrix. Unlike the failed
   unsigned energy estimate, this retains both `mu(m)` and `mu(h)`.
2. **Coherent arithmetic boundary mode.** A family of row and column
   vectors could align these two signs and violate the conjecture.
   The operator norm must detect such a mode; a small scalar sum does
   not rule it out. Characters and Mellin phases are the first modes
   to examine, followed by four-cycle correlations.
3. **Near-balanced sparsity does not create averaging.** If `M<=Q`
   and `H<=N`, each entry contains at most one determinant solution.
   Indeed `gcd(q,n)=1`, since it divides 2 and both integers are odd.
   The difference of two solutions is `(m-m',h-h')=j(q,n)`;
   the open-left dyadic intervals then force `j=0`. Thus cancellation
   must occur between entries in this regime, not inside an entry.
4. **Fixed-form correlation is insufficient.** Parametrizing one row
   or column introduces affine coefficients growing with `X`.
   The inspected ordinary two-point correlation theorem explicitly
   excludes this uniformity. Its use would leave the hard input
   unproved.
5. **The RH bridge supplies no contraction.** The certified fixed-lag
   deletion result concerns an aggregate von Mangoldt energy growth
   class. It neither bounds this signed operator nor proves a
   positive gap-two tail.

**[OPEN CORE]** Prove a quantitative cancellation bound for the
off-diagonal Gram correlations with their actual growing arithmetic
coefficients, or exhibit an actual coherent mode disproving the
candidate. No such estimate or mode has been established.

## Source audit

Corpus searches for signed arithmetic energy, determinant matrices,
local compensation, and marked divisor switching found finite
divisor-incidence factorizations, exact prime-release identities, and
RH orbit criteria. Their relevant statements were inspected; none
supplies the displayed operator estimate. In particular the finite
clock cancellation identity retains a mixed signed correlation whose
size still needs control.

Previously inspected [Bettin--Chandee](https://arxiv.org/abs/1502.00769)
determinant estimates require smooth variables absent from this
operator. The [ordinary two-point manuscript](https://github.com/openai/math/blob/main/preprints/Ordinary-two-point-correlations-of-multiplicative-functions-September-24-2026/final.pdf)
has fixed-form rather than growing-coefficient uniformity. The
[Pascadi Kloosterman bound](https://link.springer.com/article/10.1007/s00039-026-00746-0)
requires a verified Fourier reduction with the correct coefficient
norms; no such transfer is supplied here. Searches for Möbius-weighted
determinant-surface and quadrilinear estimates did not identify a
theorem matching this operator. This limited search is not a novelty
certificate.

**Verdict: SURVIVES PRELIMINARY ATTACK.** No proof or counterexample;
no assertion that it is absent from the literature. The conjecture
is stronger than the scalar application and remains under attack.

## Gates

- [x] Exact arithmetic matrix, normalization, and first failure modes.
- [ ] Complete attack on boundary modes and quantitative Gram correlations.
- [ ] Dependency-closed paper proof or exact counterexample.
- [ ] Formalize a proved, nontrivial statement without analytic premises.

## Log

- 2026-10-23 — Recorded the signed operator test. Unconditional
  twin-prime infinitude remains unproved. No new Lean assumption or
  claimed analytic theorem was introduced.
