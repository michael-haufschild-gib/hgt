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

This checks the normalization. Individual endpoints are handled by
the separation proof below. Factor blocks outside the stated
four-long-variable range and removal of marking weights remain
separate obligations. No maximal estimate follows merely by putting
a supremum outside the norm.

## Individual endpoints: complete separation argument

The operator conjecture, if proved for every fixed frequency exponent,
does imply the corresponding maximal scalar bound on these blocks.
This deduction does not assume or prove the conjecture.

Dualize the row absolute values by `|epsilon_q|<=1` and choose
individual endpoints `t_q`. Products are integers, so replace each
endpoint by `floor(t_q)+1/2`. On the product block use the periodic
coordinate `z=log(mn/(MN))/(4 log 2)`, which lies in `[0,1/2]`.
Represent the endpoint indicator by the interval with fixed left
endpoint `-1/4` and right endpoint
`log((floor(t_q)+1/2)/(MN))/(4 log 2)`, using constant indicators
when the cutoff lies outside the product block.

Its Fejer polynomial of degree `T=ceil(X^6)` has coefficients
`a_k(q)` bounded by `C/(1+|k|)`, uniformly in `q,t_q`. Every product
integer is at distance at least `c/X` from the moving jump; the
fixed jump stays away from the product block. The elementary
Fejer-kernel tail estimate therefore bounds the pointwise error
by `CX/T`. For completeness, the kernel satisfies
`F_T(z)<=min(T+1,C/((T+1)dist(z,Z)^2))`; integrating outside the
distance to either jump gives this error. The Fourier coefficients
of an interval give the stated coefficient bound.

Each retained Fourier term factors as a row weight `a_k(q)`, an
`m` phase, an `n` phase, and a constant phase. Absorb the row weight
into `epsilon_q mu(q)W_X(q)` and the `n` phase into the column vector.
The matrix frequency becomes `v+2 pi k/(4 log 2)`, bounded by
`X^(max(C,7))` for sufficiently large `X`. The conjecture is uniform
in this fixed polynomial range. The row norm is at most
`C_K sqrt(Q)/(1+|k|)` and the column norm at most `sqrt(N)log(2X)`.
Summing the harmonic coefficient majorant costs `O(log X)`.

The error is harmless without a delicate divisor estimate. For each
integer product `s<=2X`, at most `tau(s)tau(s+2)` determinant tuples
occur. The crude inequalities `tau(s)<=s`, `tau(s+2)<=s+2` bound
their total by `O(X^3)`. All coefficients except `c_V(n)` are bounded
by a fixed-band constant, and `c_V(n)<=log(2X)`. Thus the error is
`O_K(X^4 log X/T)=O_K(X^(-2)log X)`.

The resulting maximal block bound is `O(X(log X)^(2-A))` when the
operator estimate has exponent `A`. Requesting two extra logarithms
gives every prescribed saving. This closes the endpoint interface;
the operator contraction itself is still unproved.

## Exact sign reduction and fourth-moment target

Direct multiplicativity gives, on `mn+2=qh`,

`mu(m)mu(h)=lambda(q)lambda(n)
  lambda(mn)lambda(mn+2) mu(m)^2 mu(h)^2`.

The [parity bridge](../3-formalized/twin-prime-determinant-parity-bridge.md) proves
that the two matrices have exactly the same finite Euclidean
unit-ball pairing values, for arbitrary complex weights. Its Lean
certificate also proves equality of every conjugated four-cycle.
This is an isometric coordinate change,
not an estimate. At `v=0`, every remaining arithmetic weight is
nonnegative and the interior sign is the shifted parity sequence.

Consider the balanced diagnostic `M=N=Q=H=T`, `X=T^2`, with `T`
an integer. Each entry contains at most one solution, by the
uniqueness argument below, so its absolute value is at most one.
There are at most `T` rows and `T` columns. In the expansion

`tr((K K*)^2)=sum_(q1,q2,n1,n2)
 K(q1,n1) conj(K(q2,n1)) K(q2,n2) conj(K(q1,n2))`,

the terms with `q1=q2` total at most `T^3`, and those with `n1=n2`
total at most `T^3`. Their union therefore costs at most `2T^3`.
For example the first sum is
`sum_q (sum_n |K(q,n)|^2)^2 <= T*T^2`; the second is identical
with the coordinates exchanged. The two contributions are
nonnegative, so double-counting their intersection is safe.

All row and column Liouville signs cancel around each four-cycle.
For the remaining cycles the interior sign is a product of four
values `lambda(s_ij)lambda(s_ij+2)`, with the products constrained
by the shared divisor incidences. A bound of size
`O_A(T^4/(log T)^(4A))` for the real off-diagonal cycle sum would
give `||K||<<_A T/(log T)^A`: use
`||K||^4<=tr((K K*)^2)` and absorb `2T^3`. This is a sufficient
balanced test, not a proved estimate or an equivalence for all
unbalanced blocks.

**[OPEN CORE]** Cancellation of these actual nondegenerate cycle
weights. An unweighted two-point sum controls neither this
four-cycle average nor arbitrary divisor-incidence tests.

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
