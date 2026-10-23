# Root averages with partially consumed marking groups

- **ID:** twin-prime-partially-consumed-mark-energy
- **Stage:** 2-fully-proven (paper deduction from cited energy theorem; Lean pending)
- **Type:** THEOREM / BRIDGE
- **Source:** [marked root average](twin-prime-mark-preserving-root-average.md),
  [sampling question](../1-in-progress/twin-prime-cofactor-sampling-energy.md)
- **Statement:** The marked Type II root average has every fixed
  logarithmic saving on the contribution in which sufficiently many
  selected marking primes do not divide the root modulus.

## Exact statement

Use the fixed prime groups `P_1,...,P_K`, reciprocal masses `V_i`,
`L=log X`, `Z=exp(L^(24/100))`, and `rho=1/2` from the source card.
Write `omega_i(n)=#{p in P_i:p|n}` and `omega(n)=sum_i omega_i(n)`.
Take the actual Type II coefficients

`alpha_m=mu(m) R_Z(m) m^(iv)`,
`beta_n=c_V(n) R_Z(n) n^(iv)`,
`c_V(n)=sum_{ell|n,ell>V} Lambda(ell)`, `U=V=X^(1/10)`.

Their supports are the prescribed dyadic blocks above `U,V`, with
`MN` comparable to `X`, `M,N>=X^delta`, and `|v|<=X^C`, for fixed
positive `delta,C`. Put `b=mn+2`. For `I` a subset of the groups,
write `J=I^c` and define, on `q|b`,

`W_(q,I)(b) = rho^(omega(b)-K) / prod_i V_i
  * prod_(i in I)(omega_i(b)-omega_i(q))
  * prod_(j in J) omega_j(q)`.

The exponent is an integer; it need not be nonnegative. All factors
are defined because the groups are nonempty for sufficiently large
`X`. Each difference is nonnegative when `q|b`.

Set

`T_(q,I)(t)=sum_(X<mn<=t, q|mn+2)
  alpha_m beta_n mu(mn+2) W_(q,I)(mn+2)`.

For every desired `A>0`, there is a fixed integer `K_0>=1` such
that, for every fixed `K>=K_0` and fixed distinct band exponents
in `(1/10,1/5)`,

`sum_(q<=X^(51/100), q odd squarefree)
  sup_(X<=t<=2X) |sum_(I subset {1,...,K}, |I|>=K_0) T_(q,I)(t)|
  << X L^(-A)`.

The implied constant and starting point may depend on the fixed
data. `K` is not permitted to grow with `X` in this statement.
This is a Type II contribution, not a theorem about the whole
prime sum or about unmarked shifted primes.

## Exact aggregation before Cauchy--Schwarz

Expanding the product of sums gives

`sum_I W_(q,I)(b)=W_X(b)` whenever `q|b`.

For a squarefree `b`, expand the factors with indices in `I` by
selecting one prime `p_i|b` that does not divide `q`. Write
`a=prod_(i in I) p_i` and `k=b/a`. Then

`gcd(a,k)=1`, `q|k`, `mu(b)=(-1)^|I| mu(k)`,
`omega(b)=omega(k)+|I|`.

Conversely, a selected `a` and a squarefree `k` with
`gcd(a,k)=1` and `q|k` give exactly such a term. No separate
condition `gcd(a,q)=1` is needed: it follows from those two
conditions. If `mu(k)=0`, the expanded term is zero as well.
This proves the identity, including nonsquarefree `b` after
retaining the coprimality condition,

`T_(q,I)(t)=(-1)^|I| sum_(q|k) c_(q,k)^J
  sum_(a selected from I, gcd(a,k)=1, X<ak-2<=t)
    (prod_(i in I)V_i^(-1)) f(ak-2)`,

where `f(s)=sum_(mn=s) alpha_m beta_n` on the given blocks and

`c_(q,k)^J=mu(k) rho^(omega(k)-|J|)
                 prod_(j in J)(omega_j(q)/V_j)`.

The crucial point is that the selected primes in `J` have already
been counted by `omega_j(q)`. There is no separate summation over
their product and no coefficient energy for each such product.
The remaining coefficient depends on `q,k`, but not on `a`.

For `q|k`, `omega_j(q)<=omega_j(k)`. Therefore

`|c_(q,k)^J| <= prod_(j in J)
  [omega_j(k) rho^(omega_j(k)-1)/V_j] <= C_K`.

The remaining damping factors, indexed by `I`, are at most one.
The last bound uses the bounded function `u rho^(u-1)` on
nonnegative integers and reciprocal masses bounded away from zero.

## Removing the coprimality condition

If a selected `a` shares a prime with `k`, a marking prime has
its square dividing `b=ak`. Upon summing all selected labels,
their multiplicity times the damping is bounded by `C_K`:
if exactly `r` selected primes also divide `k`, then

`omega(k)-|J|=omega(b)-K+r`.

Since `rho<1`, the resulting weight is at most
`rho^(omega(b)-K) prod_i omega_i(b)/prod_i V_i`, which is bounded.
Summing root moduli costs at most `tau(b)`, and
`|f(b-2)|<=L tau(b-2)`. Thus the total maximal-endpoint error is
bounded by the same expression already proved on the source card:

`C_K L sum_(p in union P_i) sum_(b<=CX, p^2|b)
  tau(b) tau(b-2) << C_K X L^4 sum_p 1/p^2`.

This has every fixed logarithmic saving. The proof uses the
affine divisor moments there; all marking primes are odd and
subpolynomial. No error is multiplied by the number of moduli.

## The finite energy estimate accepts modulus-dependent weights

An exact finite version avoids any asymptotic notation. Put
`D(H)=sum_(1<=k<=H) tau(k)` and
`E_j(A,H)=sum_(1<=k<=H) tau(k)^j |A_k|^2`.
For any array `c_(q,k)` in the closed complex unit disk, let
`R_q=sum_(1<=k<=H,q|k)c_(q,k)A_k` and
`T=sum_(1<=q<=H)|R_q|`. Then

`T^2<=D(H) E_1(A,H)`,
`T^4<=D(H)^2 E_0(A,H) E_2(A,H)`.

Proof: the triangle inequality and finite divisor incidence give
`T<=sum_k tau(k)|A_k|`. Weighted Cauchy--Schwarz gives the first
bound. A second Cauchy--Schwarz gives `E_1^2<=E_0 E_2`, proving
the fourth-power bound. Zero weights encode any subset of moduli
and any individual cutoff. This is finite algebra, not an assumed
estimate for the arithmetic coefficients.

This finite statement is now
[formalized and audited](../3-formalized/twin-prime-root-modulus-energy.md)
as `TwinPrime.rootModulusMass_pow_four_le`. The analytic estimates
below are not consequences of that finite certificate alone.

For arbitrary `c_(q,k)` with `|c_(q,k)|<=C_K`, Cauchy--Schwarz
still gives

`(sum_q sup_u |sum_(k<=u,q|k)c_(q,k) A_k|)^2
 <= C_K^2 H(1+log H) sum_(k<=H) tau(k)|A_k|^2`.

Indeed the first factor is `sum_q floor(H/q)`, and the other
factor counts the divisors of each `k`. This proof never uses
independence of `c` from `q`. After replacing `|A_k|` by
`sup_t |A_k(t)|`, it also applies to the individual physical
product cutoffs in the exact identity above.

Partition only the remaining selected product `a` into smooth
dyadic blocks `a` comparable to `Y`. Each resulting coefficient
is precisely the cofactor coefficient for the groups in `I`:

`A_k(t)=sum_(a,m,n:mn+2=ak, mn<=t)
  eta(a/Y)(prod_(i in I)V_i^(-1)) alpha_m beta_n`.

There is no need to partition a product of consumed and remaining
labels first. That earlier order created the apparent sampling loss.

For sufficiently many remaining groups, the cited determinant
energy of [Lü--Wang--Wu, §§4--5](https://arxiv.org/html/2610.20242v1)
and the endpoint reduction on the source card give

`E_0^max << XY L^(2-D)`, `E_2^max << XY L^17`, `H << X/Y`.

The weighted-energy exponent `17` is independent of the number
of groups. Interpolating `E_1<=sqrt(E_0 E_2)` therefore bounds
each block's root sum by `X L^((21-D)/4)`. Choose
`D>=4A+41`, then choose `K_0` from the source theorem.
Its threshold is independent of the particular distinct band
exponents. There are `O_K(L)` label blocks and finitely many
subsets `I`; even including the original `O(L^2)` Type II
dyadic blocks leaves the requested saving. All constants depend
only on fixed parameters. This proves the exact stated contribution.

## Boundary, novelty, and formal status

The remaining contribution is exactly `sum_(|I|<K_0) T_(q,I)`.
For `I` empty, the coefficient is `f(k-2)` with no label
averaging. The source energy gives no arbitrary logarithmic
saving there. Neither positivity nor the above finite inequality
removes this remaining signed sum.

**Verdict: BRIDGE.** Aggregating consumed selections removes an
unnecessary pointwise sampling requirement for the stated layers.
This is a deduction from the existing determinant theorem;
scientific priority and novelty are unestablished. It does not
prove the sampling conjecture, the full root average, removal
of marks, or twin-prime infinitude.

Corpus search for divisor-multiplicity weighted energy returned
ordinary Cauchy--Schwarz results, including
`RHTower.norm_sum_mul_sq_le`; no matched analytic strengthening
was located. Current primary-source searches led back to the
same determinant method. These searches do not certify absence.

- [x] Exact contribution and dependency-closed paper deduction.
- [x] Finite modulus-energy inequality formalized and axiom-audited.
- [ ] Unconditional Lean proof, including analytic dependencies.
- [ ] Remaining layers with fewer than `K_0` unconsumed groups.

## Log

- 2026-10-23 — Reordered selection and modulus summations.
  Proved that consumed selections form a bounded cofactor weight
  before Cauchy--Schwarz; the pointwise `1/d` energy improvement
  is unnecessary for layers retaining enough groups. No new
  Lean theorem or twin-prime result claimed.
