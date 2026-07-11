# Polynomial Taylor Log-Magnitudes Force an ADE Degree Floor

- **ID:** `polynomial-taylor-log-magnitude-ade-degree-floor`
- **Stage:** 2-fully-proven / needs scientific-novelty audit
- **Type:** THEOREM (paper) / GENERAL DA COMPLEXITY LAW
- **Scientific status:** `[PROVED HERE] [NOVELTY UNVERIFIED] [SIGNIFICANCE PROVISIONAL]`
- **Statement:** If the negative logarithms of full-support Taylor magnitudes equal `B n^beta`, then every integer algebraic differential equation for the series has total dependent-variable degree at least `ceil(beta)`.

## Goal

Determine what survives when fixed-shift separation eventually fails. Polynomial profiles admit high-order moment cancellations, so they need not be phase-uniformly HT by the anti-bend method. Nevertheless, the number of moments available to two degree-`D` convolution atoms is at most `D`. This turns coefficient decay into a lower bound on the algebraic complexity of every ADE.

## Integer ADE degree

For a DA formal series `f`, define

`deg_Z^ADE(f)`

to be the least maximal total degree in `Y_0,...,Y_m` among all nonzero polynomials

`P in Z[z,Y_0,...,Y_m]`

satisfied by `f`. Mahler's normalization theorem makes this a finite positive integer for every DA series.

## Theorem `[PROVED HERE] [NOVELTY UNVERIFIED]`

Fix `B>0` and `beta>1`. Let

`f(z)=sum_(n>=0)a_nz^n`

have eventually nonzero coefficients with

`-log|a_n|=B n^beta`                                                        `(1)`

eventually. If `f` is DA, then

`deg_Z^ADE(f) >= ceil(beta)`.                                               `(2)`

Equivalently, no integer ADE of maximal total `Y`-degree `D<beta` can be satisfied by any phase realization of (1).

## Proof

Discard a finite prefix. Suppose that

`P(z,f,f',...,f^(m))=0`                                                     `(3)`

for a nonzero integer differential polynomial whose largest total `Y`-degree is `D<beta`.

Generic coefficient extraction and grouping give

`sum_(nu in A_N)c_(N,nu)a^nu=0`,                                           `(4)`

where every `c_(N,nu)` is a nonzero integer and the number and sizes of the weights are polynomially bounded in `N`. Put

`V_N(nu)=B sum_n nu_n n^beta`.                                              `(5)`

The Archimedean tropical bend law forces the two smallest grouped-atom valuations in every sufficiently large nonzero identity (4) to differ by `O_P(log N)`.

### 1. Only the least active top-degree shift can minimize

A degree-`d` differential monomial contributes source indices with sum `N+c`, for one of finitely many shifts `c`. The top-degree polarization of `P` has at least one nonzero shift group. Let `c_*` be the least shift whose polarized symmetric weight is not identically zero. Balanced survival supplies a degree-`D` fixed-offset atom in this group for every sufficiently large `N`.

For a degree `d`, convexity of `x^beta` makes the balanced tuple minimize the valuation at fixed source sum. Its leading value is

`B d (N/d)^beta = B N^beta d^(1-beta)`.                                    `(6)`

Since `beta>1`, the function `d |-> d^(1-beta)` is strictly decreasing. Hence every degree `d<D` atom is separated from the degree-`D` witness by a positive constant times `N^beta`. Degree-zero terms disappear for large `N`.

Among degree-`D` groups, increasing the source-sum shift by one raises the balanced valuation by

`B beta (N/D)^(beta-1)(1+o(1))`,                                           `(7)`

whereas a fixed offset imbalance within `c_*` costs only `O(N^(beta-2))`. Therefore no shift larger than `c_*` can contribute either of the two smallest valuations at large `N`.

### 2. Convexity confines both atoms to fixed offsets

Write `q=floor(N/D)`. The surviving witness has indices `q+O_P(1)`. Consider any degree-`D` tuple in the same shift and write its offsets as `x_i`, so `sum_i x_i=O_P(1)`.

If `D=1`, the source sum determines the sole index in each shift, so bounded confinement is automatic. Assume `D>=2`; then `D<beta` implies `beta>2`.

If `max_i|x_i|` is comparable to `q`, strict convexity gives a valuation larger than the balanced scale by a positive multiple of `q^beta`. If all offsets are `o(q)`, Taylor expansion at `q` gives, after the fixed first-moment term,

`sum_i (q+x_i)^beta`

` = Dq^beta+beta q^(beta-1)sum_i x_i`

`   +(beta(beta-1)/2)q^(beta-2)sum_i x_i^2(1+o(1))`                         `(8)`

whenever the largest offset tends to infinity slowly enough; the intermediate scales follow from the same convex secant estimate. Thus an unbounded offset costs more than the fixed witness by an unbounded multiple of `q^(beta-2)`.

More explicitly, normalize `x_i/q` along a hypothetical unbounded minimizing sequence. A nonzero limiting normalized offset gives a strict Jensen gap of order `q^beta`; if all normalized offsets tend to zero, the integral form of the convex Taylor remainder shows that the cost is asymptotic to a positive multiple of `q^(beta-2)sum_i x_i^2`, while the fixed witness has bounded `sum_i x_i^2`. In either case the minimizer must have fixed bounded offsets.

The same estimates show that every atom outside a sufficiently large fixed window is separated from the minimum by `omega(log N)` whenever `D<beta`: in the closest case the cost is at least a positive constant times `q^(beta-D)`, as also follows from the moment comparison below. Hence both atoms at the mandatory ADE bend lie in one finite set of fixed-offset, degree-`D`, shift-`c_*` patterns.

### 3. Newton moments separate distinct degree-`D` patterns

If `D=1`, two degree-one atoms in the same shift have the same sole source index and hence are one grouped atom, so the mandatory bend is already impossible. Assume `D>=2`.

Take two distinct bounded patterns and let `(d_r)` be their multiplicity difference. Since both have `D` entries and the same source sum,

`sum_r d_r=0`, `sum_r d_rr=0`.                                              `(9)`

If all power moments through degree `D` vanished,

`sum_r d_rr^j=0` for `1<=j<=D`,

Newton's identities would give equality of all elementary symmetric polynomials of the two `D`-element multisets, hence equality of the multisets. Therefore there is a least `j` with

`2<=j<=D`, `M_j:=sum_r d_rr^j != 0`.                                       `(10)`

The binomial expansion gives

`B sum_r d_r(q+r)^beta`

` = B binom(beta,j) M_j q^(beta-j)(1+O(1/q))`.                              `(11)`

Because `j<=D<beta`, the generalized binomial coefficient is nonzero and

`q^(beta-j) >= q^(beta-D)=omega(log q)`.                                    `(12)`

Thus every two distinct bounded candidates have a superlogarithmic valuation gap. The finite candidate set makes the estimate uniform. This contradicts the ADE bend law.

No integer ADE of degree `D<beta` exists. Taking the least degree proves (2). `square`

## Consequences

1. For every phase sequence, the series with `|a_n|=exp(-n^pi)` satisfies no integer ADE of total `Y`-degree at most `3`.
2. If such a series is DA at all, every Mahler-normalized ADE has degree at least `4`.
3. More generally, increasing the polynomial decay exponent forces unbounded ADE algebraic complexity across the family.

## Sharpness and failure boundary

The proof intentionally stops at `D>=beta`. Two distinct `D`-element multisets can agree in several initial power moments, and then the first surviving term in (11) can be `O(log q)`, bounded, or decaying. Prouhet--Tarry--Escott phenomena make this a real combinatorial boundary, not a defect in the estimate.

No phase-uniform HT conclusion is claimed for a fixed polynomial profile. The theorem is a degree floor, not a proof of the full super-Gaussian conjecture.

## Exact RH-route scope

This law shows that polynomial coefficient decay can force arbitrarily high algebraic-differential complexity without determining phases or zeros. Therefore an RH implementation that equates “high ADE degree” with the zeta divisor still loses essential information. The theorem excludes only bounded-degree HT/DA transition mechanisms applied to these magnitude profiles; it says nothing categorical about complete spectral, positivity, norm, or explicit-formula routes.

## Parent and novelty status

- Newton's identities and convex power-sum minimization are classical ingredients.
- Mahler normalization and the Archimedean bend law connect them to arbitrary-complex DA series.
- Arithmetic coefficient bounds, support-gap theory, and Wiman--Valiron growth theorems do not state an ADE total-degree floor from the real exponent of `-log|a_n|`.
- Exact parent and rediscovery audits remain incomplete, so the result stays `[NOVELTY UNVERIFIED]` and its scientific significance remains provisional.

## Lean status

No Lean formalization is claimed. Complete formalization requires the generic ADE coefficient machinery, convex minimization, generalized binomial asymptotics, and Newton identities for multisets. The card cannot enter stage 3 until the whole theorem is formalized unconditionally.

## Gates

- [x] Exact quantitative degree floor stated.
- [x] Complete unconditional paper proof.
- [x] Phase-uniform bounded-degree exclusion.
- [ ] Scientific significance gate beyond a complexity refinement.
- [ ] Complete parent-literature and rediscovery gates.
- [ ] Whole theorem formalized unconditionally in Lean.

## Log

- 2026-07-11 — Proved that polynomial negative-log Taylor magnitudes impose the lower bound `deg_Z^ADE(f)>=ceil(beta)` by convex confinement and Newton-moment separation.
