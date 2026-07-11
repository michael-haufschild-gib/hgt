# Stretched-Exponential Taylor Log-Magnitudes Force Hypertranscendence

- **ID:** `stretched-exponential-taylor-log-magnitude-hypertranscendence`
- **Stage:** 2-fully-proven / needs scientific-novelty audit
- **Type:** THEOREM (paper) / GENERAL HT LAW / RATIO-ONE COEFFICIENT CONSTRAINT
- **Scientific status:** `[PROVED HERE] [NOVELTY UNVERIFIED] [SIGNIFICANT]`
- **Statement:** If the negative logarithms of the eventually nonzero Taylor-coefficient moduli equal a stretched exponential `B exp(n^alpha)` with `0<alpha<1`, then the entire function is hypertranscendental for every coefficient-phase sequence.

## Goal

Enter the log-ratio boundary `b_(n+1)/b_n->1`, where the algebraicity law for limits greater than one becomes silent. The theorem shows that ratio one is not itself the DA escape. A stretched-exponential profile retains superlogarithmic separation under every fixed finite-difference pattern, while convexity confines all potentially dominant ADE convolutions to fixed offsets.

## Theorem `[PROVED HERE] [NOVELTY UNVERIFIED]`

Fix `B>0` and `0<alpha<1`. Let

`f(z)=sum_(n>=0)a_nz^n`

have eventually nonzero coefficients satisfying

`-log|a_n|=b_n:=B exp(n^alpha)`                                              `(1)`

for every sufficiently large `n`. Then `f` is entire and HT over `C(z)`, independently of all coefficient phases.

In particular, every

`F_theta(z)=sum_(n>=0) exp(-exp(sqrt n))exp(i theta_n)z^n`                  `(2)`

is HT.

## Fixed-difference asymptotic `[PROVED HERE]`

For every nonzero finitely supported real family `(d_r)`, let `j` be the first index with

`M_j=sum_r d_rr^j != 0`.

Then

`sum_r d_r exp((n+r)^alpha)`

` = (M_j alpha^j/j!) exp(n^alpha)n^(-j(1-alpha))(1+o(1))`.                  `(FD)`

Indeed, for `h(x)=exp(x^alpha)`, induction gives

`h^(k)(x)=alpha^k x^(-k(1-alpha))h(x)(1+O(x^(-alpha)))`

for each fixed `k`. Taylor expansion at `n`, followed by the moment cancellations, proves `(FD)`. In particular every nonzero fixed-difference defect has absolute value `omega(log n)`.

## Bounded-minimizer lemma `[PROVED HERE]`

Fix integers `D>=1`, a finite set `C` of source-sum shifts, and, for at least one `c in C`, a fixed-offset degree-`D` witness with indices `q+O(1)` and sum `Dq+c+O(1)`. Among any collection of degree-`D` atoms containing such a witness for the least active shift `c_*`, every minimizer of

`sum_(i=1)^D exp(k_i^alpha)`                                                `(3)`

subject to `sum_i k_i=N+c`, `c in C`, has

`k_i=floor(N/D)+O(1)`                                                       `(4)`

with a bound depending only on the fixed collection and `D`.

### Proof

Put `q=floor(N/D)` and first compare shifts. A fixed-offset tuple with shift `c` has, by Taylor expansion,

`sum_i h(q+r_i)`

` = D h(q)+alpha h(q)q^(alpha-1)sum_i r_i`

`   + O(h(q)q^(-2(1-alpha)))`.                                             `(5)`

The function `h` is eventually strictly convex. Therefore, at each fixed source sum, an arbitrary tuple has value at least that of its balanced tuple. The sum of the balanced offsets is fixed by `c` and the residue of `N modulo D`. Hence increasing the active shift by one raises (5) by

`alpha h(q)q^(-(1-alpha))(1+o(1))`,

whereas changing a fixed balanced offset pattern within one shift costs only `O(h(q)q^(-2(1-alpha)))`. Therefore every minimizer uses the least active shift `c_*` for all large `N`.

It remains to prove bounded offsets within that shift. Suppose otherwise that a sequence of minimizing tuples has offsets `x_i=k_i-q` with

`sum_i x_i=O(1)` and `R=max_i|x_i|->infinity`.                              `(6)`

The fixed-offset witness has value

`D h(q)+alpha h(q)q^(alpha-1)sum_i x_i+O(h(q)q^(-2(1-alpha)))`.             `(7)`

There are three exhaustive scales.

1. If some `|x_i|` is comparable to `q`, the sum constraint forces a positive comparable offset, and its one term divided by `h(q)` tends to infinity. This exceeds (7).
2. Suppose every `x_i=o(q)` but some `|x_i|q^(alpha-1)` does not tend to zero. After taking a subsequence, put `y_i=x_iq^(alpha-1)`. The sum constraint gives `sum_i y_i->0`, while

   `h(q+x_i)/h(q)=exp(alpha y_i+o(1))`.

   If some `y_i` is unbounded above, the normalized sum diverges. Otherwise strict convexity of the exponential and `sum_i y_i->0` give a limiting normalized sum strictly greater than `D` unless every `y_i->0`, contrary to the case assumption. Again this exceeds (7), whose normalized value tends to `D`.
3. Finally suppose `R=o(q^(1-alpha))`. Taylor expansion is uniform and the first-order terms cancel under the fixed sum. The convex quadratic term gives

   `sum_i h(q+x_i)-D h(q)-alpha h(q)q^(alpha-1)sum_i x_i`

   ` = (alpha^2/2)h(q)q^(-2(1-alpha))sum_i x_i^2(1+o(1))`.                 `(8)`

   Since `R->infinity`, (8) exceeds the fixed `O(h(q)q^(-2(1-alpha)))` witness cost.

Every unbounded-offset possibility contradicts minimality. Thus (4) holds. `square`

## Proof of the theorem

Discard a finite prefix. Condition (1) makes `f` entire. Suppose it is DA. Mahler's integer-normalization theorem supplies a nonzero

`P in Z[z,Y_0,...,Y_m]`

with

`P(z,f,f',...,f^(m))=0`.                                                     `(9)`

Let `D` be its largest total `Y`-degree. Generic coefficient extraction at `z^N`, followed by grouping equal coefficient monomials, gives

`sum_(nu in A_N)c_(N,nu)a^nu=0`,                                           `(10)`

where the nonzero integer weights, their number, and their sizes are polynomially bounded in `N`.

The Archimedean tropical bend law says that the two smallest grouped-atom valuations

`V_N(nu)=sum_n nu_nb_n`

must differ by `O_P(log N)`. Otherwise the unique largest-magnitude atom cannot be cancelled by the polynomially many integer-weighted competitors.

The top-degree polarization of `P` splits into finitely many source-sum shifts. Delete the groups whose symmetric weight polynomial vanishes identically, and take the least remaining shift `c_*`. The balanced-survival theorem supplies a fixed-offset degree-`D` atom in this group for every sufficiently large `N`.

Every lower-degree atom has an index at least `N/(D-1)-O_P(1)` when `D>=2`; its valuation divided by that of the degree-`D` witness tends to infinity because

`exp((N/(D-1))^alpha-(N/D+O(1))^alpha)->infinity`.                          `(11)`

For `D=1`, degree-zero atoms disappear at large coefficient indices. Thus both atoms at the mandatory bend have degree `D`.

The bounded-minimizer lemma now confines the smallest valuation to fixed offsets in the least active shift. Its proof also shows that every atom outside a fixed offset window, every larger active shift, and every lower degree is separated from the minimum by `omega(log N)`. Hence the second atom required by the bend must be a distinct fixed-offset degree-`D` pattern as well.

The valuation difference of two such patterns is

`B sum_r d_r exp((q+r)^alpha)`                                             `(12)`

for a nonzero finitely supported integer family `(d_r)`. By `(FD)`, its absolute value is `omega(log q)=omega(log N)`. There are only finitely many fixed patterns after the confinement, so the estimate is uniform over all candidate pairs. The global minimum is unique with a superlogarithmic gap, contradicting the ADE bend law.

Therefore `f` is HT. `square`

## Boundaries and attacks

1. **This is genuinely a ratio-one theorem.** `b_(n+1)/b_n->1`, so the log-ratio algebraicity law gives no information.
2. **Every finite difference remains macroscopic.** Although each application of `S-1` loses a factor `n^(1-alpha)`, any fixed number of applications leaves a stretched exponential and hence an `omega(log n)` defect.
3. **Convexity, not fixed-ratio growth, confines the atoms.** The least active source-sum shift wins at first order; within it, unbounded imbalance loses at the convex second-order scale.
4. **Polynomial logarithmic profiles remain open.** For `b_n=n^beta`, sufficiently high finite differences fall below `log n`; the present mechanism intentionally stops there.
5. **No converse is claimed.** Failure of fixed-difference separation does not produce a DA function.

## Consequence for the super-Gaussian program

Since `exp(n^alpha)/n^2->infinity`, the theorem closes an arbitrary-phase, full-support part of the super-Gaussian conjecture in the difficult ratio-one regime. The remaining profiles must support bounded convolution near-resonances through arbitrarily high finite-difference depth; ordinary adjacent comparability is not enough.

## Exact RH-route scope

All phases with the magnitudes (1) are HT. Therefore an RH implementation whose selector factors only through this HT bit, the magnitude profile, or its Newton envelope cannot recover phase-sensitive zero information on the phase fiber.

This does not exclude complete literature criteria. It excludes only their implementations that discard exact spectral, norm, positivity, Euler-product, heat-flow, or divisor data and retain only this forced HT/magnitude invariant.

## Parent and novelty status

- Mahler normalization and the Archimedean bend law are the differential-algebraic inputs.
- The finite-difference asymptotic is elementary and not itself claimed new.
- Valiron--Wiman theory treats maximum terms and growth restrictions, but no arbitrary-order phase-uniform theorem for the profile `-log|a_n|=B exp(n^alpha)` was located.
- Shackell's nested Hardy-field expansions concern asymptotic subterms of solutions at infinity, not Taylor-coefficient magnitude phase fibers.
- Support-gap and arithmetic-coefficient theorems do not apply: the support is full and the coefficients may be arbitrary complex numbers.
- Exact parent and rediscovery audits remain incomplete. The theorem stays `[NOVELTY UNVERIFIED]` pending full Lipshitz--Rubel inspection and specialist review.

## Lean status

No Lean formalization is claimed. A complete formalization requires Mahler normalization, balanced generic coefficient survival, the Archimedean bend law, the convex bounded-minimizer lemma, and fixed-difference asymptotics. The card cannot enter stage 3 before the entire theorem is formalized unconditionally.

## Gates

- [x] Exact ratio-one theorem stated.
- [x] Complete unconditional paper proof.
- [x] Arbitrary-phase full-support corollary.
- [x] Significance gate: closes a non-geometric, ratio-one super-Gaussian stratum by a new confinement mechanism.
- [ ] Complete parent-literature and rediscovery gates.
- [ ] Whole theorem formalized unconditionally in Lean.

## Log

- 2026-07-11 — Proved phase-uniform HT for stretched-exponential negative logarithmic Taylor magnitudes by combining least-shift selection, convex bounded confinement, and superlogarithmic finite-difference separation.
