# Rapid Convex Taylor Magnitudes: Curvature Resonance Is the Only DA Escape

- **ID:** `rapid-convex-curvature-resonance-hypertranscendence`
- **Stage:** 3-formalized / needs scientific-novelty audit
- **Type:** THEOREM CANDIDATE / GENERAL HT LAW / RATIO-ONE CURVATURE CONSTRAINT
- **Scientific status:** `[PROVED HERE] [NOVELTY UNVERIFIED] [SIGNIFICANT]`
- **Statement:** For an admissibly rapid, discretely convex logarithmic Taylor-magnitude profile, differential algebraicity forces one fixed Laurent relation in the discrete curvature `Delta^2 b` to return to logarithmic width infinitely often. Shift-separation of the curvature therefore forces hypertranscendence for every coefficient phase.

## Goal

Identify the canonical residue at the ratio-one boundary. For geometric growth with algebraic ratio `lambda`, the surviving resonance residue is `m_lambda(S)b`. When adjacent ratios tend to one and convexity forces the two atoms at an ADE bend into the same degree and source-sum class, their difference has both zero mass and zero first moment. The universal annihilator is therefore `(S-1)^2`, not `(S-1)`.

The native object is the discrete curvature

`kappa_n := Delta^2 b_n = b_(n+2)-2b_(n+1)+b_n`.                           `(K)`

## Admissibly rapid convex profiles

Call an eventually positive real sequence `(b_n)` **admissibly rapid convex** if, on a sufficiently large tail:

1. `b_n` is strictly increasing and `kappa_n>0` is nondecreasing;
2. `b_(n+1)/b_n -> 1` and, for every fixed integer `r`, `kappa_(n+r)/kappa_n -> 1`;
3. `kappa_n/Delta b_n -> 0`;
4. for every real `c>1`,

   `b_(floor(cn))/b_n -> infinity`;                                         `(RV)`

5. `kappa_n/log n -> infinity`.

Condition `(RV)` separates different convolution degrees. The quotient `kappa_n/Delta b_n->0` separates adjacent source-sum classes. Monotone positive curvature confines imbalanced tuples. Fixed-shift stability of `kappa` controls the cost of the surviving bounded witness.

Call the curvature **logarithmically shift-separated** if, for every nonzero integer Laurent polynomial `R`,

`|R(S)kappa(n)|/log n -> infinity`.                                        `(KLSS)`

## Curvature-resonance law `[PROVED HERE]`

Let `(b_n)` be admissibly rapid convex, and let

`f(z)=sum_(n>=0)a_nz^n`, `|a_n|=exp(-b_n)`,

have eventually full support. If `f` is DA over `C(z)`, then there exist a nonzero integer Laurent polynomial `R`, a constant `C>0`, and an unbounded sequence `(q_j)` such that

`|R(S)kappa(q_j)| <= C log q_j`.                                           `(CR)`

Consequently, if `(KLSS)` holds, every phase realization of the magnitude profile is entire and HT over `C(z)`.

## Log-Weibull corollary `[PROVED HERE]`

Fix `gamma>1`. Every eventually full-support series satisfying

`-log|a_n|=exp((log n)^gamma)`                                              `(LW)`

eventually is HT over `C(z)`, for every coefficient-phase sequence.

This profile lies strictly between all polynomial and all stretched-exponential scales:

`n^A=o(exp((log n)^gamma))` for every `A>0`,

while

`exp((log n)^gamma)=o(exp(n^alpha))` for every `alpha>0`.

It therefore occupies a scale not covered by either the polynomial ADE-degree floor or the stretched-exponential HT theorem.

## Discrete convex-confinement lemma `[PROVED HERE]`

Fix `D>=1`, a bounded integer shift `c`, and put `q=floor(N/D)`. Suppose a collection of degree-`D` atoms with source sum `N+c` contains a fixed-offset witness. Then there is a constant `R_0`, independent of `N`, such that every tuple `(k_1,...,k_D)` in this source-sum class with

`max_i |k_i-q|>R_0`

has valuation larger than the witness by `omega(log N)`.

### Proof

For `D=1`, the source sum fixes the sole index, so every tuple already has a fixed offset and the claim is immediate. Assume `D>=2`.

Choose a fixed integer `C_0` so large that the witness indices and every exactly balanced tuple lie above

`x=q-C_0`.

For the eventually convex sequence, use the supporting affine function at `x` with slope `Delta b_(x-1)`. For every integer `k` on the tail,

`b_k >= b_x+(k-x)Delta b_(x-1)`.                                           `(1)`

If `k=x+L` with `L>=1`, monotonicity of `kappa` strengthens this to

`b_(x+L)-b_x-L Delta b_(x-1)`

` = sum_(j=0)^(L-1)(Delta b_(x+j)-Delta b_(x-1))`

` >= L(L+1)kappa_(x-1)/2`.                                                 `(2)`

For a tuple of fixed sum, the affine terms in (1) add to a constant. If one offset is positive of size `R`, (2) gives a quadratic excess. If instead one offset is negative of size `R`, the fixed-sum constraint forces the total positive offsets, hence one positive offset, to have size at least `R/(D-1)-O_D(1)`. Thus in both cases the tuple's excess over the supporting affine value is at least

`(c_D R^2-O_D(R)-O_D(1)) kappa_(q-C_0-1)`.                                 `(3)`

The fixed witness has bounded offsets. Applying the reverse estimate over its fixed window bounds its excess over the same affine value by

`C_D max_(|r|<=C_1) kappa_(q+r)=C_D kappa_q(1+o(1))`,                      `(4)`

using fixed-shift stability of `kappa`. The same stability replaces `kappa_(q-C_0-1)` in (3) by `kappa_q(1+o(1))`. Choose `R_0` so that the quadratic coefficient in (3) exceeds twice the constant in (4). Every tuple outside that window then exceeds the witness by a positive constant times `kappa_q`, which is `omega(log q)=omega(log N)`. `square`

## Proof of the curvature-resonance law

Discard a finite Taylor prefix and reindex the remaining full-support tail, so all defining inequalities hold at every coefficient index used below. Differential algebraicity is preserved by this operation. The hypotheses make the series entire: since `kappa_n/log n->infinity` and `kappa` is positive and nondecreasing, two summations give `b_n/n->infinity`.

Suppose that `f` is DA. Mahler's integer-normalization theorem supplies a nonzero

`P in Z[z,Y_0,...,Y_m]`

with `P(z,f,f',...,f^(m))=0`. Let `D>=1` be its maximal total `Y`-degree. Generic coefficient extraction at `z^N`, followed by grouping equal coefficient monomials, gives a nonzero identity

`sum_(nu in A_N)c_(N,nu)a^nu=0`,                                          `(5)`

for every sufficiently large `N`. Its nonzero weights are integers of polynomially bounded number and size. The Archimedean tropical bend law therefore forces two grouped atoms whose valuations differ by `O_P(log N)`.

### 1. Lower degrees cannot reach the bend

The top-degree balanced-survival lemma supplies a degree-`D` fixed-offset witness at `N/D+O_P(1)`. If `D>=2`, an atom of degree `d<D` has a source index at least `N/d-O_P(1)`. Put `c=D/d>1`. Conditions `(RV)` and `b_(n+1)/b_n->1` give

`b_(N/d-O_P(1))/b_(N/D+O_P(1)) -> infinity`.                              `(6)`

Thus every lower-degree valuation exceeds the witness by a factor tending to infinity. When `D=1`, degree-zero terms contribute at only finitely many coefficient indices. Both atoms at every sufficiently large bend therefore have degree `D`.

### 2. Only the least active source-sum class can reach the bend

Polarize the top-degree part of `P` and delete the source-sum shift groups whose symmetric weight polynomial vanishes identically. Let `c_*` be the least remaining shift. Balanced survival supplies the fixed-offset witness inside this group.

For a fixed source sum, discrete convexity makes an exactly balanced tuple minimize `sum_i b_(k_i)`. Increasing the source sum by one changes one entry of such a tuple at `q+O_P(1)` and therefore raises the balanced minimum by

`Delta b_(q+O_P(1))=Delta b_q+O_P(kappa_q)=Delta b_q(1+o(1)).`             `(7)`

The witness in the `c_*` group exceeds that group's exactly balanced minimum by only `O_P(kappa_q)`, by the bounded-offset estimate (4). Since `kappa_q/Delta b_q->0`, every larger active shift is separated from this witness, and hence from the global minimum, by a positive multiple of `Delta b_q`. This is `omega(log q)` because `Delta b_q>=kappa_(q-1)` eventually. Thus both atoms at the bend lie in the same source-sum group `c_*`.

### 3. Both bend atoms have bounded offsets

Apply the discrete convex-confinement lemma to the surviving witness in `c_*`. Every atom outside one fixed offset window lies `omega(log N)` above the witness. Hence the minimum and every atom within the logarithmic bend width have indices

`k_i=q+r_i`, `|r_i|<=R_0`.                                                 `(8)`

### 4. Every bounded balanced difference is a curvature relation

If `D=1`, the degree and source sum determine the sole source index. Two surviving terms with that index are already one grouped atom, so the mandatory bend is impossible. Hence a DA realization would necessarily have `D>=2` here.

Take the two distinct grouped atoms at the bend and let

`Q(T)=sum_r d_rT^r`

be the difference of their offset-multiplicity polynomials. Equal degree and equal source sum give

`Q(1)=sum_r d_r=0`, `Q'(1)=sum_r r d_r=0`.                                `(9)`

After multiplying by a power of `T`, the integer polynomial has a double root at `1`. Division by the monic polynomial `(T-1)^2` therefore gives a nonzero integer Laurent polynomial `R` with

`Q=(T-1)^2R`.                                                              `(10)`

The valuation difference is exactly

`Q(S)b(q)=R(S)(S-1)^2b(q)=R(S)kappa(q)`.                                  `(11)`

For a fixed residue class of `N modulo D`, only finitely many ordered pairs of patterns in (8) occur. One pair recurs along an unbounded subsequence. The bend bound and `N=Dq+O_P(1)` give a fixed nonzero `R` and constant `C` satisfying `(CR)`.

If `(KLSS)` holds, `(CR)` is impossible. Hence no ADE exists and every phase realization is HT. `square`

## Smooth log-Weibull verification lemma `[PROVED HERE]`

Put

`B(x)=exp((log x)^gamma)`, `gamma>1`,

and `g(x)=(log x)^gamma`. For every fixed `k>=0`,

`B^(k)(x)=B(x)(gamma (log x)^(gamma-1)/x)^k(1+o_k(1)).`                    `(12)`

### Proof

Write `a(x)=g'(x)=gamma(log x)^(gamma-1)/x`. For every fixed `j>=2`, direct differentiation gives

`g^(j)(x)=O_j((log x)^(gamma-1)/x^j)`,

and therefore

`g^(j)(x)/a(x)^j=O_j((log x)^(-(j-1)(gamma-1)))->0`.                        `(13)`

The complete Bell-polynomial formula for `B^(k)/B` is a finite sum of monomials

`product_(j=1)^k (g^(j))^(m_j)`, `sum_j j m_j=k`.

The unique monomial using only `g'` is `a^k`. Every other monomial contains a factor with `j>=2`; after division by `a^k`, (13) makes it `o(1)`. Hence `B^(k)/B=a^k(1+o(1))`, proving (12). `square`

For every fixed `k`, (12) gives

`log(B^(k)(x)/log x)`

` = (log x)^gamma-k log x+k(gamma-1)log log x+O_k(1) -> infinity`.          `(14)`

In particular, `B'`, `B''`, and `B'''` are eventually positive. Integral finite-difference formulas give

`Delta B(n)=int_[0,1]B'(n+t)dt`,

`Delta^2B(n)=int_[0,1]^2B''(n+t+u)dtdu`,                                  `(15)`

and the analogous positive formula for `Delta^3B(n)`. Hence `b_n=B(n)` is eventually increasing, `kappa_n>0` is nondecreasing, fixed shifts of `b` and `kappa` have ratio one, and

`kappa_n/Delta b_n ~ B''(n)/B'(n) ~ gamma(log n)^(gamma-1)/n -> 0`.         `(16)`

For `c>1`,

`log(B(cn)/B(n))`

` = (log n+log c)^gamma-(log n)^gamma`

` ~ gamma log(c)(log n)^(gamma-1) -> infinity`,                            `(17)`

so `(RV)` holds. Equation (14) with `k=2` gives `kappa_n/log n->infinity`.

Finally fix a nonzero integer Laurent polynomial `R` and put `Q=(T-1)^2R`. Let `ell>=2` be the first nonvanishing power moment of the coefficients of `Q`. Taylor expansion over its fixed support, (12), and `B^(ell+1)=o(B^(ell))` give

`R(S)kappa(n)=Q(S)b(n)=C_Q B^(ell)(n)(1+o(1))`,                            `(18)`

with `C_Q!=0`. By (14), its absolute value divided by `log n` tends to infinity. Thus `(KLSS)` holds, and the curvature-resonance law proves the log-Weibull corollary. `square`

## Boundary attacks

1. **A large negative offset is not an escape.** The fixed source sum forces a compensating positive offset, and the one-sided supporting-line estimate (2) charges that positive displacement quadratically.
2. **Exact balancing need not survive coefficient grouping.** The proof uses only a fixed-offset surviving witness. Its `O(kappa_q)` excess is dominated both by larger-shift cost `Delta b_q` and by sufficiently large fixed imbalance cost `R^2kappa_q`.
3. **Polynomial profiles fail the curvature gate for a real reason.** For `b_n=n^beta`, sufficiently high Laurent shifts of `kappa=Delta^2b` are `O(log n)` or smaller. The theorem does not falsely classify the Valiron critical scale.
4. **The adjacent ratio is genuinely one.** For `(LW)`, `b_(n+1)/b_n->1`; neither the uniform-geometric theorem nor log-superlacunarity applies.
5. **The new class is below every stretched exponential.** The proof is not a reparameterization of `exp(n^alpha)`: its logarithmic exponent is `(log n)^gamma=o(n^alpha)` for every `alpha>0`.

## Parent and novelty status

- **Mahler normalization:** the reduction from an arbitrary complex-coefficient ADE to an integer differential polynomial is the essential arithmetic parent of the logarithmic bend estimate.
- **Lipshitz--Rubel:** their 1986 and 1991 gap theorems constrain the support spectrum of DA power series. The present series has full support, and the located statements do not formulate an Archimedean magnitude-curvature residue. A complete specialist comparison to the full 1986 proof remains required.
- **Valiron--Strelitz growth theory:** Valiron's third-order example shows that order-zero DA entire functions exist, while the classical first- and second-order obstructions stop below arbitrary ADE order. These results concern maximum-modulus growth and differential order, not phase-uniform Taylor magnitudes or recurrent Laurent relations in `Delta^2b`.
- **Arithmetic coefficient theory:** Pólya--Popken--Sibuya--Sperber bounds and Krattenthaler--Rivoal's refinement concern algebraic Taylor coefficients and finite-place denominators. Here the coefficient fields and phases are arbitrary.
- **Rapid-variation theory:** Karamata-style rapid variation supplies parent terminology and standard asymptotic tools for `(RV)`, but does not connect the curvature shift lattice to algebraic differential equations.
- **Tropical differential algebra:** existing tropical results treat support and local non-Archimedean vanishing orders. The valuation here is the Archimedean quantity `-log|a_n|`, and the new residue arises only after integer normalization and grouped convolution cancellation.
- **Preliminary verdict:** exact-statement, equivalent-form, coefficient-growth, logarithmic-order, rapid-variation, and proof-mechanism searches located no theorem implying `(CR)` or the phase-uniform log-Weibull corollary. Scientific novelty remains unverified pending full parent-paper inspection and independent expert review.

## Exact RH-route scope

The theorem makes HT status constant over every phase fiber satisfying `(KLSS)`. Together with fixed-modulus divisor non-identifiability, it excludes only RH implementations whose selector factors through this HT bit, the magnitude profile, its Newton geometry, or the curvature-resonance spectrum. It does not exclude complete spectral, positivity, norm, explicit-formula, or divisor criteria that retain data outside this quotient.

## Lean status

The theorem and its log-Weibull corollaries are formalized unconditionally in Lean 4.

- `formal/GaloisForLFunctions/HTGeometry/RapidConvexCurvatureResonance.lean` contains the generic discrete-convex confinement, integer shift-operator factorization, ADE bend extraction, recurrent curvature-resonance law, and shift-separation hypertranscendence theorem.
- `formal/GaloisForLFunctions/HTGeometry/LogWeibullFiniteDifference.lean` contains the all-order log-Weibull derivative asymptotic, arbitrary first-surviving-moment finite-difference asymptotic, fixed-shift stability, and logarithmic domination theorem.
- `formal/GaloisForLFunctions/HTGeometry/RapidConvexCurvatureResonanceHypertranscendence.lean` proves log-Weibull admissibility, curvature shift-separation, finite-prefix invariance, the eventual magnitude and log-magnitude corollaries, and hypertranscendence of every arbitrary-phase log-Weibull entire function.

The formal resonance theorem is slightly stronger than the paper interface: monotonicity of the discrete curvature is not required, and curvature positivity is needed only eventually. The checked theorem surface uses only `propext`, `Classical.choice`, and `Quot.sound`.

## Gates

- [x] Exact candidate law and scale-separated corollary stated.
- [x] Complete unconditional paper proof.
- [ ] Parent-theory and literature novelty gates.
- [x] Whole theorem formalized unconditionally in Lean.

## Log

- 2026-07-11 — Isolated `(S-1)^2 b` as the canonical balanced ratio-one resonance residue and opened the confinement proof.
- 2026-07-11 — Closed the discrete confinement, fixed-source factorization, and all-order log-Weibull derivative arguments; promoted to paper-proven with novelty still unverified.
