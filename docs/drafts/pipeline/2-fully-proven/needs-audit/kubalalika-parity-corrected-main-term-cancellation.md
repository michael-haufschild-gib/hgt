# Kubalalika Parity-Corrected Main-Term Cancellation

- **ID:** `kubalalika-parity-corrected-main-term-cancellation`
- **Stage:** 2-fully-proven / needs-audit
- **Type:** THEOREM (paper) / exact obstruction to a claimed RH disproof
- **Scientific status:** `[PROVED HERE] [NOVELTY UNAUDITED] [SIGNIFICANT ROUTE KILL] [NOT FORMALIZED]`
- **Source:** Tatenda Kubalalika, *The Riemann Hypothesis is False*, equations (15)--(17),
  (27)--(32), (53)--(57); the prime number theorem; the odd-harmonic Fourier series
- **Statement:** Restoring the parity condition omitted in the near-diagonal substitution replaces
  the source's sawtooth main term by a square-wave main term. Its large-`n` coefficient is
  `+log(2)/(2*pi)`, which cancels the small-`n` Landau--Gonek coefficient
  `-log(2)/(2*pi)` exactly.

## 1. The Lost Lattice Condition

The positive near-diagonal substitution is

`2n=m+r`.

It is a bijection only when

`r congruent m (mod 2)`.                                  (1)

The negative substitution `2n=m-r` has the same condition. The source drops (1) when equations
(15)--(17) and (27)--(30) replace sums over `n` by unrestricted sums over `r`.

The von Mangoldt weight simplifies the correction. If `m` is even and `Lambda(m)` is nonzero, then
`m=2^j`; all such terms together are `o(T)`. Thus the order-`T` contribution comes from odd `m`, and
for odd `m`, condition (1) permits only odd `r`.

## 2. The Correct Fourier Kernel

For `theta` outside `pi*Z`,

`sum_(r>=1, r odd) sin(r*theta)/r
   = (pi/4)*sgn(sin(theta))`.                             (2)

One proof subtracts the even harmonics from the usual sawtooth:

`sum_(r odd) sin(r*theta)/r
 = sum_(r>=1) sin(r*theta)/r
   -(1/2)*sum_(k>=1) sin(2k*theta)/k`.

The finite truncation error is bounded by the sum of the two standard Dirichlet-kernel errors

`O(1/(1+R*||theta/(2*pi)||)
  +1/(1+(R/2)*||theta/pi||))`.                            (3)

With `R=T^(1/4)`, the spacing count in equations (33)--(35) of the source applies separately to
the two distances in (3), giving total weighted error `o(T)`. The omitted even-`m` prime powers
also contribute only `o(T)`.

## 3. Endpoint Asymptotic

After multiplication by the endpoint factor `e/(2*pi*i)` from equation (9), equations (1)--(3)
turn the near-diagonal contribution at height `Y` into

`A_Y=(1/4)*sum_(V<=m<=T*(1+epsilon), m odd)
              Lambda(m)*sgn(sin(Y/m))+o(T)`,             (4)

where `V=T/((1+epsilon)log(T)^2)` and `epsilon=T^(-1/4)`.

For fixed `alpha>0` and `Y/T -> alpha`, the prime number theorem gives

`A_Y/T -> (1/4)*J(alpha)`,                               (5)

where

`J(alpha)=alpha*integral_[alpha,infinity]
                    sgn(sin x)/x^2 dx`.                  (6)

To justify (5), truncate (6) at a fixed `K`. Between `alpha` and `K` there are only finitely many
jump points, so partial summation and the prime number theorem apply interval by interval. The tail
`x>K` corresponds to `m<Y/K` and is `O(Y/K)` by the Chebyshev bound. First let `T` tend to infinity,
then let `K` tend to infinity. Restricting to odd `m` changes the sum only at powers of two and hence
does not affect the limit.

## 4. Exact Evaluation of the Difference

Let

`I(a)=integral_[a,infinity] sgn(sin x)/x^2 dx`.

Because `sin x>0` on `[1,2]`,

`J(1)-J(2)=I(1)-2*I(2)=1-I(1)`.                         (7)

Moreover,

`1-I(1)
 =2*sum_(k>=1) integral_[((2*k-1)*pi),(2*k*pi)] x^(-2) dx
 =(2/pi)*sum_(k>=1) (1/(2*k-1)-1/(2*k))
 =2*log(2)/pi`.                                          (8)

The last series is the alternating harmonic series.

Since the source selects `H=2T+O(1)`, equations (5)--(8) show that its large-`n` endpoint difference
is

`A_T-A_H=T*log(2)/(2*pi)+o(T)`.                          (9)

The small-`n` Landau--Gonek calculation in equations (53)--(55) gives

`-T*log(2)/(2*pi)+o(T)`.                                 (10)

Equations (9) and (10) cancel exactly. Therefore the source's claimed coefficient
`1-EulerGamma+log(pi/4)` is not the coefficient of the parity-corrected decomposition, and its
terminal `Theta<1` contradiction is unavailable.

## Scope

This theorem is a route kill, not a theorem about the truth value of RH. It proves the exact
parity-corrected endpoint law and the cancellation of the two asserted linear terms. It does not
need every other contour error in the preprint to be correct: even granting all of them as `o(T)`,
the claimed nonzero main term vanishes.

## Gates

- [x] Exact substitution lattice checked.
- [x] Even von-Mangoldt support reduced to powers of two.
- [x] Correct odd-harmonic Fourier identity proved.
- [x] Truncation error reduced to the source's two spacing counts.
- [x] Endpoint limit derived from the prime number theorem without numerical computation.
- [x] Difference evaluated exactly by the alternating harmonic series.
- [x] Corrected large-`n` term matched against the small-`n` Landau--Gonek term.
- [ ] Independent novelty/priority audit.
- [ ] Formalize only if the obstruction becomes a reusable dependency; it cannot produce
  `not RiemannHypothesis`.

## Log

- 2026-07-17 -- Proved during a line-by-line audit of the 2026 preprint. The parity omission is
  fatal: it converts the sawtooth to a square wave and forces exact main-term cancellation.
- 2026-07-24 -- Formalization assessed and deferred. The self-contained quantitative core is the
  exact evaluation `∫_1^∞ sgn(sin x)/x² dx = 1 − (2/π)·log 2` (Section 4). It needs two pieces of
  infrastructure absent from mathlib: (i) the grouped alternating-harmonic value
  `∑_{k≥1}(1/(2k−1) − 1/(2k)) = log 2` — mathlib's `HasSum` is unconditional convergence, so this
  requires an Abel/Euler–Mascheroni construction; (ii) the decomposition of the improper integral
  over `[1,∞)` into the countable disjoint family `((2k−1)π, 2kπ)`. Tractable but a large build; the
  PNT-asymptotic Sections 1–3 are tied to the preprint's contour machinery not in the corpus. Left
  for a session that first builds the alternating-harmonic infrastructure in `HTGeometry`.
- 2026-07-26 -- First of the two named missing pieces built:
  `GaloisForLFunctions.HTGeometry.AlternatingHarmonicPair` formalizes the grouped alternating
  harmonic value `sum_{k>=0} (1/(2k+1) - 1/(2k+2)) = log 2`, unconditionally, axioms
  `[propext, Classical.choice, Quot.sound]`.

  The 2026-07-24 note anticipated an Abel/Euler--Mascheroni construction; mathlib in fact already
  carries the harmonic numbers and `Real.tendsto_harmonic_sub_log_add_one`
  (`Mathlib/NumberTheory/Harmonic/EulerMascheroni.lean`), so no Abel summation is needed. The proof
  is: `sum_alternatingHarmonicPair_eq` telescopes the partial sums to `harmonic (2n) - harmonic n`,
  and splitting that as a difference of two Euler--Mascheroni increments cancels `gamma` and leaves
  `log(2n+1) - log(n+1) -> log 2` (`tendsto_harmonic_two_mul_sub_harmonic`).

  Grouping matters and is respected: the grouped terms are `1/((2k+1)(2k+2)) > 0`
  (`alternatingHarmonicPair_eq`, `alternatingHarmonicPair_pos`), hence absolutely summable
  (`summable_alternatingHarmonicPair`), so the value is a genuine `HasSum`
  (`hasSum_alternatingHarmonicPair`, `tsum_alternatingHarmonicPair`) and not merely a limit of
  partial sums of a conditionally convergent series.

  Remaining for the card's Section 4 core `int_1^infty sgn(sin x)/x^2 dx = 1 - (2/pi) log 2`: the
  second named piece, the decomposition of the improper integral over `[1,infty)` into the countable
  disjoint family `((2k-1)pi, 2k pi)` on which `sin` is negative. Sections 1--3 remain tied to the
  preprint's contour machinery and are not in scope.
