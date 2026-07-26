# Kubalalika Parity-Corrected Main-Term Cancellation

- **ID:** `kubalalika-parity-corrected-main-term-cancellation`
- **Stage:** 2-fully-proven / needs-audit
- **Type:** THEOREM (paper) / exact obstruction to a claimed RH disproof
- **Scientific status:** `[PROVED HERE] [NOVELTY UNAUDITED] [SIGNIFICANT ROUTE KILL]`
  `[SECTION 4 CORE FORMALIZED IN LEAN, AXIOMS CLEAN]`
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
- [x] Section 4 formalized in Lean, equations (7)--(8) included:
  `GaloisForLFunctions.HTGeometry.SgnSinIntegral.integral_sign_sin_mul_inv_sq_Ici` proves
  `int_{[a,infty)} sgn(sin x)/x^2 = 1/a - (2/pi) log 2` for every `1 <= a <= pi`, and
  `sgnSin_endpoint_difference` proves `J(1) - J(2) = (2/pi) log 2`. Unconditional, axioms
  `[propext, Classical.choice, Quot.sound]`.
- [x] Section 1 formalized in Lean: `GaloisForLFunctions.HTGeometry.NearDiagonalParity`
  (`range_nearDiagonalSubst`, `range_nearDiagonalSubst_of_odd`,
  `exists_pow_two_of_even_of_vonMangoldt_ne_zero`).
- [ ] Section 2 (the odd-harmonic Fourier identity) formalizable but not yet built; see the route
  note below.
- [ ] Section 3 remains outside scope: prime number theorem plus the preprint's contour machinery,
  neither in the corpus.

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
- 2026-07-26 -- Prerequisite for the second missing piece built:
  `GaloisForLFunctions.HTGeometry.SinSignIntervals` gives the global sign characterisation of the
  real sine, which mathlib does not carry (it supplies only the first half-period plus the
  reflection `sin (x + n pi) = (-1)^n sin x`). Axioms clean.
  * `sin_eq_zpow_mul_sin_sub` -- reduction of `sin x` to its first half-period;
  * `sin_neg_of_mem_oddInterval`, `sin_pos_of_mem_evenInterval` -- the sign on each half-period;
  * `exists_int_mem_halfPeriod` -- every real lies in `[m pi, (m+1) pi)` with `m = floor (x/pi)`;
  * `sin_neg_iff` -- **`sin x < 0` iff `x` lies in some odd half-period `((2k+1)pi, (2k+2)pi)`**;
  * `pairwise_disjoint_oddInterval` -- the odd half-periods are pairwise disjoint;
  * `zero_le_of_oddInterval_mem_Ici` -- an odd half-period meeting `[1,infty)` has index `k >= 0`,
    so the decomposition of `int_1^infty` is indexed by the naturals.

  This is exactly the set-level input the card's Section 4 needs: the square wave `sgn (sin x)` has
  `{x : sin x < 0}` equal to a countable disjoint union of explicit intervals, all of which lie in
  `[1,infty)`. What remains is the measure-theoretic assembly: `integral_iUnion` over that family,
  `int_a^b x^-2 = 1/a - 1/b`, and summing with `tsum_alternatingHarmonicPair` (already built) to
  reach `int_1^infty sgn(sin x)/x^2 dx = 1 - (2/pi) log 2`.
- 2026-07-26 -- Second missing piece substantially built
  (`GaloisForLFunctions.HTGeometry.SgnSinIntegral`), axioms clean:
  * `oddHalfPeriod` -- the family `((2k+1)pi, (2k+2)pi)` indexed by the naturals, with
    `measurableSet_oddHalfPeriod`, `oddHalfPeriod_subset_Ici` (each lies in `[1,infty)` since
    `pi > 1`) and `pairwise_disjoint_oddHalfPeriod`;
  * `Ici_inter_sin_neg_eq_iUnion` -- **the decomposition the card asked for**:
    `[1,infty) inter {sin < 0} = union_k oddHalfPeriod k`, the natural indexing coming from
    `zero_le_of_oddInterval_mem_Ici`;
  * `integral_inv_sq_oddHalfPeriod` -- `int_{I_k} x^-2 = 1/((2k+1)pi) - 1/((2k+2)pi)`;
  * `tsum_integral_inv_sq_oddHalfPeriod` -- **`sum_k int_{I_k} x^-2 = (log 2)/pi`**, obtained by
    factoring `1/pi` out of `tsum_alternatingHarmonicPair`.

  So the mass that the square wave removes from `int_1^infty x^-2 = 1` is exactly `(log 2)/pi`, and
  the card's Section 4 value `1 - (2/pi) log 2` follows once the final Bochner assembly is written:
  `integral_iUnion` over the disjoint family (hypotheses now all available), the null-set argument
  discarding `{sin = 0} = pi * ZZ` (countable), and `int_{Ici 1} x^-2 = 1`.
- 2026-07-26 -- **Section 4 closed in Lean.**
  `GaloisForLFunctions.HTGeometry.SgnSinIntegral.integral_sign_sin_mul_inv_sq_Ici_one`:
  `int_{[1,infty)} Real.sign (sin x) * (x^2)^{-1} = 1 - (2/pi) log 2`, unconditional, axioms clean.
  Supporting results in the same module: `integrableOn_inv_sq_Ici_one`, `integral_inv_sq_Ici_one`
  (`int_{[1,infty)} x^-2 = 1`), `sinNegAboveOne` with `measurableSet_sinNegAboveOne` and
  `sinNegAboveOne_subset_Ici`, `integral_indicator_sinNegAboveOne` (the removed mass is
  `(log 2)/pi`), and `ae_sin_ne_zero` (the zero set `pi * ZZ` is countable, hence null, so the
  three-valued `Real.sign` may be replaced almost everywhere by `1 - 2 * indicator`).

  All three pieces the 2026-07-24 assessment named as blocking are now built and none needed the
  anticipated Abel summation: the grouped alternating harmonic value came from mathlib's
  Euler--Mascheroni limit (`AlternatingHarmonicPair`), the interval decomposition from a new global
  sign characterisation of `sin` (`SinSignIntervals`), and the assembly from `integral_iUnion` over
  the disjoint half-periods.

  The card's own gate wording ("formalize only if the obstruction becomes a reusable dependency") is
  now satisfied on the reusability side: `SinSignIntervals` and `AlternatingHarmonicPair` are
  general-purpose and independent of this preprint.
- 2026-07-26 -- Equations (7)--(8) closed, completing Section 4. The right generalisation removed
  the need for any interval-integral or sign-positivity argument on `[1,2]`: since every odd
  half-period starts at or beyond `pi` (`sinNegAboveOne_subset_Ici_of_le_pi`), the square-wave defect
  is the *same* for every base point `a` in `[1, pi]`, so
  `integral_sign_sin_mul_inv_sq_Ici : int_{[a,infty)} sgn(sin x)/x^2 = 1/a - (2/pi) log 2`.
  Specialising to `a = 1` and `a = 2` (legitimate because `2 <= pi`) and forming `I(1) - 2 I(2)`
  gives `sgnSin_endpoint_difference : J(1) - J(2) = (2/pi) log 2` -- exactly the card's `(8)`, hence
  the `+log(2)/(2 pi)` coefficient that cancels the small-`n` Landau--Gonek term.

  Also generalised in passing: `integral_inv_sq_Ici` (`int_{[a,infty)} x^-2 = 1/a`) and
  `integrableOn_inv_sq_Ici`, both for arbitrary `a > 0`.

  Section 4 of the card is now fully formalized. Sections 1--3 stay out of scope: they rest on the
  preprint's contour machinery and the prime number theorem input, neither of which is in the corpus.
- 2026-07-26 -- **Section 1 formalized** (`GaloisForLFunctions.HTGeometry.NearDiagonalParity`),
  axioms clean. This is the actual error the card identifies, now machine-checked:
  * `nearDiagonalSubst m n = 2n - m` with `two_mul_eq_add_nearDiagonalSubst` and
    `nearDiagonalSubst_injective`;
  * `range_nearDiagonalSubst : Set.range (nearDiagonalSubst m) = {r | Even (r + m)}` -- **the lost
    lattice condition**: the substitution reaches exactly the parity class of `m`, not all `r`;
  * `not_surjective_nearDiagonalSubst` -- so an unrestricted sum over `r` is provably not the
    substituted sum;
  * `range_nearDiagonalSubst_of_odd` -- for odd `m` the reachable `r` are exactly the odd ones,
    which is the restriction that turns the sawtooth kernel into the square wave;
  * `exists_pow_two_of_even_of_vonMangoldt_ne_zero` -- an even integer with `Lambda m != 0` is a
    power of two, with contrapositive `vonMangoldt_eq_zero_of_even_of_not_pow_two`. This is the
    card's reduction of the even-`m` correction to the powers of two.

  Route note for Section 2, so it is not re-planned from scratch. The identity
  `sum_{r odd} sin(r theta)/r = (pi/4) sgn(sin theta)` is *conditionally* convergent, so it is not a
  `tsum` statement: it must be phrased as convergence of the partial sums. The intended route is
  (i) Dirichlet test for convergence, (ii) mathlib's Abel limit theorem
  (`Mathlib/Analysis/Complex/AbelLimit.lean`, `tendsto_tsum_powerSeries_nhdsWithin_stolzSet`) to
  identify the limit with the radial limit, (iii) the radial limit from
  `Complex.hasSum_taylorSeries_neg_log`, giving `(1/2) arg((1+e^{i theta})/(1-e^{i theta}))` and
  hence `(pi/4) sgn(sin theta)`. The `sgn(sin)` side is already available from
  `HTGeometry/SinSignIntervals.lean`.
- 2026-07-26 -- Section 2 groundwork: the **odd Dirichlet kernel**
  (`GaloisForLFunctions.HTGeometry.OddDirichletKernel`), axioms clean. Corpus search found
  `RHTower.sum_cos_closed_form`, the general arithmetic-progression cosine sum in *polar* form under
  a complex hypothesis on `e^{i beta}/(1 - e^{i theta})`; the closed forms here are the real
  specialisation (`beta = theta`, common difference `2 theta`) and are proved directly by
  telescoping, which is shorter than discharging that hypothesis.
  * `two_mul_sin_mul_cos`, `two_mul_sin_mul_sin` -- the product-to-sum steps;
  * `sum_cos_odd` -- `sum_{k<N} cos((2k+1)theta) = sin(2 N theta) / (2 sin theta)`;
  * `sum_sin_odd` -- `sum_{k<N} sin((2k+1)theta) = sin(N theta)^2 / sin theta`;
  * `abs_sum_cos_odd_le`, `abs_sum_sin_odd_le` -- the partial sums are bounded uniformly in `N` by
    `1/(2|sin theta|)` and `1/|sin theta|`.

  The uniform bound is exactly the Dirichlet-test input for the conditionally convergent series
  `sum sin((2k+1)theta)/(2k+1)`, i.e. step (i) of the route recorded above; it is also the source of
  the "standard Dirichlet-kernel errors" that the card's truncation estimate `(3)` invokes. Steps
  (ii)-(iii), Abel's limit theorem and the radial limit of `-log(1-z)`, remain.
