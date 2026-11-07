# Sum-product arithmetic of the logarithm

Namespace `GaloisForLFunctions.SumProductArithmeticOfTheLogarithm`;
umbrella `SumProductArithmeticOfTheLogarithm.lean`.

## Motivation

The phase `φ_t(n) = t log n` has two simultaneous structures: multiplication of
integers becomes addition of phases, while translation of integers produces a
smooth, curved phase. This programme studies their compatibility at one fixed
height, retaining the integer winding numbers lost on passage to the circle.
Its source is §2.9 of [Obstacles summary](../../../docs/reports/review-0711/obstacles-summary.md).

The intended arithmetic input uses neither positivity of a quadratic form nor a
self-adjoint operator. Exact identities alone do not exclude a zeta zero: the
cut calculus already annihilates every zero mode. A useful new input must bound
an actual count, phase concentration, or carry distribution.

## Objects and language

* **Phase level set:** integers in an interval whose `t log n` lie in a prescribed
  arc modulo `2π`. The location of the arc and the height are part of the data.
* **Shifted product signature:** products of a tuple before and after integer
  translations. Simultaneous coincidences couple addition to multiplication.
* **Mixed collision count:** number of tuples with equal product signatures.
  This is a combinatorial count, without a quadratic-form sign assumption.
* **Winding:** the integer removed when reducing a real phase modulo `2π`.
  **Carry:** the correction to winding under an addition or multiplication law.
* **First return:** least height at least one aligning the primes below a given
  cutoff to prescribed precision. An upper bound and a lower bound are different
  problems; recurrence by itself supplies no exclusion.
* **Finite oscillation:** the trigonometric leading term in a putative finite
  layer of right zeros. A contradiction must use more than its exact dilation
  annihilator.
* **Count distance:** discrepancy between the integer counting functions of
  two Beurling systems, with exponent as well as amplitude retained.

## Mechanisms and foundational questions

Two translated product readings can recover information absent from either
reading alone. The initial algebraic question is to classify their common
fibres, then establish quantitative separation of different fibres. The
analytic question is whether the winding numbers can be controlled at the
precision required to transfer that separation to a fixed height.

The integer gap makes distinct products distinguishable at inverse-product
resolution. Translation exposes coefficients of the polynomial
`∏ᵢ(X + nᵢ)`. Carries record the difference between an exact real identity and
its reduction modulo a period. These mechanisms must be combined with counts
of actual integers, rather than arbitrary torus points.

## Foundational theorems

These results couple translation to multiplication without an analytic sign
assumption. They classify exact fibres and the resolution needed to separate
them; occupation across distinct winding cells remains a separate question.
For Beurling counts, write `N(x)` for the number of generalized integers of
norm at most `x`, and `D(n)=N(n)−n`.

| Theorem | Exact content | Lean declaration |
|---|---|---|
| Pair reconstruction | `S(a,b)=(ab,(a+1)(b+1))` determines the unordered pair. On an alphabet of size `M`, its ordered collision count `E` satisfies `E+M=2M²`. | [`pairSignature_eq_iff`, `mixedCollisionCount_add_card`](ShiftedProductRigidity.lean) |
| Real-cell separation | In `[1,N]`, a radius-`ε` cell for both coordinates of `t log S` contains at most two ordered pairs when `2ε(N+1)²<|t|`. | [`card_logPairCell_le_two`](LogarithmicCollisionCells.lean) |
| Winding occupation | If `M` integers have their own and their successor's phases in prescribed radius-`ε` arcs, their pair-winding signatures number at least `M²/2` when `4ε(N+1)²<|t|`. | [`card_sq_le_two_mul_windingSignatures`](WindingOccupancy.lean) |
| Optimal resolution order | Pairs `(n+1,n+4)` and `(n+2,n+3)` are distinct but their translated products differ by two at every nonnegative integer shift. Corresponding logarithms differ by at most `2/(n+1)²`. | [`neighbouring_pair_log_gap`, `neighbouring_pair_signatures_ne`](SharpnessOfProductResolution.lean) |
| Tuple reconstruction | A multiset of size `k` is determined by products of its translates at any `k` distinct complex parameters. | [`eq_of_shifted_products`, `translated_products_complete`](TranslatedTupleReconstruction.lean) |
| Fine smooth × prime energy | For `y`-smooth rows `A` and primes `P>y`, all in `(X,2X]`, energy at width `1/T`, `T>0`, is at most `#A #P + 2 Σ_(1≤h≤floor(4X²/T)) Σ_(d∣h) d #A_d(h)²`, where `A_d(h)={m∈A:gcd(m,h)=d}`. | [`smoothPrimeLogEnergy_le_floor_gcd_classes`](CumulativeSmoothPrimeEnergy.lean) |
| Cumulative incidence envelope | Energy at width `1/T` is at most `#A #P+2 floor(4X²/T)#A²`. It is exactly diagonal for `T>4X²`. Summing compatible differences cancels the gcd loss. | [`smoothPrimeLogEnergy_le_floor_at_height`, `smoothPrimeLogEnergy_eq_diagonal_of_height`](CumulativeSmoothPrimeEnergy.lean) |
| Finite recurrence | Every finite set `A` aligns to precision `2π/(Q+1)` at some height in `[L,L(Q+1)^|A|]`, for every `L>0`. There is no last aligned height. | [`exists_alignment_in_scaled_interval`, `not_exists_last_alignment`](FiniteAlignmentReturns.lean) |
| Effective discrete half-turn | For `α=log 3/log 4` and `Q≥2`, some integer `1≤k≤Q4^Q log 4/2` satisfies `|kα−ℓ−1/2|<1/Q`. Integer-log separation controls the size of the preceding homogeneous return. | [`exists_effective_three_four_half_turn`, `threeFourRotation_gap`](EffectiveLogarithmicHalfTurn.lean) |
| Initial-index exclusion | Every discrete half-turn has error at least `1/((3^k+1)log 4)`. Precision `1/Q` forces `k>(log Q−log(2 log 4))/log 3`; an attained return also satisfies the upper bound above. | [`threeFourRotation_half_turn_gap`, `exists_three_four_half_turn_window`](DiscreteLogarithmicHalfTurnSeparation.lean) |
| Polynomial discrete returns | Fixed constants give a half-turn return by index `A Q^(D+1)` for every `Q≥2`; every such return satisfies `Q<A' k^D'`. The proved two-prime Baker bound controls both directions. | [`exists_polynomial_three_four_half_turn`, `exists_polynomial_half_turn_precision_bound`](PolynomialLogarithmicReturns.lean) |
| Collision amplification | Distinct factorizations of norm `m` give at least `k+1` factorizations of `m^k`. Uniformly bounded multiplicities force injective norm. | [`intCount_pow_ge_of_collision`, `bounded_intCount_iff_norm_injective`](NormCollisionAmplification.lean) |
| Count-distance trichotomy | A locally finite positive integer-norm system is classical, has `k≤|D(m^k)|+|D(m^k−1)|` for some `m≥2`, or has `N(m(4k+1))+k≤m(4k+1)` for some `m≥2`. | [`count_distance_trichotomy`](CountDistanceRigidity.lean) |
| Logarithmic isolation | Every nonclassical such system has `|D(n)|≥c log n` arbitrarily far out, for some `c>0`. Error `o(log n)` forces a norm-preserving equivalence of labels with rational primes. | [`primes_or_logarithmic_count_distance`, `primes_of_sublogarithmic_count_error`](LogarithmicCountFloor.lean) |
| Positive-generator near-count model | Odd primes together with extra norm-three and norm-four labels give a nonclassical positive system with `|N(x)−x|≤(log x/log 3+1)(log x/log 4+1)/2+2` for `x≥1`. | [`PositiveNearCount.count_error_log_bound`, `PositiveNearCount.count_error_log_sq`, `PositiveNearCount.not_prime_equiv`](PositiveNearCountEstimate.lean) |
| Signed carry excursions | The model satisfies `2(N(n)+N(⌊n/2⌋))+s₃(n)=3n`. Arbitrarily large `n` have `N(n)≤n−log n/(2 log 3)`. | [`PositiveNearCount.count_add_half_digit_sum`, `PositiveNearCount.negative_log_excursions`](PositiveNearCountCarries.lean) |
| Sharp averaged deficit | For the same model, `R(x)=∫₀ˣN(t)dt` satisfies `x log x/(12 log 3)≤x²/2−R(x)≤(2/3)x(log x/log 3+1)+x/2` for `x≥1`. | [`PositiveNearCount.riesz_log_bound`, `PositiveNearCount.integral_count_deficit`](PositiveNearCountRiesz.lean) |
| Exact averaged coefficient | `(x²/2−∫₀ˣN(t)dt)/(x log x) → 1/(4 log 3)` for the actual positive model. Its norm-four profile has uniform orbit average `1/4`. | [`PositiveNearCount.tendsto_integral_count_deficit`, `PositiveNearCount.uniform_profile_average`](PositiveNearCountExactAverage.lean) |
| Effective averaged remainder | Uniform profile error is at most `C log log n/log n`; the actual integral-count coefficient error is at most `C' log log log x/log log x`, with explicit constants and cutoffs. | [`PositiveNearCount.profile_log_rate`, `PositiveNearCount.integral_count_coefficient_log_rate`](PositiveNearCountConvergenceRate.lean) |
| Power convergence | Some fixed `0<η≤1`, `K,L>0` bound the uniform profile error by `K n^(−η)` for every `n≥1` and the actual integral-count coefficient error by `L(log x)^(−η)` for every `x≥exp 1`. | [`PositiveNearCount.exists_profile_and_count_power_rate`](PositiveNearCountPowerRate.lean) |
| Euler continuation and zero divisor | The actual model series is `ζ(s)/((1+2^(−s))(1−3^(−s)))` for `Re s>1`; its continuation has residue one and the same zeros, with multiplicities, as `ζ` on `Re s>0` away from one. | [`PositiveNearCount.zetaSeriesC_eq_continuation`, `PositiveNearCount.analyticOrderAt_zetaContinuation`, `PositiveNearCount.zetaContinuation_residue_one`](PositiveNearCountEuler.lean) |

Pair reconstruction follows by recovering the sum from the two products.
Tuple reconstruction recovers the monic polynomial `∏ᵢ(X+nᵢ)` by interpolation.
Real-cell separation uses the integer gap between distinct products. Winding
occupation applies this separation to sums of two phase remainders. The close
neighbouring pairs show why exact interpolation alone does not remove the
need for quantitative resolution.

Fine multiplicative energy also retains an arithmetic partition. If all prime
factors of `m,m'` are at most `y` and primes `p,p'` exceed `y`, then
`mp+h=m'p'` forces `gcd(m,h)=gcd(m',h)=gcd(m,m')`. In the balanced interval,
each fixed-row fibre has at most this gcd many column pairs. Summing within
the disjoint exact gcd classes gives the fine-energy bound above, with an
exact diagonal from smooth/rough product uniqueness. A logarithmic window
contains only differences at most `floor(4X²/T)`. For fixed rows of gcd `g`,
only multiples of `g` contribute, each with at most `g` column pairs. Summing
to `H` costs `g floor(H/g)≤H`, giving the uniform envelope above. A cutoff
below one leaves the exact diagonal. Recovering the prime-density factors
needed for random energy remains open.

At the discrete scale ratio `log 3/log 4`, oddness supplies a complementary
exclusion: half a power of three is a half-integer, separated from every
integer power of four. The logarithm preserves an explicit lower gap.
Together with the constructive half-turn return, this bounds an attained
index from both sides. The proved two-prime Baker estimate improves both
orders to fixed powers: it gives `c/q^D≤|qα−m|` for `0≤m≤q`, which bounds
the number of small Dirichlet steps needed to reach a half-turn. Applied to
`k log 3−(2ℓ+1)log 2`, it also bounds every half-turn's achievable precision
by a power of its index. These results concern two fixed scales; they do not
resolve the dependence on the cutoff in many-prime first returns.

The count-distance argument uses the free monoid of generator labels. A norm
collision amplifies along powers. Without collisions, representations of
`r,r+1,mr,m(r+1)` force a representation of `m`: the first two factorizations
have disjoint supports, and cancellation identifies the quotient. A missing
integer therefore forces omissions in every such quadruple. Counting their
incidences gives a linear deficit. These two alternatives isolate the rational
primes among systems with count error `o(log n)`, with the leading coefficient
fixed at one. Bounded-error rigidity is a corollary. They do not determine the
distance needed for an exceptional zero or settle the corresponding question
for generators of arbitrary real norm.

The near-count model supplies an upper construction with genuine nonnegative
generator multiplicities. Its generalized integers have unique coordinates
`(u,a,b)`, where `u` is positive odd, and norm `u 3^a4^b`. The odd-integer
density and the two geometric factors multiply to one. Summing the half-unit
rounding errors over the exponent rectangle gives `O((log x)²)` discrepancy.
The smallest possible nonclassical count distance therefore lies between
the logarithmic lower obstruction and this quadratic logarithmic construction.
The model does not insert a new zero in the right half-plane; the distance
required for an exceptional zero remains a separate question.

The model also tests actual integer carries. Adding its counts at `n` and
`⌊n/2⌋` telescopes the norm-four exponent and exposes the ternary digit sum
`s₃(n)`. At `n=3^k−1`, its discrepancy obeys `D(n)+D(n/2)=−k`, forcing a
negative logarithmic excursion at one of those two thresholds. Controlling
alternating ternary digit sums along the dyadic orbit remains necessary
to improve the pointwise upper bound.

Its first count average has a sharper description. Odd-integer midpoint
rounding and the omitted norm-four geometric tail force a deficit between
`x/12` and `2x/3` at every retained norm-three exponent. Consequently the
integrated count deficit has exact order `x log x`, with explicit constants.
Its leading coefficient is exactly `1/(4 log 3)`. The normalized norm-four
deficit converges along powers of four to a continuous profile `P` with
`P(x)+P(x/2)=1/2`. Rotation by `log 3` on the circle of length `log 4` has a
dense orbit. Pairing a finite orbit with an approximate half-period translate
forces its average to `1/4`, uniformly in its starting scale. The actual count
differs from the profile sum by a bounded normalized error. This identifies
logarithmic distance after averaging while leaving the pointwise
logarithmic-to-quadratic-logarithmic gap open.

The averaging is effective. Write
`R(Q)=(8 log Q+32 log 4+2/3)/Q` and `B(Q)=Q4^Q log 4/4`.
For every `Q≥2`, every orbit length `n≥1` and every positive starting
scale, the profile average differs from `1/4` by at most `R(Q)+B(Q)/n`.
An explicit complementary return and the profile's logarithmic modulus
produce these two costs. Choosing `Q=⌊log n/log 16⌋` gives the uniform
iterated-logarithmic rate above; choosing at scale `log x` transfers it
to the actual integral count. The finite bound is
[`effective_integral_count_coefficient_error`](PositiveNearCountEffectiveAverage.lean).

Polynomial return costs sharpen the rates further. For fixed `M≥2,A>0`,
the error is at most `R(Q)+A Q^M/n`. The modulus obeys
`R(Q)≤(16+32 log 4+2/3)Q^(−1/2)`. Choosing
`Q=ceil(Y^(1/(2M)))+1` gives a bound `K Y^(−η)` for every `Y≥1`, with
`η=1/(4M)>0`. Use `Y=n` for the uniform profile average and `Y=log x`
for the actual integrated count. Thus
`∫₀ˣN(t)dt=x²/2−x log x/(4 log 3)+O(x(log x)^(1−η))`.
These fixed-scale constants are existentially supplied by Baker's theorem;
the elementary estimates above retain explicit constants. Neither averaged
bound improves the pointwise count-distance estimate.

The model’s Dirichlet series is also identified from its actual generalized
integers. Absolute convergence and the coordinate bijection produce its
finite Euler quotient. The correction is analytic and nonzero throughout
the open right half-plane, and equals one at the pole. Thus the count
deformation preserves both the residue and the complete zero divisor there.
Count distance alone does not measure insertion of new right zeros.

## Tools and open research topics

| Required tool | Mathematical target |
|---|---|
| Energy beyond diagonal moments | Bound simultaneous shifted-product concentration of actual phase level sets, including nonzero windings. |
| Exponential sums beyond the polynomial barrier | Savings for `t log(n+h)` when the necessary Taylor degree exceeds `(log length)²`. |
| Carry contradiction for finite oscillations | Decide whether the rigid finite-zero asymptotic can coexist with `N(x)=⌊x⌋`. |
| Effective Kronecker in both directions | Quantitative return bounds that retain the start of the height orbit. |
| Beurling metric geometry above the isolation gap | Determine the smallest count distance carrying an exceptional zero, beyond the known deletion-exponent obstruction. |

Four questions organize the programme. What information survives when a dilation
is written as an average of translations? Which density and interval-length
conditions make small-arc concentration constrain the height? Can carries rule
out a single off-line zero? What count distance is necessary and sufficient to
insert one among integer-norm systems? The small-arc question needs an explicit
dependence of cutoff on height. Even an entire fixed finite interval returns
arbitrarily close to alignment at arbitrarily large heights, by simultaneous
Dirichlet approximation. Thus the target concerns the first return as the
cutoff grows, or exclusion in a specified initial height range.

## Relation to the corpus and calibration

**PrimeTorusTheory** supplies integer-log separation, finite-time recurrence,
non-alignment estimates, and the word/polynomial-phase ceilings. This programme
asks for information involving translations of the integer argument.
**RigidArithmeticOfCuts** supplies exact carries, dilation averages, zero-mode
blindness, parity/strip equivalence, and Beurling isolation. Its exact identities
are boundary conditions for a new inequality, not the inequality itself.
**ArithmeticCastelnuovoSeveri** and **ArithmeticOrientationGeometry** explain the
spectral receivers and impure models; their positivity mechanisms are outside
this programme's allowed inputs.

Finite-field calibration must recover Hasse–Weil in counting language through
Stepanov. The corpus already proves it for squarefree odd-degree hyperelliptic
curves over every finite field of odd characteristic, using splitting-field
descent; see [`abs_card_points_sub_le_oddHyperelliptic`](../RHTower/HyperellipticDescent.lean).
Arbitrary curves remain a broader calibration requirement.
Further tests are Burgess, smooth moduli and depth aspect, continuous Beurling
systems without integer carries, and the Golden discrete model. A theorem about
all integer sets alone cannot distinguish rational primes from a different
integer-norm system; that distinction also requires the prime amplitude.

The distinction between integer counts and Beurling systems is essential.
`RigidArithmeticOfCuts/ABoundedCountWithANewZero.lean` gives nonnegative integral
multiplicative coefficients with bounded count error and new right zeros.
Its Euler generators have negative multiplicities, and its added zeros form
vertical progressions. It supplies neither a positive-generator Beurling
counterexample nor a single exceptional zero pair.

## Traps and success criteria

Multiplicative energies of additive shifts already belong to classical
sum-product theory; see [Rudnev–Shkredov–Stevens](https://arxiv.org/abs/1607.05053).
Moreover, arbitrarily large real sets can have both `AA` and `(A+1)(A+1)`
of size `O(|A|^{2-c})` for a fixed `c>0`, by
[Roche-Newton–Schildkraut–Warren](https://arxiv.org/abs/2606.24583).
Thus near-quadratic growth of one projection is not a general real-set
principle. Any proposed improvement must state its integer and phase inputs.

An exact collision classification is foundational algebra, not a fixed-height
cancellation theorem. Small real phase difference and small difference modulo
`2π` must never be interchanged. Diagonal moments, one word, and one Taylor
polynomial have proved ceilings. Complete multiplicativity makes an untreated
Type II factorization empty. A power-saving parity claim must expose its
zero-free-strip consequence. Typical-height information does not exclude an
exceptional height or a finite exceptional zero set.

A contribution must state an unconditional theorem, identify the arithmetic
input and the quantitative range, give its exact Lean declaration, and explain
what it adds beyond existing corpus results. Foundational identities are labeled
as such. A claimed advance on the open core must improve a named estimate or
exclude a named obstruction and must survive the relevant fake-model tests.

Completion requires the five tools above, answers to the four organizing
questions, finite-field calibration, and an explicit strip output for any
power-saving parity mechanism. Establishing only algebraic foundations does
not complete this programme. No improvement beyond Vinogradov–Korobov or
exclusion of a finite right-zero layer is currently asserted here.
