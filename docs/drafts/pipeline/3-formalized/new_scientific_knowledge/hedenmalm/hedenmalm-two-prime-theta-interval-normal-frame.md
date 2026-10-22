# Two prime theta-interval anomalies generate the complete Xi normal module

- **ID:** `hedenmalm-two-prime-theta-interval-normal-frame`
- **Stage:** 3-formalized
- **Type:** THEOREM / SOURCE-NORMAL PRIME FRAME / ESSENTIAL COMPACT-BOUNDARY SYMBOL
- **Scientific status:** `[PAPER-PROVED] [NOVELTY UNVERIFIED] [NOT RH]`
- **Parents:**
  `hedenmalm-prime-translation-rank-one-anomaly.md`;
  `hedenmalm-theta-source-compressed-inverse-determinant.md`;
  `../../1-in-progress/perspective-neutral-prime-clock-rigging.md`;
  `../../4-publication-ready/riemann-source-modular-superselection/main.tex`.

## Question closed

The updated source-modular synthesis separates a scalar Xi conormal from the independent
prime-labelled normal frame required by a genuine boundary consumer.  The Hedenmalm translation
commutator gives such a frame after taking the source-normal class, but not before it.

Let `k` be the positive even Hedenmalm theta source, normalized by

\[
 \widehat k(z)=\Xi_C(z),
 \qquad
 \widehat f(z)=\int_{\mathbb R}f(x)e^{izx}\,dx.
 \tag{1}
\]

Use the exponential source core, the compact-source inverse `B`, the normalized integer shifts

\[
 (T_nf)(x)=n^{-1/2}f(x+\log n),
 \tag{2}
\]

and the rank-one anomaly vectors

\[
 r_n=V(T_nk-n^{-1/2}k),
 \qquad
 (Vg)(x)=i\int_{-\infty}^xg(y)\,dy.
 \tag{3}
\]

## Theorem

### 1. Exact interval transgression and divisor factorization

Put `L_n=log n`.  Direct integration gives

\[
 r_n(x)=i n^{-1/2}\int_x^{x+L_n}k(t)\,dt.
 \tag{4}
\]

Consequently

\[
 \widehat r_n(z)
 =q_n(z)\Xi_C(z),
 \qquad
 q_n(z)=n^{-1/2}\frac{1-e^{-izL_n}}{z},
 \tag{5}
\]

where the apparent singularity at zero is removable.  Thus the nonzero core commutator anomaly is
zero in the analytic divisor cokernel `O(C)/XiC O(C)`.  It is a source coboundary, not an extension
class on the divisor fibre.

The anomaly satisfies the exact multiplicative Wess--Zumino law

\[
 r_{mn}=n^{-1/2}r_m+T_mr_n,
 \qquad
 q_{mn}(z)=n^{-1/2}q_m(z)+m^{-1/2-iz}q_n(z).
 \tag{5a}
\]

This follows either from `[B,T_mT_n]=[B,T_m]T_n+T_m[B,T_n]` or directly from `(5)`.
Thus the finite integer-shift anomaly is a flat, exact monoid cocycle.  Any RH-bearing anomaly must
survive the source-normal all-prime completion; finite cocycle curvature cannot supply it.

Center the interval by defining

\[
 c_n=-iS_{L_n/2}r_n,
 \qquad
 c_n(x)=n^{-1/2}\int_{x-L_n/2}^{x+L_n/2}k(t)\,dt.
 \tag{6}
\]

Then `c_n` is positive, real, even, and rapidly decreasing, and

\[
 \widehat c_n(z)=a_n(z)\Xi_C(z),
 \qquad
 a_n(z)=2n^{-1/2}\frac{\sin(zL_n/2)}{z},
 \qquad
 a_n(0)=n^{-1/2}L_n.
 \tag{7}
\]

The multiplier `a_n` is even and Real:

\[
 a_n(-z)=a_n(z),
 \qquad
 a_n(\overline z)=\overline{a_n(z)}.
 \tag{8}
\]

### 2. Two literal primes frame every normal direction

The entire functions `a_2` and `a_3` have no common zero in `C`.

Indeed, zero is not a zero of either function.  Every other zero of `a_n` is real and satisfies

\[
 z\log n=2\pi k
 \quad\text{for some nonzero }k\in\mathbb Z.
 \tag{9}
\]

A common zero would give nonzero integers `k,l` with

\[
 \frac{\log2}{\log3}=\frac{k}{l},
 \tag{10}
\]

and hence an equality between positive powers of `2` and `3`, contradicting unique factorization.

Let `I=(XiC)` in `O(C)`.  The conormal module is

\[
 I/I^2\simeq \bigl(O(C)/(\Xi_C)\bigr)[\Xi_C].
 \tag{11}
\]

Equations `(7)` and the no-common-zero theorem show that

\[
 [\widehat c_2]=a_2[\Xi_C],
 \qquad
 [\widehat c_3]=a_3[\Xi_C]
 \tag{12}
\]

generate `I/I^2` everywhere.  Equivalently, Cartan's theorem B on `C` gives entire functions
`b_2,b_3` with

\[
 b_2a_2+b_3a_3=1,
 \tag{13}
\]

so

\[
 (\widehat c_2,\widehat c_3)=(\Xi_C)
 \quad\text{as ideals of }O(C).
 \tag{14}
\]

This is a source-defined two-prime resolution before any zero is selected.

### 3. Multiplicity and source-normal nonannihilation

Let `zeta` be a zero of `XiC` of order `m`.  For `0 <= j < m`,

\[
 \widehat c_n^{(j)}(\zeta)=0,
 \tag{15}
\]

while

\[
 \widehat c_n^{(m)}(\zeta)
 =a_n(\zeta)\Xi_C^{(m)}(\zeta).
 \tag{16}
\]

At least one of the values `a_2(zeta),a_3(zeta)` is nonzero.  Hence the pair of first nonzero
normal jets in `(16)` retains every Xi point and its exact analytic multiplicity.  The value-level
anomaly is invisible on the divisor, but its source-normal class is nowhere zero.

This closes the nonvanishing half of the defect-factorization question

```text
source covariance defect = XiC * on-shell normal frame.
```

It does not produce a normal CCR intertwiner or a positive invariant metric.

### 4. Positive-kernel self-adjoint source channels, but no Hilbert spectrum

Convolution by `c_2` and `c_3` defines two bounded self-adjoint operators on ordinary
`L2(R)`, because both kernels are real, even, and integrable.  Their analytic multiplier row has
cokernel

\[
 \operatorname{coker}\left(
  O(C)^2\xrightarrow{(f_2,f_3)\mapsto
    \widehat c_2f_2+\widehat c_3f_3}O(C)
 \right)
 \simeq O(C)/(\Xi_C).
 \tag{17}
\]

Thus two positive-kernel, self-adjoint source channels recover the complete Xi divisor analytically.
The convolution operators themselves are not claimed positive: their real Fourier multipliers can
change sign.
They do **not** realize it as ordinary Hilbert spectrum: on the real Fourier axis their common zero
set has Lebesgue measure zero, so the corresponding reduced `L2` defect is zero.  This is an exact
positive realization of source incidence, not Hedenmalm's missing positive spectral realization.

### 5. Essential singularity in compact reciprocal coordinates

For a Hedenmalm root block, the compact Grushin inverse has eigenvalue

\[
 \mu=-\frac1\zeta.
 \tag{18}
\]

The normal multiplier `(7)` becomes

\[
 A_n(\mu)=a_n(-1/\mu)
 =2n^{-1/2}\mu\sin\left(\frac{L_n}{2\mu}\right).
 \tag{19}
\]

It has an essential singularity at the compact spectral boundary `mu=0`.  Nevertheless, on every
Xi root block,

\[
 A_n(-1/\zeta)=a_n(\zeta),
 \tag{20}
\]

and `(a_2(zeta),a_3(zeta))` is nonzero.  If `f_zeta` is the source-normalized global right mode,
then

\[
 \bigl(A_2(-1/\zeta)f_\zeta,
       A_3(-1/\zeta)f_\zeta\bigr)\ne(0,0).
 \tag{21}
\]

Equation `(21)` is the requested essential-singular, source-pointed, multiplicity-faithful
root-block landing at the algebraic boundary level.  A closed operator with symbol `(19)` on the
whole compact root expansion is not asserted.

## Ordinary-multiplier instability theorem

The analytic frame `(12)` cannot be promoted to a bounded Bezout corona by ordinary bounded
Fourier multipliers on the real axis.  Already

\[
 |a_2(t)|+|a_3(t)|\longrightarrow0
 \quad(|t|\longrightarrow\infty)
 \tag{22}
\]

because the sine factors are bounded.  More sharply, after removing the common first-order decay,

\[
 t a_n(t)=2n^{-1/2}\sin(tL_n/2),
 \tag{23}
\]

there is a sequence `t_j -> infinity` for which both terms in `(23)` tend to zero.  Choose
integers `q_j -> infinity` with `q_j log(3)/log(2)` approaching integers and put
`t_j=2 pi q_j/log(2)`.  Then the prime-2 term is zero and the prime-3 term tends to zero.

Therefore no Bezout pair in `(13)` is jointly bounded on the real axis, and even the
first-normalized two-prime frame has no uniform lower frame bound.  Pointwise conormal
nonannihilation and closed Hilbert descent are genuinely different theorems.

### Finite-versus-Hilbert prime-rank fracture

The instability is not special to the pair `2,3`.  For every prime `p`, put

\[
 b_p(t)=t a_p(t)=2p^{-1/2}\sin(t\log p/2).
 \tag{24}
\]

Let `P` be any finite nonempty set of primes.  Unique factorization makes
`(log p)_(p in P)` linearly independent over `Q`.  Kronecker recurrence therefore gives
arbitrarily large real `t` for which every phase `t log p/2` is simultaneously as close as desired
to an integral multiple of `2 pi`.  Hence

\[
 \liminf_{t\to+\infty}\sum_{p\in P}|b_p(t)|^2=0.
 \tag{25}
\]

More generally, let `omega_p >= 0` and assume

\[
 \sum_p\frac{\omega_p}{p}<\infty.
 \tag{26}
\]

Then

\[
 \boxed{\quad
 \liminf_{t\to+\infty}
 \sum_p\omega_p|b_p(t)|^2=0.
 \quad}
 \tag{27}
\]

To prove `(27)`, first choose a finite prime head so that the uniformly bounded tail
`4 sum omega_p/p` is arbitrarily small.  Apply finite-dimensional Kronecker recurrence to make the
head arbitrarily small simultaneously.  The recurrence times can be taken arbitrarily large.

Thus the Xi normal line has **algebraic prime rank two** but no finite or summably weighted
diagonal **Hilbert frame rank**.  Any uniformly coercive source completion must use at least one of:

1. a nonsummable all-prime weight requiring renormalization;
2. genuinely non-diagonal cross-prime coupling;
3. a singular graph/bornological topology not controlled by an ordinary frame lower bound.

This is the exact finite-to-infinite boundary.  Merely adding a countable `l2` direct sum leaves the
same near-resonance obstruction.

## What this changes

The source-modular paper said that a scalar conormal cannot generate the independent
prime-labelled normal frame required downstream.  Equations `(6)`--`(16)` now construct that frame
from two literal prime translations of the theta source.  They also explain why it was absent in
regular categories:

```text
core commutator anomaly: nonzero but divisor-exact;
source-normal blow-up: two-prime frame is everywhere nonzero;
analytic category: complete Xi cokernel recovered;
ordinary Hilbert category: cokernel disappears;
compact reciprocal chart: frame becomes essential-singular;
bounded corona: fails by high-frequency simultaneous resonance.
```

The missing RH theorem has consequently moved.  It is no longer conormal acquisition or
nonannihilation.  It is a strict completion theorem which makes the essential pair `(19)` a closed
reflection-compatible boundary operator while retaining the unsymmetrized prime phase.  Equations
`(25)`--`(27)` force that completion to be nonsummable/renormalized or genuinely cross-prime.  Any
proof must overcome this rank fracture rather than assume a bounded frame estimate.

The child bridge `prime-log-jump-sonin-mellin-grade-frame.md` makes this compatibility explicit.
It does not close another frontier gate: two-window BV conormal faithfulness and Sonin aperture
grade were already proved elsewhere in the corpus.  The inverse
Fourier transforms of the coefficients `a_p` are literal prime-log windows; a two-prime difference
is a discontinuous annulus packet.  Essential modulation sends that packet to the already
constructed cofinal Sonin partial-unitary face, while its first rescaled Mellin trace is a globally
coprime two-channel entire frame.  Dilation changes the trace by `r^(1/2-s)`.  Thus conormal landing
and the exact critical-line grade are explicit in one theta/Sonin chart.  Remaining open theorem is
continuity of this jump-Mellin normal in the same canonical closed boundary topology as the Hilbert
adjoint, together with the undeconvolved theta-to-Sonin action intertwiner.

## Hostile audit

1. **Not an RH proof.**  A positive Real frame can exist at nonreal divisor points; it does not
   make multiplication by the spectral coordinate symmetric.
2. **No false extension class.**  The raw anomaly is divisible by `XiC` and vanishes in the
   analytic divisor cokernel.  Only its class after deformation to the normal cone is nonzero.
3. **No contradiction with finite-frame no-gos.**  This frame generates the divisor normal line;
   it does not factor the horizontal Xi orientation current into a positive finite local Gram.
4. **No bounded corona.**  Equation `(13)` is analytic, not `H-infinity`, `L2`, or operator-norm
   controlled.
5. **No hidden zero selection.**  `c_2,c_3`, their factorization, and their Bezout ideal are defined
   before evaluating a zero.
6. **No simplicity assumption.**  Equation `(16)` uses the first nonzero jet of arbitrary order.
7. **Divisor-universal normal geometry.**  Multiplying any entire function by the same coprime
   interval frame gives an analogous normal resolution.  Arithmetic force must enter the strict
   all-prime/Gamma completion, not the two-prime frame alone.
8. **Only the ordinary bounded-multiplier route is excluded.**  Equations `(22)`--`(23)` do not
   exclude every singular graph topology; such a topology is exactly the remaining target.
9. **No zero-subsequence inference.**  Equation `(27)` concerns coercivity on the full real
   boundary.  Its recurrence sequence is not asserted to contain Xi zeros.

## Preliminary literature boundary

Hedenmalm constructs the theta differential pencil, its complex zero modes, and the pair
self-adjointness question, but does not state `(4)`--`(21)`:
<https://arxiv.org/abs/2606.17494>.

Interval Fourier transforms, coprime sine zero sets, Cartan--Bezout generation on `O(C)`, and
self-adjoint convolution by real even kernels are classical.  Targeted searches found no primary
source combining them with the Hedenmalm translation commutator, the Xi conormal module, and the
essential compact reciprocal symbol.  Novelty remains unverified and attaches only to that exact
conjunction.


## Lean status

`[FORMALIZED]`  `formal/GaloisForLFunctions/RHTower/Hedenmalm/HedenmalmIntervalAnomaly.lean`
(namespace `RHTower.HedenmalmIntervalAnomaly`), built on the rank-one anomaly module
`RHTower/Hedenmalm/HedenmalmPrimeTranslationAnomaly.lean` of the parent card.  All declarations are
`#print axioms`-clean.

| # | statement | Lean declaration |
|---|---|---|
| `(3)` | the rank-one anomaly vectors `r_n` | `HedenmalmPrimeTranslation.integerAnomaly` |
| `(4)` | exact interval transgression `r_n(x) = i n^(-1/2) integral_x^(x+log n) k` | `intervalMass`, `mass_mul_cdfFun_sub`, `integerAnomaly_eq_intervalMass` |
| `(5a)` | multiplicative Wess--Zumino law `r_(mn) = n^(-1/2) r_m + T_m r_n` | `intervalMass_add`, `integerAnomaly_mul` |
| `(5)` | the interval multiplier `q_n` and its exact zero set `z log n in 2 pi Z` | `shiftMultiplier`, `shiftMultiplier_eq_zero_iff` |
| `(6)` | uniform bound `c_n <= n^(-1/2) M` | `intervalMass_le_mass`, `centeredWindow_le` |
| `(7)` | the centered multiplier `a_n` and its zero set | `centeredMultiplier`, `centeredMultiplier_eq`, `centeredMultiplier_eq_zero_iff` |
| — | **prime-2 / prime-3 no common zero**, raw and centered | `eq_zero_of_log_three_eq_log_two`, `no_common_zero_two_three`, `no_common_zero_centered_two_three` |
| `(6)` | the centered window `c_n = -i S_(L_n/2) r_n`, strictly positive and even | `centeredWindow`, `centeredWindow_eq`, `centeredWindow_pos`, `intervalMass_pos`, `cdfFun_neg`, `intervalMass_neg`, `centeredWindow_neg` |

**Unconditional divisor factorization.**  `formal/GaloisForLFunctions/RHTower/Hedenmalm/HedenmalmThetaIntervalTransform.lean`
(namespace `RHTower.HedenmalmThetaSource`) proves the factorization at the actual arithmetic
source, with no hypothesis: one integration by parts on the line, the window derivative
`k(. + L) - k`, and the vanishing of the boundary terms from the exponential decay of the source.

| # | statement | Lean declaration |
|---|---|---|
| `(4)` | the sliding window inherits the source decay | `intervalMass_le_exp`, `norm_windowFun`, `continuous_windowFun` |
| `(4)` | the window derivative is `k(. + L) - k` | `windowFun_eq_sub`, `hasDerivAt_windowFun` |
| `(5)` | boundary terms vanish; the window transform converges | `norm_windowFun_sourceChar_le`, `integrable_windowFun_sourceChar`, `tendsto_windowFun_sourceChar` |
| `(5)` | translated source integral `= e^(-izL) Xi_C` | `sourceChar_add`, `shifted_char_factor`, `integral_shifted_k_sourceChar` |
| `(5)` | **`hat w_L(z) = (1 - e^(-izL))/(iz) Xi_C(z)`** | `integral_windowFun_sourceChar` |
| `(5)` | **`hat r_n = q_n Xi_C`** | `integral_integerAnomaly_sourceChar` |
| `(7)` | **`hat c_n = a_n Xi_C`** | `integral_centeredWindow_sourceChar` |

**Normal frame and compact coordinate.**  `formal/GaloisForLFunctions/RHTower/Hedenmalm/HedenmalmTwoPrimeNormalFrame.lean`
(namespace `RHTower.HedenmalmThetaSource`).

| # | statement | Lean declaration |
|---|---|---|
| `(7)` | closed trigonometric form `a_n(z) = 2 n^(-1/2) sin(z log n / 2)/z` | `centeredMultiplier_eq_sin` |
| `(11)` | the multiplier is analytic off the origin | `analyticAt_centeredMultiplier` |
| `(15)`,`(16)` | **a nonvanishing multiplier retains the exact analytic order of `Xi_C`** | `centeredWindowTransform`, `analyticOrderAt_centeredWindowTransform` |
| `(16)` | **two literal primes retain every `Xi` point and its exact multiplicity** | `two_prime_retains_analyticOrder`, `two_prime_retains_divisor` |
| `(18)`,`(19)` | the compact reciprocal multiplier `A_n(mu) = 2 n^(-1/2) mu sin(L_n/(2 mu))` | `compactNormalMultiplier`, `compactNormalMultiplier_eq` |
| `(20)` | `A_n(-1/zeta) = a_n(zeta)` on every root block | `compactNormalMultiplier_root` |
| `(21)` | **the essential-singular pair does not annihilate a nonzero root mode** | `essential_pair_ne_zero` |
| `(23)` | the first-order normalized frame symbol `b_n(t) = t a_n(t) = 2 n^(-1/2) sin(t log n / 2)` | `frameSymbol`, `mul_centeredMultiplier_eq_frameSymbol`, `abs_frameSymbol_le` |
| `(22)` | **the multiplier decays like `1/abs t`, so `abs a_2 + abs a_3 -> 0`** | `norm_centeredMultiplier_le`, `tendsto_norm_centeredMultiplier_atTop` |

**Kronecker frame obstruction.**  `formal/GaloisForLFunctions/HTGeometry/KroneckerApproxRecurrence.lean`
strengthens the corpus Kronecker theorem to arbitrarily large times, and
`formal/GaloisForLFunctions/RHTower/Hedenmalm/HedenmalmPrimeFrameObstruction.lean` applies it.

| # | statement | Lean declaration |
|---|---|---|
| — | **Kronecker recurrence at arbitrarily large times** | `GaloisForLFunctions.kronecker_approx_atTop` |
| `(24)` | the sine is dominated by the character defect | `abs_sin_le_norm_expChar_sub_one`, `sq_frameSymbol_le` |
| `(25)` | **for every finite prime set the diagonal sum of squares drops below any tolerance at arbitrarily large times** | `exists_gt_sum_sq_frameSymbol_lt` |
| `(9)` | the zero set `2 pi k / log n` of `a_n`: nonvanishing and square-summable reciprocals | `centeredMultiplierZero`, `centeredMultiplierZero_ne_zero`, `summable_inv_sq_centeredMultiplierZero`, `centeredZero`, `summable_inv_sq_centeredZero` |
| `(13)` | **the genus-one canonical product over those zeros exists**, is entire, and vanishes only there (first input to the conormal generation clause) | `centeredCanonicalProduct`, `hasProdLocallyUniformlyOn_centeredCanonicalProduct`, `analyticOnNhd_centeredCanonicalProduct`, `centeredCanonicalProduct_ne_zero` |
| `(9)`,`(13)` | **the two divisors agree off the origin**: `a_n(z) = 0` iff `z` is one of the prescribed zeros | `centeredMultiplier_eq_zero_iff_mem_zeros` |
| `(9)` | the derivative of `a_n` off the origin (input to simplicity of the zeros) | `hasDerivAt_centeredMultiplier` |
| `(24)` | the pointwise ceiling `b_p(t)^2 <= 4/p` | `sq_rpow_neg_half`, `sq_frameSymbol_le_four_div`, `summable_weighted_frameSymbol` |
| `(26)`,`(27)` | **the summably weighted all-prime diagonal sum drops below any tolerance at arbitrarily large times** | `exists_gt_tsum_weighted_frameSymbol_lt` |

**Positive-kernel self-adjoint channels.**  `formal/GaloisForLFunctions/RHTower/Hedenmalm/HedenmalmThetaPrimeChannels.lean`
(namespace `RHTower.HedenmalmThetaSource`).

| # | statement | Lean declaration |
|---|---|---|
| `(6)` | the centered window is a positive even kernel with exponential envelope | `centeredWindow_eq_cdf`, `continuous_centeredWindow`, `centeredWindow_nonneg`, `centeredWindow_le_exp` |
| `(6)` | **it is integrable**, so it is an honest convolution kernel | `integrable_centeredWindow` |
| `(7)` | its real Fourier symbol, and the closed form `hat c_n = a_n Xi_C` | `channelSymbol`, `channelSymbol_eq_integral`, `measurable_channelSymbol` |
| `(8)` | **the symbol is real** (kernel real and even) | `conj_channelSymbol` |
| — | the symbol is bounded by the total mass of the kernel | `norm_channelSymbol_le` |
| `(17)` | **the two bounded self-adjoint prime channels** | `channelOperator`, `channelOperator_inner` |
| `(17)` | the common real symbol zero set is exactly the real `Xi` divisor | `channelSymbol_eq_zero_iff` |

**The conormal generation statement `(13)`--`(14)` and the analytic cokernel `(17)` are proved.**
Three new modules carry them.

`formal/GaloisForLFunctions/HTGeometry/EntireInterpolation.lean`:

| # | statement | Lean declaration |
|---|---|---|
| — | **Mittag-Leffler interpolation**: arbitrary values may be prescribed at the simple zeros of an entire function when they are nonzero and escape to infinity | `exists_entire_interpolation` |

`formal/GaloisForLFunctions/HTGeometry/EntireBezout.lean`:

| # | statement | Lean declaration |
|---|---|---|
| — | **analytic division**: an entire function whose analytic order dominates that of a nonzero entire `g` everywhere is an entire multiple of `g` | `exists_entire_quotient` |
| `(13)` | **Wedderburn's lemma**: two entire functions without a common zero, the zeros of the first simple, nonzero and escaping, generate the unit ideal | `exists_entire_bezout` |

`formal/GaloisForLFunctions/RHTower/Hedenmalm/HedenmalmTwoPrimeBezout.lean`
(namespace `RHTower.HedenmalmThetaSource`):

| # | statement | Lean declaration |
|---|---|---|
| `(7)` | the entire representative of `a_n`, with the removable singularity at the origin filled in, and its value `n^{-1/2} log n` there | `centeredMultiplierE`, `differentiable_centeredMultiplierE`, `centeredMultiplierE_eq`, `centeredMultiplierE_at_zero` |
| `(9)` | its zero set is exactly the nonzero part of the progression `2 pi k / log n` | `centeredMultiplierE_eq_zero_iff` |
| `(9)` | those zeros are simple, injectively indexed, and escape to infinity | `deriv_centeredMultiplierE_ne_zero`, `injective_centeredZero`, `tendsto_norm_centeredZero_cofinite` |
| `(8)` | **the multiplier is even and real**, `a_n(-z) = a_n(z)` and `a_n(conj z) = conj a_n(z)` | `centeredMultiplierE_neg`, `centeredMultiplierE_conj` |
| `(13)` | **the two-prime Bezout identity** `b_2 a_2 + b_3 a_3 = 1` with `b_2`, `b_3` entire | `exists_two_prime_bezout` |

`formal/GaloisForLFunctions/RHTower/Hedenmalm/HedenmalmTwoPrimeIdeal.lean`
(namespace `RHTower.HedenmalmThetaSource`):

| # | statement | Lean declaration |
|---|---|---|
| `(13)` | the Bezout identity inside the entire-function algebra | `exists_entire_two_prime_bezout` |
| — | **entire functions have no zero divisors** (the identity theorem) | `deningerEntire_cancel`, `deningerEntireXi_cancel` |
| `(11)` | **the conormal module of a principal divisor**, `I/I^2 ≃ R/(g)` | `GaloisForLFunctions.HTGeometry.principalCotangentEquiv` |
| `(11)` | **the Xi conormal module is the Xi comparison quotient** | `xiConormalEquiv` |
| `(12)` | **the two prime window classes generate `I/I^2`** | `windowCotangent`, `span_windowCotangent_eq_top` |
| `(14)` | **the two prime windows generate the Xi ideal**, `(hat c_2, hat c_3) = (Xi_C)` | `span_entireCenteredWindow_eq_xiIdeal` |
| `(17)` | the range of the two-prime row map is the Xi ideal | `windowRow`, `range_windowRow` |
| `(17)` | **the analytic cokernel is `O(C)/(Xi_C)`** | `twoPrimeCokernelEquiv` |

The interpolation series is the classical one, `sum_i c_i (z / w_i)^{N_i} dslope F w_i z / F'(w_i)`,
with the exponents `N_i` chosen index by index so that the `i`-th term is dominated by a summable
majorant on the disc of radius `‖w_i‖ / 2`; on a fixed disc that domination holds for all but
finitely many `i`.  Division uses the meromorphic normal form: the pointwise quotient has
non-negative divisor, hence its normal form is analytic, and the factorization propagates from a
punctured neighbourhood of a non-zero of the divisor by the identity theorem.

**All three frame obstructions are formalized**: `(22)`/`(23)` (no bounded Bezout pair on the real
axis), `(25)` (the finite-prime Kronecker obstruction) and `(26)`/`(27)` (the summably weighted
all-prime form).  The last one is the head/tail split: a finite head chosen by
`tendsto_tsum_compl_atTop_zero` on `sum of 4 omega_p / p`, then the finite theorem applied to the
head with tolerance `delta / 2` and weight ceiling `sum over P of omega_p`.

## Gates

- [x] exact rank-one anomaly integrated to a theta interval
- [x] Lean interval transgression `(4)` and multiplicative cocycle law `(5a)`
- [x] centered positive even prime-window source constructed
- [x] exact `a_n XiC` factorization proved
- [x] exact multiplicative anomaly cocycle proved
- [x] prime-2/prime-3 no-common-zero theorem proved
- [x] Lean prime-2/prime-3 no-common-zero theorem
- [x] global analytic conormal generation proved
- [x] arbitrary multiplicity retained by first nonzero normal jets
- [x] two bounded self-adjoint source channels constructed
- [x] ordinary-`L2` spectral defect shown to vanish
- [x] essential compact-boundary symbol identified
- [x] bounded-corona/high-frequency frame obstruction proved
- [x] arbitrary finite-prime frame obstruction proved
- [x] summably weighted all-prime diagonal frame obstruction proved
- [x] preliminary corpus noncollision audit
- [x] preliminary external noncollision search
- [x] Lean conormal generation, Bezout identity and analytic cokernel
- [ ] independent specialist literature audit
- [ ] closed strict boundary realization of `(19)`
- [ ] positive self-adjoint divisor spectrum
- [ ] RH
