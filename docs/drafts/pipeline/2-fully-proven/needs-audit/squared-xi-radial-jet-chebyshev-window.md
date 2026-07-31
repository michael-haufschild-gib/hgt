# Squared-Xi radial jets are completed Chebyshev windows

- **ID:** squared-xi-radial-jet-chebyshev-window
- **Stage:** 2-fully-proven / needs-audit
- **Type:** THEOREM (paper) / cancellation-preserving moving-source reduction
- **Scientific status:** `[PROVED HERE] [NOVELTY UNAUDITED]`
  `[EQUATIONS (2)-(6), THE MODAL SCALE (8)-(10), THE CONCENTRATION (11) AND THE WINDOW (12)`
  `FORMALIZED, AXIOMS CLEAN; ONLY THE OPEN CORE REMAINS]`
- **Parents:** `squared-xi-radial-jet-reverse-bessel-source-alignment.md`; `reverse-bessel-fixed-frequency-blindness.md`
- **Statement:** The polar jet and the sign-aligned von Mangoldt jet are the Lebesgue and Chebyshev--Stieltjes integrals of one positive reverse-Bessel kernel; at fixed Euler base point, its normalized polar mass concentrates at `log x = n/(s(s-1))`.

## Exact pole--prime identity

Fix real `s>1`, put `w=s-1/2`, `a=s-1`, and let

```text
B_n(z)=sum_(j=0)^n b_(n,j) z^j,
f_(n,s)(x)=x^(-s) B_n(w log x),    x>=1.                (1)
```

Let

```text
psi(x)=sum_(m<=x) Lambda(m)
```

be the Chebyshev function.  Then

```text
sum_(j=0)^n b_(n,j) j! w^j/a^(j+1)
  = integral_1^infinity f_(n,s)(x) dx,                 (2)

sum_(m>=2) Lambda(m) m^(-s) B_n(w log m)
  = integral_[1,infinity) f_(n,s)(x) d psi(x).         (3)
```

Consequently the alternating radial jet of
`1/(s-1)+zeta'(s)/zeta(s)` is exactly

```text
integral_[1,infinity) f_(n,s)(x) d(x-psi(x)).          (4)
```

No estimate and no separation of divergent boundary pieces occurs in `(4)`.

### Proof `[PROVED HERE]`

For `(2)`, substitute `x=exp(t)`:

```text
integral_1^infinity x^(-s)B_n(w log x) dx
  = integral_0^infinity exp(-a t)B_n(wt) dt
  = sum_(j=0)^n b_(n,j)w^j integral_0^infinity
      exp(-a t)t^j dt
  = sum_(j=0)^n b_(n,j)j!w^j/a^(j+1).
```

Equation `(3)` is the defining Stieltjes integral of the step function
`psi`, since its jump at the integer `m` is `Lambda(m)`.  Subtraction proves
`(4)`.  Absolute Euler convergence justifies every finite-polynomial
interchange.

## Full completed jet

Let

```text
C_n(s)=sum_(j=0)^n (-1)^j b_(n,j)w^j
  * d^j/ds^j [1/s-log(pi)/2+(1/2)digamma(s/2)].         (5)
```

The completed squared-Xi source polynomial is therefore

```text
Q_n(w)
  = C_n(s)
    + integral_[1,infinity) f_(n,s)(x) d(x-psi(x)).    (6)
```

Equation `(6)` is the exact source object whose strict negativity would
disprove RH.  The first term is the trivial-zero/archimedean correction; the
second is one smoothed prime-counting discrepancy.

## Exact modal scale and concentration

Normalize the positive polar density in logarithmic coordinates:

```text
d nu_(n,s)(t)
  = exp(-a t)B_n(wt)dt
    / integral_0^infinity exp(-a u)B_n(wu)du.           (7)
```

Expanding `B_n`, this is a finite mixture of Gamma laws with shape `j+1`
and rate `a`.  The unnormalized mixture weights are

```text
c_(n,j)=b_(n,j)j!(w/a)^j,                               (8)
```

and their adjacent ratio is exactly

```text
c_(n,j+1)/c_(n,j)
  = 2(n-j)w/((2n-j)a).                                  (9)
```

Since `w=a+1/2` and `s=w+1/2`, ratio `(9)` is greater than one exactly when

```text
j < n/s.                                                (10)
```

Thus the Gamma-mixture index is unimodal at the integer(s) adjacent to
`n/s`.

More strongly, if `T_n` has law `nu_(n,s)`, then

```text
T_n/n -> 1/(s(s-1))                                    (11)
```

in probability as `n->infinity` with `s` fixed.

To prove `(11)`, use `(9)`: outside any fixed relative neighborhood of
`j=n/s`, the adjacent ratios are uniformly separated from one, so products
of the ratios make both mixture tails exponentially smaller than the modal
weight.  Hence `J_n/n->1/s` for the random mixture index.  Conditional on
`J_n=j`, the Gamma law has mean `(j+1)/a` and variance `(j+1)/a^2`.
Chebyshev's inequality, uniformly for `0<=j<=n`, then gives
`T_n/n-J_n/(an)->0` in probability.  Since `a=s-1`, `(11)` follows.

In the original prime variable, the polar cancellation window is therefore

```text
x = exp(n/(s(s-1)) + o(n)).                             (12)
```

## RH-false route consequence

The fixed-frequency theorem showed that no finite Euler prefix controls the
growing-order limit.  Equation `(12)` identifies where the mass goes.  A
growing-order disproof must prove a signed asymptotic for the completed
Chebyshev discrepancy `(6)` on this exponential window.  Pointwise prime
bounds, least-prime dominance, and estimates that separate the zeta pole
from the prime sum cannot decide it.

`[OPEN CORE]` Derive a one-sided asymptotic for `(6)` that retains the
archimedean correction and is strict in the negative direction for some
order/base-point sequence.  An asymptotic for the Lebesgue model alone merely
reconstructs the cancelled pole.

## Gates

- [x] exact common-kernel pole--prime identity
- [x] exact Chebyshev--Stieltjes discrepancy
- [x] full completed radial source formula
- [x] exact mixture ratio and modal index
- [x] logarithmic-window concentration
- [x] formalize the Lebesgue side `(2)` and the exact modal scale `(8)`–`(10)`
- [x] formalize the Chebyshev--Stieltjes side `(3)`/`(4)`
- [x] formalize the concentration `(11)`
- [ ] completed signed asymptotic on the window `(12)`
- [ ] strict negative source witness

## Lean status

`formal/GaloisForLFunctions/RHTower/SquaredXiChebyshevWindow.lean`, axioms
`[propext, Classical.choice, Quot.sound]`.

- `exp_image_Ioi_zero`, `integral_Ioi_one_comp_exp` — the substitution `x = exp t` as a measure
  statement, `∫_{x>1} g = ∫_{t>0} e^t g(e^t)`, from mathlib's
  `integral_image_eq_integral_abs_deriv_smul`.
- `integrableOn_pow_mul_exp_neg_mul_Ioi`, `integral_pow_mul_exp_neg_mul_Ioi` — the scaled Gamma
  integral `∫_0^∞ t^j e^{-r t} dt = j!/r^(j+1)`, with its integrability, obtained from
  `Real.GammaIntegral_convergent` and `Real.integral_rpow_mul_exp_neg_mul_Ioi` by rate scaling.
- `radialBesselKernel` — the kernel `f_{n,s} x = x^(-s) B_n((s-1/2) log x)`.
- **`integral_radialBesselKernel`** — equation `(2)`:
  `∫_1^∞ f_{n,s} = sum_j b_{n,j} j! w^j / a^(j+1)`.  The substitution turns the kernel into the
  finite Gamma mixture, and the finite sum passes through the integral by termwise integrability.
- `radialMixtureWeight` — equation `(8)`, `c_{n,j} = b_{n,j} j! (w/a)^j`, with positivity on the
  triangular range.
- `squaredRadialJetWeight_adjacent` — the exact factorial recurrence
  `(j+1) b_{n,j+1} (2n-j) = 2(n-j) b_{n,j}`, from the corpus reverse-Bessel closed form.
- **`radialMixtureWeight_adjacent`** — equation `(9)` in cleared form:
  `c_{n,j+1} (2n-j) a = c_{n,j} 2(n-j) w`.
- **`radialMixtureWeight_lt_succ_iff`** — equation `(10)`: `c_{n,j} < c_{n,j+1}` exactly when
  `j s < n`, so the Gamma-mixture index is unimodal at the integers adjacent to `n/s`.

### `GaloisForLFunctions/RHTower/ChebyshevStieltjesMeasure.lean`

The Stieltjes layer for `psi`, which the corpus did not have (`chebyshevPsi` existed only as a
function of a natural argument).

- `chebyshevPsiReal`, `chebyshevPsiReal_mono`, `chebyshevPsiReal_rightContinuous`,
  `chebyshevPsiStieltjes` — Chebyshev's `psi` as a real-variable monotone right-continuous step
  function, hence a `StieltjesFunction`.  Right-continuity is the observation that `psi` is
  constant on `[x, floor x + 1)`, which also covers `x < 0` since `Nat.floor` is `0` there.
- `vonMangoldtAtomMeasure` — the atomic measure with mass `Lambda m` at each natural `m`.
- `vonMangoldtAtomMeasure_Ioc` — its value on `Ioc a b` is `psi (floor b) - psi (floor a)`.  The
  only subtlety is `m = 0`, which the `Ioc (floor a) (floor b)` index set omits when `a < 0`; that
  term vanishes because `Lambda 0 = 0`.
- **`chebyshevPsiStieltjes_measure_eq`** — `d psi = sum_m Lambda m * delta_m`, by
  `Measure.ext_of_Ioc`.
- **`integral_chebyshevPsiStieltjes`** — every Chebyshev--Stieltjes integral is the von Mangoldt
  series of the integrand at the naturals.
- `integrable_chebyshevPsiStieltjes`, `vonMangoldt_mul_norm_radialBesselKernel`,
  `summable_vonMangoldt_mul_norm_radialBesselKernel` — the integrability side: the von Mangoldt
  weight of the radial kernel is a finite combination of the log-weighted von Mangoldt series of
  `BoseZipfCumulants`, hence summable above the Euler abscissa.
- **`integral_radialBesselKernel_chebyshev`** — equation `(3)`:
  `∫ f_{n,s} d psi = sum_m Lambda m f_{n,s}(m)`, which is the card's
  `sum_{m>=2} Lambda m m^(-s) B_n(w log m)` since `Lambda 0 = Lambda 1 = 0`.
- **`integral_radialBesselKernel_discrepancy`** — equation `(4)`: the completed radial discrepancy
  `∫ f d(x - psi)` with both sides in closed form.

### `GaloisForLFunctions/RHTower/GammaMixtureConcentration.lean`

The two mechanisms of the concentration `(11)`, both unconditional.

- `integral_gammaLeg`, `integrableOn_sq_sub_mul_gammaLeg` — the unnormalized Gamma leg
  `t^j exp(-a t)` on the positive ray and its integrability against a quadratic weight.
- **`integral_sq_sub_mean_gammaLeg`** — the exact second moment about the mean,
  `∫_0^∞ (t - (j+1)/a)^2 t^j exp(-a t) dt = ((j+1)/a^2) * (j!/a^(j+1))`: the leg has mean `(j+1)/a`
  and variance `(j+1)/a^2` times its mass.
- **`gammaLeg_chebyshev`** — Chebyshev's inequality for a leg: any measurable subset of the positive
  ray at distance at least `R` from the mean carries at most `(j+1)/(a^2 R^2)` of the leg mass.
  This is the card's "Chebyshev's inequality, uniformly for `0 <= j <= n`" step; the bound depends
  on `j` only through `j+1`, so it is uniform once `j <= n`.
- `radialMixtureRatio`, `radialMixtureRatio_lt_one` — the fixed relative ratio
  `r theta = 2(1-theta) w / ((2-theta) a)`, strictly below one exactly when `theta s > 1`.
- **`radialMixtureWeight_succ_le`** — beyond `theta n` the adjacent mixture ratio never exceeds
  `r theta`.  The inequality is *equivalent* to `theta n <= j`, because the ratio depends on `j`
  only through `j/n`.
- **`radialMixtureWeight_le_pow`** — the resulting geometric decay
  `c_{n, j0+k} <= r theta ^ k * c_{n, j0}` above a fixed relative index.
- `radialMixtureRatio_one_lt`, **`radialMixtureWeight_le_succ`**,
  **`radialMixtureWeight_pow_le`** — the mirror statements below the modal ratio: for
  `theta s < 1` the ratio exceeds one and the weights grow geometrically up to `theta n`.
- `geomSum_range_le`, **`sum_Icc_radialMixtureWeight_le`**,
  **`sum_range_radialMixtureWeight_le`** — both tail sums are bounded by a fixed multiple of the
  boundary weight: `sum_{j >= j0} c_j <= c_{j0}/(1 - r theta+)` above, and
  `sum_{j <= j1} c_j <= c_{j1}/(1 - 1/r theta-)` below.
- `radialMixtureWeight_nonneg`, `radialMixtureWeight_le_total`,
  **`sum_Icc_radialMixtureWeight_le_total`**, **`sum_range_radialMixtureWeight_le_total`** — the
  modal-weight comparison: against a comparison index `jm` strictly on the far side of the modal
  ratio, each tail is at most `C * r ^ |j - jm|` times the *total* mixture mass, with `C` and `r`
  depending only on `s` and the relative offset.  This is the whole `n`-uniform content of the
  index concentration.
- `tendsto_pow_of_tendsto_atTop`, `tendsto_ceil_sub_ceil_atTop`, `tendsto_floor_sub_floor_atTop`,
  **`tendsto_upper_tail_fraction`**, **`tendsto_lower_tail_fraction`** — the limit: for relative
  cutoffs strictly on either side of the modal ratio `1/s`, the mixture mass beyond them is a
  vanishing fraction of the total.  With `theta' < theta` the index gap
  `ceil (theta n) - ceil (theta' n)` grows linearly, so the geometric factor vanishes; the
  fractions are then squeezed to zero.  **The index concentration of `(11)` is complete.**
- `radialMixtureDensity`, `radialMixtureDensity_nonneg`, `integrableOn_radialMixtureLeg` — the
  unnormalized radial density `e^{-a t} B_n(w t)` of equation `(7)`, as a finite sum of Gamma legs.
- **`integral_radialMixtureDensity_eq`** — the leg decomposition: on any measurable subset of the
  positive ray the mixture integral is the finite sum of the leg integrals.
- **`integral_radialMixtureDensity_Ioi`** — the total mass is `(1/a) * sum_j c_{n,j}`, so the
  normalization of `(7)` is exactly the mixture-weight sum of `(8)`.
- **`integral_radialMixtureLeg_le`** — each leg contributes at most its whole mass `(1/a) c_{n,j}`
  over any subset.  This is the crude bound used on the bad indices.
- `radialMixtureLeg_mass`, **`integral_radialMixtureLeg_good_le`** — a leg whose mean `(j+1)/a`
  stays at distance `R` from the set contributes at most an `(n+1)/(a^2 R^2)` fraction of its own
  mass; this is `gammaLeg_chebyshev` transported to the mixture normalization.
- **`integral_radialMixtureDensity_le_blocks`** — the block split: cutting the leg sum at `j1` and
  `j0`, the two outer blocks are bounded by their whole mass and the middle block by Chebyshev,
  giving
  `∫_S density <= (1/a)(lower tail + upper tail) + ((n+1)/(a^2 R^2)) * (total mass)`.
  **This is the last mathematical step of `(11)`.**

- `radialBadSet`, `measurableSet_radialBadSet`, `radialBadSet_subset`, `radialBadSet_mono` — the
  bad set `{t > 0 : |t - L n| >= eps n}` at relative scale `eps` around the modal ray
  `L = 1/(s(s-1))`; it shrinks as `eps` grows.
- **`radialBadSet_mass_le`** — the `eps`-instantiation of the block split, with
  `theta± = 1/s ± eps a/4`, `j1 = floor(theta- n)`, `j0 = ceil(theta+ n)` and `R = eps n / 2`:
  a good index keeps the leg mean `(j+1)/a` within `eps n/2` of `L n`, so the middle block is
  controlled by Chebyshev and the two outer blocks by their whole mass.
- `tendsto_chebyshevTerm` — the Chebyshev term `(n+1)/(a^2 (eps n/2)^2)` is `O(1/n)` and vanishes.
- **`tendsto_radialBadSet_fraction`** — equation `(11)` at small relative scale: the bad mass is a
  vanishing fraction of the total.  The three pieces of `radialBadSet_mass_le` are sent to zero by
  the two tail theorems (at the intermediate cutoffs `1/s ± eps a/8`, strictly inside the outer
  ones) and by `tendsto_chebyshevTerm`, and the fraction is squeezed between zero and their sum.
- `integrableOn_radialMixtureDensity`, **`tendsto_radialBadSet_fraction_of_pos`** — equation `(11)`
  **for every** `eps > 0`: the bad set is monotone in `eps`, so the small-scale statement transfers
  to all scales.  **The concentration `(11)` is complete and unconditional.**

### `GaloisForLFunctions/RHTower/CompletedChebyshevJet.lean`

Equation `(4)` in the form the card states it: as the alternating radial jet of the pole-corrected
logarithmic derivative, not merely as a difference of two integrals in closed form.

- `radialJet n s g = sum_j b_{n,j} (s-1/2)^j (-1)^j (d/ds)^j g` — the alternating reverse-Bessel
  radial jet of a real function at the base point `s`; `radialJet_add` splits it over a sum of two
  functions smooth at `s`.
- **`iteratedDeriv_poleTerm`** — the `j`-fold derivative of the simple pole,
  `(d/ds)^j (s-1)^{-1} = (-1)^j j!/(s-1)^{j+1}`, by induction through the eventual equality on the
  ray.
- **`radialJet_poleTerm`** — the polar half of the jet is exactly the closed form of the Lebesgue
  integral `(2)`: the two alternating signs cancel.
- `realZetaLogDeriv_eq`, **`contDiffAt_realZetaLogDeriv`** — `zeta'/zeta` is the real trace of a
  function holomorphic on `Re z > 1` (where `zeta` has no zero and `deriv zeta` is analytic), hence
  real-smooth at every order on the ray.  This is what licenses splitting the jet of the sum.
- `contDiffAt_poleTerm` — the polar term is smooth at every `s > 1`.
- **`iteratedDeriv_realZetaLogDeriv`** — `(d/ds)^j (zeta'/zeta) = (-1)^{j+1} sum_m Lambda m
  (log m)^j m^{-s}`: the logarithmic derivative is one derivative of `log zeta`, so the corpus's
  termwise-differentiated Dirichlet series supplies every order.
- **`sum_radialJetWeight_vonMangoldtLogSeries`** — the exchange of the finite radial sum with the
  Dirichlet sum, valid termwise because each log-weighted von Mangoldt series is summable on the
  ray; the result is the von Mangoldt series of the radial reverse-Bessel kernel.
- **`radialJet_logDeriv`** — the arithmetic half of the jet is minus the Chebyshev--Stieltjes
  integral.
- **`radialJet_poleCorrectedLogDeriv`** — **equation `(4)`**:
  `radialJet n s (1/(s-1) + zeta'/zeta) = ∫_1^∞ f_{n,s} dx - ∫_[1,∞) f_{n,s} d psi`.
  No estimate and no separation of divergent boundary pieces occurs.

### `GaloisForLFunctions/RHTower/CompletedRadialSourcePolynomial.lean`

Equations `(5)` and `(6)`: the completed source polynomial as archimedean correction plus one
smoothed prime-counting discrepancy.

- `xiRayLogDeriv`, `archimedeanRayLogDeriv` — the real traces on the Euler ray of `xi'/xi` and of
  the archimedean correction `1/s - (log pi)/2 + (1/2) psi (s/2)` of equation `(5)`.
- **`xiRayLogDeriv_split`** — **equation `(5)`**: on the ray, `xi'/xi` is the archimedean
  correction plus `1/(s-1) + zeta'/zeta`.  This is the real trace of the corpus's complex
  logarithmic-derivative weld.
- **`contDiffAt_xiRayLogDeriv`** — `xi'/xi` is real-smooth at every order on the ray, because `xi`
  is entire and does not vanish for `Re z > 1`, so `xi'/xi` is holomorphic there and its real trace
  transfers.  `contDiffAt_archimedeanRayLogDeriv` follows by subtraction; together they license the
  splitting of the jet.
- **`radialJet_xiRayLogDeriv`** — **equation `(6)`**:
  `radialJet n s (xi'/xi) = C_n s + (∫_1^∞ f_{n,s} dx - ∫_[1,∞) f_{n,s} d psi)`.
  The exact source object of the card, machine-checked as the sum of the archimedean jet and one
  smoothed prime-counting discrepancy.

The remaining gates are the card's own open core: the completed signed asymptotic on the window
`(12)` and the strict negative source witness.

## Log

- 2026-07-31 — Lebesgue side and modal scale formalized.  `(2)` needed only the exponential
  substitution plus the scaled Gamma integral; mathlib has both ingredients but not the scaled
  integral itself, which was built here.  `(3)`/`(4)` needed the Stieltjes layer for `psi`, built
  the same day: the whole content is that `psi` is a right-continuous step function whose jump at
  `m` is `Lambda m`, so its Lebesgue--Stieltjes measure is the atomic measure `sum Lambda m delta_m`
  and every Stieltjes integral collapses to the von Mangoldt series.
- 2026-07-31 — Both mechanisms of `(11)` formalized.  The conditional step is an exact
  second-moment computation, which the scaled Gamma integral built for `(2)` makes immediate, plus
  Chebyshev as a pointwise comparison against the indicator.  The index step is sharper than the
  card's sketch: because the adjacent ratio `2(n-j)w/((2n-j)a)` depends on `j` only through `j/n`,
  the bound `c_{j+1} <= r(theta) c_j` above `theta n` is not merely uniform in `n` but *equivalent*
  to `theta n <= j`, so the geometric decay needs no asymptotics at all.  Both tails are now
  bounded by a fixed multiple of the boundary weight, on each side of the modal ratio; what remains
  is the comparison of those boundary weights with a modal weight and the limit in `n`.
- 2026-07-31 — Modal-weight comparison formalized on both sides: each index tail is at most a
  geometric fraction of the *total* mixture mass, with constants free of `n`.  Everything in `(11)`
  that is uniform in `n` is now machine-checked; the residue is the ceiling/floor bookkeeping and
  the limit.
- 2026-07-31 — Index concentration of `(11)` completed.  Both tail fractions tend to zero, for any
  relative cutoffs strictly bracketing the modal ratio `1/s`.  The only step left in `(11)` is the
  passage from the index law to the radial variable, which needs the normalized mixture measure and
  the leg decomposition of its integral.
- 2026-07-31 — The radial mixture density, its leg decomposition, its total mass in terms of the
  mixture weights, and the crude per-leg bound are formalized.  Every ingredient of `(11)` is now
  in the corpus; what is left is the block split of the leg sum and the limit.
- 2026-07-31 — Block split proved.  Every mathematical step of `(11)` is now machine-checked: the
  mixture mass on a far set is bounded by the two index tails plus a Chebyshev term of relative
  size `(n+1)/(a^2 R^2)`.  What remains is the `eps`-instantiation, which is arithmetic.  `(9)`/`(10)` are pure algebra on the corpus's
  reverse-Bessel closed form `b(n,j) = (2n-j)!/(2^(n-j)(n-j)! j!)`: the adjacent ratio reduces to
  `(j+1) b_{n,j+1}(2n-j) = 2(n-j) b_{n,j}`, and the threshold `j < n/s` follows because
  `(2n-j)(s-1) < 2(n-j)(s-1/2)` is equivalent to `j s < n`.
- 2026-07-31 — Concentration `(11)` closed.  The `eps`-instantiation is exactly the block split at
  `theta± = 1/s ± eps a/4` with radius `eps n/2`; the two tail theorems are then applied at the
  *intermediate* cutoffs `1/s ± eps a/8`, which sit strictly inside the outer ones, so the index
  gaps grow linearly and the geometric factors vanish.  The arbitrary-`eps` form follows from
  monotonicity of the bad set in `eps` with no further analysis.  The normalized radial mixture
  therefore concentrates unconditionally at the modal ray `L = 1/(s(s-1))`; only the card's two
  open-core gates remain.
- 2026-07-31 — Window `(12)` and the jet form of `(4)` formalized.  `(12)` is `(11)` transported by
  `x = exp t`: the radial bad set is exactly the exponential preimage of the complement of the
  window `exp((L±eps) n)`, so no new analysis is needed.  `(4)` had been machine-checked only as a
  difference of two integrals in closed form; it is now proved in the form the card states, as the
  alternating radial jet of `1/(s-1) + zeta'/zeta`.  The two halves are the `j`-fold derivative of
  the simple pole and the termwise-differentiated von Mangoldt series, and the jet of the sum
  splits because `zeta'/zeta` is the real trace of a function holomorphic on `Re z > 1`.  Every
  proved statement of this card is now formalized unconditionally with clean axioms; the two
  remaining gates are the declared open core.
- 2026-07-31 — Equations `(5)` and `(6)` formalized.  The corpus already carried the complex
  logarithmic-derivative weld `xi'/xi = 1/s + 1/(s-1) - (log pi)/2 + (1/2) psi (s/2) + zeta'/zeta`
  on the half plane of absolute convergence, so `(5)` is its real trace on the ray and needed no
  new analysis.  The only genuinely new input was smoothness: `xi'/xi` is real-smooth at every
  order because `xi` is entire and zero-free to the right of `Re z = 1`, and the archimedean
  correction is then the difference of two smooth functions.  With that, `(6)` is the jet of `(5)`
  plus `(4)`.  Every proved equation of the card, `(2)` through `(12)`, is now formalized
  unconditionally with clean axioms.
