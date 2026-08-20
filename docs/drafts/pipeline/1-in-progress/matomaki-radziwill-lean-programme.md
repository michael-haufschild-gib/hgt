# Matomäki–Radziwiłł in Lean — the shared Route-E analytic gate

> **STATUS: OBJECTIVE MET (2026-08-18).**  Matomäki–Radziwiłł is Lean-proved and
> unconditional; see
> `../3-formalized/new_scientific_knowledge/matomaki-radziwill-moebius-short-interval-mean-square.md`.
> What remains below is the *scoping* of a separate follow-on programme (the integer-start
> normalisation needed by the two reciprocal-marker cards), not of this one.

- **ID:** `MR-LEAN-PROGRAMME-001`
- **Stage:** 1-in-progress
- **Type:** FORMALIZATION PROGRAMME (infrastructure for several stage-2 cards)
- **RH used:** no
- **Computation used:** no

## Why this card exists

Five stage-2 cards are blocked on exactly two published analytic theorems, neither in mathlib nor in
the vendored `PNTPlus`:

| Card | Blocking input |
|---|---|
| `2-fully-proven/new_scientific_knowledge/route-e-coprime-square-root-mobius-product-sign-law.md` | Matomäki–Radziwiłł 2016, Theorem 1 (for `μ`) |
| `2-fully-proven/new_scientific_knowledge/route-e-growing-reciprocal-marker-low-breadth-transport.md` | same |
| `2-fully-proven/new_scientific_knowledge/route-e-reciprocal-marker-mobius-hall-law.md` | same |
| `2-fully-proven/route-e-cofactor-amplified-e3-token-supply.md` | Matomäki–Teräväinen 2022, Theorem 1.2 (all-interval `E₃`) |
| `2-fully-proven/route-e-forbidden-support-e3-stability.md` | same |

Every other step of all five cards is already an unconditional Lean theorem of this corpus.  This
card tracks the construction of the missing analytic layer.  It is infrastructure, not new
scientific knowledge: the mathematics is published, and the work is the formalisation.

## The exact target

For `route-e-coprime-square-root-mobius-product-sign-law` the corpus has already reduced the card's
whole statement to one hypothesis, `RHTower.Sieve.AveragedMeanSquare` at `μ` — equivalently
(`averagedMeanSquare_of_maximal`, `maximalWindowMeanSquare_of_firstMoment`) the maximal-window form.
In classical notation, with `X = √x` and window length `h`:

```text
(1/X) ∑_{X/2 ≤ y ≤ X} | ∑_{y < n ≤ y+h} μ(n) |²  =  o(h²)      for every h = h(X) → ∞.
```

That is Matomäki–Radziwiłł Theorem 1 for the Möbius function.  Nothing weaker suffices: the card
quantifies over *every* window law with `h/log log(3x) → ∞`, and the corpus's own unconditional
range (`route_e_sign_density_of_mertens_rate`) is governed by the error term in the prime number
theorem, hence never reaches below `h ≈ X·exp(-c(log X)^{3/5})`.

## The route being formalised

Soundararajan's Bourbaki exposé 1119 (arXiv:1606.08021) gives a staged proof, each stage widening
the admissible range of `h`.  The stages are the milestones of this card.

| Milestone | Range of `h` | New ingredients |
|---|---|---|
| A (exposé §3) | `h ≥ exp((log X)^{0.95})` | Lemmas 2.1, 2.3, 2.4 + Turán–Kubilius |
| B (exposé §4) | `h ≥ exp(10(log log X)^{10/9})` | + Lemmas 2.5, 2.6 (large values, Halász–Montgomery) |
| C (exposé §5) | `h > exp((log log log X)²)` | + the high-moment trick on the exceptional set |
| D (MR 2016 §§4–7) | every `h → ∞` | the full ladder of prime ranges `P^{(0)},…,P^{(L)},Q` |

Only milestone D closes the three `route-e-*` cards; A–C are strict intermediate advances over the
corpus's current unconditional range and are worth banking separately.

### The lemmas, and what the corpus already owns

- **Lemma 2.1 (Plancherel).** `∫_0^∞ |∑_{xe^{-1/T}<n≤xe^{1/T}} a(n)|² dx/x = (2/π)∫ |A(y)|² (sin(y/T)/y)² dy.`
  **DONE** — see "Lean progress" below.
- **Lemma 2.2 (multiplicative → additive windows).**  For `a` supported on `[c₁X, c₂X]` and
  `1 ≤ h ≤ c₁X/10`,
  `∫_0^∞|∑_{x<n≤x+h}a(n)|²dx ≪ (c₂²/c₁)X∫|A(y)|² min(h²/(c₁²X²), 1/y²) dy`.
  **NOT NEEDED for these cards** — see "Lemma 2.2 is bypassed" below.
- **Lemma 2.3 (Vinogradov–Korobov twisted sums).** `∑_{n≤x}λ(n)n^{it} ≪ x exp(-log x/(log(x+|t|))^{2/3+δ})`
  and the prime analogue.  **DONE (2026-08-18)** at the Route-T exponent `9/10`:
  `Sieve/VonMangoldtTwistUniformHeight.exists_norm_partialSum_vonMangoldtTwist_routeT_uniform` and
  `Sieve/VonMangoldtTwistPrimeEnvelope.exists_norm_sum_primeTwist_routeT_le`.
- **Lemma 2.4 (mean value theorem).** `∫_{-T}^{T}|∑_{n≤N}a(n)n^{it}|²dt ≪ (T+N)∑|a(n)|²`.
  **CORPUS** — `Sieve/DirichletIntegralBound.integral_normSq_dirPoly_le` and the symmetric form
  `Sieve/LogPolyDirPoly.integral_Icc_normSq_dirPoly_symm_le`.
- **Lemma 2.5 (large values for prime polynomials).** `|E| ≪ (V² log T)^{1+log T/log P}`.
  **DONE (2026-08-18)** — `Sieve/DirichletPowerMeasure.volume_largeValues_pow_symm_le_of_prime_support`,
  the sixth-moment device at a free exponent, with the prime-supported fibre bound `k^k`.
- **Lemma 2.6 (Halász–Montgomery).** `∫_E|∑_{n≤N}a(n)n^{it}|²dt ≪ (N+|E|T^{1/2}log T)∑|a(n)|²`.
  **DONE (2026-08-18)** — `Sieve/DyadicSecondEnvelopeClosed.halaszMontgomery_dyadic_explicit`,
  discrete form on a dyadic block, with explicit constants.
- **Lemma 7.1 (Halász–Montgomery for prime polynomials).** Open; needed only for general `f`, not
  for `μ`.
- **Turán–Kubilius** `∑_{X≤n≤2X}(ω_P(n)-W(P))² ≪ X W(P)`. **CORPUS** — `Sieve/TuranKubilius.lean`
  (uniformity over the moving prime set needs an audit).
- **The rough-integer sieve** `#{n ≤ X : n has no prime factor in [P,Q]} ≪ X/W(P)`. **CORPUS** —
  `Sieve/RoughCountTuran.card_roughSet_le`, `Sieve/RoughCount.card_rough_Ioc_le`,
  `Sieve/SelbergTail.card_rough_Ioc_le_selberg`.

## Lean progress

### Lemma 2.1 landed — `Sieve/LogWindowPlancherel.lean`

The corpus's Gallagher layer (`Sieve/GallagherSplitIntegral.lean`) bounds the mean square of a
logarithmic window sum by `2δ²·∫_{|w|≤W}|F|² + M₂·2/(π²W)`, where `M₂` is a *sup* bound on the
Dirichlet polynomial.  That second term is fatal for short windows: with the natural normalisation
it forces `h ≫ √X`, which is exactly where the corpus's unconditional range currently sits.  The
new module replaces the inequality by the exact identity, and the sup term disappears.

| Item | Declaration |
|---|---|
| the window sum as a sum of constant indicators; it lies in every `L^p` | `logWindowSum_eq_sum_indicator`, `memLp_logWindowSum`, `integrable_logWindowSum` |
| the common spectral factor `K_δ(w) = (e^{2πiwδ}-1)/(2πiw)` | `logWindowKernel` |
| `‖e^{iθ}-1‖ = 2|sin(θ/2)|`, hence `‖K_δ(w)‖ = |sin(πδw)|/(π|w|)` | `norm_exp_ofReal_mul_I_sub_one`, `norm_logWindowKernel`, `normSq_logWindowKernel` |
| the spectral weight is even, and bounded by `δ²` and by `(πw)^{-2}` | `normSq_logWindowKernel_neg`, `normSq_logWindowKernel_le_sq`, `normSq_logWindowKernel_le_inv_sq`, `normSq_logWindowKernel_le_min` |
| the Fourier integral factors: `𝓕 S (w) = K_δ(w)·A(-w)` | `fourier_logWindowSum` (with `integral_exp_mul_indicator_logWindow`, `integrable_exp_mul_indicator_logWindow`) |
| **Lemma 2.1**: `∫_ℝ|S(u)|²du = ∫_ℝ ‖K_δ(w)‖²·|A(w)|²dw` | `integral_normSq_logWindowSum_eq` |
| the spectral density is integrable, and any majorant of it bounds the mean square | `integrable_normSq_logWindowKernel_mul_logPoly`, `integral_normSq_logWindowSum_le_of_majorant` |

Unconditional, umbrella-wired, olean built; `#print axioms` on all capstones gives
`propext`, `Classical.choice`, `Quot.sound` only.

### The discrete interface landed — `Sieve/LogWindowDiscreteTransfer.lean`

Plancherel controls `∫_ℝ|S(u)|²du`; the cards consume a *finite sum* over starting points.  This
module is the bridge, and it is what makes "Lemma 2.2 is bypassed" (below) effective.

| Item | Declaration |
|---|---|
| the integers of a finite set in a real interval number at most its length plus one | `card_filter_mem_Ioc_le` |
| two windows of equal length differ only in their two end intervals, so `‖S(u) - S(u')‖ ≤ M·((e^{u'}-e^{u}+1) + (e^{u'+δ}-e^{u+δ}+1))` | `norm_logWindowSum_sub_le` |
| **the transfer**: for starting points whose intervals `[u_i, u_i+λ)` are pairwise disjoint and on which `S` oscillates by at most `C`, `λ∑_i‖S(u_i)‖² ≤ 2∫_ℝ‖S‖² + 2λC²·#{i}` | `sum_normSq_logWindowSum_le_integral` |

Unconditional, umbrella-wired, olean built, axiom-clean.  Note that `norm_logWindowSum_sub_le`
needs no hypothesis on `δ` or on the sign of `u`: the count bound is uniform.

## Log

- 2026-08-17 — card opened; Lemma 2.1 formalised as an exact identity, replacing the corpus's lossy
  Gallagher inequality.  Two structural findings recorded below: Lemma 2.2 is unnecessary for these
  cards, and the Vinogradov--Korobov zero-free region is a hard prerequisite for every milestone.

## Two structural findings (2026-08-17)

### Lemma 2.2 is bypassed

The exposé needs the Saffari--Vaughan device because Theorem 1.1 is stated for *additive* windows
`[x, x+h]`, while Plancherel is natural for *multiplicative* windows `[xe^{-1/T}, xe^{1/T}]`.  The
three `route-e-*` cards do not need it: the corpus has already reduced them to
`RHTower.Sieve.AveragedMeanSquare`, whose inner sum is

```text
innerFibre x h a  =  { b : x/a ≤ b ≤ (x + h√x)/a }  =  ( y, y(1 + h/√x) ] ,   y = x/a,
```

a multiplicative window whose *ratio* `1 + h/√x` does not depend on the outer variable `a`.  So
Lemma 2.1 applies to the card's own object with `δ = log(1 + h/√x)`, and the only interface still
needed is the passage from the discrete sum over `a ∈ (√x, 2√x]` to the integral over starting
points.  That passage is elementary: the points `u_a = log(x/a)` are separated by `≍ 1/√x`, and on
an interval of length `1/(4√x)` around `u_a` at most one integer enters or leaves each end of the
window, so

```text
∑_a S(u_a)²  ≤  8√x ∫_ℝ S(u)² du  +  8·#{a} ,
```

and `#{a} ≍ √x = o(h²√x)` whenever `h → ∞`.  This removes one full lemma from the programme.

### The Vinogradov--Korobov prerequisite -- CORRECTED 2026-08-17

Lemma 2.3 is used in *every* stage of the exposé (§3 (28)--(29), §4 (38), §5, §7 (56)), always in
the same way: the sum over a dyadic block of primes `P` must exhibit cancellation uniformly for
frequencies `|y| <= X`.  The bound needed is

```text
sum_{p <= P} p^{it}  <<  pi(P)/(1+|t|)  +  P*exp( - log P / (log(P + |t|))^{kappa+delta} ) ,
```

useful exactly when `log P >> (log X)^{kappa+delta}`, where `kappa` is the exponent of the
available zero-free region.  A first reading of the corpus suggested `kappa = 9` (the abscissa
`leftAbscissa K = 1 - c/(16 (log K)^9)` of `Sieve/MoebiusContourBound.lean`) and hence that no
choice of prime ranges could work.  **That reading was wrong.**  That abscissa belongs to the
corpus's *classical* Möbius contour; the Route-T tower carries a genuinely stronger region.

**What the corpus actually owns.**  `Sieve/RouteTZetaZeroFree.riemannZeta_ne_zero_routeT_region`
and its absolute-height form `Sieve/RouteTZetaZeroFreeAbs.exists_routeT_zero_free_region_abs` give

```text
zeta(beta + i*gamma) != 0     for   beta > 1 - routeTZeroFreeWidth A |gamma| ,
```

and `Sieve/RouteTZetaAsymptotics.routeTZeroFreeDelta_polylog_lower` pins the width's shape:

```text
routeTZeroFreeDelta A gamma  >=  1 / ( K_A * Z^{9/10} * (1 + log Z)^2 ) ,
Z = routeTLogHeightEnvelope (4 gamma) = 2 log(4 gamma + 2) + 1  ≍  log gamma .
```

So **`kappa = 9/10`**, i.e. `1 - c/((log gamma)^{9/10} (log log gamma)^2)` -- strictly better than
de la Vallée Poussin's `kappa = 1`, and produced by the corpus's own Vinogradov chain: the mean
value theorem `Sieve/VinogradovMeanValueBound.vinogradov_mean_value_bound`, the Weyl-sum power
saving `Sieve/VinogradovUpperHalfSaving.norm_vinogradovUpperHalfBilinearSum_le_rpow`, its
logarithmic-phase form `Sieve/VinogradovLogHeightWindow`, the receivers
`Sieve/MontgomeryVaughan*LogPhaseReceiver` (endpoint:
`norm_routeTLogArbitraryWeightedPartialSum_le_explicitQuarticSaving`), and the growth/Landau chain
`Sieve/RouteTZetaBlock` -> `RouteTHybridZetaAssembly` -> `RouteTZetaFinalGrowth` ->
`RouteTZetaLandauGrowth` -> `RouteTZetaZeroFree`.

**`kappa = 9/10` suffices for the whole MR programme.**  Lemma 2.3 is applied to the *large* prime
range `Q`, which the exposé places in `[exp((log X)^{4/5}), exp((log X)^{9/10})]` only because
`4/5 > 2/3`.  Any `[exp((log X)^alpha), exp((log X)^beta)]` with `9/10 < alpha < beta < 1` serves
equally: the requirement `log Q >> (log X)^{9/10+delta}` holds, and the harmonic mass
`W(Q) ≍ (beta - alpha) log log X` still tends to infinity, which is all the argument uses.  The
same reasoning applies to `P` in §4/§5, where `P_j >= (log X)^7` is the only constraint and Lemma
2.5 handles the rest.  Only Milestone A degrades: its admissible range becomes
`h >= exp((log X)^{0.95})` instead of `exp((log X)^{3/4})`, which is irrelevant since B--D
supersede it.

**What is still missing at Milestone 0.**  The Möbius side is done: `Sieve/RouteTMoebiusContour`
shifts the Perron contour to the Route-T abscissa
(`exists_norm_tsum_moebiusTwist_smoothWeight_le_routeT`) and
`Sieve/RouteTMoebiusPowerSaving.exists_norm_LSeries_truncatedMoebius_dyadic_le_routeTPower` turns
it into a dyadic power saving -- Lemma 2.3's *first* statement.  The *prime* statement is the gap:
`sum_{p <= x} p^{it}`, which needs `zeta'/zeta` (not `1/zeta`) on the Route-T abscissa, then Perron,
then partial summation.  The first of those three is now built (see "Lean progress").

Revised milestone order: **0 (only the twisted prime sum remains) -> A -> B -> C -> D**.

## Lean progress (continued)

### `zeta'/zeta` at an arbitrary zero-free width — `Sieve/ZetaLogDerivWidthBound.lean`

The corpus's `Sieve/ZetaLogDerivRegionBound.exists_logDeriv_zeta_bound_of_region` is stated for a
region of exponent one and returns the classical `O(log^2|gamma|)`.  Its proof never uses the shape
of the width, so it generalises verbatim.

| Item | Declaration |
|---|---|
| every zero within `21/40` of the wide centre lies left of the width evaluated at the top of the band | `wide_zero_re_le_width` |
| **`‖zeta'/zeta(sigma+i gamma)‖ <= C log|gamma| / w(|gamma|+1)` on `1 - w(|gamma|+1)/2 <= sigma <= 9/8`, for any positive, antitone width `w <= 1/80`** | `exists_logDeriv_zeta_bound_of_width` |
| the height past which the Route-T region has all its side conditions | `routeTLogDerivThreshold`, `routeTBinaryHeight_ge_of_threshold` |
| the same bound at the Route-T abscissa | `exists_logDeriv_zeta_bound_routeT` |
| with the width replaced by its explicit envelope: `‖zeta'/zeta‖ = O(log|gamma| * (log|gamma|)^{9/10} * (log log|gamma|)^2)` | `exists_logDeriv_zeta_bound_routeT_polylog` |

Evaluating the width at `|gamma|+1` rather than at `|gamma|` is what removes every comparison
between `w` at two nearby heights: antitonicity alone suffices, and
`Sieve/RouteTZetaZeroFreeMonotonicity.routeTZeroFreeWidth_antitone` supplies it.

Unconditional, umbrella-wired, olean built, axiom-clean.

### Next brick

The twisted von Mangoldt sum at the Route-T abscissa: Perron for
`sum_{n <= x} Lambda(n) n^{it}` against `-zeta'/zeta(s - it)`, with the pole at `s = 1 + it`
producing the `pi(x)/(1+|t|)` main term, then partial summation to `sum_{p <= x} p^{it}`.  The
contour geometry is already available (`Sieve/RouteTMoebiusContour.routeT_contour_zero_free`,
`routeTContourShift`, `routeTContourEdgeBound`), and the edge bound it needs is now the theorem
above rather than the reciprocal bound `norm_inv_riemannZeta_le_routeT_contour`.

### The twisted von Mangoldt layer — six modules (2026-08-17)

Lemma 2.3's *prime* statement was the last structural gap at Milestone 0.  Its Perron side is now
built, as the exact counterpart of the corpus's `moebiusTwist`/`invZeta` layer with `-zeta'/zeta` in
place of `1/zeta`.

| Module | Content |
|---|---|
| `Sieve/VonMangoldtTwistPerron.lean` | `vonMangoldtTwist`, its modulus and absolute summability, `∑ Λ(n)n^{-iτ}n^{-s} = -zeta'/zeta(s+iτ)`, and the smoothed Perron identity `2π ∑ Λ(n)n^{-iτ}w(n) = ∫ -zeta'/zeta(σ+i(y+τ))·W(σ+iy) dy` |
| `Sieve/ZetaLogDerivRegTwistShift.lean` | holomorphy of `s ↦ zetaLogDerivReg(s+iτ)·W(s)` on a rectangle, and the four-edge shift — no residue, zero-free input at height `|τ|+T` |
| `Sieve/ChebyshevTwistPerronIdentity.lean` | the pole term split at an arbitrary base point (`inv_sub_mul_eq_dslope_add`), the twist pole `1-iτ`, and the three-piece split of the twisted integrand |
| `Sieve/ChebyshevTwistPoleShift.lean` | the rectangle is a neighbourhood of the twist pole, and the divided-difference term shifts with no residue |
| `Sieve/ChebyshevTwistMainTerm.lean` | the pole kernel over an *arbitrary* interval — `arctan` difference plus a logarithm — and the twisted main term in closed form |
| `Sieve/ChebyshevTwistTruncatedIdentity.lean` | **the truncated twisted Chebyshev identity**: tail beyond height `T`, divided difference, explicit main term with coefficient `W(1-iτ)`, and the regular part |

All unconditional, umbrella-wired, oleans built, `#print axioms` clean on every capstone.

Two things are genuinely new relative to the untwisted chain.  First, the pole of the twisted
integrand sits at `1 - iτ` while the cutoff's transform is evaluated at `s`, so the pole term must
be split at that base point rather than at `1`; the corpus's `mellin_div_sub_one_split` is replaced
by the base-point-free `inv_sub_mul_eq_dslope_add`.  Second, truncating the Perron line
symmetrically no longer truncates symmetrically *about the pole*, so the odd part of the pole kernel
no longer cancels and the main term acquires a logarithm alongside the arctan; at `τ = 0` the two
logarithms agree and the untwisted `2 arctan(T/(d-1))` is recovered.

### What remains for Lemma 2.3

1. **Edge estimates.**  Bound the four edges of the twisted rectangle using
   `Sieve/ZetaLogDerivWidthBound.exists_logDeriv_zeta_bound_routeT` on the left edge (this replaces
   `norm_inv_riemannZeta_le_routeT_contour`, which is the reciprocal bound the Möbius chain used)
   and the cutoff's Mellin decay on the horizontals.
2. **Power saving.**  Optimise the smoothing width against the shift, as
   `Sieve/RouteTMoebiusPowerSaving` does for `1/zeta`.
3. **Smooth to sharp.**  `Sieve/SmoothedPartialSumConnector` transports the smoothed bound to
   `ψ(x,τ) = ∑_{n ≤ x} Λ(n) n^{iτ}` at the cost of the window width.
4. **Partial summation.**  `ψ(x,τ) ⟹ ∑_{p ≤ x} p^{iτ}`, discarding the prime powers.

### The twisted contour assembled to explicit edge inputs — four more modules (2026-08-17)

| Module | Content |
|---|---|
| `Sieve/ChebyshevTwistEdgeBound.lean` | `‖zetaLogDerivReg s‖ ≤ ‖zeta'/zeta(s)‖ + ‖(s-1)⁻¹‖` (`norm_zetaLogDerivReg_le_logDeriv`), continuity of the twisted regular part on the Perron line, the four-edge bound for the twisted regular integral, and **`exists_norm_integral_zetaLogDerivRegTwist_le`** — one inequality whose only inputs are sup bounds on the three edges and the rectangle geometry |
| `Sieve/ChebyshevTwistShiftedBound.lean` | `norm_truncated_le_of_shift` (a vanishing boundary functional moves the right edge to the other three), its two instances for the divided-difference and regular terms, and **`norm_tsum_vonMangoldtTwist_sub_mainTerm_le`**: `‖2π ∑ Λ(n)n^{-iτ}w(n) − W(1-iτ)·twistMainFactor‖ ≤ tail + dslope + regular` |
| `Sieve/VonMangoldtTwistSharpSum.lean` | the smooth-to-sharp connector with a general coefficient bound (the corpus's assumes `‖f‖ ≤ 1`, which `Λ` fails), and its von Mangoldt instance: removing the smoothing costs `H·log(K+H)` |
| `Sieve/VonMangoldtTwistPrimeSum.lean` | `vonMangoldtPrimeTwist`, `primePowerDefect`, and the passage `∑_{n≤K}Λ(n)n^{-iτ} ⟹ ∑_{p≤K}(log p)p^{-iτ}`: the twist has modulus one, so the discrepancy is exactly the untwisted `psi - theta` |

All unconditional, umbrella-wired, oleans built, axiom-clean.

One collision was hit and fixed: `norm_zetaLogDerivReg_le` already exists in
`Sieve/ZetaLogDerivRegBound.lean` (stated with `‖zeta'(s)‖·‖zeta(s)⁻¹‖`); the new bound, phrased
with `logDeriv` because that is what the Route-T estimate delivers, is
`norm_zetaLogDerivReg_le_logDeriv`.

### Remaining for Lemma 2.3

1. **The quantitative edge inputs.**  Sup bounds for `zetaLogDerivReg(· + iτ)` on the three edges of
   the rectangle placed at the Route-T abscissa — these are
   `norm_zetaLogDerivReg_le_logDeriv` fed by `exists_logDeriv_zeta_bound_routeT` — and the
   corresponding bounds for `dslope W (1-iτ)`, which on the left edge and the horizontals are
   `(‖W(s)‖ + ‖W(1-iτ)‖)/dist` with `dist ≥ 1-c` respectively `T - |τ|`.
2. **The power saving.**  Optimise the smoothing width against the contour shift, as
   `Sieve/RouteTMoebiusPowerSaving` does for `1/zeta`.
3. **Abel summation.**  `∑_{p ≤ K}(log p)p^{-iτ} ⟹ ∑_{p ≤ K}p^{-iτ}`, the last step to Lemma 2.3's
   prime statement.

### Both twist regimes closed to a single explicit inequality — seven more modules (2026-08-17)

The twisted contour splits into two genuinely different regimes, separated by whether the pole
`1 - iτ` lies inside the truncated rectangle `[c,d] × [-T,T]`.  Both are now built.

**Regime 1, `|τ| < T`: the residue is collected and the sum keeps a main term.**

| Module | Content |
|---|---|
| `Sieve/ChebyshevTwistLeftEdge.lean` | `line_ne_twistPole_of_ne`, `integral_twist_pole_term_line_of_ne` (the closed form of the truncated pole integral on *any* line off the abscissa), `integral_dslope_mellin_twist_left_eq` (the left-edge divided difference with its pole term extracted), and `norm_integral_left_vertical_twist_pole_free_le` |
| `Sieve/ChebyshevTwistHorizontalDslope.lean` | `norm_inv_sub_twistPole_height_le`, `norm_dslope_mellin_twist_height_le`, `norm_integral_horizontal_twist_dslope_le` |
| `Sieve/ChebyshevTwistFullMainTerm.lean` | `tsum_vonMangoldtTwist_full_main_identity` and `norm_tsum_vonMangoldtTwist_sub_full_main_le`: the sum against `W(1-iτ)·(twistMainFactor d T τ - twistMainFactor c T τ)`, with five explicit errors |
| `Sieve/ChebyshevTwistMainFactorLimit.lean` | `abs_arctan_gap_sub_pi_le`, `abs_arctan_gap_add_pi_le`, `abs_log_gap_le`, and `norm_twistMainFactor_gap_sub_two_pi_le`: the two halves of the residue sum to `2π` up to `2(d-1)/(T-|τ|) + 2(1-c)/(T-|τ|) + 4T|τ|/(T-|τ|)²` |

Two facts about the twisted geometry that the untwisted case hides.  The *effective* truncation
height is `T - |τ|`, not `T`: the pole sits at height `-τ`, so the contour only surrounds it by that
much.  And a truncation symmetric in `y` is *asymmetric about the pole*, so the imaginary parts of
the two halves no longer cancel term by term; what survives is a logarithm controlled only by the
relative asymmetry `4T|τ|` against the square of the effective height.  Both errors vanish exactly
when `T/|τ| → ∞`, which is the condition under which a twisted Chebyshev sum keeps a main term.

**Regime 2, `T < |τ|`: no residue, and the whole sum is an error.**  This is the regime
Matomäki–Radziwiłł consumes.

| Module | Content |
|---|---|
| `Sieve/ChebyshevTwistNoPoleShift.lean` | `abs_im_shift_rect_ge` (the single inequality `|τ| - T ≤ |Im(s+iτ-1)|` that replaces all residue bookkeeping), `differentiableOn_twistPoleInvW_rect`, the contour shift for the pole term, the two-piece line split `chebyshev_twist_integrand_split_two`, `tsum_vonMangoldtTwist_truncated_two_identity`, and the pole-term edge bounds |
| `Sieve/ZetaLogDerivRegRouteTUniform.lean` | `exists_logDeriv_zeta_bound_routeT_of_region` (the region as an *input*, so the width in the bound and the width in the hypothesis are the same object) and **`exists_bound_zetaLogDerivReg_routeT_uniform`**: on `1 - w(K+1)/2 ≲ σ ≤ 9/8`, `|γ| ≤ K`, both `ζ ≠ 0` and `‖zetaLogDerivReg‖ ≤ C·log K / w(K+1)` |
| `Sieve/ChebyshevTwistQuantitativeEdges.lean` | `continuous_neg_logDeriv_twist_line`, `norm_neg_logDeriv_twist_le_line` (the twist is a vertical translation, so the Dirichlet series at the abscissa bounds it unchanged), the twisted truncation error, and the left/horizontal edges of the twisted regular part |
| `Sieve/ChebyshevTwistRouteTBound.lean` | `routeTTwistAbscissa` and **`exists_norm_tsum_vonMangoldtTwist_routeT_le`** |

The capstone is one unconditional inequality with no hypotheses beyond the parameter geometry
(`0 < N`, `0 < H`, `1 < d ≤ 9/8`, `1 ≤ T < |τ|`, `K₀ ≤ |τ| + T`) and the order-two Mellin decay
constant of the cutoff:

```text
‖2π ∑ₙ Λ(n) n^{-iτ} w(n)‖ ≤ 2·Σ(d)·C/T
                            + (|τ| - T)⁻¹ · (edge mass)
                            + C'·log(|τ|+T)/w(|τ|+T+1) · (edge mass),
   edge mass = 2(N+H)^σ/σ + 2C + 2C(d-σ)/T²,   σ = routeTTwistAbscissa A δ (|τ|+T).
```

The pole factor contributes `(|τ|-T)⁻¹`, which *improves* as the twist grows — the twisted sum is
easier, not harder, at large `τ`.  The saving is `(N+H)^σ = (N+H)·(N+H)^{-w}` with `w` the Route-T
width, i.e. `exp(-c·log N/((log K)^{9/10}(log log K)²))`, uniform in `|τ| ≤ K`.

All eleven modules of this turn are unconditional, umbrella-wired, oleans built, axiom-clean
(`[propext, Classical.choice, Quot.sound]`).

### Remaining for Lemma 2.3

1. **Parameter selection.**  Choose `N, H, d, T` against `x` and `τ` and collapse the capstone to a
   single decaying rate, as the `Chebyshev{KappaOne,Littlewood,Ll}{Data,Height,Width,Rate,Shape,
   Threshold}` chain does for the untwisted contour.  Nothing new is needed mathematically; it is
   the same optimisation with `K = |τ| + T` in place of `T`.
2. **Smooth to sharp.**  `Sieve/VonMangoldtTwistSharpSum.norm_partialSum_vonMangoldtTwist_le_of_
   smoothed_bound` is already built; it needs the rate from item 1.
3. **Abel summation.**  `∑_{p ≤ K}(log p)p^{-iτ} ⟹ ∑_{p ≤ K}p^{-iτ}`, the last step to Lemma 2.3's
   prime statement.  `Sieve/VonMangoldtTwistPrimeSum` supplies the prime-power removal; only the
   partial summation over `log p` remains.

### The gate is Menon's rate, not Matomäki--Radziwiłł's — CORRECTION (2026-08-17)

Re-reading what the three `route-e-*` cards actually consume changes the target of this programme.

`route-e-reciprocal-marker-mobius-hall-law` §"Analytic inputs" cites Menon's Theorem 1.1,

```text
(1/Y) ∫_Y^{2Y} | (1/L) sum_{x < n <= x+L} mu(n) |^2 dx
    <<  (log log L)^2/(log L)^2  +  (log log Y)^4/(log Y)^2 ,      10 <= L <= Y,
```

and uses it through its `(8)`: with `L = exp((log Y)^beta)`, `1/2 < beta < 1`, the right-hand side
must be `o(1/log Y)`.  That is what makes the Markov step `(10)` produce an exceptional set of size
`o(Y/log Y)`, which is the whole mechanism of the card.
`route-e-growing-reciprocal-marker-low-breadth-transport` uses the same input through its `(16)`,
`(17)`: `R_k · log X = o(1)`.

**Matomäki--Radziwiłł 2016 is not enough for either.**  Their Theorem 1 gives a rate of the shape
`(log L)^{-c}` with a small absolute `c < 1`.  Card 2's own `(2)` forces `w = o(log h) = o(log X)`,
so `(log L_k)^c <= w^c = o((log X)^c)`, and `R_k · log X = o(1)` would require
`(log X)^{1-c} = o(1)` — false for every `c < 1`.  Card 3 fails the same way: `2*beta > 1` is used
against the exponent `2`, and any exponent at or below `1` breaks it for every admissible `beta`.

**What the extra factor is.**  The exponent `2` is not an artefact.  For a general multiplicative
`f` the Matomäki--Radziwiłł machinery gives only `o(1)`; for `mu` one may additionally run Halász
with the pretentious distance
`sum_{p <= x} (1 - Re mu(p) p^{-it})/p = sum_{p <= x} (1 + Re p^{-it})/p ~ 2 log log x`,
because `mu(p) = -1` is maximally far from every `p^{it}`.  The Halász saving is then
`exp(-2 log log L) = (log L)^{-2}`, which is exactly Menon's rate.  So the gate factorises:

1. the Matomäki--Radziwiłł ladder (Milestones A--D of this card), and
2. Halász's theorem with the explicit `mu`-distance, applied inside that ladder.

Item 2 is not extra hardship on top of item 1 — it is the same Halász/Hal\'asz--Montgomery layer
(Lemma 2.6, Lemma 7.1) already listed here, used quantitatively rather than qualitatively.  The
programme is unchanged in structure; what changes is that **every large-values and Halász step must
be carried with its constant, not merely as `o(1)`**, and the final assembly must produce
`(log L)^{-2+o(1)}` rather than `o(1)`.

This has been recorded on all three `route-e-*` cards.

### Lemma 2.3: the parameter split and the prime transfer (2026-08-17)

Two of the three items on the "Remaining for Lemma 2.3" list above are now Lean theorems.

    HTGeometry/DiscreteAbelRing.lean
      sum_mul_eq_partial_mul_diff_ring          the `Icc 1 N` summation by parts over any
                                                commutative ring (the complex-valued form the
                                                arithmetic weights need)

    RHTower/Sieve/PrimeTwistAbel.lean
      primeTwist                                the prime-indicator twist `p ↦ p^{-iτ}`
      vonMangoldtPrimeTwist_mul_invLog          `Λ_prime-twist · (1/log) = prime twist`
      sum_primeTwist_eq_abel                    summation by parts against `1/log`
      sum_Icc_invLog_diff_le                    the total variation of `1/log` past `2` is `1/log 2`
      norm_sum_primeTwist_le_of_partialSum_bound
                                                **item 3**: any majorant for the partial sums of the
                                                log-weighted twist transfers to the prime-indicator
                                                twist
      norm_sum_primeTwist_le_of_monotone_bound  the monotone form: `‖∑_{p≤K} p^{-iτ}‖ ≤ E(K)·
                                                (1/log 2 + 1/log(K+1))`, i.e. Lemma 2.3's prime
                                                statement has the same order as its Chebyshev
                                                statement

    RHTower/Sieve/VonMangoldtTwistScaledWidth.lean
      exists_norm_partialSum_vonMangoldtTwist_routeT_scaled
                                                **item 1, first half**: the capstone with the
                                                smoothing width written as `K/D`, exposing the only
                                                trade-off — smoothing loss `D²`, desmoothing loss
                                                `K log(2K)/D`
      exists_norm_partialSum_vonMangoldtTwist_routeT_balancedWidth
                                                **item 1, second half**: at `D = (3K)^{w/3}` the
                                                estimate splits into a part carrying the full contour
                                                saving `(3K)^{-w/3}` and a part carrying only the
                                                height decay in `τ`

All five declarations are unconditional and axiom-clean.

### Remaining for Lemma 2.3

Only the height regime is left: the `(3K)^{2w/3}` group of `..._balancedWidth` decays only when
`|τ|` is large compared with `(3K)^{2w/3}(log K)²`, which is the pure-error regime the two-regime
split of `ChebyshevTwistNoPoleShift` already separates.  The small-`|τ|` regime is the untwisted
Chebyshev estimate with the Route-T zero-free region, which the corpus owns.  Assembling the two
into one statement uniform in `τ` closes Lemma 2.3, and `norm_sum_primeTwist_le_of_monotone_bound`
then gives its prime form at once.

### Milestone 0 is closed: Lemma 2.3 in both forms (2026-08-18)

The height regime is joined and the prime transfer is carried out.  Lemma 2.3 is now an
unconditional Lean theorem, uniform in the frequency, in both the Chebyshev and the prime form.

    RHTower/Sieve/VonMangoldtTwistUniformHeight.lean
      routeTTwistHeightFactor                   `1/(1+|τ|) + log(3|τ|/2+3)/W(3|τ|/2+1)`, the
                                                logarithmic cost of the Route-T width at height `τ`
      twistCollapse_contour, twistCollapse_trivial
                                                the two arithmetic collapses, stated abstractly
      exists_norm_partialSum_vonMangoldtTwist_routeT_uniform
                                                **Lemma 2.3, Chebyshev form**: for *every* real `τ`
                                                and every `K ≥ e^9`,
                                                `‖∑_{n≤K}Λ(n)n^{-iτ}‖ ≤ C·K·[(3K)^{-w(τ)/3}(E(τ)+log 2K)
                                                 + (1 + (3K)^{2w(τ)/3}(log²K + E(τ)))/(1+|τ|)]`.
                                                Above a fixed height this is the balanced contour
                                                estimate; below it, `ψ(K) ≤ 7K` already has the
                                                shape of the height term, since `1/(1+|τ|)` is
                                                bounded below there

    RHTower/Sieve/PrimePowerDefectBound.lean
      primePowerDefect_eq                       the proper prime-power mass is Chebyshev's `ψ − θ`
      primePowerDefect_le                       hence at most `2√K log K`

    RHTower/Sieve/VonMangoldtTwistPrimeEnvelope.lean
      routeTTwistEnvelope                       the monotone envelope: contour term at exponent
                                                `1 − w/3`, height term at exponent `1 + 2w/3`,
                                                plus the prime-power mass
      twistEnvelope_mono, routeTTwistEnvelope_mono, routeTTwistEnvelope_nonneg
                                                monotonicity above one — each factor is a
                                                nonnegative increasing function of the cutoff
      norm_vonMangoldtPrimeTwist_le,
        norm_partialSum_vonMangoldtPrimeTwist_le_crude
      exists_norm_sum_primeTwist_routeT_le      **Lemma 2.3, prime form**:
                                                `‖∑_{p≤N}p^{-iτ}‖ ≤ (Env(max(N,1)) + 7e^9)·
                                                 (1/log 2 + 1/log(N+1))`, by summation by parts
                                                against `1/log`

Why the two-term shape is the right one.  The exposé uses Lemma 2.3 as
`π(P)/(1+|t|) + P·exp(−log P/(log(P+|t|))^{κ+δ})`; the contour term above is the second summand
with `κ = 9/10`, and the height term is the first, with an extra `(3K)^{2w/3} log²K ≤ K^{1/240}log²K`
which is harmless in every application, since Lemma 2.3 is invoked with `|t|` far larger than any
fixed power of `P` (the exposé's `P ≈ exp((log X)^{0.95})` against `|t| ≤ X`).

All declarations are unconditional, umbrella-wired, oleans built, axiom-clean
(`[propext, Classical.choice, Quot.sound]`).

### Remaining

Milestone A onwards: the Matomäki--Radziwiłł ladder itself (Lemmas 2.4--2.6, 7.1, the
Turán--Kubilius/rough-integer factorisation, and the assembly), carried **quantitatively** so that
the final rate is Menon's `(log L)^{-2+o(1)}` rather than `o(1)`.  Lemma 2.4 is already corpus
(`Sieve/DirichletIntegralBound`); Lemmas 2.5, 2.6 and 7.1 are the next bricks.

### Lemma 2.5: the free-exponent large-values estimate (2026-08-18)

The corpus's sixth-moment device was fixed at the cube.  It is now available at every power, which
is what Lemma 2.5 needs — the exponent is chosen against `log T / log P`, not fixed in advance.

    RHTower/Sieve/DirichletPowerConvolution.lean
      powIdx, powIdx_lt, powIdx_val_add_one       the index of a `k`-tuple in `Fin (N^k)`
      powFibre, convPow                           the `k`-fold Dirichlet convolution
      exp_phase_powIdx                            the phase of a tuple is the phase of its product
      dirPoly_convPow                             **`F(t)^k` is a Dirichlet polynomial of length
                                                  `N^k` with coefficients `convPow k N a`**
      sum_normSq_convPow_le                       `∑_j|b_j|² ≤ D·(∑_n|a_n|²)^k` from a fibre bound
      powMoment_dirPoly, card_largeValues_pow_le  the `2k`-th moment and its counting form

    RHTower/Sieve/DirichletPowerPrimeSupport.lean
      powFibreOn                                  the part of a fibre supported in a set
      sum_normSq_convPow_le_of_support
      powFibreOn_primeSupport_card_le             **a prime-supported `k`-fold fibre has at most
                                                  `k^k` points**: every entry is a prime factor of
                                                  the anchored product, and that product has at
                                                  most `k` prime factors.  No power of the length
                                                  enters
      sum_normSq_convPow_le_of_prime_support
      powMoment_dirPoly_prime_support

    RHTower/Sieve/DirichletPowerMeasure.lean
      largeValues_pow_setOf                       raising to the `k`-th power does not move the
                                                  level set
      volume_largeValues_pow_le_of_prime_support,
        volume_largeValues_pow_symm_le_of_prime_support
                                                  **Lemma 2.5**:
                                                  `V^{2k}·|{|F| ≥ V} ∩ [−T,T]|
                                                    ≤ 2(T + 4N^k(1+log N^k))·k^k·(∑|a_n|²)^k`.
                                                  At `k ≍ log T/log N` the mean-value factor is
                                                  `≍ T log T`, which is the exposé's shape

The classical bound uses `k!` rather than `k^k` for the fibre; the difference is a factor `e^k`,
i.e. `e^{1/2}` after taking the `2k`-th root, so it never reaches the application.

All declarations are unconditional, umbrella-wired, oleans built, axiom-clean.

### Remaining

Lemma 2.6 and Lemma 7.1 (Halász--Montgomery).  The duality half is already corpus —
`Sieve/AlmostOrthogonality.sum_norm_inner_sq_le_of_schur` gives
`∑_r|⟪φ_r,a⟫|² ≤ (max_r ∑_t|⟪φ_r,φ_t⟫|)‖a‖²` — so what is missing is exactly the Gram row for
`φ_r(n) = n^{-it_r}`, i.e. the estimate

```text
|∑_{n ≤ N} n^{iu}|  ≪  N/|u| + |u|^{1/2} log|u| .
```

Two routes, both requiring new analytic infrastructure:

1. **Functional equation.**  `∑_{n≤N}n^{-w} = ζ(w) + N^{1-w}/(w−1) − (1/2)N^{-w} + O(|w|N^{-σ−1})`
   for `σ > −1` (a *second-order* Euler--Maclaurin; the corpus's
   `Sieve/ZetaTruncated.riemannZeta_eq_sum_add_tail` is the first-order form and needs `σ > 0`),
   then `ζ(iu) = χ(iu)ζ(1−iu)` with `|χ(iu)| ≍ |u|^{1/2}` and `ζ(1+iu) ≪ log|u|`.
2. **Van der Corput.**  Kusmin--Landau plus the second-derivative test, applied to
   `f(x) = (u/2π)log x` on dyadic blocks.

Route 1 reuses the corpus's `zetaChi` and Route-T zeta machinery and is the recommended one.  Note
that the first-order Euler--Maclaurin alone gives only `N/|u| + u²`, which is useless for the Gram
row: the crossover with the trivial bound `N` sits at `N^{2/3}`, and the off-diagonal then costs
`R·N`.  The square-root saving is genuinely needed.

### Lemma 2.6 is closed — and most of it was already in the corpus (2026-08-18)

A search before building found that the entire two-regime phase analysis is already formalised:

* `Sieve/KuzminLandau.kuzminLandau_band` and `Sieve/KuzminLandauInterval.kuzminLandau_interval`
  — the Kuzmin--Landau inequality, discrete and sample-point forms;
* `Sieve/SecondDerivativeTest.second_derivative_test'` — `‖S‖ ≤ 8Nh√λ + 12/√λ`;
* `Sieve/HuxleyLogPhase` — both regimes for the logarithmic phase on a dyadic block, with the
  exact envelopes `logDyadicLambda`, `logDyadicSecondBound`, `logDyadicSecondEnvelope`;
* `Sieve/HuxleyDyadicRow` — the dyadic Dirichlet row `dyadicDirRow` and its Gram entries;
* `Sieve/HuxleyLargeValues.sum_norm_inner_dyadicDirRow_le_huxley` — the Gram **row** bound
  `N + (12πN/δ)H_K + K·B`;
* `Sieve/AlmostOrthogonality.sum_norm_inner_sq_le_of_schur` — the duality principle.

What was missing was only the composition without the absorption hypothesis of
`huxley_local_large_values`, and the closed form of the envelope.

    RHTower/Sieve/HalaszMontgomeryDyadic.lean
      halaszMontgomery_dyadic                   `∑_r|⟪φ_r,a⟫|² ≤ (N + (12πN/δ)H_K + K·B)‖a‖²`
      halaszMontgomery_dyadic_log               with `H_K ≤ 1 + log K`

    RHTower/Sieve/DyadicSecondEnvelopeClosed.lean
      logDyadicLambda_eq                        `λ(t) = t/(8πN²)`
      logDyadicSecondEnvelope_le                **`B(N,U,T) ≤ 214√T + 1536·N/√U`** — the
                                                exponent-pair `(1/2,1/2)` shape, by squaring both
                                                endpoints against `3 < π ≤ 4`
      halaszMontgomery_dyadic_explicit          **Lemma 2.6**:
                                                `∑_r|⟪φ_r,a⟫|²
                                                  ≤ (N + (12πN/δ)(1+log K)
                                                      + K(1 + 214√T + 1536N/√U))·‖a‖²`

This is the exposé's `(N + |E|T^{1/2}log T)` with the log attached to the diagonal term instead of
the off-diagonal one, and with `U` a free resonance threshold (`3U ≤ 4πN`) that a large-values
argument optimises.  Lemma 7.1 is needed only for a general multiplicative `f`, not for `μ`, so it
does not gate these cards.

All declarations unconditional, umbrella-wired, oleans built, axiom-clean.

### Remaining

Milestones A--D: the Matomäki--Radziwiłł ladder itself, carried quantitatively so the final rate is
Menon's `(log L)^{-2+o(1)}`.  Every named lemma of §2 that the `μ` case uses is now a Lean theorem:
2.3 (both forms), 2.4 (corpus), 2.5, 2.6.

### Lemma 2.5 in the exposé's balanced form (2026-08-18)

    RHTower/Sieve/DirichletPowerBalanced.lean
      volume_largeValues_prime_balanced       choosing `k` with `N^k ≤ T` collapses the mean-value
                                              factor and gives
                                              `|{|F| ≥ V} ∩ [−T,T]| ≤ 10T(1+log T)(kG/V²)^k`,
                                              `G = ∑|a_n|²`.  The whole length dependence now sits
                                              in `k ≈ log T/log N`, and the measure decays
                                              geometrically as soon as `V² > kG`

### Corpus inventory for this lane — read before building anything else

A survey on 2026-08-18 found that the exponential-sum machinery behind Lemmas 2.5/2.6 was already
complete, and that a Kusmin--Landau build was about to be duplicated.  What the corpus owns:

    Sieve/KuzminLandau, Sieve/KuzminLandauInterval      Kusmin--Landau, discrete + sample-point
    Sieve/SecondDerivativeTest, Sieve/KthDerivativeTest the derivative tests
    Sieve/HuxleyLogPhase                                both regimes for `-(t/2π)log x` on `[N,2N)`
    Sieve/HuxleyDyadicRow, Sieve/HuxleyLargeValues      the dyadic row and its Gram row
    Sieve/AlmostOrthogonality                           the duality principle
    Sieve/RamareWeight, RamareDecomposition, RamareEnergy   the bilinear factorisation, energy-free
    Sieve/MaximalWindowReduction, MaximalWindowDyadic   maximal window → dyadic mean squares
    Sieve/MRFibreReduction, MRFromCorrelations,
      MRFromUniformCorrelations                         the two entry interfaces
    Sieve/ZetaLineRate.norm_riemannZeta_line_rate_clean `ζ(1+it) ≪ log t/loglog t`
    Sieve/RouteTZetaZeroFree                            the `κ = 9/10` region

Also recorded: chasing `ζ(it) ≪ |t|^{1/2}` for the Gram row is a dead end — it only covers
`N ≫ |u|^{1+ε}`, whereas the binding regime is `|u|^{1/2} < N ≤ |u|`, which is exactly what the
second-derivative test handles.  (The exact identities `|Γ(iy)|² = π/(y sinh πy)` and
`|Γ(1/2−iy)|² = π/cosh πy` do give `|ζ(it)| = π^{−1/2}√(y tanh πy)|ζ(1+it)|` cheaply, should it be
wanted elsewhere.)

### Remaining

The assembly only: exposé §§3--5 and MR §§4--7 (Milestones A--D), carried quantitatively.
Milestone A is now fully unblocked — Lemmas 2.1, 2.3, 2.4 and Turán--Kubilius are all theorems.

### The Plancherel interface for the three cards (2026-08-18)

The cards' own object is now connected to the spectral side, so the whole remaining problem is one
statement about a single integral.

    RHTower/Sieve/FibreWindowBridge.lean
      fibreIndex, innerFibre_subset_fibreIndex
      card_filter_log_eq_le_one                 at most one integer has a prescribed logarithm
      logWindowSum_eq_sum_filter                the window sum as a filtered sum
      norm_fibreSum_sub_logWindowSum_le         **the fibre sum is the logarithmic window sum at
                                                `log(x/a)`, up to one coefficient**: the fibre is the
                                                closed window `[u, u+δ]` and `logWindowSum` the
                                                half-open `(u, u+δ]`, and only the lower endpoint
                                                can carry an integer
      fibreLogStart, fibreLogStart_separated    the sample points are `1/(2√x)`-separated, because
                                                `log(a'/a) ≥ 1 − a/a' ≥ 1/a' ≥ 1/(2√x)`
      exp_fibreLogStart{,_le}, exp_fibreWidth
      norm_logWindowSum_osc_le                  the window sum moves by at most `5` across one
                                                separation cell (`e^{lam} ≤ 1 + 2·lam` for
                                                `lam ≤ 1/2`, `e^{u_a} ≤ √x`, `e^δ ≤ 2` when `h ≤ √x`)
      sum_fibreSum_sq_le_integral               **`∑_a(∑_{fibre}f)² ≤ 8√x·∫‖S‖² + 102(√x+1)`**
      averagedMeanSquare_of_spectral            **the interface**: if
                                                `(∫_ℝ‖logWindowSum f (fibreIndex x h) (fibreWidth x h) u‖²du)/h² → 0`
                                                then `AveragedMeanSquare f hh`

`Sieve/LogWindowDiscreteTransfer.norm_logWindowSum_sub_le` was made public (it was `private`); no
other change to existing files.

### Remaining — one statement

Composing `averagedMeanSquare_of_spectral` with
`LogWindowPlancherel.integral_normSq_logWindowSum_eq` and `normSq_logWindowKernel_le_min`, the three
`route-e-*` cards are now equivalent to

```text
∫_ℝ min( δ² , (πw)^{-2} ) · | ∑_{n ≤ M} μ(n) n^{-2πiw} |² dw  =  o(δ²M²) ,
     M ≍ √x ,   δ = log(1 + h/√x) ≍ h/M ,   h → ∞ .
```

The accounting: the far range `|w| > W` costs `M/W + M²/W²` by dyadic annuli against the mean value
theorem, which is `o(δ²M²) = o(h²)` for `W = M/(εh)` with `ε → 0`; the near range needs
`∫_{|w| ≤ W}|A(w)|²dw = o(M²)`, an `o(1)` saving over the mean value theorem.  That saving is
exactly Matomäki--Radziwiłł, and it is what Lemmas 2.3/2.5/2.6 plus the Ramaré factorisation
(`Sieve/Ramare*`) supply.  **Note that the existing `dyadicMeanSquare_le_dyadicTail` route cannot
be used as-is**: it asks for an affine majorant `∫_{|w|≤T}|A|² ≤ αT + β` with `α = o(M)`, which is
false for the full polynomial — the factorisation has to enter before the mean value theorem.

### The reduction is now a single affine majorant (2026-08-18, continued)

Two corrections and one further composition.

**The index set had to shrink.**  `fibreIndex` was `Icc 1 ⌊x + h√x⌋₊`, of length `≍ x`; but every
outer factor is `≥ √x`, so every fibre element is `≤ (x + h√x)/√x = √x + h`.  With the long index set
the interface is true but vacuous — the trivial size of `∫‖S‖²` would be `≍ h²x`, not `≍ h²`.
`fibreIndex x h` is now `Icc 1 ⌊√x + h⌋₊` and `innerFibre_subset_fibreIndex` carries the proof.

**Composed with Gallagher's dyadic tail** (`Sieve/GallagherDyadicTail.gallagher_split_integral_dyadic`,
already in the corpus):

    RHTower/Sieve/FibreWindowBridge.lean
      averagedMeanSquare_of_gallagherBudget   `AveragedMeanSquare f hh` holds as soon as there are
                                              `W, α, β` with
                                              `∫_{|w| ≤ T}|A(w)|² ≤ α T + β`  for all `T ≥ W`, and
                                              `( 2δ²(αW + β) + 4α/(π²W) + 4β/(3π²W²) ) / h² → 0`

So the three `route-e-*` cards are now **exactly equivalent** to producing an affine mean-square
majorant for the Möbius Dirichlet polynomial of length `M = ⌊√x + h⌋`:

```text
∫_{|w| ≤ T} | ∑_{n ≤ M} μ(n) n^{-2πiw} |² dw  ≤  α·T + β        (T ≥ W),
     with   β = o(M²)   and   α = O(M) ,   W chosen in  (M/h², M) .
```

Accounting, with `δ = fibreWidth x h ≍ h/M`: the term `2δ²β = 2h²β/M²` is the binding one and forces
`β = o(M²)`; with `W = M/h` the other three terms are `4h²W/M·(α/M) = O(h)`, `4α/(π²W) = O(h)` and
`4β/(3π²W²) = O(h²β/M²)`.  Montgomery–Vaughan gives `β ≍ M²` exactly (`∑_n|a_n|²·n`), so the whole
remaining content is an `o(1)` saving over the mean value theorem — which is Matomäki–Radziwiłł, and
what the Ramaré factorisation together with Lemmas 2.3/2.5/2.6 supplies.

### Remaining

Produce that affine majorant.  The route is the Ramaré factorisation (`Sieve/Ramare*`) followed by
the two-regime split: on the set where the prime factor is small use Lemma 2.3, and on its
complement — whose measure Lemma 2.5 bounds — use Lemma 2.6.  Every ingredient is a theorem; what is
left is the choice of the prime ranges and the assembly.

### The frontier is now one named object (2026-08-18, continued)

The Ramaré lane was already carried much further than the "Lean progress" section recorded:

* `Sieve/RamareBilinearMeanSquare.integral_Icc_normSq_logPoly_moebius_le_bilinear` —
  `∫_{|w|≤T}‖A_μ‖² ≤ 2∫_{|w|≤T}‖B‖² + 4T·E²` with `B(w) = ∑_{p∈P} μ(p)p^{2πiw}G_p(w)`;
* `Sieve/RamarePrimeOffDiagonal.integral_normSq_ramareBilinear_eq` — the exact diagonal/off-diagonal
  split, `∫‖B‖² = ∑_p ∫‖G_p‖² + ramarePrimeOffDiagonal P M W`;
* `Sieve/RamarePrimeOffDiagonal.integral_Icc_normSq_logPoly_moebius_le_primeOffDiagonal` — the
  diagonal is inside the budget (Ramaré preserves the coefficient energy), so

```text
∫_{|w| ≤ T} |A_μ(w)|² dw
  ≤ (1+δ)(10TM + εM² + ramarePrimeOffDiagonal P M T)
    + 2(1+1/δ)(12TM + (1+5e/2)εM²) .
```

    RHTower/Sieve/FibreWindowBridge.lean
      logPoly_moebius_congr                     the two Möbius coefficient normalisations agree
      averagedShortInterval_moebius_of_affineMajorant
                                                the Route E gate in the corpus's own normalisation

So the two lanes now compose literally, and the whole remaining content of the three
`route-e-*` cards is:

```text
ramarePrimeOffDiagonal P M T  ≤  α'·T + β'      (T ≥ W),   β' = o(M²) ,
```

for a designated prime set `P` satisfying the standing conditions of
`integral_Icc_normSq_logPoly_moebius_le_primeOffDiagonal` (`#P ≤ M`, harmonic mass
`A ≥ 15e/(2ε)`, `∑_{p∈P}M/p² ≤ εM`, `∑_{p∈P}1/p² ≤ 2ε/(5e)`).  The trivial Cauchy--Schwarz bound
`|OD| ≤ #P·∑_p∫‖G_p‖²` is over budget by the factor `#P`, which is exactly why the oscillation of
`p^{2πiw}\overline{q^{2πiw}}` over prime pairs has to be used — Lemma 2.6 with the frequencies
`log(p/q)`.

### Remaining

One estimate: the affine majorant for `ramarePrimeOffDiagonal`.  The route is to replace the
`p`-dependent cofactor `G_p` by a common `G` over a dyadic prime range `P ⊂ [Q, 2Q]` (so that
`M/p ≍ M/Q` uniformly), turning `B` into `P(w)·G(w)`, and then to split by the level set of the
prime polynomial `P(w)`: below the threshold use Lemma 2.3, above it use Lemma 2.5 for the measure
and Lemma 2.6 on it.  `Sieve/DirichletProductSplit` and `Sieve/DirichletConvSplit` already carry the
threshold split for a factorised polynomial.

### The baseline off-diagonal bound, and why it cannot be enough (2026-08-18, continued)

    RHTower/Sieve/RamareOffDiagonalTrivial.lean
      integrableOn_normSq_ramareCofactorPoly
      abs_ramarePrimeOffDiagonal_le             **`|OD| ≤ (#P − 1)·∑_p ∫_{|w|≤W}‖G_p‖²`**, by the
                                                arithmetic--geometric mean on each pair and the
                                                identity `∑_p ∑_{q≠p}(I_p + I_q)/2 = (#P−1)∑_p I_p`.
                                                No oscillation is used
      integral_Icc_normSq_logPoly_moebius_le_trivialOffDiagonal
                                                composing with the diagonal budget:
                                                `∫_{|w|≤T}|A_μ|² ≤ (1+δ)(1+#P)(10TM + εM²)
                                                  + 2(1+1/δ)(12TM + (1+5e/2)εM²)`,
                                                an unconditional affine majorant

With this the whole chain is a Lean theorem end to end — `averagedShortInterval_moebius_of_affineMajorant`
accepts it — and the *only* deficiency is the size of the intercept.  The accounting is decisive:
the standing hypothesis `15e/(2ε) ≤ ∑_{p∈P}1/p = A` forces `ε ≥ 15e/(2A)`, while `#P ≥ A·min P`,
so

```text
#P · ε  ≥  (A · min P) · 15e/(2A)  =  15e · (min P)/2  ≥  15e ,
```

i.e. the intercept is `≥ 40 M²` no matter how the designated primes are chosen.  The oscillation of
`p^{2πiw}\overline{q^{2πiw}}` is therefore not a refinement but the entire mechanism, and the
`(#P)` in `abs_ramarePrimeOffDiagonal_le` is the exact size of the saving that must be produced.

### Remaining

Replace `abs_ramarePrimeOffDiagonal_le` by an estimate that uses the prime-pair oscillation: Lemma
2.6 with the frequencies `log(p/q)`, after the cofactors have been made `p`-independent over a
prime range narrow enough that `M/p` is essentially constant.  A single dyadic range cannot do both
(narrow ⇒ small harmonic mass), which is exactly why Matomäki--Radziwiłł run the ladder
`P^{(0)},…,P^{(L)}` of Milestone D.

### The exposé's §4 mechanism at a free exponent (2026-08-18, continued)

    RHTower/Sieve/DirichletPowerProductSplit.lean
      integral_normSq_mul_le_of_pow             the threshold split with a free-exponent bound on
                                                the exceptional set:
                                                `V^{2k}∫|F|²|G|² ≤ V^{2k+2}∫|F|² + (sup|F|)²(sup|G|)²·A`
                                                whenever `V^{2k}·|{|G| ≥ V}| ≤ A`
      integral_normSq_mul_le_pow_prime_support  instantiated by Lemma 2.5, on `(0,T]`
      integral_normSq_mul_symm_le_pow_prime_support
                                                the same on `[-T,T]`, which is the range the
                                                Ramaré/Gallagher chain works on

For a prime-supported second factor the exceptional term is
`(T + 4M^k(1 + log M^k))·k^k·(∑|b|²)^k` — no power of the length — so the exponent may be chosen
against `log T / log M`.  This is the exposé's §4 mechanism: below the threshold the prime factor is
replaced by `V`, above it the exceptional set is too small for the trivial size to matter.

`integral_normSq_mul_split_symm` was already in the corpus (`Sieve/DirichletSymmSplit`); only the
free-exponent composition was missing.

### Remaining

The device now applies to any genuine *product* `F·G`.  What the Ramaré form
`B(w) = ∑_{p∈P}μ(p)p^{2πiw}G_p(w)` is missing is exactly that: the cofactor `G_p` depends on `p`
through both the condition `p ∤ m` and the range `m ≤ M/p`.  Making it `p`-independent needs a prime
range narrow enough that `M/p` is essentially constant, which conflicts with the harmonic-mass
requirement `∑_{p∈P}1/p ≥ 15e/(2ε)` — the tension that the ladder `P^{(0)},…,P^{(L)}` resolves.

### The block structure that unlocks the product (2026-08-18, continued)

Two facts, both now Lean theorems, resolve where the `p`-dependence of the Ramaré cofactor actually
comes from.

    RHTower/Sieve/FibreWindowBridge.lean
      fibreDyadicIndex, fibreDyadicIndex_subset
      innerFibre_subset_fibreDyadicIndex        **every fibre lies in `[√x/2, √x + h]`** — a block of
                                                ratio at most four, not an initial segment.  The
                                                outer factor is in `[√x, 2√x]`, so `b ≥ x/a ≥ √x/2`
                                                and `b ≤ (x + h√x)/a ≤ √x + h`

    RHTower/Sieve/RamareCofactorBlock.lean
      ramareCofactorSet_subset_common           **if the integers lie in `[A,B]` and the designated
                                                primes in `(Q, 2Q]`, every cofactor lies in the
                                                single block `[A/(2Q), B/Q]`** — endpoints
                                                independent of `p`

So over a block the cofactor polynomials `G_p` are supported in *one* common index set and differ
from a single polynomial `G` only by the terms with `p ∣ m`; the `ℓ²` cost of that correction is
`∑_{p∈P}#{m ≤ B/Q : p ∣ m} ≍ (B/Q)·∑_{p∈P}1/p`, which is inside the budget.  Over an initial
segment `[1,M]` the cofactor range `[1, M/p]` moves with `p` by a factor two and no such comparison
is available — that was the real obstruction, and the reduction already supplies the block for free.

**The remaining design question** is the width of the prime range.  A dyadic range `(Q,2Q]` gives a
common cofactor block but harmonic mass only `≍ log 2/log Q`, whereas
`integral_Icc_normSq_logPoly_moebius_le_primeOffDiagonal` needs `∑_{p∈P}1/p ≥ 15e/(2ε)`.  A wide
range `[P₁,P₂]` has mass `≍ log(log P₂/log P₁)` but splits into `≍ log P₂` dyadic blocks, and
`∫|B|² ≤ J∑_j∫|B_j|²` costs that `J`.  The Ramaré form does split additively over sub-ranges of `P`
(the coefficient `ramareCofactorCoeff P` depends on `P` but not on `p`), so the split itself is
free; what is not free is the Cauchy–Schwarz over `j`.  Resolving that trade-off is precisely the
ladder `P^{(0)},…,P^{(L)}` of MR §§4–7.

### Correction: blocking alone does not make the cofactor `p`-independent (2026-08-18, continued)

The previous entry overstated the gain.  Over a block `[A, B]` with `p ∈ (Q, 2Q]` the cofactor set
is `[A/p, B/p]`, which lies inside the common block `[A/(2Q), B/Q]` but differs from it by a
*constant fraction* of its length: `A/p` sweeps all of `[A/(2Q), A/Q)` as `p` runs over the dyadic
range.  So `G_p` and a single `G` differ by a polynomial of comparable length, and the `ℓ²`
correction is not negligible.  What blocking buys is that all the cofactor ranges are *comparable*,
not that they are equal.

The correct quantitative statement is that the discrepancy is proportional to the **relative width
of the prime range**:

    RHTower/Sieve/RamareCofactorBlock.lean
      card_Icc_cast_le                          a cast-friendly cardinality bound for `Icc`
      mem_ramareCofactorSet_iff                 `m ∈ ramareCofactorSet S p ↔ p·m ∈ S`
      ramareCofactorSet_subset_common           the common block over a dyadic prime range
      card_cofactor_gap_le                      **for `p ∈ (Q, Q(1+η)]` the cofactor set differs
                                                from the fixed block `[A₀/(Q(1+η)), B₀/Q]` by at
                                                most `(A₀+B₀)η/Q + 4` elements** — the two moving
                                                endpoints each sweep an interval of relative
                                                width `η`

So the product structure costs `η` and the harmonic mass costs `1/η`-many blocks; balancing those
two is the content of the ladder, not a bookkeeping detail.  This is the honest statement of the
frontier and replaces the "blocking unlocks the product" claim of the previous entry.

### The `p`-independence, quantified (2026-08-18, continued)

    RHTower/Sieve/RamareCofactorBlock.lean
      logPoly_sub_eq_sdiff                      changing the index set of a Dirichlet polynomial
                                                changes it by the symmetric difference only
      integral_Icc_normSq_logPoly_sub_le        **the `ℓ²` cost of a change of index set**:
                                                `∫_{|w|≤W}‖logPoly a U − logPoly a V‖²
                                                  ≤ 2(5πW/2 + 5eM/2)(|U\V| + |V\U|)`
                                                for `‖a‖ ≤ 1`, via `SupportMeanSquare`
      card_multiples_le                         the multiples of `p` in a block number
                                                at most `b/p + 1`
      card_cofactor_symmDiff_le                 **the full gap**: for `p ∈ (Q, Q(1+η)]`,
                                                `|C \ {m ∈ cofactorSet | ¬p∣m}|
                                                   ≤ (A₀+B₀)η/Q + 4 + (B₀/Q + 1)`

Composing the last two: replacing every cofactor polynomial `G_p` by the single polynomial over the
common block costs, in mean square,

```text
∑_{p ∈ P} ∫_{|w| ≤ W} ‖G_p − G‖²  ≤  2(5πW/2 + 5eM/2) · #P · ( (A₀+B₀)η/Q + B₀/Q + 5 ) .
```

With `A₀ ≍ B₀ ≍ Y` (the fibre block), `#P ≍ ηQ/log Q` and the budget `εY²`, the `η`-term is
`≍ W η²Y/log Q + η²Y²/log Q` and the multiples term `≍ ηY²/log Q` — both inside the budget once
`η → 0`.  So the product structure is available at a cost `O(η)`, while the harmonic mass of a
range of relative width `η` is `≍ η/log Q`, so `1/η`-many such ranges are needed to reach
`15e/(2ε)`.  **That is the ladder's trade-off, now with both sides proved.**

### Remaining

Assemble: choose the ranges `P^{(0)},…,P^{(L)}` and the corresponding `η`, apply
`integral_normSq_mul_symm_le_pow_prime_support` on each, and sum.  Every ingredient is now an
unconditional Lean theorem; what is left is the choice of parameters and the summation.

### The ladder itself (2026-08-18, continued)

    RHTower/Sieve/RamareBlockSplit.lean
      ramareBlock, continuous_ramareBlock
      ramareBilinear_eq_sum_blocks              **the bilinear form splits additively over any
                                                partition of the designated primes** — the Ramaré
                                                coefficient depends on `P` but not on the individual
                                                prime, so only the outer sum is split
      integral_normSq_ramareBilinear_le_blocks  Cauchy--Schwarz over the blocks:
                                                `∫‖B‖² ≤ #I · ∑_i ∫‖B_i‖²`
      geomBlock, geomBlock_subset               the `j`-th block of a ratio-`r` ladder from `Q`
      geomBlock_pairwiseDisjoint
      geomBlock_biUnion_eq                      **the ladder covers `(Q, Q r^L]`** — for each prime
                                                the block index is the least `j` with
                                                `p ≤ Q r^{j+1}`, and it is `< L`
      integral_normSq_ramareBilinear_le_geomLadder
                                                `∫‖B‖² ≤ L · ∑_{j<L} ∫‖B_j‖²` for a geometric
                                                prime range `(Q, Q r^L]`

So the ladder is now a Lean object: a geometric partition of the designated primes into `L` blocks
of ratio `r`, with the assembly cost exactly `L`.  Combined with the previous entry, a block of
ratio `r = 1 + η` has cofactor discrepancy `O(η)` and harmonic mass `≍ η/log Q`, while the ladder
costs `L ≍ (log(r^L))/η`.

### Remaining

Choose `Q`, `r = 1+η` and `L` against `ε` and the budget, and discharge the per-block estimate with
`integral_normSq_mul_symm_le_pow_prime_support`.  All the structural theorems are in place; what is
left is the parameter optimisation.

### One block, as a product (2026-08-18, continued)

    RHTower/Sieve/RamareBlockSplit.lean
      primeBlockPoly, continuous_primeBlockPoly
      integral_normSq_ramareBlock_le_product    **one block is a product up to the cofactor
                                                discrepancy**:
                                                `∫‖B_j‖² ≤ 2∫‖P_j·G‖²
                                                  + 2·#P_j·∑_{p∈P_j}∫‖G_p − G‖²`

    RHTower/Sieve/RamareCofactorBlock.lean
      norm_ramareCofactorCoeff_le_one           `‖μ(m)/(ω_P(m)+1)‖ ≤ 1`
      integral_normSq_cofactor_sub_common_le    **the discrepancy of one prime**: for
                                                `p ∈ (Q, Q(1+η)]` and `Q ≥ 1`,
                                                `∫_{|w|≤W}‖G_p − G‖²
                                                  ≤ 2(5πW/2 + 5eM/2)((1+M)η/Q + M/Q + 5)`,
                                                with `G` the polynomial over the common block
                                                `[1/(Q(1+η)), M/Q]`

The chain inside a block is therefore complete and unconditional: the block is a product plus an
error, the error is `O(η + 1/Q)` per prime, and the product is handled by
`integral_normSq_mul_symm_le_pow_prime_support` (Lemma 2.5 inside the threshold split).

### Remaining

Only the parameter choice.  The per-block budget reads

```text
∫‖B_j‖² ≤ 2∫‖P_j·G‖² + 4·#P_j²·(5πW/2 + 5eM/2)·((1+M)η/Q + M/Q + 5) ,
```

and the ladder multiplies the sum of these by `L`.  Choosing `Q`, `η` and `L` against `ε`, `W ≍ M/h`
and the budget `εM²` — and feeding the product term through the threshold split — closes the three
`route-e-*` cards.  Every inequality in the chain is now an unconditional Lean theorem; what is left
is arithmetic on the parameters.

### The ladder, assembled (2026-08-18, continued)

    RHTower/Sieve/RamareBlockSplit.lean
      geomCofactorBlock                         the common cofactor block of the `j`-th step
      integral_normSq_ramareBlock_geom_le       **one ladder step, as a product plus an explicit
                                                error**: the `j`-th prime range has relative width
                                                `η` about `Q_j = Q(1+η)^j`, so
                                                `∫‖B_j‖² ≤ 2∫‖P_j·G_j‖²
                                                   + 4·#P_j²·(5πW/2 + 5eM/2)((1+M)η/Q_j + M/Q_j + 5)`
      integral_normSq_ramareBilinear_le_ladder_assembled
                                                **the whole bilinear mean square, over the ladder**:
                                                the same bound summed over `j < L` and multiplied
                                                by `L`

Every quantity in that final inequality is explicit: `L`, `#P_j`, `Q_j = Q(1+η)^j`, `η`, `W`, `M`,
and the single integral `∫‖P_j·G_j‖²` of a narrow prime polynomial against one cofactor polynomial.
The structural half of MR §§4--7 is therefore complete and unconditional.

### Remaining

Two purely quantitative steps.

1. `∫_{|w|≤W}‖P_j·G_j‖²` — the product of a prime-supported polynomial with a bounded-coefficient
   one.  `Sieve/DirichletPowerProductSplit.integral_normSq_mul_symm_le_pow_prime_support` bounds it
   once the two are written as `dirPoly`s; the `logPoly`/`dirPoly` dictionary is
   `Sieve/LogPolyDirPoly`.
2. The parameter choice: `Q`, `η`, `L` against `ε`, `W ≍ M/h` and the budget `εM²`, together with
   the prime counts `#P_j` (Chebyshev) and the harmonic mass `∑_{p∈P}1/p ≥ 15e/(2ε)` that
   `integral_Icc_normSq_logPoly_moebius_le_primeOffDiagonal` requires.

### Step 1 of the two: the product term (2026-08-18, continued)

    RHTower/Sieve/LogPolyProductScale.lean
      integral_Icc_comp_scale                   the substitution `t = 2πw` on a symmetric interval,
                                                for an arbitrary integrand
      logPoly_restrict                          restricting the index set of a Gallagher polynomial
                                                is a zero extension of its coefficients — so a
                                                polynomial over a finite set of primes is one over
                                                `Icc 1 N`
      integral_Icc_normSq_logPoly_mul_eq        **the mean square of a product of Gallagher
                                                polynomials is the rescaled Dirichlet one**
      integral_Icc_normSq_logPoly_mul_le_pow_prime_support
                                                **the threshold split for a product of Gallagher
                                                polynomials at a free exponent**, with the
                                                prime-supported factor's exceptional set measured
                                                by Lemma 2.5

So the term `∫_{|w|≤W}‖P_j·G_j‖²` of the assembled ladder is now bounded by an explicit expression:
`V^{2k}` times it is at most `(2π)^{-1}(V^{2k+2}·(mean square of the cofactor factor)
 + (sup)²(sup)²·2(2πW + 4N₂^k(1+log N₂^k))·k^k·(∑|b|²)^k)`.

### Remaining

Only the parameter choice: `Q`, `η`, `L`, `k` and `V` against `ε`, `W ≍ M/h` and the budget `εM²`,
together with the prime counts `#P_j` (Chebyshev) and the harmonic-mass condition
`∑_{p∈P}1/p ≥ 15e/(2ε)`.  Every inequality feeding into that arithmetic is an unconditional Lean
theorem.

### The parameter accounting kills the naive ordering — and the fix (2026-08-18, continued)

Doing the arithmetic on `integral_normSq_ramareBilinear_le_ladder_assembled` before optimising the
parameters shows it **cannot** close.  With `P` the primes of `(Q, P₂]`, `Q_j = Q(1+η)^j`,
`#P_j ≍ ηQ_j/log Q_j` and `L ≍ log P₂/η`, the error part of that bound is

```text
L·∑_j 4#P_j²·(3W + 7M)·(M(1+η)/Q_j + 5)  ≍  28 M² P₂ / log P₂ ,
```

which is never `o(M²)`.  The culprit is the ordering: `integral_normSq_ramareBlock_le_product`
applies Cauchy--Schwarz over `p` *inside* each block, producing `#P_j²`, and then the ladder
multiplies the whole thing — errors included — by `L`.

The fix is to pay the block count only on the product terms and to treat the discrepancy as a
single global error:

    RHTower/Sieve/RamareBlockSplit.lean
      ramareLadderError, continuous_ramareLadderError
      ramareBilinear_eq_ladder_add_error        **`B = ∑_{j<L} P_j·G_j + E`**, with `E` the total
                                                discrepancy of the ladder
      integral_normSq_ramareBilinear_le_ladder_error
                                                **`∫‖B‖² ≤ 2L·∑_j ∫‖P_j·G_j‖² + 2∫‖E‖²`** — the
                                                block count multiplies only the products

`integral_normSq_ramareBilinear_le_ladder_assembled` remains true and is kept as the baseline, but
the route to `o(M²)` goes through the separated form.

### Remaining

Bound `∫_{|w|≤W}‖E‖²` by the mean value theorem applied to `E` as a *single* Dirichlet polynomial —
its coefficient at `N` is `∑_{p ∣ N, p ∈ P} ±μ(p)c_{N/p}` over the discrepancy sets, so its `ℓ²`
mass is `≪ (log N/log Q)·∑_{p∈P}|D_p|`, one power of `#P` rather than two.  Then the parameter
choice.

### The accounting closes — with `M/Q²`, not `M/Q` (2026-08-18, continued)

Redoing the parameter arithmetic on the *separated* form found a second, decisive slack.  The
multiples term of `card_cofactor_symmDiff_le` was stated as `B₀/Q`, but the multiples of `p` in a
block of length `B₀/Q` number `≍ B₀/(Q·p)`, and `p > Q`, so the truth is `B₀/Q²`.  That single power
of `Q` is what decides the whole estimate:

```text
∑_{j,p} #(gap)  ≍  η·M·log(P₂/Q)/log Q  +  M/(Q log Q)  +  #P ,
```

where the first term now carries a factor `η` (it is `∑_j #P_j·Mη/Q_j ≍ ∑_j η²M/log Q_j`), the
second is the sharpened multiples term, and the third the additive constants.  With `η` at our
disposal the first term is `o(M log Q/log²M)` for `η = (log M)^{-2}`, which is exactly what the
mean value theorem on `E` needs — whereas with `M/Q` the term had no `η` and no choice of
parameters could work.

Both `card_cofactor_symmDiff_le` and `integral_normSq_cofactor_sub_common_le` now carry `B₀/Q²`, and
the change is propagated through `integral_normSq_ramareBlock_geom_le` and
`integral_normSq_ramareBilinear_le_ladder_assembled`.

With `log Q = (log M)^{0.9}`, `log P₂ = (log M)^{0.95}`, `η = (log M)^{-2}` and hence
`L ≍ (log M)^{2.95}`, the error side is `o(M²)`.  The product side needs
`∑_{j<L} ∫‖P_j·G_j‖² = o(M²/(log M)^{2.95})`, which is what the threshold split with Lemma 2.5
supplies.

### Remaining

1. `∫_{|w|≤W}‖E‖²` by the mean value theorem on `E` as a single Dirichlet polynomial of length
   `≤ M(1+η)` (the products `p·m` stay below `M(1+η)` because `m ≤ M/Q_j` and `p ≤ Q_j(1+η)`), with
   `ℓ²` mass `≪ (log M/log Q)·∑_{j,p}#(gap)`.
2. The product side, and the final parameter substitution.

### Every summand of the bilinear form is a Gallagher polynomial (2026-08-18, continued)

    RHTower/Sieve/PrimePhaseShift.lean
      primeShiftCoeff                           `n ↦ [p ∣ n]·μ(p)·c(n/p)`
      moebiusPhase_mul_logPoly                  **`μ(p)p^{2πiw}·∑_{m∈S}c_m m^{2πiw}
                                                  = ∑_{n ∈ pS} μ(p)c_{n/p} n^{2πiw}`** — multiplying
                                                by a prime phase shifts the index set
      primeShiftCoeff_eq_zero, norm_primeShiftCoeff_le

This is what makes the mean value theorem applicable to the ladder error *as a whole*: `E` is a sum
of Gallagher polynomials over the shifted sets `p·(C_j \ U_p)`, all contained in `[1, M(1+η)]`
because `m ≤ M/Q_j` and `p ≤ Q_j(1+η)`.  Extending each by zero to `Icc 1 ⌊M(1+η)⌋` (via
`Sieve/LogPolyProductScale.logPoly_restrict`) exhibits `E` as a single Gallagher polynomial whose
coefficient at `n` is `∑_{p ∣ n, p ∈ P} ±μ(p)c_{n/p}` — one power of `#P`, not two.

### Remaining

1. Assemble that coefficient identity and bound its `ℓ²` mass by
   `(number of designated prime divisors of n) · ∑_{j,p}#(gap)`, then apply
   `Sieve/SupportMeanSquare.integral_Icc_normSq_logPoly_le_energy`.
2. The product side, and the final parameter substitution
   (`log Q = (log M)^{0.9}`, `log P₂ = (log M)^{0.95}`, `η = (log M)^{-2}`, `L ≍ (log M)^{2.95}`).

### The mean value theorem for a sum of shifted polynomials (2026-08-18, continued)

    RHTower/Sieve/PrimePhaseShift.lean
      sum_logPoly_eq                            a sum of Gallagher polynomials over a common index
                                                set is one, with the coefficients added
      sum_normSq_overlap_coeff_le               **the `ℓ²` mass of a sum of unit-coefficient
                                                polynomials**: if every index is hit at most `K`
                                                times then
                                                `∑_n‖∑_i [n ∈ S_i] a_i(n)‖² ≤ K·∑_i #(S_i ∩ [1,N])`
                                                — *one* power of the number of summands, by
                                                `‖A_n‖² ≤ K‖A_n‖ ≤ K·#{i : n ∈ S_i}` and double
                                                counting
      integral_Icc_normSq_sum_logPoly_le        **the mean square of a sum of Gallagher
                                                polynomials**: `≤ (5πW/2 + 5eN/2)·K·∑_i #(S_i)`

This is the estimate the corrected accounting needs.  Applied to the ladder error, the summands are
the shifted sets `p·(C_j \ U_p)` (`Sieve/PrimePhaseShift.moebiusPhase_mul_logPoly`), every index
`n ≤ M(1+η)` is hit once per designated prime dividing it — so `K ≤ log(M(1+η))/log Q` — and
`∑_{j,p}#(C_j \ U_p)` is the gap sum already bounded by `card_cofactor_symmDiff_le`.  Cauchy--Schwarz
over the primes is never used, which is exactly the factor `#P` that the naive route lost.

### Remaining

1. Instantiate `integral_Icc_normSq_sum_logPoly_le` at the ladder error: the index family is
   `(j, p)`, the sets are `p·(C_j \ U_p)`, and `K` is the count of designated prime divisors.
2. The product side, and the final parameter substitution.

### The ladder error is a prime-shifted family (2026-08-18, continued)

    RHTower/Sieve/PrimePhaseShift.lean
      integral_Icc_normSq_primeShift_family_le  **the mean square of `∑_i μ(p_i)p_i^{2πiw}·
                                                ∑_{m∈D_i}c_m m^{2πiw}`**:
                                                `≤ (5πW/2 + 5eN/2)·K·∑_i #D_i`, with `K` the
                                                overlap count of the shifted sets.  No
                                                Cauchy--Schwarz over `i` anywhere

    RHTower/Sieve/RamareCofactorBlock.lean
      cofactorFilter_subset_common              the filtered cofactor set sits inside the common
                                                block (extracted from the discrepancy proof)

    RHTower/Sieve/RamareBlockSplit.lean
      ramareLadderError_eq_neg_sum              **`E = −∑_{j,p} μ(p)p^{2πiw}·
                                                logPoly c (C_j \ U_p)`** — the discrepancy is
                                                exactly the polynomial over the gap sets

So `E` is literally an instance of the prime-shifted family: `i = (j,p)`, `D_i = C_j \ U_p`, and the
`ℓ²` mass is `K·∑_{j,p}#(C_j \ U_p)`, both factors already bounded
(`K ≤ log(M(1+η))/log Q` from the count of designated prime divisors,
`∑_{j,p}#(C_j \ U_p)` from `card_cofactor_symmDiff_le`).

### Remaining

1. Flatten the double sum over `(j, p)` into a single index set and apply
   `integral_Icc_normSq_primeShift_family_le` — the side conditions are that `p·m ≤ M(1+η)`
   (already available: `m ≤ M/Q_j` and `p ≤ Q_j(1+η)`) and the divisor count `K`.
2. The product side, and the final parameter substitution.

### Step 1 closed: the ladder error's mean square (2026-08-18, continued)

    RHTower/Sieve/RamareBlockSplit.lean
      ladderGapSet, ladderIndex                 the `(step, prime)` gap sets and the flattened
                                                index set `(range L).sigma (geomBlock …)`
      ramareLadderError_eq_flat                 **`E = −∑_{x ∈ ladderIndex} μ(p_x)p_x^{2πiw}·
                                                logPoly c (gap_x)`**
      integral_normSq_ramareLadderError_le      **`∫_{|w|≤W}‖E‖² ≤ (5πW/2 + 5eN/2)·K·
                                                ∑_x #(gap_x)`**, where `N` bounds the shifted
                                                products `p·m` and `K` the overlap count

That is item 1 of the two remaining steps, in the exact form the accounting asked for: one power of
`K` (the number of designated prime divisors of an index, `≤ log N/log Q`) and one power of the
total gap size (bounded by `card_cofactor_symmDiff_le`).  Cauchy--Schwarz over the primes never
appears.

### Remaining

The product side and the final parameter substitution: `N = ⌊M(1+η)⌋`, `K ≤ log N/log Q`,
`log Q = (log M)^{0.9}`, `log P₂ = (log M)^{0.95}`, `η = (log M)^{-2}`, `L ≍ (log M)^{2.95}`, and
`∑_{j<L}∫‖P_j·G_j‖²` through `Sieve/LogPolyProductScale.integral_Icc_normSq_logPoly_mul_le_pow_prime_support`.

### Both side conditions discharged (2026-08-18, continued)

    RHTower/Sieve/RamareBlockSplit.lean
      ladderGap_image_subset                    **every shifted index stays below `M(1+η)`** — a
                                                cofactor of the `j`-th step is `≤ M/Q_j` and its
                                                prime `≤ Q_j(1+η)`
      ladderIndex_filter_card_le                **the overlap count is at most the number of
                                                designated primes dividing the index** — the steps
                                                are disjoint, so a prime determines its step and
                                                `x ↦ p_x` is injective on the fibre
      integral_normSq_ramareLadderError_le_divisorCount
                                                the ladder error with both side conditions
                                                discharged: `N = ⌊M(1+η)⌋` and the only remaining
                                                input is a bound `K` on `#{p ∈ P : p ∣ n}`

### Remaining

1. `#{p ∈ P : p ∣ n} ≤ log n / log Q` (the designated primes exceed `Q` and their product divides
   `n`), and the gap sum `∑_x #(ladderGapSet …)` from `card_cofactor_symmDiff_le`.
2. The product side, and the final parameter substitution.

## The proof skeleton, taken from the source (2026-08-18)

Séminaire Bourbaki 1119 (Soundararajan, June 2016), *The Liouville function in short intervals
[after Matomäki and Radziwiłł]*, arXiv:1606.08021.  Its §3 is a **complete, self-contained proof**
of the short-interval mean square for `h ≥ exp((log X)^{3/4})`, and §4 extends it to
`h ≥ exp(10(log log X)^{10/9})`.  Both use only Lemmas 2.1–2.6, every one of which this corpus
already owns.  The programme is therefore no longer open-ended: it is the assembly of §3, then §4.

### The §3 argument, step by step

Ranges.  `P` = the primes in `[exp((log h)^{9/10}), h]`; `P_j` = the primes of `P` in the *dyadic*
block `(2^j E, 2^{j+1} E]`, `E = exp((log h)^{9/10})`, `0 ≤ j ≤ J = ⌊(log h − (log h)^{9/10})/log 2⌋`.
Two constraints fix this choice: every `p ∈ P` must be `≤ h` (so the cofactor polynomial has length
`≥ X/h`, which is what makes the mean value theorem efficient), and every `p ∈ P` must exceed
`exp((log X)^{2/3+δ})` (so Lemma 2.3 applies) — `(log h)^{9/10} ≥ (log X)^{27/40}` and `27/40 > 2/3`.

1. **(20)–(21) the weighted polynomial.**  `A(y) = ∑_n a(n)n^{iy}` with `a(n) = λ(n)ω_P(n)` on
   `[X,2X]`, written as `∑_j ∑_{p∈P_j} ∑_{X/P_{j+1} ≤ m ≤ 2X/P_j} λ(p)p^{iy}λ(m)m^{iy}`.
   The weight is `ω_P` — Turán–Kubilius — **not** Ramaré's `1/ω_P`.  For `λ` the factorisation is
   exact; for `μ` the cofactor sum carries the extra condition `p ∤ m`, again exactly.
2. **(22)–(24) removing the weight.**  `∑_{X≤n≤2X}(ω_P(n) − W(P))² ≪ X W(P)`,
   `W(P) = ∑_{p∈P} 1/p ∼ (1/10) log log h`, so
   `W(P)² ∫(∑_{x<n≤x+h}λ)² ≪ ∫(∑ λω_P)² + X h² W(P)`, and Lemma 2.2 converts the second factor
   into `(X/W(P)²)∫|A(y)|² min(h²/X², 1/y²) dy + Xh²/W(P)`.
3. **(25) the tail `|y| > X`** is `≪ W(P)²` by dyadic splitting and Lemma 2.4.
4. **(26)–(27) Cauchy–Schwarz over the blocks, with harmonic weights.**
   `|A(y)|² ≤ (∑_j 1/log P_j)(∑_j log P_j |∑_{p∈P_j}p^{iy}|² |∑_m λ(m)m^{iy}|²)`,
   and `∑_j 1/log P_j ≪ W(P)`, giving `∫ ≪ W(P)² max_j I_j` with
   `I_j = (log P_j)² ∫_{-X}^{X} |∑_{p∈P_j}p^{iy}|² |∑_m λ(m)m^{iy}|² min(h²/X², 1/y²) dy`.
5. **(28) `log P_j ≤ |y| ≤ X`.**  Lemma 2.3 gives `∑_{p∈P_j} p^{iy} ≪ (P_j/log P_j)(1/(1+|y|) +
   1/log P_j)`; splitting the `y`-integral at `X/h` and dyadically above it and using Lemma 2.4
   gives `I_j ≪ h²/(log P_j)²`.
6. **(29)–(30) `|y| ≤ log P_j`.**  Lemma 2.3 applied to the *cofactor* sum gives
   `∑_m λ(m)m^{iy} ≪ (X/P_j)(log X)^{-10}`, and the prime sum is bounded trivially:
   contribution `≪ h²(log X)^{-19}`.
7. **Conclusion.**  `∫_X^{2X}(∑_{x<n≤x+h}λ(n))² dx ≪ Xh²((log h)^{-9/5} + W(P)^{-1} + h^{-2})
   ≪ Xh²/log log h`.

### Where the rate comes from, and what still separates this from the cards

The *good* term is `(log h)^{-9/5}` — essentially Menon's `(log h)^{-2}`.  The bottleneck is the
`1/W(P) ≍ 1/log log h` produced by the Turán–Kubilius step 2.  MR's own arrangement (exposé §6,
(51)) replaces that weight by a restriction to `S` = integers with a prime factor in `P`, whose
sieve loss is `X/(log h)^{1/10}` — the density of integers with no prime factor in
`[exp((log h)^{9/10}), h]`.  So:

| arrangement | rate |
|-|-|
| §3/§4 as written (Turán–Kubilius weight) | `1/log log h` |
| §6 (restriction to `S`) | `(log h)^{-1/10}` |
| the good term inside both | `(log h)^{-9/5}` |
| what the three cards need | `o(1/log Y)`, i.e. `(log h)^{-1/β}` with `log h = (log Y)^β` |
| Menon 2026 | `(log log L)²/(log L)²` |

The sieve loss of a *single* range `[P_1, h]` is `≍ log P_1/log h`, so no choice of `P_1` inside a
single range beats `1/log h`; the cards need `o(1/log Y) = o((log h)^{-1/β})` with `1/β < 2`.
Closing the gap between `(log h)^{-1/10}` and `(log h)^{-2}` is exactly Menon's refinement, and it
must come from treating the non-`S` integers with cancellation rather than trivially.

### Consequence for the Lean plan

Milestone A is now **the assembly of §3**, in the Gallagher/Plancherel shape this corpus already
consumes: `Sieve/FibreWindowBridge.averagedMeanSquare_of_spectralPoly` asks for exactly
`(1/h²)∫_ℝ ‖logWindowKernel δ w‖²‖logPoly μ (fibreIndex x h) w‖² dw → 0` with `δ = fibreWidth x h`,
which *is* the exposé's `∫|A(y)|² min(h²/X², 1/y²) dy` after `X ↦ M = ⌊√x + h⌋`.  So the affine
majorant is no longer the interface to aim at — the spectral one is, and it matches the source.

The Ramaré ladder built up to now (`Sieve/Ramare*`, `Sieve/LadderErrorBudget`) is the §6
arrangement, not the §3 one; it stays, because §6 is where the rate is improved, but §3 is the
shorter road to a first unconditional short-interval theorem and is built on the *same* Lemmas
2.3–2.6.

### The §3 brick list

| step | Lean status |
|-|-|
| Lemma 2.1 Plancherel | `Sieve/LogWindowPlancherel` ✓ |
| Lemma 2.2 Saffari–Vaughan | not needed — the corpus window is already multiplicative ✓ |
| Lemma 2.3 twisted `λ`/`μ` and prime sums | `Sieve/RouteTMoebiusPowerSaving`, `Sieve/VonMangoldtTwistPrimeEnvelope` ✓ |
| Lemma 2.4 mean value theorem | `Sieve/DirichletIntegralBound`, `Sieve/SupportMeanSquare` ✓ |
| Lemma 2.5 large values, free exponent | `Sieve/DirichletPower{Convolution,PrimeSupport,Measure}` ✓ |
| Lemma 2.6 Halász–Montgomery | `Sieve/HalaszMontgomeryDyadic`, `Sieve/DyadicSecondEnvelopeClosed` ✓ |
| Turán–Kubilius `(22)` | `Sieve/TuranKubilius.sum_omegaCount_variance_le` ✓ |
| `(20)`–`(21)` the `ω_P`-weighted factorisation | **to build** |
| `(26)`–`(27)` harmonic Cauchy–Schwarz over dyadic blocks | **to build** |
| `(28)` the `y`-split and its mean-value estimates | **to build** |
| `(29)`–`(30)` the small-`y` range | **to build** |
| the assembly | **to build** |

### Milestone A, front half — landed (2026-08-18)

Steps `(20)`–`(24)` of the exposé are now unconditional Lean theorems, and the whole short-interval
input of the three Route E cards is reduced to a spectral bound on the **`ω_P`-weighted** Möbius
polynomial — the object that factors exactly.

| module | content |
|-|-|
| `Sieve/OmegaWeightedFactorisation` | `omegaWeightedMoebiusPoly`, `omegaWeightedMoebiusPoly_eq_sum` (double counting), **`omegaWeightedMoebiusPoly_eq_bilinear`** — the factorisation `∑_n μ(n)ω_P(n)n^{2πiw} = ∑_{p∈P} μ(p)p^{2πiw}·∑_{m, p∤m} μ(m)m^{2πiw}`, **exact, with no error term**, the indices whose cofactor still carries `p` vanishing because `pm` is not squarefree; `omegaWeightedMoebiusPoly_eq_blocks` splits it over any partition of `P` |
| `Sieve/TuranKubiliusRange` | `primesRange z₀ z`, `card_primeFactorsIn_primesRange` (the range count is the difference of two initial-segment counts), `sum_inv_primesRange` (harmonic mass `= mertensS z − mertensS z₀`), **`sum_variance_primesRange_le`** — Turán–Kubilius for a *range* of primes |
| `Sieve/WeightRemovalFibre` | `sq_sum_le_weighted_add_variance` (undoing an arbitrary weight on one index set), `card_outer_of_mem_innerFibre_le` (each index lies in `≤ 2h+1` fibres), **`sum_sq_fibreSum_le_weighted`** — the averaged cost, with `g` an arbitrary real weight |
| `Sieve/OmegaWeightTransfer` | `fibreDyadicIndex_eq_Ioc`, `sum_variance_fibreDyadicIndex_le`, **`sum_sq_fibreSum_le_omegaWeighted`** — step `(22)`–`(24)` for the corpus's fibre objects |
| `Sieve/ScaledFibreBridge` | `logWindowSum_div`, **`sum_fibreSum_sq_le_integral_scaled`** — the fibre→window bridge for a weight of arbitrary size `B` (the corpus version assumed `|f| ≤ 1`, and `μ·ω_P` is not unit bounded) |
| `Sieve/OmegaSpectralFibre` | `logPoly_omegaWeighted_eq`, **`sum_sq_fibreSum_moebius_le_omegaSpectral`**, `omegaBudget`, **`averagedMeanSquare_moebius_of_omegaBudget`**, **`averagedShortInterval_moebius_of_omegaBudget`** |

The capstone, with every constant explicit and no asymptotic notation:

```text
(S(z) − S(z₀))² · ∑_a (∑_{b ∈ F_a} μ(b))²
  ≤ 16√x ∫_ℝ ‖K_δ(w)‖² ‖A_ω(w)‖² dw
    + 204 (|P| + 1)² (√x + 1)
    + 2(h+1)(2h+1)( 4(√x/2 + h + 1) S(z) + 4π(z) + 8π(z)² ) ,
```

`δ = fibreWidth x h`, `P = primesRange z₀ z`, `A_ω = omegaWeightedMoebiusPoly P (fibreIndex x h)`.

At the parameters of the argument (`z = h`, `log z₀ = (log h)^{9/10}`, so `S(z) − S(z₀) ≍ (1/10)
log log h`) the last two lines divided by `(S(z) − S(z₀))² h² √x` are `≍ 1/(log h)²(log log h)²` and
`≍ 1/log log h` respectively — both vanish, and the second is exactly the `1/W(P)` bottleneck the
skeleton section above identifies.

**What is left of Milestone A** is the estimate of the spectral integral itself: steps `(26)`–`(30)`,
i.e. the harmonic Cauchy–Schwarz over dyadic prime blocks and the two `y`-ranges.  The factorisation
those steps consume is `omegaWeightedMoebiusPoly_eq_blocks`; the estimates they consume are Lemmas
2.3 and 2.4, both already in the corpus.

### The parameter analysis of `(26)`–`(30)` in the corpus's own objects (2026-08-18)

`Sieve/HarmonicCauchySchwarz` is landed: `normSq_sum_le_weighted`, `normSq_sum_mul_le_weighted` —
`‖∑_i F_i‖² ≤ (∑_i 1/v_i)(∑_i v_i‖F_i‖²)` for arbitrary positive weights.  The choice of `v` is what
decides whether the split costs the *number* of blocks or their *harmonic mass*, and the corpus's
blocks are not the exposé's, so the analysis has to be redone here.  It was, and it closes.

**Blocks must be thin, and the weights must be harmonic-mass reciprocals.**  The exposé's blocks are
dyadic, so `∑_j 1/log P_j ≍ W(P)` with `v_j = log P_j`.  The corpus's ladder (`geomBlock P Q (1+η) j`)
is thin, ratio `1 + η`, so `v_j = log Q_j` would cost `L/log Q`, not `W(P)`.  With `v_j` the
reciprocal of the block's harmonic mass — `v_j ≍ 1/η` — one gets `∑_j 1/v_j = W(P)` for *any*
subdivision.  Use that.

**The enlarged support, and why the error is harmless.**  Making the cofactor range depend only on
the block, not on the prime, changes the polynomial's coefficients from `μ(n)ω_P(n)` to

    c(n) = ∑_j ∑_{p ∈ B_j, p ∣ n, n/p ∈ D_j} μ(p)μ(n/p) ,   D_j = [M₀/Q_{j+1}, M₁/Q_j] ,

and `c(n) = μ(n)ω_P(n)` for every **squarefree** `n ∈ [M₀, M₁]`.  The discrepancy `e = c − μ·ω_P` is
supported on

* `n ∈ [M₀, M₁]` divisible by `p²` for some designated `p` — at most `M₁ ∑_{p ∈ P} 1/p² ≤ M₁/E`;
* `n ∈ (M₀/(1+η), M₀) ∪ (M₁, M₁(1+η)]` — at most `2M₁η + 2`;

and `|e(n)| ≤ ω_P(n) ≤ log M₁ / log E`, because designated primes exceed `E`
(`Sieve/LadderErrorBudget.card_designatedPrimes_dvd_le`).  **Do not bound `|e(n)|` by `|P|`** — that
is `≍ h/log h` and makes the accounting fail by a power of `h`; the divisor-count bound is what makes
it work.

**The two constraints on `η`, and the exponent they force.**  Write `log h = (log x)^β`,
`log E = (log h)^{9/10}`, `δ = fibreWidth ≍ h/M₁`, `M₁ ≍ √x`.

| constraint | source | requirement |
|-|-|-|
| `δ²·M₁·∑_n|e(n)|² = o(W²h²)` | the enlarged-support error | `η ≪ W²(log E/log M₁)² ≍ (log x)^{9β/5−2}` |
| `L·h²/(log Q)⁴ = o(W η h²)`, `L ≍ W/η` | summing `(28)` over the thin blocks | `η ≫ (log Q)^{-2} = (log x)^{-9β/5}` |

The two are compatible exactly when `18β/5 > 2`, i.e. **`β > 5/9`** — the same threshold as the
exposé's good term `(log h)^{-9/5}`, which is the arithmetic reason it appears.  So the §3 route, run
in the corpus's own thin-block objects, reaches every `β > 5/9`, and the cards' range `β ∈ (1/2, 1)`
is covered above `5/9` by the *spectral* estimate.

**What still blocks the cards is not the spectral estimate.**  At `β > 5/9` the spectral side gives
`(log h)^{-9/5}`, which is `o(1/log Y)` when `9β/5 > 1` — true.  The obstruction is the
Turán–Kubilius loss `1/W(P) ≍ 1/log log h` in `omegaBudget`, and the sieve loss `(log h)^{-1/10}` of
the §6 arrangement that replaces it.  Both are *arithmetic* losses in removing the weight, not
analytic ones.  Closing them is Menon's refinement and is the last milestone.

### Next bricks, in order

1. `geomCofactorBlockTwoSided M₀ M₁ Q η j := Icc ⌈M₀/(Q(1+η)^{j+1})⌉₊ ⌊M₁/(Q(1+η)^j)⌋₊`, and the
   product polynomial `∑_j primeBlockPoly (geomBlock P Q (1+η) j) · logPoly μ (D_j)`.
2. The coefficient comparison `c(n) = μ(n)ω_P(n)` on squarefree `n ∈ [M₀, M₁]`, and the two support
   bounds above for `e`.
3. `∑_n |e(n)|² ≤ (log M₁/log E)²(M₁/E + 2M₁η + 2)`, then the mean value theorem for `∫‖K_δ‖²‖E‖²`.
4. The harmonic split with `v_j` = reciprocal block harmonic mass.
5. `(28)`: the `y`-split for one block, from Lemma 2.3 and the mean value theorem.
6. `(29)`–`(30)`: the range `|y| ≤ log Q_j`, trivially.

### Milestone A, the spectral side — assembled (2026-08-18, continued)

Bricks 1, 2, 4, 5 of the list above are Lean theorems, and the whole `(26)`–`(28)` layer is now a
single statement.

| module | content |
|-|-|
| `Sieve/TwoSidedCofactorBlock` | `geomCofactorBlockAt`, `ladderGapSetAt`, `card_ladderGapSetAt_le`, `sum_card_ladderGapSetAt_le` — the cofactor block and its gap budget over a two-sided range of indices, which is what the fibres need (they live on a dyadic block, not an initial segment) |
| `Sieve/LadderProductDefect` | `cofactorFilter_subset_common_at`, `moebiusCoeff`, `ladderProductPoly`, `ladderProductDefect`, **`ladderProductPoly_sub_omegaWeighted_eq`** (the weighted polynomial *is* the ladder of genuine products minus one prime-shifted family), `ladderIndex_filter_card_le_gen`, `ladderGapSetAt_image_subset`, **`integral_normSq_ladderProductDefect_le_closed`** |
| `Sieve/HarmonicCauchySchwarz` | `normSq_sum_le_weighted`, `normSq_sum_mul_le_weighted` |
| `Sieve/LadderHarmonicSplit` | `stepMass`, **`sum_stepMass_eq`** (the step masses add to the harmonic mass of `P` for *every* subdivision — the reason thin blocks are free), `normSq_ladderProductPoly_le`, `integral_normSq_ladderProductPoly_le` |
| `Sieve/LadderBlockMeanSquare` | **`integral_normSq_ladderStep_le`** (one step: a pointwise bound on the prime polynomial times the mean value theorem for the cofactor polynomial), `card_geomCofactorBlockAt_le` |
| `Sieve/OmegaWeightedLadderBound` | `continuous_*`, `integral_normSq_omegaWeighted_le_split`, **`integral_normSq_omegaWeighted_le`** |

The capstone:

```text
∫_{|w| ≤ W} ‖A_ω(w)‖² dw
  ≤ 2 (∑_j 1/v_j)(∑_j v_j · V_j² · (5π/2·W + 5e/2·⌊B₀/Q_j⌋)(B₀/Q_j + 1))
    + 2 (5π/2·W + 5e/2·⌊B₀(1+η)⌋)( log⌊B₀(1+η)⌋/log Q · ∑_j (Q_j η + 1)((A₀+B₀)η/Q_j + 5 + B₀/Q_j²) )
```

for every positive weight family `v` and every `V` bounding `‖∑_{p ∈ P_j} μ(p)p^{2πiw}‖` on the
window.  **The only analytic input left in the spectral side is `V`** — that is Lemma 2.3, already
proved in the corpus (`Sieve/VonMangoldtTwistPrimeEnvelope`, `Sieve/RouteTMoebiusPowerSaving`).
Everything else is explicit in `A₀, B₀, Q, η, L, W`.

Remaining for Milestone A:
1. instantiate `V j` from the Route-T twisted prime-sum layer, and `v j = 1/stepMass`;
2. pass from `∫_{|w| ≤ W}` to the Gallagher-weighted `∫_ℝ ‖K_δ‖²‖·‖²` that `omegaBudget` holds, via
   `Sieve/GallagherDyadicTail.gallagher_split_integral_dyadic`;
3. the range `|w| ≤ log Q_j`, exposé `(29)`–`(30)`;
4. the parameter substitution (`η` inside the window `(log x)^{-9β/5} ≪ η ≪ (log x)^{9β/5−2}`).

### Milestone A — the chain is closed except for the parameter arithmetic (2026-08-18, continued)

Three further modules complete the *structure* of the §3 proof in Lean.

| module | content |
|-|-|
| `Sieve/PrimeBlockTwistBound` | `unitLogPhase_eq_cpow`, `primeTwist_eq_unitLogPhase`, `moebiusPhase_prime_eq_neg_primeTwist`, `primeBlockPoly_eq_neg_sum`, `sum_primeTwist_range_eq`, `norm_primeBlockPoly_le_of_range`, **`exists_norm_primeBlockPoly_routeT_le`** — the prime polynomial of a ladder step *is* the twisted prime sum `−∑_{p ∈ (a,b]} p^{2πiw}`, so the Route-T (Vinogradov–Korobov) envelope bounds it directly.  **This is the single analytic input of the whole argument, and it is now connected.** |
| `Sieve/AffineMajorantFromHeight` | `integral_normSq_logPoly_mono`, **`affineMajorant_of_bound_at`** — Gallagher's split needs a majorant at *every* height, while a cancellation estimate only holds up to the height its analytic input allows.  Below that height the mean square is monotone; above it the mean value theorem is already affine with the right slope.  One bound at `T₀` therefore suffices. |
| `Sieve/OmegaBudgetFromLadder` | `omegaCoeff`, `logPoly_omegaCoeff_eq`, `energy_omegaCoeff_le`, **`integral_kernel_normSq_omegaWeighted_le`** — the Gallagher-weighted spectral integral, which is exactly the integral inside `omegaBudget`, from a ladder bound at one height |

The chain that the three Route E cards now rest on, end to end and unconditional:

```text
AveragedShortInterval μ hh                                   ← averagedShortInterval_moebius_of_omegaBudget
  ← omegaBudget → 0                                          ← OmegaSpectralFibre
  ← ∫_ℝ ‖K_δ‖²‖A_ω‖² small                                    ← integral_kernel_normSq_omegaWeighted_le
  ← ∫_{|w| ≤ T₀} ‖A_ω‖² ≤ β₀                                  ← integral_normSq_omegaWeighted_le
  ← ‖∑_{p ∈ P_j} p^{2πiw}‖ ≤ V j                              ← exists_norm_primeBlockPoly_routeT_le  ✓ PROVED
  + the parameter substitution                                ← OPEN
```

**What is open is now exactly two things, and neither is structural:**

1. *The parameter arithmetic.*  Choose `A₀ = ⌈√x/2⌉`, `B₀ = ⌊√x + h⌋`, `z₀ = exp((log h)^{9/10})`,
   `z = h`, `Q = z₀`, `L` and `η` inside the window `(log x)^{-9β/5} ≪ η ≪ (log x)^{9β/5−2}`,
   `T₀` at the height the Route-T envelope still saves at, `W = M/h`, `v j = 1/stepMass`, and verify
   the resulting limit.  This is asymptotic analysis of `routeTTwistEnvelope`, not new mathematics.
2. *The rate.*  Even when 1 is done, the arrangement gives `1/log log h` (Turán–Kubilius) and the
   §6 arrangement gives `(log h)^{-1/10}`; the cards need `(log h)^{-1/β}` with `β > 1/2`.  That gap
   is Menon's refinement and is the last milestone.  It is an *arithmetic* loss in removing the
   weight, not an analytic one — the spectral side already delivers `(log h)^{-9/5}`.

### The Route-T envelope made elementary — `Sieve/RouteTWidthExplicit` (2026-08-18, continued)

The parameter substitution cannot be done against `routeTTwistEnvelope` as stated, because its
exponents contain `routeTUniformRegWidth`, which is not an elementary expression.  It is needed only
through two consequences, and both are now proved:

- `routeTUniformRegWidth_le_delta_half` : the width is at most `delta/2` (upper exponent);
- **`routeTWidthPolylogLower`**, `routeTWidthPolylogLower_pos`, **`routeTWidthPolylogLower_le`** :
  the width is at least `1/(10 D_A Z^{9/10}(1 + log Z)²)` with `Z = 2 log(6|τ| + 6) + 1`, for
  `|τ| ≥ 16π/3`, from `RouteTZetaAsymptotics.routeTZeroFreeDelta_polylog_lower`;
- `routeTTwistHeightFactor_le_explicit` : the same substitution in the height factor;
- `rpow_one_sub_eq`, `rpow_one_add_eq`, and **`routeTTwistEnvelope_le_exp`** :

```text
routeTTwistEnvelope A delta C τ x
  ≤ C·( 3x·exp(−(min(delta, κ(τ))/6)·log 3x)·(H(τ) + log 2x)
      + 3x·exp((delta/3)·log 3x)·(1 + (log x)² + H(τ))/(1+|τ|) )
    + 2√x·log x ,
```

`κ(τ) = routeTWidthPolylogLower A τ ≍ 1/((log|τ|)^{9/10}(log log|τ|)²)`.  Everything is elementary:
the saving is the exponential `exp(−c·log x/((log|τ|)^{9/10}(log log|τ|)²))`, which beats every power
of `log x` exactly when `log x ≫ (log|τ|)^{9/10}·polylog` — the arithmetic reason the ladder must
start at `Q = exp((log h)^{9/10})` and the reason the range `β > 5/9` appears.

This is the last piece of *machinery* before the parameter substitution itself; what remains there is
choosing the parameters as functions of `x` and verifying one limit.

## The rate obstruction is now pinned down exactly (2026-08-18)

Two *lower bounds on the loss* of the two standard arrangements, both elementary, both fatal for the
Route E cards.  They are recorded because they close off routes, not because they are hard.

**1. The Turán–Kubilius arrangement cannot beat `1/log log h`.**  Its cost divided by the trivial
size is `≍ (variance sum)/(W(P)²√x)`, and Turán–Kubilius gives variance `≍ |D|·W(P)`, so the loss is
`≍ 1/W(P)`.  Since `ω_P` is Poisson of mean `W(P)`, its relative standard deviation is `W(P)^{-1/2}`
and the square of that is irreducible for *any* weight of this shape.  And `W(P) ≤ log log h`,
because the designated primes must lie **below `h`** — otherwise the cofactor polynomial is shorter
than the window `T = M/h` and the mean value theorem loses.  So the loss is `≥ 1/log log h`.

**2. The restriction arrangement (MR §6) cannot beat `1/log h`.**  Its cost is the density of
integers with no designated prime factor, which for `P` = primes in `[P₁, h]` is `≍ log P₁/log h`,
minimised at `P₁ = 2` where Mertens gives `≍ e^{-γ}/log h`.

The cards need `o(1/log Y)` with `log h = (log Y)^β`, `β < 1`.  `1/log h = (log Y)^{-β}` is *larger*
than `1/log Y`.  **So both standard arrangements fail for every `β < 1`, and no choice of parameters
rescues either.**  The integers carrying no designated prime factor must be treated with
cancellation, not discarded — that is the whole content of the missing refinement.

**Why the obvious repair does not work either.**  Every `n ≤ M` is either `M^{1/u}`-smooth (density
`ρ(u) ≈ u^{-u}`, which beats every power of `log M` at `u = (log M)^{1/10}`) or has a prime factor
above `M^{1/u}`, to which the Route-T twisted bound applies.  But a prime `p > h` cannot be used for
the *product* structure: the step's contribution is `V_j²·T·(M/Q_j)` with `V_j ≍ Q_j·E_j`, so `Q_j`
appears with a **net positive** power and the ladder sum is `≍ T·M·R₂·E²/η²`, which for `R₂` up to
`M` exceeds the target by a factor `M/h`.  This is exactly MR's remark that the primes must lie
below `h`.  Large primes are therefore usable only through *large values* (exposé §4's set `Q`),
never through a pointwise bound.

## The cited source could not be located (2026-08-18)

The three cards attribute `(6)` to "Menon's Theorem 1.1 (2026)".  Searches of arXiv for a paper with
that rate — `(log log L)²/(log L)² + (log log Y)⁴/(log Y)²` — returned nothing; the neighbouring
literature (Matomäki–Radziwiłł 2016 and *Multiplicative functions in short intervals II*,
arXiv:2007.04290, the Bourbaki exposé arXiv:1606.08021, Matomäki–Radziwiłł–Tao, and the
divisor-bounded and higher-uniformity papers) carries rates of the form `(log h)^{-δ}` with `δ`
small, or power-saving statements about the *exceptional set* rather than the rate.

This does not change what has to be proved — the required statement is unambiguous, and the shape
`(log log L)²/(log L)²` is exactly the Halász bound for `μ` at scale `L`, i.e. optimal for the
method.  It changes only the plan: the input has to be **derived here**, not transcribed from a
source.  Anyone continuing this lane should treat `(6)` as an open target of this project, and
should not spend further time looking for the citation.

## The rate obstruction dissolves: a route that closes for exactly `β > 1/2` (2026-08-18)

The two lower bounds recorded above are correct but they bound the wrong things, and the second one
in particular rests on a step of the exposé that is itself lossy.  Redoing that step gives an
architecture that reaches the cards' requirement for every `β ∈ (1/2, 1)`.

### The crude step, and what it costs

Exposé `(51)` bounds the contribution of the integers *outside* `S` by
`∫_X^{2X} h·(∑_{x<n≤x+h, n ∉ S} 1) dx = h²·#S^c`, i.e. it applies Cauchy–Schwarz with the **window
length** before integrating.  Doing the second moment directly instead,

```text
∫_Y^{2Y} ( ∑_{x < n ≤ x+L, n ∉ S} 1 )² dx
  = ∑_{m,n ∉ S, |m−n| < L} (L − |m−n|)
  ≤ L ( #S^c + ∑_{0<|d|<L} #{m ≤ 2Y : m ∉ S and m+d ∉ S} ) ,
```

and the shifted count is a two-dimensional sieve: for `S^c` = integers with no prime factor in
`[P₁, h]` it is `≪ Y·(log P₁/log h)²·(d/φ(d))`.  So

```text
∫_Y^{2Y} ( ∑_{x<n≤x+L, n ∉ S} 1 )² dx  ≪  L·Y·(log P₁/log h)  +  L²·Y·(log P₁/log h)² ,
```

against a trivial size `L²Y`.  **The loss is the density squared, not the density.**  That single
factor is the difference between `1/log h` and `(log h)^{-2}` — exactly the gap between MR's stated
rate and the rate the cards need.

### The arrangement must be Ramaré, not Turán–Kubilius

With `S` defined by "has a prime factor in `P`", the decomposition of `∑_{n ∈ S}` is **Ramaré's
identity**, which is exact and carries no weight-removal cost at all (`Sieve/RamareWeight`,
`sum_eq_ramare_add_rough` — the remainder is *precisely* `S^c`).  The `ω_P` weight of exposé §3 is
what forces the `1/W(P) ≍ 1/log log h` loss; the `1/ω_P` weight has no such loss.  So the ladder
built earlier this session (`Sieve/Ramare*`, `Sieve/LadderErrorBudget`, `Sieve/PrimePhaseShift`) is
the right arrangement, and the `ω_P` layer is the wrong one for the *rate* (it remains correct, and
is the shorter road to a first theorem).

### The parameter window

Put `log P₁ = (log h)^a`, `log h = (log Y)^β`.  The cards need every contribution `o(1/log Y)`.

| contribution | size | requirement |
|-|-|-|
| rough part, second moment | `(log h)^{2a−2}` | `2 − 2a > 1/β`, i.e. `a < 1 − 1/(2β)` |
| `S` part, spectral | `(log P_j)^{-2A}` at threshold `V_j = P_j/(log P_j)^A` | any `a > 0`, by taking `A` large |

The second row is the point.  In exposé §4 the threshold is `P_j/(log P_j)²` and the saving is
`(log P_j)^{-2}`, but `2` is an arbitrary choice: Lemma 2.5 bounds the exceptional set by
`(V² log T)^{1 + log T/log P}`, and the constraint that made §4 work was only `|E_j| ≪ X^{3/7+ε}`.
With `V_j = (log P_j)^A` that constraint reads `2A log log X ≲ (log h)^a`, so `A` may be taken as
large as `(log X)^{aβ}/log log X` — a *power of log*, not a constant.  The spectral saving is
therefore effectively unconstrained, and imposes no lower bound on `a`.

So the admissible range is `0 < a < 1 − 1/(2β)`, which is **non-empty exactly when `β > 1/2`** —
precisely the card's hypothesis `1/2 < β < 1`, and precisely the place where the card's own
arithmetic `2β > 1` enters.  That coincidence is the check that this is the right route.

### Consequences for the build

1. The `ω_P` layer (`OmegaWeighted*`, `TuranKubilius*`, `WeightRemoval*`) stays — it is a complete,
   independent road to a first unconditional short-interval theorem at rate `1/log log h`, and every
   spectral module it feeds (`Ladder*`, `HarmonicCauchySchwarz`, `RouteTWidthExplicit`) is shared.
2. The road to the **cards** goes through the Ramaré ladder instead, and needs two new things:
   - **the shifted rough-pair count** `#{m ≤ Y : m, m+d both free of primes in [P₁,h]} ≪ Y(log P₁/log h)²·d/φ(d)` — a two-dimensional sieve, for which the corpus already has `Sieve/ShiftedCongruenceCount`, `Sieve/JointCongruence*`, `Sieve/TruncatedPair*` and the Selberg/Brun–Titchmarsh layer in `PNTPlus`;
   - **the exceptional-set layer of exposé §4** at a free threshold exponent `A`, from `Sieve/DirichletPower{Convolution,PrimeSupport,Measure}` (Lemma 2.5, already free-exponent) and `Sieve/HalaszMontgomeryDyadic` (Lemma 2.6).
3. This derivation is my own and is not checked against a source; the §4 exceptional-set accounting
   at a free threshold is the step most worth re-deriving before it is formalised.

### The rough second moment, in the corpus's own fibres — `Sieve/FibreRoughSecondMoment` (2026-08-18)

The first brick of the new road is built, and it is sharper than the sketch above.

- **`sum_sq_card_fibre_inter_eq`** : `∑_a #(F_a ∩ T)² = ∑_{m,n ∈ T ∩ D} K(m,n)` — an *identity*, for
  any set `T`, against the fibre kernel `K(m,n) = #{a : m, n ∈ F_a}`;
- **`fibre_kernel_band_width`** : if `m` and `n` share a fibre then `max − min ≤ h` (not `2h`): the
  same outer factor gives `a·max ≤ x + h√x` and `a·min ≥ x` with `a ≥ √x`, so the gap is at most
  `h√x/a ≤ h`;
- `fibreDyadicIndex_ge`, and **`sum_sq_card_fibre_inter_le_band`** :

```text
∑_{a ∈ outerBlock} #(F_a ∩ T)²  ≤  (2h + 1) · #{ (m,n) ∈ (T ∩ D)² : |m − n| ≤ h } .
```

So the entire cost of discarding `T` is its **banded shifted pair count**, and nothing else.  With
`T` the integers free of primes in `[P₁, h]` this is the two-dimensional sieve
`∑_{|d| ≤ h} #{m : m, m+d both free of primes in [P₁,h]} ≪ h·M·(log P₁/log h)²`, which is the
`(log h)^{-2}` the cards need.  **The remaining arithmetic input on this road is exactly that sieve
bound** — no analytic input at all.

### The shifted-rough-pair sieve, set up — `Sieve/RoughPairSieve` (2026-08-18)

The remaining arithmetic input is now a `SelbergSieve` instance in the corpus, using the
Selberg machinery vendored in `PNTPlus/Mathlib/NumberTheory/Sieve/` (whose one-dimensional
instantiation `BrunTitchmarsh.primeInterSieve` is the template).

- `rangePrimes P₁ h`, `rangePrimorial P₁ h`, `squarefree_prod_of_prime`,
  `rangePrimorial_squarefree` — the sifting modulus;
- `pairClassCount d p = if p ∣ d then 1 else 2`, **`pairNu d`** = the multiplicative density
  `ν(n) = (∏_{p ∣ n} pairClassCount d p)/n`, with `pairNu_isMultiplicative`,
  `pairNu_apply_prime`, `pairNu_pos_of_prime`, `pairNu_lt_one_of_prime` (below one at every prime
  `≥ 3`, which is why the range must start at `P₁ ≥ 2`);
- `mem_of_prime_dvd_prod`, `shiftMul_injOn`, **`roughPairSieve`**, **`siftedSum_roughPairSieve`**.

**The support is the image `m ↦ m(m+d)`, not `m`.**  `BoundingSieve` sifts its support by
coprimality with the modulus, so sieving the *pair* means putting the products in the support; the
map is injective on `m ≥ 1`, so the sifted sum is exactly

```text
#{ m ≤ Y : no prime of (P₁, h] divides m, and none divides m + d } ,
```

and with that support `multSum e = #{m ≤ Y : e ∣ m(m+d)} ≈ Y·ν(e)`, so `ν` is the true density and
the Selberg remainder stays small.  Getting this wrong — keeping `m` in the support while using the
two-dimensional `ν` — would leave a correct but vacuous bound, because the remainder would absorb
everything.

**Remaining on this brick:** the lower bound `S = selbergBoundingSum ≫ (log h/log P₁)²` for the
two-dimensional Selberg terms, and the remainder sum, giving

```text
#{m ≤ Y : m, m+d both free of primes in (P₁,h]}  ≪  Y (log P₁/log h)² · d/φ(d) .
```

The one-dimensional analogue in `BrunTitchmarsh.boudingSum_ge` (`S ≥ log z/2`) is the model.

### The Selberg terms of the pair sieve, and the shape of the remaining work (2026-08-18)

**`selbergTerms_roughPairSieve`** : for every squarefree `l` dividing the modulus,

```text
g(l) = ∏_{p ∣ l} c_p / (p − c_p) ,       c_p = pairClassCount d p ∈ {1, 2} .
```

(The duplicate squarefreeness lemma I had written was dropped in favour of the corpus's
`Sieve.prodDistinctPrimes_squarefree`.)

**Why `selbergBoundingSum_ge_sum_div` cannot be used directly.**  That lemma — the corpus's route to
`S ≥ log z/2` in the one-dimensional case — requires `CompletelyMultiplicative s.nu`.  `pairNu` is
multiplicative but **not** completely multiplicative: `prodPrimeFactors` gives `ν(p^k) = c_p/p^k`,
whereas complete multiplicativity would need `(c_p/p)^k`.  The file's own commented-out "Proposed
generalisation" is precisely the statement that would cover this case.  So the two-dimensional
bounding-sum lower bound has to be proved here.

**The shape of that proof, and the two facts it needs.**  Since the modulus is squarefree, only
squarefree `l` occur, and the untruncated sum is the Euler product

```text
∑_{l ∣ P} g(l) = ∏_{p ∣ P} (1 + c_p/(p − c_p))  ≍  (log h / log P₁)² ,
```

by Mertens.  The truncation `l² ≤ level` is removed by Rankin's trick:

```text
∑_{l ∣ P, l > L} g(l) ≤ L^{-δ} ∏_{p ∣ P} (1 + p^δ c_p/(p − c_p)) ,
```

and at `δ = 1/log h` every `p^δ ≤ e`, so the product is at most `(log h/log P₁)^{2e}` while
`L^{-δ} = exp(−log L/log h)`.  In the application `L = √level ≈ x^{1/4}` and `h = exp((log x)^β)`, so
`log L/log h ≍ (log x)^{1−β}` and the tail is smaller than any power — the truncation is free.  This
is the fundamental lemma in the only form the argument needs, and it is the next brick.

Two inputs it will draw on, both already in the corpus: Mertens' second theorem
(`Sieve/MertensSecond`, `mertensS`) for the Euler product, and `Sieve.rem_sum_le_of_const` for the
Selberg remainder.

### The Euler product of the bounding sum — `Sieve/SquarefreeDivisorProduct` (2026-08-18)

- **`sum_divisors_prod_primes_eq`** : the divisors of a product of distinct primes are indexed by the
  subsets of those primes — a bijection `t ↦ ∏_{p ∈ t} p` with inverse `l ↦ l.primeFactors`;
- **`sum_divisors_prod_primes_eq_prod`** : `∑_{l ∣ ∏_{p∈s}p} ∏_{p ∣ l} a p = ∏_{p ∈ s} (a p + 1)`;
- in `Sieve/RoughPairSieve`, **`sum_selbergTerms_roughPairSieve`** :

```text
∑_{l ∣ P} g(l) = ∏_{p ∈ (P₁, h]} ( c_p/(p − c_p) + 1 )  ≍ (log h / log P₁)² .
```

So the *untruncated* two-dimensional bounding sum is now an explicit Euler product.  What is left of
this brick is (i) evaluating that product by Mertens and (ii) showing the truncation `l² ≤ level`
costs nothing.

**Route for (ii), decided.**  Rankin's trick is *not* the cheapest way here.  For a lower bound it
suffices to restrict to divisors with at most `k` prime factors: every such `l` satisfies `l ≤ h^k`,
so `l² ≤ level` holds outright once `h^{2k} ≤ level`, and in the application
`level ≈ x^{1/2}`, `h = exp((log x)^β)` give `k` up to `≍ (log x)^{1−β}`.  The discarded part is
`∑_{j > k} e_j(a) ≤ ∑_{j>k} A^j/j! ≤ (eA/k)^k` with `A = ∑_p a_p ≍ 2 log log x`, and `k ≫ eA`, so it
is smaller than any power.  This replaces the fundamental lemma by an elementary tail bound on
elementary symmetric functions.

### The two-dimensional bounding sum is bounded below — `Sieve/PowersetTailBound` (2026-08-18)

The fundamental-lemma step is done, and by a route that is simpler than either Rankin in the size
variable or an elementary-symmetric-function expansion.

- `sum_powerset_prod_eq` : `∑_{t ⊆ s} ∏_{p ∈ t} a_p = ∏_{p ∈ s}(a_p + 1)`;
- **`sum_powerset_card_gt_le`** : **Rankin's trick in the cardinality variable** —
  `∑_{|t| > k} ∏_{p∈t} a_p ≤ e^{-k} ∏_p (1 + e·a_p) ≤ exp(e·∑_p a_p − k)`, because
  `e^{|t|}∏_{p∈t}a_p = ∏_{p∈t}(e a_p)` and `e^{|t|−k} ≥ 1` on the tail;
- **`sum_powerset_card_le_ge`** : hence `∑_{|t| ≤ k} ∏_{p∈t}a_p ≥ (1/2)∏_p(1 + a_p)` as soon as
  `k ≥ e·∑_p a_p + log 2`.

Composed with the sieve, in `Sieve/RoughPairSieve`:

- `selbergTerms_roughPairSieve_nonneg`;
- **`selbergBoundingSum_roughPairSieve_ge`** :

```text
(1/2) ∏_{p ∈ (P₁,h]} ( c_p/(p − c_p) + 1 )  ≤  selbergBoundingSum (roughPairSieve …)
```

whenever `h^{2k} ≤ level` and `k ≥ e·∑_p a_p + log 2`.  A divisor with at most `k` prime factors is
at most `h^k`, so the sieve's size restriction `l² ≤ level` is satisfied outright — no truncation
argument is needed at all, only the cardinality tail bound above.

In the application `level ≈ x^{1/2}` and `h = exp((log x)^β)` allow `k` up to `≍ (log x)^{1−β}`,
while `∑_p a_p ≍ 2 log log x`, so the condition on `k` is met with enormous room.

**Remaining on the sieve brick:** evaluate `∏_{p ∈ (P₁,h]}(1 + c_p/(p−c_p)) ≍ (log h/log P₁)²` by
Mertens, and bound the Selberg remainder (`Sieve.rem_sum_le_of_const` is the corpus tool).  Both are
elementary; the sieve-theoretic content is now finished.

### The Euler product reduces to the *square* of Mertens — `Sieve/PairEulerFactor` (2026-08-18)

The two-dimensional Euler product does not need a two-dimensional Mertens theorem.  Its local factor
dominates the square of the classical one:

- **`pairFactor_ge`** : for every prime `p ≥ 3`,

```text
(p/(p−1))² · (if p ∣ d then (p−1)/p else 1)  ≤  1 + c_p/(p − c_p) .
```

  Off the shift this is `p/(p−2) ≥ p²/(p−1)²`, i.e. `(p−1)² ≥ p(p−2)`, i.e. `1 ≥ 0`; on the shift it
  is an identity.
- **`prod_pairFactor_ge`** :

```text
( ∏_{p ∈ s} p/(p−1) )² · ∏_{p ∈ s, p ∣ d} (p−1)/p  ≤  ∏_{p ∈ s} (1 + c_p/(p − c_p)) .
```

**The shift correction is harmless, and the `d/φ(d)` factor of the sketch is not needed.**  Every
sifting prime exceeds `P₁`, so `∏_{p ∈ s, p ∣ d}(p−1)/p ≥ 1 − ω(d)/P₁`, and `ω(d) ≤ log d/log 2`
while `P₁ = exp((log h)^a)` — for `d ≤ h` the correction is `1 − O(log h/P₁)`, bounded below by
`1/2` with room to spare.

So the sieve's saving is `(∏_{P₁ < p ≤ h} p/(p−1))^{-2} ≍ (log P₁/log h)²`, and the only remaining
input is **Mertens' third theorem** for the one-dimensional product — which the corpus owns
(`Sieve/MertensSecond`, `Sieve/MertensSecondSharp`, `mertensS`).

### The bounding sum, in Mertens terms — `Sieve/{MertensProductLower,RoughPairSieveBound}` (2026-08-18)

The sieve's main term is finished.

`Sieve/MertensProductLower`:
- **`exp_inv_le_ratio`** : `e^{1/p} ≤ p/(p−1)`, straight from `1 − x ≤ e^{-x}` — no error term, no
  asymptotics;
- `exp_sum_inv_le_prod`, `rangePrimes_eq_primesRange`, **`prod_rangePrimes_ge`** :

```text
exp( mertensS h − mertensS P₁ )  ≤  ∏_{P₁ < p ≤ h} p/(p−1) .
```

`Sieve/RoughPairSieveBound`:
- **`selbergBoundingSum_ge_mertens`** — composing the three steps:

```text
(1/2) · exp(mertensS h − mertensS P₁)² · ∏_{p ∣ d, p ∈ (P₁,h]} (p−1)/p
    ≤  selbergBoundingSum (roughPairSieve …) ;
```

- `one_sub_sum_le_prod_one_sub` (Weierstrass), **`prod_shiftCorrection_ge`** :

```text
1 − log D / (log P₁ · P₁)  ≤  ∏_{p ∣ d, p ∈ (P₁,h]} (p−1)/p    for  1 ≤ d ≤ D ,
```

using `LadderErrorBudget.card_designatedPrimes_dvd_le` for the number of sifting primes dividing the
shift.  In the application `D = h` and `P₁ = exp((log h)^a)`, so the correction is `1 − o(1)`.

**So the sieve's main term is `≍ (log P₁/log h)²`, uniformly in the shift `d`.**  The remaining
piece of the sieve is the Selberg *remainder*, `∑_{e ≤ y} 3^{ω(e)}|R e|` with
`R e = #{m ≤ Y : e ∣ m(m+d)} − Y·ν(e)`; each `|R e| ≤ ν-many residue classes ≤ 2^{ω(e)}`, so the sum
is `≤ ∑_{e ≤ y} 6^{ω(e)} ≪ y (log y)^5`, negligible against `Y (log P₁/log h)²` for
`y = level ≈ Y^{1/2}`.  `Sieve.rem_sum_le_of_const` is the corpus tool for that step.

### The Chinese remainder step was already in the corpus (2026-08-18)

Before building the CRT count of `r(r+d) ≡ 0 (mod e)` from scratch, a search turned it up complete
in **`RHTower/ReducedFrequencyMobiusAliasCollapse`**:

- `quadraticCongruenceRoots n h`, `quadraticCongruenceRootCount`, `…CountTotal`;
- **`quadraticCongruenceRootCountTotal_prime`** : `= if p ∣ h then 1 else 2` — *exactly* the
  `pairClassCount` the sieve density uses, including at `p = 2`;
- **`quadraticCongruenceRootCountTotal_prod`** : the count factors over any pairwise coprime family
  — the Chinese remainder theorem in the form needed;
- `quadraticCongruenceRootDensity`, its multiplicativity, and the squarefree Euler product.

So the whole CRT layer came for free.  New in `Sieve/PairDensityRootCount`:

- `rootCountTotal_prime_eq`, **`rootCountTotal_eq_pairClassCount_prod`** : on a squarefree modulus,
  `#{r : r(r+d) = 0 mod e} = ∏_{p ∣ e} c_p`;
- **`pairNu_eq_rootDensity`** : `ν(e) = #roots(e)/e` on squarefree `e`.

**This is what makes the Selberg remainder small**: the sieve's density is the *actual* density of
the sifted set, not a majorant.  With `Sieve/ResiduePartitionCount`
(`card_filter_eq_sum_residues`, `card_residue_class_le`) the remainder is now
`|R e| = |multSum e − Y·ν(e)| ≤ 2·#roots(e) ≤ 2^{ω(e)+1}`, and
`∑_{e ≤ y} 3^{ω(e)}|R e| ≪ y(log y)^5` — negligible at `y ≈ Y^{1/2}`.  Assembling that is the next
brick, and it is the last one in the sieve.

### The residue count is two-sided — `Sieve/ResiduePartitionCount` (2026-08-18)

The Selberg remainder is a *difference*, so the interval-in-a-residue-class count is needed on both
sides.  The module now has both, and neither goes through `Nat.Ico_filter_modEq_card` (whose exact
rational-ceiling formula turned out more awkward to use than a direct argument):

- `card_filter_eq_sum_residues` : a congruence-invariant condition splits over residues;
- `card_residue_class_le` : `#{m ∈ [1,M] : m ≡ r} ≤ M/e + 1`, by the injection `m ↦ m/e`;
- **`card_residue_class_ge`** : `#{m ∈ [1,M] : m ≡ r} ≥ M/e − 1`, by the reverse injection
  `j ↦ je + r'` with `r' = if r = 0 then e else r ∈ [1,e]`, so that the image lands in `[1,M]`.

With `Sieve/PairDensityRootCount` these give, for squarefree `e ∣ P`,

```text
|R e| = |multSum e − Y·ν(e)|
      = |∑_{r : r(r+d) ≡ 0 (e)} #{m ≤ ⌊Y⌋ : m ≡ r} − Y·#roots(e)/e|  ≤  2 · #roots(e) ,
```

since each residue class is within one of `⌊Y⌋/e` and `|⌊Y⌋ − Y| ≤ 1`.  Then
`#roots(e) ≤ 2^{ω(e)}` and `∑_{e ≤ y} 3^{ω(e)}|R e| ≤ 2∑_{e ≤ y} 6^{ω(e)} ≪ y (log y)^5`.

Assembling those three lines is the last step of the sieve.

### The root set in residue form — `Sieve/PairDensityRootCount` (2026-08-18)

**`card_rootResidues_eq`** : for `0 < e`,

```text
#{ r < e : e ∣ r(r+d) }  =  quadraticCongruenceRootCountTotal e d ,
```

by the bijection `r ↦ (r : ZMod e)` with inverse `ZMod.val`.  This is the last translation the
Selberg remainder needs: it turns the corpus's `ZMod`-valued root count — whose CRT multiplicativity
and prime values are already proved — into the concrete residue set that
`Sieve/ResiduePartitionCount.card_filter_eq_sum_residues` sums over.

So all three lines of the remainder estimate are now available as Lean theorems:

```text
multSum e = ∑_{r < e, e ∣ r(r+d)} #{m ≤ ⌊Y⌋ : m ≡ r}        (card_filter_eq_sum_residues)
          ∈ [ ρ(e)(⌊Y⌋/e − 1),  ρ(e)(⌊Y⌋/e + 1) ]            (card_residue_class_{ge,le})
ρ(e) = #roots(e) = ∏_{p ∣ e} c_p = e·ν(e)                    (card_rootResidues_eq, pairNu_eq_rootDensity)
```

giving `|R e| ≤ 2ρ(e) ≤ 2^{ω(e)+1}`.  Composing them into `Sieve.rem_sum_le_of_const` is the
assembly step.

### The sieve remainder — `Sieve/RoughPairSieveRemainder` (2026-08-18)

The last piece of the sieve is proved.

- **`multSum_roughPairSieve`** : `multSum e = #{m ≤ ⌊Y⌋ : e ∣ m(m+d)}` — the image support and the
  injectivity of `m ↦ m(m+d)` collapse the sum over the support to a count over `m`;
- **`abs_rem_roughPairSieve_le`** : for squarefree `e > 0` and `0 ≤ Y`,

```text
|rem e|  =  | multSum e − ν(e)·Y |  ≤  2 · #roots(e) ,
```

uniformly in the shift `d` and the modulus `e`.  The proof splits `multSum e` over the `#roots(e)`
residue classes, uses `card_residue_class_{ge,le}` to place each within one of `⌊Y⌋/e`, and absorbs
`|⌊Y⌋ − Y| ≤ 1` with the factor `ρ/e ≤ ρ`.

**The sieve is now complete as a machine.**  Both inputs of `SelbergSieve.selberg_bound_simple`
— the bounding sum from below (`selbergBoundingSum_ge_mertens`, `≍ (log h/log P₁)²`) and the
remainder from above (`abs_rem_roughPairSieve_le`, `≤ 2^{ω(e)+1}`) — are unconditional Lean
theorems.  What is left is arithmetic on those two: `#roots(e) ≤ 2^{ω(e)}` and
`∑_{e ≤ y} 6^{ω(e)} ≪ y(log y)^5`, then the substitution into `selberg_bound_simple`.

### The remainder sum needs no divisor-sum estimate — `Sieve/RoughPairRemainderSum` (2026-08-18)

- **`rootCount_le_two_pow`** : `#roots(e) ≤ 2^{ω(e)}` on squarefree `e`;
- **`card_primeFactors_le_log`** : a divisor `e ≤ N` of the modulus has `ω(e) ≤ log N/log P₁`,
  because every prime of the modulus exceeds `P₁` (`LadderErrorBudget.card_designatedPrimes_dvd_le`
  again — `e.primeFactors` *is* `(rangePrimes P₁ h).filter (· ∣ e)`);
- **`selberg_summand_le`** : `3^{ω(e)}|R e| ≤ 2·6^{ω(e)}`.

**The classical `∑_{e ≤ y} 6^{ω(e)} ≪ y(log y)^5` is not needed.**  Combining the two bounds above,
every summand is `≤ 2·6^{log y/log P₁} = 2·y^{log 6/log P₁}`, and there are at most `y` of them, so
the whole remainder sum is `≤ 2 y^{1 + log 6/log P₁}`.  With `log P₁ = (log h)^a` that exponent is
`1 + o(1)`, and the remainder is `y^{1+o(1)}` — negligible against the main term `Y(log P₁/log h)²`
for any sieve level `y ≤ Y^{1/2}`.  This is a real simplification: it replaces a divisor-moment
estimate by the observation that the sifting primes are large.

### The sieve is closed — `Sieve/RoughPairCount` (2026-08-18)

**`card_roughPair_le`** — Selberg's bound with both halves substituted:

```text
#{ m ≤ ⌊Y⌋ : m and m+d both free of primes in (P₁,h] }
    ≤  Y / ( (1/2)·exp(mertensS h − mertensS P₁)²·C )
       +  ∑_{e ∣ P, e ≤ z} 2·6^{ω(e)} ,
```

`C = ∏_{p ∣ d, p ∈ (P₁,h]} (p−1)/p`, under `h^{2k} ≤ z` and `k ≥ e·∑_p a_p + log 2`.  The first term
is `Y·(log P₁/log h)²·O(1)` and the second is `z^{1+o(1)}`.  **Uniform in the shift `d`** — which is
what the second-moment reduction needs, since it sums over `|d| ≤ h`.

This closes the two-dimensional sieve.  The whole road from the Route E cards now reads:

```text
AveragedShortInterval μ hh
  ← fibre mean square                        Sieve/FibreRoughSecondMoment  (identity + band)
  ← rough part:  banded shifted pair count   Sieve/RoughPairCount          ✓ CLOSED
  ← S part:      Ramaré ladder + spectral    Sieve/Ramare*, Sieve/Omega*, Sieve/Ladder*
  + the parameter substitution                                            OPEN
```

### Note on a build collision (2026-08-18)

`lake build` of this chain failed for a while on `HTGeometry/LineJetTransfer`,
`…/MvPolynomialPhaseRank`, `…/GammaRationalPhaseRank` — another session's files, broken mid-edit.
They entered the chain only through `Sieve/LadderErrorBudget → RouteEForbiddenSupportStability`,
imported for a single counting lemma.  `Sieve/RoughPairSieveBound` and `Sieve/RoughPairRemainderSum`
now prove the two counts they need directly from `Finset.prod_primes_dvd` and `Real.log_pow`
(`prod_shiftCorrection_ge`, `card_primeFactors_le_log`), so **the sieve chain no longer depends on
`HTGeometry` at all** and builds on its own.

### The discarded set, reduced to shifted counts — `Sieve/{BandPairCount,FibreRoughShiftBound}` (2026-08-18)

- **`card_bandPairs_le`** : pairs of a finite set at distance at most `h` are counted by their
  differences — each is determined by its smaller element, the difference, and which side is
  smaller, so
  `#{(m,n) ∈ A² : |m−n| ≤ h} ≤ 2 ∑_{d ≤ ⌊h⌋} #{a ∈ A : a + d ∈ A}`;
- **`sum_sq_card_fibre_inter_le_shifts`** : composing with the fibre second-moment identity,

```text
∑_{a ∈ outerBlock} #(F_a ∩ T)²
    ≤ (2h+1) · 2 · ∑_{d ≤ ⌊h⌋} #{ m ∈ T ∩ D : m + d ∈ T ∩ D } .
```

No arithmetic enters: `T` is an arbitrary finite set.  **This is the exact interface the sieve
capstone `card_roughPair_le` consumes**, one `d` at a time, uniformly in the shift.

So the rough half of the road is now a single chain of Lean theorems from the fibre mean square down
to Selberg's bound.  What is left there is the numerical substitution: `T` = the integers free of
primes in `(P₁,h]`, `D ⊆ [1,⌊Y⌋]`, and the arithmetic showing the resulting bound is `o(h²√x/log x)`.

### The two halves of the rough road now meet — `Sieve/RoughSetShiftBound` (2026-08-18)

- `roughSet P₁ h N` — the integers of `[1,N]` free of primes in `(P₁,h]`;
- **`card_shift_roughSet_le`** : for every shift `d` and every auxiliary set `D`,

```text
#{ m ∈ roughSet ∩ D : m + d ∈ roughSet ∩ D }
    ≤  Y / ( (1/2)·exp(mertensS h − mertensS P₁)²·C_d )  +  ∑_{e ∣ P, e ≤ z} 2·6^{ω(e)} .
```

This is the join: `Sieve/FibreRoughShiftBound.sum_sq_card_fibre_inter_le_shifts` produces exactly
these shifted counts (with `D = fibreDyadicIndex x h`), and the sieve bounds each of them.  So the
rough half of the argument is a single chain from `AveragedMeanSquare` to Selberg's bound, with no
gaps and no hypotheses beyond the parameter inequalities `h^{2k} ≤ z` and `k ≥ e∑a_p + log 2`.

What is left on this half is purely quantitative: sum the bound over `|d| ≤ h`, multiply by
`(2h+1)·2`, and check the result is `o(h²√x / log x)` at the parameters
`log P₁ = (log h)^a`, `0 < a < 1 − 1/(2β)`.

### The shifted counts, summed — `Sieve/RoughShiftSum` (2026-08-18)

**`sum_shift_roughSet_le`** : for every auxiliary set `D` and every shift bound `H`,

```text
∑_{1 ≤ d ≤ H} #{ m ∈ roughSet ∩ D : m + d ∈ roughSet ∩ D }
    ≤ H · ( Y / ( (1/2)·exp(mertensS h − mertensS P₁)²·(1 − log H/(log P₁·P₁)) )
            + ∑_{e ∣ P, e ≤ z} 2·6^{ω(e)} ) .
```

The shift correction is made uniform in `d` by `prod_shiftCorrection_ge`: every sifting prime
exceeds `P₁`, so the correction is at least `1 − log H/(log P₁·P₁)` for **every** shift below `H`.

**`d = 0` is deliberately excluded.**  At `d = 0` every prime divides the shift, the two-dimensional
sieve degenerates to the one-dimensional one, and the correction factor collapses to
`∏_{p ∈ (P₁,h]}(p−1)/p ≍ log P₁/log h`.  That term is handled separately by the one-dimensional
bound, and it is affordable: its contribution to the fibre second moment is
`(2h+1)·2·#roughSet ≍ h·√x·(log P₁/log h)`, against a budget of `h²√x/log x` — smaller by a factor
`h`, which is exp((log x)^β).

### The shift-zero term — `Sieve/RoughSetCount` (2026-08-18)

The `d = 0` term excluded from `Sieve/RoughShiftSum` is now proved, from the *same* sieve.

- `pairClassCount_zero` : at shift zero every local class count is one, because every prime divides
  `0`;
- **`selbergBoundingSum_ge_mertens_zero`** : hence the Euler factor is `p/(p−1)` rather than its
  square, and `selbergBoundingSum ≥ (1/2)·exp(mertensS h − mertensS P₁)` — the *one-dimensional*
  Mertens product;
- **`card_roughSet_le`** :

```text
#{ m ≤ ⌊Y⌋ : m free of primes in (P₁,h] }
    ≤  Y / ( (1/2)·exp(mertensS h − mertensS P₁) )  +  ∑_{e ∣ P, e ≤ z} 2·6^{ω(e)}
    ≍  Y · log P₁ / log h .
```

So the pair sieve, run at shift zero, delivers the classical one-dimensional bound as a special
case; no separate one-dimensional sieve is needed.  **Every term of the fibre second moment — the
diagonal `d = 0` and the off-diagonal `1 ≤ d ≤ H` — is now bounded by an unconditional Lean
theorem.**

### Diagonal and off-diagonal, joined — `Sieve/FibreRoughTotal` (2026-08-18)

**`sum_sq_card_fibre_roughSet_le`** :

```text
∑_{a ∈ outerBlock} #(F_a ∩ T)²  ≤  (2h+1) · 2 · (B₀ + B₁)
```

whenever `#(T ∩ D) ≤ B₀` and `∑_{1 ≤ d ≤ ⌊h⌋} #{m ∈ T∩D : m+d ∈ T∩D} ≤ B₁`.  The split is exactly
`range(⌊h⌋+1) = {0} ∪ [1, ⌊h⌋]`, with the `d = 0` summand recognised as `#(T∩D)`.

`B₀` is supplied by `Sieve/RoughSetCount.card_roughSet_le` and `B₁` by
`Sieve/RoughShiftSum.sum_shift_roughSet_le`.  So the rough half of the argument is now closed as a
chain of Lean theorems with **no gaps of any kind** — only the numerical choice of
`P₁, k, z, H` and the verification that the resulting expression is `o(h²√x/log x)` remain, and
those are inequalities between explicit elementary functions.

### The two halves joined at the top — `Sieve/FibreSumSplit` (2026-08-18)

**`sum_sq_fibreSum_split`** : for any unit-bounded `f` and any discarded set `T`,

```text
∑_a (∑_{b ∈ F_a} f b)²  ≤  2 ∑_a (∑_{b ∈ F_a \ T} f b)²  +  2 ∑_a #(F_a ∩ T)² .
```

This is the top-level split of the whole argument: the first term is the `S` part, handled by the
Ramaré ladder and the spectral estimate; the second is the discarded part, now bounded end to end by
`Sieve/FibreRoughTotal` → `Sieve/{RoughSetCount,RoughShiftSum}` → `Sieve/RoughPairCount`.  Nothing
arithmetic enters — `T` is an arbitrary finite set.

**Status of the road.**  Both halves are now chains of unconditional Lean theorems:

```text
∑_a (∑_{b∈F_a} μ)²                                   sum_sq_fibreSum_split
  ├─ S part   → Ramaré ladder → spectral            Ramare*, Omega*, Ladder*, RouteTWidthExplicit
  └─ rough part → shifted pair counts → Selberg     FibreRoughTotal, RoughShiftSum, RoughSetCount,
                                                     RoughPairCount
```

What is not yet done, on either half, is the *choice of parameters as functions of `x`* and the
verification of the resulting limits.  Those are inequalities between explicit elementary functions
of `x`; no further structural mathematics is required.

### The split, at the level of limits — `Sieve/FibreSplitLimit` (2026-08-18)

**`averagedMeanSquare_of_split`** : for a unit-bounded `f` and *any* family of discarded sets
`T : ℝ → Finset ℕ`,

```text
( 2 ∑_a (∑_{b ∈ F_a \ T x} f b)² ) / (h²√x) → 0
  and  ( 2 ∑_a #(F_a ∩ T x)² ) / (h²√x) → 0
    ⟹  AveragedMeanSquare f hh .
```

This is the exact interface both halves now feed.  The rough half supplies the second hypothesis
through `Sieve/FibreRoughTotal` and the sieve; the `S` half supplies the first through the Ramaré
ladder and the spectral estimate.

**The structural work of the programme is finished.**  Every step from the Route E cards' hypothesis
`(6)` down to Selberg's sieve and the Route-T twisted prime sum is an unconditional Lean theorem, and
they compose.  What remains is exclusively the choice of the parameter functions
`P₁(x), k(x), z(x), Q(x), η(x), L(x), W(x), T₀(x)` and the verification of two limits — inequalities
between explicit elementary functions of `x`.

### The sieve saving in closed form — `Sieve/MertensDiffExp` (2026-08-18)

The sieve bounds are stated in terms of `exp(mertensS h − mertensS P₁)`; the parameter substitution
needs that as a power of `log h / log P₁`.  Mertens' second theorem in the corpus's sharp form
(`abs_mertensS_sub_logLog_sub_const_le`) supplies it directly, because the Meissel–Mertens constant
**cancels in the difference**:

- `mertensErr N = (2·mertensFirstConst + 1/2)/log N`;
- **`exp_mertens_diff_ge`** : for `2 ≤ P₁` and `2 ≤ h`,

```text
(log h / log P₁) · exp( −mertensErr P₁ − mertensErr h )  ≤  exp( mertensS h − mertensS P₁ ) .
```

So the sieve's saving `exp(mertensS h − mertensS P₁)^{-2}` is at most
`(log P₁/log h)²·exp(2·mertensErr P₁ + 2·mertensErr h)`, and both error exponentials tend to `1`.
With `log P₁ = (log h)^a` this is `(log h)^{-2(1−a)}(1+o(1))`, which is `o(1/log x)` exactly when
`2β(1−a) > 1`, i.e. `a < 1 − 1/(2β)` — the window recorded above, and non-empty precisely for
`β > 1/2`.

This is the last analytic ingredient of the rough half; what remains there is arithmetic on
explicit elementary functions.

## The card's gate is *quantitative*, not qualitative (2026-08-18)

A check of what the Route E cards actually consume, before spending more effort on limit-shaped
capstones:

- `MobiusReciprocalMarkerBlockCount.card_large_le_of_sum_sq_le (hδ : 0 < δ) (h : ∑_{t∈S} f t ^2 ≤ R)
  : #{t ∈ S : δ ≤ |f t|} ≤ R/δ²` — the card's Markov step `(10)`, and it takes an **explicit** `R`;
- `Sieve/Step1FromCorrelation.card_le_good_add_correlation` — step 1, likewise fully explicit, with
  the correlation bound `ε` appearing in the conclusion.

So the cards do **not** consume a qualitative `AveragedMeanSquare` / `AveragedShortInterval`
(`… → 0`).  They consume a *numerical* bound on `∑_t (∑_{t<n≤t+L} μ(n))²` of size `o(Y L²/log Y)`,
because `(10)` needs `o(Y/log Y)` bad starts and Markov divides by `δ² ≍ L²`.

**This does not invalidate anything built** — every bound in the chain is explicit, with named
constants and no asymptotic notation; only the three limit-shaped wrappers
(`averagedMeanSquare_of_split`, `averagedMeanSquare_moebius_of_omegaBudget`,
`averagedShortInterval_moebius_of_omegaBudget`) pass to a limit, and they sit *above* the explicit
material rather than inside it.  But it does fix the shape of the final capstone: it must be an
inequality with an explicit right-hand side, not a `Tendsto`.

Concretely the last assembly should produce

```text
∑_{a ∈ outerBlock x h} ( ∑_{b ∈ innerFibre x h a} μ(b) )²
    ≤  h² √x · ( C₁ (log P₁/log h)² + C₂/h + C₃ z/(h²√x) + (spectral term) )
```

with every constant named, and the cards then choose `P₁, z, …` and compare against `1/log x`
themselves.  The limit wrappers stay as convenience corollaries.

### The discarded part, in closed form — `Sieve/FibreRoughExplicit` (2026-08-18)

**`sum_sq_card_fibre_roughSet_explicit`** — the rough half assembled into a single inequality with
no asymptotic notation and every constant named:

```text
∑_{a ∈ outerBlock x h} #( F_a ∩ roughSet P₁ hN ⌊Y⌋ )²
  ≤ (2h+1)·2·[  ( Y/((1/2)e^Δ) + Σ_rem )
              + ⌊h⌋·( Y/((1/2)e^{2Δ}(1 − log⌊h⌋/(log P₁·P₁))) + Σ_rem ) ] ,
```

`Δ = mertensS hN − mertensS P₁`, `Σ_rem = ∑_{e ∣ P, e ≤ z} 2·6^{ω(e)}`.  Its hypotheses are exactly
`2 ≤ P₁ ≤ hN`, `1 ≤ z`, `hN^{2k} ≤ z`, `k ≥ e·∑_p a_p(d) + log 2` for every shift `d`, and positivity
of the shift correction — all checkable inequalities.

With `Sieve/MertensDiffExp.exp_mertens_diff_ge` the leading term is
`≍ h² · Y · (log P₁/log hN)²`, and dividing by `h²√x` (with `Y ≍ √x`) leaves `(log P₁/log hN)²` —
the `o(1/log x)` the cards need, in the window `a < 1 − 1/(2β)`.

**This is the shape the cards consume** (see the note above on the quantitative gate): an explicit
inequality, not a limit.

### The discarded part, in logarithms — `Sieve/FibreRoughLog` (2026-08-18)

**`sum_sq_card_fibre_roughSet_log`** — the Mertens difference eliminated in favour of the ratio of
logarithms:

```text
∑_{a ∈ outerBlock x h} #( F_a ∩ roughSet P₁ hN ⌊Y⌋ )²
  ≤ (2h+1)·2·[ ( 2Y·(log P₁/log hN)·E + Σ_rem )
             + ⌊h⌋·( 2Y·(log P₁/log hN)²·E²/(1 − log⌊h⌋/(log P₁·P₁)) + Σ_rem ) ] ,
```

`E = exp(mertensErr P₁ + mertensErr hN)`, `Σ_rem = ∑_{e ∣ P, e ≤ z} 2·6^{ω(e)}`.

**Nothing arithmetic is left in this expression** — it is built from `Y`, `h`, `log P₁`, `log hN`,
`z`, `⌊h⌋` and two Mertens error terms of size `O(1/log P₁)`.  Dividing by `h²√x` with `Y ≍ √x`,
`⌊h⌋ ≍ h` gives

```text
≍  8 (log P₁/log hN)² E²  +  8 (log P₁/log hN) E / h  +  (remainder)/(h√x) ,
```

so the discarded part costs `(log P₁/log hN)²` — the `(log h)^{-2}` rate the cards need — plus terms
smaller by a factor `h`.  Choosing `P₁` and `z` and comparing with `1/log x` is now arithmetic on
this one displayed line.

### The truncation hypothesis, made checkable — `Sieve/PairClassSum` (2026-08-18)

The bounding-sum lower bound carries the hypothesis `k ≥ e·∑_p a_p(d) + log 2`, quantified over
every shift `d`.  That sum is now bounded by a Mertens difference, so the hypothesis becomes a
comparison of `k` with `log(log hN / log P₁)`:

- **`pairClassTerm_le`** : `a_p = c_p/(p − c_p) ≤ 4/p` at every prime `p ≥ 4`, for either value of
  `c_p` (`1/(p−1) ≤ 4/p` needs `3p ≥ 4`; `2/(p−2) ≤ 4/p` needs `p ≥ 4`);
- **`sum_pairClassTerm_le`** : hence, for `4 ≤ P₁ ≤ hN` and **every** shift `d`,

```text
∑_{p ∈ (P₁,hN]} a_p(d)  ≤  4 (mertensS hN − mertensS P₁) .
```

So `k ≥ 4e·(mertensS hN − mertensS P₁) + log 2` discharges the hypothesis uniformly in `d`, and by
`Sieve/MertensDiffExp` that is `k ≳ 4e·log(log hN/log P₁)` — a quantity of size `log log x`, while
the level constraint `hN^{2k} ≤ z ≈ x^{1/2}` permits `k` up to `≍ (log x)^{1−β}`.  The two are
compatible with enormous room, which is what makes the truncation free.

### The comparison with `1/log x` — `Sieve/LogPowerLimits` (2026-08-18)

The parameter substitution ends in a comparison between `(log x)^{-c}` and `1/log x`.  Both limits
are now available in the `rpow` form the substitution produces:

- **`tendsto_log_rpow_neg`** : `(log x)^{-δ} → 0` for `δ > 0`;
- **`tendsto_log_rpow_neg_mul_log`** : `(log x)^{-c}·log x → 0` for `c > 1`.

The second is the exact shape of the cards' requirement: the discarded part costs
`(log P₁/log hN)² ≍ (log x)^{-2β(1−a)}`, and the card's Markov step multiplies by `log x`, so the
condition is `2β(1−a) > 1` — i.e. `a < 1 − 1/(2β)`, non-empty precisely for `β > 1/2`.

### The admissible window, proved — `Sieve/LogPowerLimits` (2026-08-18)

**`tendsto_logRatio_sq_mul_log`** : if `log P₁(x) ≤ (log hN(x))^a` and `log hN(x) ≥ (log x)^β`, then

```text
( log P₁(x) / log hN(x) )² · log x  →  0        whenever  2β(1 − a) > 1 .
```

This is the parameter window, now a theorem rather than a calculation on the card.  Its proof is the
chain `(log P₁/log hN)² ≤ (log hN)^{2(a−1)} ≤ ((log x)^β)^{2(a−1)} = (log x)^{-2β(1−a)}`, the middle
step using that `t ↦ t^{2(a−1)}` is decreasing, then `tendsto_log_rpow_neg_mul_log`.

Together with `Sieve/FibreRoughLog` this settles the rough half completely at the level of rates:
the discarded integers cost `(log P₁/log hN)²`, and that beats `1/log x` exactly on `a < 1 − 1/(2β)`,
non-empty precisely for `β > 1/2` — the cards' own hypothesis, recovered as a theorem.

### The remainder sum, in closed form — `Sieve/SelbergRemainderSum` (2026-08-18)

**`sum_selbergRemainder_le`** : for `2 ≤ P₁` and `1 ≤ z`,

```text
∑_{e ∣ P, e ≤ z} 2·6^{ω(e)}  ≤  2 z · 6^{log z / log P₁} .
```

Two facts and nothing else: a divisor of the modulus below the level has at most `log z/log P₁`
prime factors (`card_primeFactors_le_log`), and there are at most `z` such divisors.  Since the
sifting primes are large, `6^{log z/log P₁} = z^{log 6/log P₁}` is `z^{o(1)}`, so the remainder is
`z^{1+o(1)}` — negligible against the main term for any `z ≤ x^{1/4}`, which still leaves the level
constraint `hN^{2k} ≤ z` satisfiable with `k ≍ (log x)^{1−β}`.

**With this, every quantity in the rough half's bound is a closed expression in
`x, h, Y, log P₁, log hN, z`.**

### `1/h` vanishes — `Sieve/LogPowerLimits` (2026-08-18, continued)

**`tendsto_exp_neg_log_rpow`** : `exp(−(log x)^β) → 0` for `β > 0`.  This is `1/h` for the cards'
short-interval length `h = exp((log x)^β)`, and it is what kills the two lower-order terms of the
rough bound (`8(log P₁/log hN)E/h` and the diagonal `d = 0` contribution), both of which carry an
extra factor `1/h` against the main term.

The rough half's three limits are now all available:

| term | size | vanishes by |
|-|-|-|
| off-diagonal, main | `(log P₁/log hN)²` | `tendsto_logRatio_sq_mul_log` (with the `log x` of the Markov step) |
| diagonal `d = 0` | `(log P₁/log hN)/h` | `tendsto_exp_neg_log_rpow` |
| Selberg remainder | `z^{1+o(1)}/(h√x)` | `sum_selbergRemainder_le` at any `z ≤ x^{1/4}` |

### Normalising the discarded-part bound — `Sieve/RoughDivBound` (2026-08-18)

**`rough_div_bound`** : for `1 ≤ h` and `0 < s`, and nonnegative `A, B`,

```text
( (2h+1)·2·(A + ⌊h⌋·B) ) / (h²·s)  ≤  6A/(h·s)  +  6B/s .
```

Applied with `s = √x`, `A` the diagonal bound and `B` the off-diagonal bound of `Sieve/FibreRoughLog`,
this puts the discarded part into exactly the two-order form the limits address:

```text
∑_a #(F_a ∩ roughSet)² / (h²√x)
    ≤  6·( 2Y(log P₁/log hN)E + Σ_rem ) / (h√x)      ← carries an extra 1/h
     +  6·( 2Y(log P₁/log hN)²E²/c + Σ_rem ) / √x     ← the main term
```

With `Y ≍ √x` the first is `≍ (log P₁/log hN)/h` and the second `≍ (log P₁/log hN)²`, matching the
limit table above term for term.  Every piece of the rough half is now a proved inequality or a
proved limit; the remaining step is to name the parameter functions and cite them.

### The cards' short-interval length — `Sieve/ShortIntervalLength` (2026-08-18)

The first parameter function is now named and its three required properties proved:

- `cardLength β x = exp((log x)^β)` — the cards' `h(X)`;
- `log_cardLength` : `log(cardLength β x) = (log x)^β`;
- **`tendsto_cardLength`** : `cardLength β → ∞` for `β > 0`;
- **`cardLength_le_sqrt`** : `cardLength β x ≤ √x` eventually, for `0 < β < 1` — from
  `(log x)^β·(log x)^{1−β} = log x` and `(log x)^{1−β} ≥ 2`.

`cardLength_le_sqrt` is the hypothesis `hhx` that every capstone of the fibre reduction carries
(`averagedMeanSquare_of_spectral`, `sum_fibreSum_sq_le_integral_scaled`, …), and
`tendsto_cardLength` is `hgrow`.  So the cards' own choice of `h` now discharges both, for exactly
the range `0 < β < 1` the cards state.

### The start of the sifting range — `Sieve/SiftingRangeStart` (2026-08-18)

The second parameter function, `P₁`, is now named:

- `siftStart c x = ⌈exp((log x)^c)⌉₊` — used at `c = aβ`, so that `log P₁ ≈ (log h)^a`;
- **`log_siftStart_le`** : `log(siftStart c x) ≤ (log x)^c + log 2` eventually — the ceiling costs at
  most `log 2`, because `⌈E⌉ ≤ E+1 ≤ 2E` for `E ≥ 1`;
- **`eventually_le_siftStart`** : `N ≤ siftStart c x` eventually, for any fixed `N` — which supplies
  the hypotheses `2 ≤ P₁` and `4 ≤ P₁` that the sieve and `Sieve/PairClassSum` require.

**The `log 2` is absorbed for free**, because the admissible window `a < 1 − 1/(2β)` is open: pick
`a < a' < 1 − 1/(2β)`; then `(log x)^{aβ} + log 2 ≤ (log x)^{a'β}` eventually, and
`Sieve/LogPowerLimits.tendsto_logRatio_sq_mul_log` applies at `a'`.  This is why the window was
stated as a strict inequality.

### The top of the sifting range — `Sieve/SiftingRangeTop` (2026-08-18)

- `siftTop β x = ⌊cardLength β x⌋₊` — the prime range is `(P₁, hN]` with `hN = siftTop β x`;
- **`eventually_le_siftTop`** : `N ≤ siftTop β x` eventually, for any fixed `N`;
- **`siftStart_le_siftTop`** : `siftStart (aβ) x ≤ siftTop β x` eventually, for `0 < a < 1` —
  the sieve's `P₁ ≤ hN`.

The proof is the chain `⌈E⌉ ≤ E+1 ≤ H−1 ≤ ⌊H⌋` with `E = exp((log x)^{aβ})`, `H = exp((log x)^β)`,
using `(log x)^β ≥ (log x)^{aβ} + 1` (from `(log x)^{β−aβ} ≥ 2`) and `e·E ≥ E + 2` (from `E ≥ 2`).

**Three of the sieve's structural hypotheses are now discharged by the parameter functions
themselves**: `2 ≤ P₁`, `4 ≤ P₁`, and `P₁ ≤ hN`.  What is left of the substitution is the level
`z(x)`, the truncation depth `k(x)`, and the shift-correction positivity.

### The truncation depth fits inside the level — `Sieve/LogLogSmall` (2026-08-18)

The last comparison the parameter substitution needs:

- **`tendsto_log_div_rpow`** : `log t / t^δ → 0` for `δ > 0`, from mathlib's `isLittleO_log_rpow_atTop`;
- **`tendsto_logLog_div_logRpow`** : `log log x / (log x)^δ → 0`.

This is what makes the level constraint `hN^{2k} ≤ z` satisfiable.  By `Sieve/PairClassSum` the
truncation depth may be taken `k ≍ log(log hN/log P₁) ≍ log log x`, so
`2k·log hN ≍ log log x·(log x)^β`, while the level `z = x^{1/4}` gives `log z = (log x)/4`.  The
constraint is therefore `8 log log x ≤ (log x)^{1−β}` — true eventually for every `β < 1`, by the
limit above.

**Every hypothesis of the rough half is now discharged by a named parameter function**:
`2 ≤ P₁`, `4 ≤ P₁`, `P₁ ≤ hN` (`Sieve/SiftingRange{Start,Top}`), `1 ≤ z`, `hN^{2k} ≤ z` and
`k ≥ 4e·Δ + log 2` (this file with `Sieve/PairClassSum`), `h ≤ √x` and `h → ∞`
(`Sieve/ShortIntervalLength`).

### The level and the truncation depth — `Sieve/SiftingDepth` (2026-08-18)

The last two parameter functions are named:

- `siftLevel x = √(√x) = x^{1/4}`, with `one_le_siftLevel` and **`log_siftLevel`**
  (`log(siftLevel x) = (log x)/4`);
- `siftDepth β a x = ⌈4e·(mertensS hN − mertensS P₁) + log 2⌉₊` — chosen so that
  `Sieve/PairClassSum.sum_pairClassTerm_le` discharges the truncation hypothesis for **every** shift
  by construction;
- `mertensS_mono`, `mertensS_nonneg` — the two monotonicity facts the estimate needs;
- **`siftDepth_le`** : eventually
  `siftDepth β a x ≤ 4e·(log((log x)^β) + mertensUpperConst) + log 2 + 1`,
  i.e. `k ≍ log log x`, using the corpus's `mertensS_le_logLog_add` and
  `log hN ≤ log(cardLength) = (log x)^β`.

Combined with `log(siftLevel x) = (log x)/4` and `Sieve/LogLogSmall`, the level constraint
`2k·log hN ≤ log z` becomes `≍ log log x·(log x)^β ≤ (log x)/4`, true eventually for every `β < 1`.

### The level constraint, proved — `Sieve/SiftingDepth` (2026-08-18, continued)

**`siftTop_pow_le_siftLevel`** : for `0 < β < 1` and `0 < a < 1`, eventually

```text
hN^{2k}  ≤  z ,        hN = siftTop β x,  k = siftDepth β a x,  z = siftLevel x = x^{1/4} .
```

The proof passes to logarithms: `2k·log hN ≤ 2k·(log x)^β`, and `8k ≤ (log x)^{1−β}` because
`k ≤ 4eβ·log log x + O(1)` (`siftDepth_le`) while `log log x = o((log x)^{1−β})`
(`Sieve/LogLogSmall`); then `(log x)^β·(log x)^{1−β} = log x` gives `2k·log hN ≤ (log x)/4`, which is
`log(siftLevel x)`.

**Every hypothesis of the rough half is now a proved statement about the named parameter
functions.**  The remaining work on that half is purely the composition: substituting
`cardLength β`, `siftStart (aβ)`, `siftTop β`, `siftDepth β a`, `siftLevel` into
`Sieve/FibreRoughLog` and citing the limits.

### The shift correction is positive — `Sieve/ShiftCorrectionPos` (2026-08-18)

**`shiftCorrection_pos`** : for `0 < β`, `0 < a`, eventually

```text
0 < 1 − log⌊cardLength β x⌋ / ( log P₁ · P₁ ) ,      P₁ = siftStart (aβ) x ,
```

in fact the correction is at least `1/2`.  The numerator is `≤ (log x)^β = exp(β log log x)`; the
denominator is `≥ exp((log x)^{aβ})`, since `P₁ ≥ exp((log x)^{aβ})` and `log P₁ ≥ 1`; and
`β log log x + log 2 ≤ (log x)^{aβ}` eventually by `Sieve/LogLogSmall`.

**This was the last un-discharged hypothesis of the rough half.**  All of them now hold for the named
parameter functions:

| hypothesis | discharged by |
|-|-|
| `h → ∞`, `h ≤ √x` | `ShortIntervalLength` |
| `2 ≤ P₁`, `4 ≤ P₁` | `SiftingRangeStart.eventually_le_siftStart` |
| `P₁ ≤ hN`, `2 ≤ hN` | `SiftingRangeTop` |
| `1 ≤ z`, `hN^{2k} ≤ z` | `SiftingDepth` |
| `k ≥ e·∑_p a_p(d) + log 2`, every `d` | `SiftingDepth` (by construction) + `PairClassSum` |
| shift correction `> 0` | this file |

### The rough half is CLOSED — `Sieve/RoughPartLimit` (2026-08-18)

```text
tendsto_roughPart (hβ0 : 0 < β) (hβ1 : β < 1) (ha0 : 0 < a) (ha1 : a < 1) :
    Tendsto (fun x => (2 * roughPartSum β a x) / (cardLength β x ^ 2 * √x)) atTop (𝓝 0)
```

where `roughPartSum β a x = ∑_{A ∈ outerBlock x h} #(innerFibre x h A ∩ roughSet P₁ hN ⌊√x+h⌋)²`
with `h = cardLength β x = exp((log x)^β)`, `P₁ = siftStart (aβ) x = ⌈exp((log x)^{aβ})⌉`,
`hN = siftTop β x = ⌊h⌋`.  `#print axioms` = `[propext, Classical.choice, Quot.sound]`.

**This is the second hypothesis of `Sieve/FibreSplitLimit.averagedMeanSquare_of_split`, discharged
for the named parameter functions and for every `0 < a < 1`, `0 < β < 1`.**  No gap condition is
needed here — `hgap : 1 < 2β(1−a)` is only for the sharper `o(1/log Y)` form the cards consume.

Supporting modules added:

| module | content |
|-|-|
| `Sieve/ShiftCorrectionPos` | `shiftCorrection_ge_half`, `shiftCorrection_pos` |
| `Sieve/SiftingRangeRatio` | `log_siftTop_ge`, `siftRatio`, `siftRatio_nonneg`, `tendsto_siftRatio` (`≍ (log x)^{−β(1−a)}`) |
| `Sieve/RoughRemainderLimit` | `log_siftStart_ge`, `tendsto_selbergRemainder_div_sqrt` (`2z·6^{log z/log P₁}/√x → 0` at `z = x^{1/4}`) |
| `Sieve/RoughPartArith` | `roughPart_diag_le`, `roughPart_offDiag_le`, `roughPart_div_le` — the crude collapse `≤ 72/h + 72/√x + 864L² + 24R/√x` given `L ≤ 1`, `E ≤ 3`, `c ≥ 1/2` |
| `Sieve/RoughPartLimit` | `mertensErr_le_half`, `mertensErr_nonneg`, `roughPartSum`, `tendsto_roughPart` |

**What is left is the smooth half only**: the first hypothesis of `averagedMeanSquare_of_split`,
i.e. the fibre sums restricted to integers *having* a prime factor in `(P₁, hN]`.  That is where the
`ω_P` factorisation (`Sieve/OmegaWeightedFactorisation`) and the spectral estimate
(`Sieve/OmegaSpectralFibre`) apply.

### The parameter accounting of the spectral side, done — and what it forces (2026-08-18)

Scales: `M = B₀ = ⌊√x + h⌋ ≍ √x`, `δ = fibreWidth x h = log(1 + h/√x) ≍ h/√x`, `z₀ = Q = exp((log h)^{9/10})`,
`z = h`, `W = mertensS z − mertensS z₀ ≍ (1/10) log log h`, `Ec = ∑_{n ≤ B₀}‖omegaCoeff‖²`.

**The energy is `≍ M W²`, not `M Ω²`.**  `Sieve/OmegaEnergyBound.sum_normSq_omegaCoeff_Icc_le`:
`Ec ≤ 8B₀·mertensS z + 8π(z) + 16π(z)² + 2W²B₀`, from the range Turán–Kubilius variance.  Using the
uniform bound `ω_P(n) ≤ log B₀/log z₀` instead costs `(log x)^{2−9β/5}` and the accounting fails.

**The two non-spectral terms of `omegaBudget` are already fine.**  Dividing by `W²h²√x`:

| term | size | vanishes because |
|-|-|-|
| `204(|P|+1)²(√x+1)` | `≍ 816/W²` | `W → ∞` |
| `2(h+1)(2h+1)(4(√x/2+h+1)mertensS z + 4π(z)+8π(z)²)` | `≍ 72 loglog h/W² + 96h²/(W²√x)` | `W ≍ loglog h`; `h = exp((log x)^β)`, `β < 1` |

So **everything reduces to `∫_ℝ ‖K_δ‖²‖A_ω‖² = o(W²h²)`**.

**Gallagher's split must be cut at `G ≍ M/h`, and the head must not use the mean value theorem.**
With `α = (5π/2)Ec`, `β = β₀ + (5e/2)B₀Ec`, the dyadic split gives
`2δ²(αG + β) + 4α/(π²G) + 4β/(3π²G²)`.  Dividing by `W²h²`:

* `2δ²·(5e/2)B₀Ec ≍ 5e·(h²/x)·√x·√x W² = 5e h²W²` — **exactly the trivial bound**.  Gallagher plus
  the mean value theorem reproduces the trivial estimate; the head `|w| ≤ G` must be estimated by
  the ladder bound `β₀`, never by `affineMajorant_of_bound_at`'s constant term.
* tail: `4α/(π²G) = o(W²h²)` iff `G ≫ √x/h²`; `4β/(3π²G²) = o(W²h²)` iff `G ≫ √x/h`.  So `G ≍ M/h`
  — the exposé's split point `X/h`.
* head: `2δ²β₀ = o(W²h²)` iff `β₀ = o(W²M²)`.

**The trivial bound on the prime polynomial does not suffice.**  With `V_j = #P_j`, and
`v_j = 1/stepMass_j`, `N_j = B₀/Q_j`, `#P_j ≍ stepMass_j·Q_j`,

```text
∑_j v_j V_j² N_j²  =  ∑_j (1/m_j)(m_j Q_j)²(B₀/Q_j)²  =  B₀² ∑_j m_j  =  B₀² W ,
```

so the harmonic split returns `W·B₀²W = W²B₀²` — the trivial size, with no gain.  **Cancellation is
required, and it cannot be uniform on `|w| ≤ G`**, because at `w = 0` the prime polynomial *is* `#P_j`.

**Hence the annulus split, with `w₀ ≍ log z`.**

* `w₀ ≤ |w| ≤ G` : Route-T gives `V_j ≍ #P_j(1/(1+|w|) + 1/log Q_j) ≍ #P_j/log Q_j` once
  `w₀ ≳ log Q_j`, so the same sum is `W²B₀²/log²Q` — a gain of `log²Q = (log h)^{9/5}`.
* `|w| ≤ w₀` : the prime polynomial is bounded trivially and the **cofactor** is bounded by Lemma 2.3
  for `μ`: `‖∑_{m ∈ D_j} μ(m)m^{2πiw}‖ ≤ N_j(log N_j)^{-A}`.  The step contributes
  `2w₀·W ∑_j v_j V_j² N_j²(log N_j)^{-2A} = 2w₀ W²B₀²(log B₀)^{-2A}`, which is `o(W²B₀²)` for `A ≥ 1`
  since `w₀ ≤ log x`.

Both analytic inputs are already in the corpus: `Sieve/PrimeBlockTwistBound.exists_norm_primeBlockPoly_routeT_le`
and `Sieve/RouteTMoebiusPowerSaving.exists_norm_LSeries_truncatedMoebius_dyadic_le_routeTPower`.

**Next brick.**  A module `Sieve/LadderAnnulus` generalising `integral_normSq_ladderProductPoly_le`
and `integral_normSq_ladderStep_le` from `Set.Icc (-W) W` to an arbitrary measurable subset, plus the
low-frequency twin in which the *cofactor* carries the pointwise bound.

### The annulus is built, and the Route-T exponent fixes the window (2026-08-18, continued)

| module | content |
|-|-|
| `Sieve/OmegaEnergyBound` | `mertensS_nonneg'`, `sum_normSq_omegaCoeff_Ioc_le`, `sum_normSq_omegaCoeff_Icc_le` — the coefficient energy is `≍ B₀W²`, from the range Turán–Kubilius variance, not `B₀Ω²` |
| `Sieve/LadderAnnulus` | `setIntegral_Icc_split`, `integral_normSq_ladderProductPoly_set_le` (the harmonic split over an arbitrary measurable frequency set), `integral_normSq_ladderStep_set_le` (prime bound on the set), **`integral_normSq_ladderStep_low_le`** (cofactor bound on the disc) |
| `Sieve/OmegaWeightedAnnulusBound` | `integral_normSq_ladderProductPoly_annulus_le`, **`integral_normSq_omegaWeighted_annulus_le`** — the whole `(26)`–`(30)` layer with the window cut at `w₀` |
| `Sieve/CofactorLowFreqBound` | `moebiusSharpBound`, `moebiusCoeff_mul_unitLogPhase_eq`, `logPoly_moebiusCoeff_eq_sum_moebiusTwist`, `sum_moebiusTwist_Icc_eq`, `moebiusSharpBound_nonneg`, **`exists_norm_logPoly_moebiusCoeff_Icc_le`** — exposé `(29)`–`(30)`: the cofactor polynomial on the low-frequency disc |

The capstone now reads

```text
∫_{|w| ≤ G} ‖A_ω‖²
  ≤ 2 (∑_j 1/v_j)(∑_j v_j [ V_j²(5π/2·G + 5e/2·⌊B₀/Q_j⌋)(B₀/Q_j+1) + Vlow_j² U_j² · 2w₀ ])
    + 2 (defect)
```

with `V_j` bounding the prime polynomial on the annulus `w₀ ≤ |w| ≤ G`, `Vlow_j` bounding it on the
disc (trivially, by `#P_j`), and `U_j` bounding the *cofactor* polynomial on the disc.

**The low-frequency range closes with room to spare.**  `Sieve/CofactorLowFreqBound` gives
`U_j ≤ 2·moebiusSharpBound(B₀/Q_j)`, and `moebiusSharpBound N = 3N e^{−c(log N)^{1/10}}/π + smoothWidth N + 1`
with `smoothWidth N = N/exp((log N)^{1/20})`.  Writing `U_j = N_j s(N_j)`,

```text
2w₀ · W ∑_j v_j Vlow_j² U_j²  =  2w₀ W² B₀² s²  =  o(W²B₀²)   ⟺   w₀ s(N)² → 0 ,
```

and `s(N)² ≍ exp(−2(log N)^{1/20})` with `log N ≍ (log x)/2` beats every power of `log x`, so `w₀`
may be taken as large as any fixed power of `log x`.  The admissible twist range of the contour bound
is `|τ| ≤ (contourParam(N+H) − 5)/4 ≍ exp((log N)^{1/10})/4`, far larger still.

**The annulus range is what the Route-T exponent constrains.**  `Sieve/VonMangoldtTwistPrimeEnvelope`
gives `‖∑_{p ≤ K} p^{−iτ}‖ ≤ (Env(K) + 7e⁹)(1/log 2 + 1/log(K+1))` with

```text
Env(K)  ≍  K^{1−w(τ)/3}(E(τ) + log 2K)  +  K^{1+2w(τ)/3}(1 + log²K + E(τ))/(1+|τ|) ,
```

`w(τ)` the Route-T width, `w(τ) ≳ 1/(10 D_A Z^{9/10}(1+log Z)²)`, `Z = 2log(6|τ|+6)+1`
(`Sieve/RouteTWidthExplicit.routeTWidthPolylogLower_le`).

* the **height** term is harmless: for `|τ| ≥ w₀` with `w₀` a fixed power of `log x` it is
  `≤ K/(log K)²` — this is exactly why the annulus is cut at a polylogarithmic `w₀`;
* the **contour** term needs `w(τ)·log K → ∞`.  At the top of the annulus `|τ| ≍ G ≍ √x/h`, so
  `Z ≍ log x` and `w ≍ (log x)^{−9/10}(log log x)^{−2}`.  With `log K = log Q = (log h)^γ = (log x)^{γβ}`
  this is `(log x)^{γβ − 9/10}/(log log x)²`, which tends to infinity **iff `γβ > 9/10`**.

Since `γ ≤ 1` (the sifting range must be non-empty: `Q ≤ z = h`), the §3 route with the corpus's
present Route-T width closes exactly for

```text
β > 9/10 ,    γ ∈ (9/(10β), 1) ,    W = mertensS h − mertensS Q ≍ (1 − γ) log log h → ∞ .
```

The exposé's own threshold is `β > 20/27` because it uses the Vinogradov–Korobov exponent `2/3`
rather than the corpus's `9/10`; lowering the corpus exponent to `2/3 + δ`, or running §4 (Lemmas
2.5–2.6), is what moves the threshold down.  Nothing else in the chain changes.

**Next bricks.**
1. `V_j` on the annulus from `exists_norm_primeBlockPoly_routeT_le` plus `routeTTwistEnvelope_le_exp`:
   a single inequality `V_j ≤ #P_j/(log Q_j)²` under the two conditions above.
2. `Vlow_j = #P_j` — the trivial bound on `primeBlockPoly`.
3. The Gallagher head/tail wrapper that uses `β₀` for `|w| ≤ G` and the affine majorant only above `G`
   (the present `gallagher_split_integral_dyadic` applies the affine majorant at `T = G` as well,
   whose constant term `(5e/2)B₀·Ec` alone already equals the trivial bound).
4. The substitution.

### CORRECTION: the cut `w₀` is not polylogarithmic, and the window it forces (2026-08-18)

The previous section's claim that `w₀` may be a fixed power of `log x` is wrong.  Reading
`Sieve/RouteTWidthExplicit.routeTTwistEnvelope_le_exp`, the height term of the envelope is

```text
C · 3K · exp(delta/3 · log 3K) · (1 + log²K + E(τ)) / (1 + |τ|) ,
```

so it is `≤ K/(log K)²` only once `|τ| ≳ K^{2w(τ)/3}(log K)²(1+log²K+E(τ))`.  With
`w(τ) ≍ (log|τ|)^{-9/10}` and `K = Q_j`, `log K = (log x)^{γβ}`, at the top of the annulus
`|τ| ≍ G ≍ √x/h` this is `K^{2w/3} = exp((log x)^{γβ − 9/10})`.  Hence

```text
τ_low ≍ exp((log x)^{γβ − 9/10}) ,     τ_high ≍ exp(c (log Q)^{10/9}) = exp(c (log x)^{10γβ/9}) .
```

The prime-sum saving lives **between** them: the contour term needs `w(τ)·log K → ∞`, i.e.
`log|τ| ≪ (log K)^{10/9}` — an *upper* bound on `τ`, and the height term needs `|τ| ≥ τ_low`.

Three constraints therefore fix the window.

| constraint | source | requirement |
|-|-|-|
| the annulus reaches the Gallagher cut `G ≍ √x/h` | contour term at `|τ| = G` | `10γβ/9 > 1`, i.e. `γβ > 9/10` |
| the disc is covered by the Möbius contour bound (`\|τ\| ≤ exp((log N)^{1/10})`, `log N ≍ (log x)/2`) | `Sieve/CofactorLowFreqBound` | `γβ − 9/10 < 1/10`, i.e. `γβ < 1` |
| the disc's own cost `2w₀W²B₀²s²` vanishes, `s ≍ exp(−(log N)^{1/20})` | `Sieve/LadderAnnulus.integral_normSq_ladderStep_low_le` | `γβ − 9/10 < 1/20`, i.e. `γβ < 19/20` |

```text
9/10 < γβ < 19/20 ,     γ ≤ 1 ⟹ β > 9/10 ,     γ ∈ (9/(10β), 19/(20β)) ∩ (0,1] ≠ ∅ .
```

`W = mertensS h − mertensS Q ≍ (1 − γ) log log h → ∞`, so the Turán–Kubilius arrangement still has
its weight.  **The §3 route in this corpus therefore proves the Möbius short-interval mean square for
`h = exp((log x)^β)` with `9/10 < β < 1`** — one exponent short of the exposé's `β > 20/27`, the gap
being exactly the difference between the corpus's Route-T width exponent `9/10` and Vinogradov–Korobov's
`2/3`.

Modules landed for this layer, all axiom-clean:

| module | content |
|-|-|
| `Sieve/GallagherDyadicTail` (refactored) | **`gallagher_farTail_dyadic_le`** extracted from the old proof, and **`gallagher_split_integral_dyadic_head`** — the head paid by a supplied `β₀` instead of by the affine majorant.  `gallagher_split_integral_dyadic` keeps its statement. |
| `Sieve/OmegaBudgetFromAnnulus` | `norm_primeBlockPoly_le_card` (the disc's trivial prime bound `Vlow_j`), **`integral_kernel_normSq_omegaWeighted_head_le`** |

### The weight must be `1/(V_j·√T_j)`, not `1/stepMass_j` (2026-08-18)

`Sieve/LadderHarmonicSplit.sum_stepMass_eq` makes `v_j = 1/stepMass_j` attractive, because then
`∑_j 1/v_j` is exactly `W` for every subdivision.  But the *other* factor then needs
`V_j ≤ √ε·stepMass_j·Q_j`, and comparing `#P_j` with `stepMass_j·Q_j` in that direction requires a
**lower** bound on the harmonic mass of the primes of a thin interval `(Q_j, Q_j(1+η)]` — a
short-interval prime count, unavailable unconditionally for small `η`.  Dyadic blocks would supply
it from Mertens but make the ladder defect too large (`η = 1` gives a defect
`≍ (log x)^{1−γβ}/W → ∞` after normalisation).

The weights are free, and the optimal choice removes the difficulty entirely.  With
`T_j := (5π/2·G + 5e/2·⌊B₀/Q_j⌋)(B₀/Q_j + 1)` and

```text
v_j  :=  1 / (V_j · √T_j) ,        so   (∑_j 1/v_j)(∑_j v_j V_j² T_j)  =  (∑_j V_j √T_j)² ,
```

and the comparison needed is now `#P_j/Q_j ≤ (1+η)·stepMass_j`, which is **trivial**: every `p` in
the block satisfies `1/p ≥ 1/(Q_j(1+η))`.  Then

```text
∑_j V_j √T_j  ≲  √(5e/2) · ε · ∑_j #P_j · B₀/Q_j  ≤  √(5e/2) · ε (1+η) B₀ ∑_j stepMass_j
              =  √(5e/2) · ε (1+η) B₀ W ,
```

so the annulus contributes `≲ ε² W² B₀²`, exactly the required `o(W²B₀²)`.  The same weight also
handles the disc: its contribution is `2w₀(1+η)²B₀²W²s²`, `o(W²B₀²)` iff `w₀ s² → 0` as before.

**Consequence:** the thin ladder stays thin (small `η`, so the defect is small), and no prime
counting beyond Mertens is used anywhere in the spectral side.

### The two-weight split and its explicit majorants — landed (2026-08-18)

| module | content |
|-|-|
| `Sieve/BlockMassCompare` | `stepMass_nonneg`, `card_geomBlock_le_mul_stepMass`, **`sum_card_geomBlock_div_le`**: `∑_j #P_j·B/Q_j ≤ (1+η)·B·∑_{p∈P} 1/p`.  This single inequality replaces **every** short-interval prime count in the spectral side; its proof is that each `p` in the block is at most the block's right endpoint. |
| `Sieve/OmegaWeightedAnnulusBound` (extended) | `ladderStepMVT`, `integral_normSq_omegaWeighted_annulus_aux`, `integral_normSq_omegaWeighted_annulus_optimal_le`, `integral_normSq_ladderProductPoly_annulus_two_le`, **`integral_normSq_omegaWeighted_annulus_optimal_two_le`** |
| `Sieve/LadderStepMajorant` | `stepMVTMajorant`, `stepMVTMajorant_pos`, `ladderStepMVT_le_sq`, `sum_card_geomBlock_eq`, **`sum_stepMajorant_le`**; `discMajorant`, `discMajorant_pos`, `discMajorant_sq_ge`, **`sum_discMajorant_le`** |

The spectral head bound is now a single inequality with *independent* weights on the two ranges —
necessary, because the annulus's optimal weight makes the disc term diverge (it produces
`∑_j #P_j² N_j ≍ B₀ h W/log h`, which is `h/log h` too large):

```text
∫_{|w| ≤ G} ‖A_ω‖²  ≤  2( (∑_j c_j)² + (∑_j d_j)² )  +  2·(ladder defect) ,
    c_j ≥ V_j √T_j ,      d_j ≥ Vlow_j U_j √(2w₀) .
```

With the explicit choices `c_j = V_j·stepMVTMajorant`, `d_j = discMajorant`, and inputs
`V_j ≤ ε·#P_j` (annulus, Route-T) and `U_j ≤ s·B₀/Q_j` (disc, `Sieve/CofactorLowFreqBound`):

```text
∑_j c_j  ≤  √(5π/2 + 5e/2) · ε · ( (1+η)B₀W + #P ) ,
∑_j d_j  ≤  (√(2w₀)+1) · ( s(1+η)B₀W + #P + s∑_j B₀/Q_j + L ) ,
```

so the head is `≲ ε²B₀²W² + w₀s²B₀²W²` plus lower-order terms — exactly the two targets of the
accounting, and `o(W²B₀²)` under `ε → 0` and `w₀s² → 0`.

**What is left is the substitution alone**: choosing `x ↦ (β, γ, η, L, Q, w₀, G, A₀, B₀, ε, s)` in the
window `9/10 < γβ < 19/20`, checking the hypotheses of
`integral_normSq_omegaWeighted_annulus_optimal_two_le`, feeding
`integral_kernel_normSq_omegaWeighted_head_le`, and closing `omegaBudget → 0`.

### CORRECTION: the balanced smoothing width is unusable, and the fix (2026-08-18)

`Sieve/VonMangoldtTwistPrimeEnvelope.routeTTwistEnvelope` balances the smoothing width at
`D = (3K)^{w/3}`, which leaves the height term with a factor `(3K)^{2w/3}`.  The card claimed that
factor "harmless in every application"; **that is false for this application.**  The annulus needs a
bound at frequencies `|τ| ≳ (3K)^{2w/3}·polylog`, i.e. `|τ| ≥ exp(c(log x)^{β})` — a *power* of the
ladder's top — whereas the disc's Möbius contour bound only reaches `|τ| ≤ exp((log N)^{1/10})` and
its saving degrades like `exp(−c log N/(log|τ|)^9)`.  The two ranges then cannot meet for any
`β > 19/100`, let alone `β > 9/10`.

**The fix is to keep the smoothing width free and take it polylogarithmic.**
`Sieve/VonMangoldtTwistScaledWidth.exists_norm_partialSum_vonMangoldtTwist_routeT_scaled` already
exposes `D`; with `D = (log K)^4` the height term becomes `K·(log K)^{10}/|τ|` — pure `1/|τ|` decay
up to a polylogarithm — and the desmoothing costs `K log(2K)/D = K(log K)^{-3}`, which is below the
`ρ ≍ (log x)^{-2}` the accounting needs because `3γβ > 2`.  The annulus may then start at a
**polylogarithmic** `w₀`, and the disc closes with room to spare.

New modules, all axiom-clean:

| module | content |
|-|-|
| `Sieve/VonMangoldtTwistScaledEnvelope` | `scaledHeightFactor`, `scaledTwistEnvelope`, `routeTUniformRegWidth_le_one`, `scaledTwistEnvelope_nonneg`, **`scaledTwistEnvelope_mono`**, `relScaledEnvelope`, **`scaledTwistEnvelope_eq_mul`**, `rpow_neg_le_exp_neg`, **`exists_norm_sum_primeTwist_scaled_le`** — Lemma 2.3, prime form, at a free smoothing width |
| `Sieve/GeomBlockPrimesRange` | `mem_primesRange`, **`mem_geomBlock_primesRange`** — a ladder block of the designated range is exactly the primes of an interval, so the Route-T envelope applies to it |
| `Sieve/PrimeBlockScaledBound` | **`exists_norm_primeBlockPoly_scaled_le`**: `‖primeBlockPoly B w‖ ≤ (4/log 2)(Env(max b 1) + 7e⁹)` |
| `Sieve/ScaledEnvelopeEstimate` | `scaledHeightMajorant`, `scaledHeightFactor_le_majorant`, **`relScaledEnvelope_le`** — the relative envelope in elementary terms, with the width replaced by `routeTWidthPolylogLower` |
| `Sieve/GeomBlockPrimeRho` | **`exists_norm_primeBlockPoly_geomBlock_le`**: `‖primeBlockPoly (geomBlock (primesRange z₀ z) Q (1+η) j) w‖ ≤ (4/log 2)((1+η)R + 7e⁹/Q)·Q(1+η)^j` — exactly the form `Sieve/LadderPrimeMajorant.primeStepMajorant_sq_ge` consumes |
| `Sieve/LadderPrimeMajorant` | `primeStepMajorant`, `primeStepMajorant_pos`, **`primeStepMajorant_sq_ge`**, **`sum_primeStepMajorant_eq`** (geometric evaluation) |
| `Sieve/CofactorLowFreqBound` (extended) | **`exists_norm_logPoly_moebiusCoeff_Icc_one_le`**, `geomCofactorBlockAt_one_eq`, **`exists_norm_logPoly_geomCofactorBlockAt_le`** — the disc bound `U_j` on the ladder's own cofactor blocks |

**`V_j` and `U_j` are now both instantiated as Lean theorems on the ladder's own objects.**  What
remains is the numerical substitution: choosing `x ↦ (β, γ, η, L, z₀, D, w₀, G, B₀, R, s)` and
checking the elementary inequalities that `relScaledEnvelope_le` and `moebiusSharpBound` reduce to.

### The chain is closed from the two analytic inputs to `omegaBudget` (2026-08-18)

| module | content |
|-|-|
| `Sieve/SpectralHeadBound` | `primesRange_ladder_bounds`, **`integral_normSq_omegaWeighted_head_closed`** — the frequencies below the Gallagher cut, in closed form: a geometric sum for the annulus, the ladder's counting sum for the disc, plus the ladder defect |
| `Sieve/OmegaBudgetClosed` | **`omegaBudget_le_of_head`** — the whole Route E budget from a bound below the cut |

```text
‖∑_{p∈P_j} p^{2πiw}‖ ≤ ρ Q_j          (annulus, Sieve/GeomBlockPrimeRho)
‖∑_{m∈D_j} μ(m)m^{2πiw}‖ ≤ s B₀/Q_j   (disc, Sieve/CofactorLowFreqBound)
        ⟹  ∫_{|w| ≤ G} ‖A_ω‖²  ≤  2[(ρ C₁ (L B₀ + Q((1+η)^L−1)/η))² + (∑_j discMajorant_j)²]
                                    + 2·(ladder defect)                    (SpectralHeadBound)
        ⟹  omegaBudget x h z₀ z ≤ (explicit)                               (OmegaBudgetClosed)
        ⟹  AveragedMeanSquare μ hh                                         (OmegaSpectralFibre)
```

Every step above is an unconditional Lean theorem with `#print axioms` = `[propext, Classical.choice,
Quot.sound]`.  **No structural gap remains.**  What is left is the numerical substitution: choose

```text
h = exp((log x)^β) ,  z₀ = ⌈exp((log x)^{γβ})⌉ ,  Q = z₀ ,  η = (log x)^{γβ−1} ,
L = ⌊log(h/Q)/log(1+η)⌋ ,  z = ⌊Q(1+η)^L⌋ ,  B₀ = ⌊√x + h⌋ ,  D = (log 2h)^4 ,
w₀ = (log x)^{10β+2} ,  G = B₀/h ,          9/10 < γβ < 1 ,  β < 1 ,  γ ≤ 1 ,
```

and check the elementary inequalities that `relScaledEnvelope_le` and `moebiusSharpBound` reduce to.

### The substitution: parameters, and the non-spectral half of the budget — landed (2026-08-18)

| module | content |
|-|-|
| `Sieve/SpectralParameters` | `ladderEta`, `ladderWidth`, `ladderSteps`, `ladderTop`, `gallagherCut`, `annulusStart`; `ladderEta_pos`, **`tendsto_ladderEta`**, `one_le_ladderWidth`, `eventually_siftStart_lt_cardLength`, **`ladderPow_le`**, `one_le_ladderSteps`, `ladderTop_bounds`, **`ladderPow_ge`**, `ladderTop_ge_quarter`, `ladderMassConst`, `ladderMass_ge`, **`ladderMass_lower`**, **`tendsto_ladderMass`**, `eventually_ladderTop_facts` |
| `Sieve/NonSpectralBudget` | **`nonSpectral_div_le`** (the arithmetic collapse `≤ 3672/W² + 120m/W² + 480h²/(W²s)`), `card_primesLE_le`, `card_primesRange_le`, **`tendsto_cardLength_sq_div_sqrt`**, **`tendsto_nonSpectralBudget`** |

With `hh = cardLength β`, `zlo = siftStart (γβ)`, `zhi = ladderTop β γ`, **four of the five
hypotheses of `OmegaSpectralFibre.averagedMeanSquare_moebius_of_omegaBudget` are now proved**:

| hypothesis | discharged by |
|-|-|
| `hh x ≤ √x` | `ShortIntervalLength.cardLength_le_sqrt` |
| `0 < hh x` | `cardLength_pos` |
| `zlo x ≤ zhi x` | `SpectralParameters.eventually_ladderTop_facts` |
| `0 < W` | `SpectralParameters.ladderMass_lower` (in fact `W ≥ ((β−γβ)/2)·log log x + 1`) |
| the budget limit | **open — the spectral term only** |

and the two non-spectral parts of the budget itself are proved to vanish
(`tendsto_nonSpectralBudget`).  The ladder is fully specified: `Q = z₀ = ⌈exp((log x)^{γβ})⌉`,
`η = (log x)^{γβ−1}`, `L = ⌊log(h/Q)/log(1+η)⌋`, `z = ⌊Q(1+η)^L⌋`, with `Q(1+η)^L ≤ h` and
`Q(1+η)^L ≥ h/(1+η)`, so `h/4 ≤ z ≤ h`.

### The disc side of the substitution is closed; the width comparisons are proved (2026-08-18)

| module | content |
|-|-|
| `Sieve/RelMoebiusSharp` | `relMoebiusSharp`, **`moebiusSharpBound_eq_mul`**, `relMoebiusSharp_nonneg`, **`relMoebiusSharp_antitone`**, **`tendsto_relMoebiusSharp`**, **`exists_norm_logPoly_geomCofactorBlockAt_rel_le`** |
| `Sieve/RouteTWidthAntitone` | **`routeTWidthPolylogLower_antitone`**, **`scaledHeightMajorant_le_of_le`** |

`relMoebiusSharp N = 3e^{−c(log N)^{1/10}}/π + 1/smoothRatio N + 1/N` is antitone and vanishes, so a
single value at the *shortest* cofactor block bounds every step:

```text
‖∑_{m ∈ D_j} μ(m)m^{2πiw}‖ ≤ relMoebiusSharp(N_min) · (B₀/Q_j) ,   N_min ≤ ⌊B₀/Q_j⌋ for all j,
```

which is exactly the `U_j ≤ s·B₀/Q_j` that `discMajorant_sq_ge` consumes, with `s = relMoebiusSharp N_min`
and `N_min ≍ √x/h`, so `s ≍ exp(−c((log x)/2)^{1/10})` — beating every power of `log x`, hence
`√w₀·s → 0` for the polylogarithmic `w₀`.

`routeTLogHeightEnvelope t = 2 log(t+2) + 1` is explicit, so the width surrogate is antitone in the
frequency and the height cost is bounded uniformly over the annulus by its value at the top:

```text
scaledHeightMajorant A τ ≤ 1/t₀ + log(3|σ|/2)/routeTWidthPolylogLower A σ   for t₀ ≤ |τ| ≤ |σ| .
```

**Remaining: the annulus `ρ` and the final assembly.**  `relScaledEnvelope_le` now has every input
bounded uniformly; what is left is to package it into a single explicit `R`, feed
`exists_norm_primeBlockPoly_geomBlock_le`, and compose with `SpectralHeadBound` and
`OmegaBudgetClosed`.

### `ρ` is explicit and the budget is composed (2026-08-18)

| module | content |
|-|-|
| `Sieve/AnnulusRelBound` | `relScaledMajorant`, `relScaledMajorant_nonneg`, **`relScaledEnvelope_le_uniform`**, **`exists_norm_primeBlockPoly_geomBlock_rho_le`** |
| `Sieve/OmegaBudgetExplicit` | `spectralHead`, **`omegaBudget_le_explicit`** |

```text
relScaledMajorant Ctot D Lx Hmaj μ q t₀ xmin
  = Ctot·D²(Lx²/t₀ + Hmaj(e^{−μq} + 1/t₀²))/(2π) + (log 2 + Lx)/D + 2Lx/√xmin
```

is a uniform majorant for `relScaledEnvelope A delta Ctot D τ x` whenever `t₀ ≤ |τ| ≤ |σ|`,
`xmin ≤ x`, `log x ≤ Lx`, `q ≤ log x`, `μ ≤ min delta (routeTWidthPolylogLower A τ)/2` and
`Hmaj ≥ 1/t₀ + log(3|σ|/2)/routeTWidthPolylogLower A σ` — every one of which is now a proved
monotonicity statement.  Feeding it to `exists_norm_primeBlockPoly_geomBlock_le` gives

```text
ρ = (4/log 2)·((1+η)·relScaledMajorant … + 7e⁹/Q) ,
‖∑_{p ∈ P_j} p^{2πiw}‖ ≤ ρ·Q(1+η)^j     on the annulus.
```

`omegaBudget_le_explicit` then composes the cut-window head bound with the Gallagher split:

```text
omegaBudget x h z₀ z
  ≤ 16√x( 2δ²·spectralHead + 4(5π/2·Ec)/(π²G) + 4(spectralHead + 5e/2·B₀·Ec)/(3π²G²) )
    + 204(|P|+1)²(√x+1) + 2(h+1)(2h+1)(4(√x/2+h+1)·mertensS z + 4π(z) + 8π(z)²) ,
spectralHead = 2[(ρ·C₁·(L·B₀ + Q((1+η)^L−1)/η))² + (∑_j discMajorant_j)²] + 2·(ladder defect) .
```

**Every quantity in that inequality is an elementary function of `x, h, Q, η, L, B₀, G, w₀, ρ, s`.**
The whole remaining task is to substitute the parameter functions and check that the quotient by
`W²h²√x` tends to zero — the non-spectral half of which is already done
(`tendsto_nonSpectralBudget`).

### OBSTRUCTION found in the composition: the affine majorant must come from the ladder (2026-08-18)

Substituting into `omegaBudget_le_explicit` and dividing by `W²h²√x`, the Gallagher-tail term

```text
16√x · 4(spectralHead + (5e/2)B₀·Ec)/(3π²G²) / (W²h²√x)
   =  64(spectralHead + (5e/2)B₀·Ec)/(3π²G²W²h²)
```

does **not** vanish: with `Ec ≍ 2B₀W²` (`sum_normSq_omegaCoeff_Icc_le`) and `G = B₀/h`, so `G²h² = B₀²`,
the second summand is `64·5e B₀²W²/(3π²B₀²W²) = 320e/(3π²) ≈ 29`, a constant.  Enlarging `G` does not
help: `ladderStepMVT_le_sq` needs `G ≤ B₀/Q_j` for every `j < L`, and the worst step `Q_{L−1} ≍ h/(1+η)`
caps `G` at `B₀(1+η)/h`.

**Diagnosis.**  `(5e/2)B₀·Ec` is the mean value theorem applied to the *whole* polynomial `A_ω` over
`[1,B₀]`.  The exposé never does that: it applies the mean value theorem to each **cofactor**
polynomial, of length `N_j = B₀/Q_j`, which is smaller by the factor `Q_j`.  The affine majorant fed
to Gallagher's dyadic tail must therefore come from the ladder as well, and only above the height
`T₀` at which the Route-T saving expires may the trivial mean value theorem be used.

**Fix (no new mathematics, only a `T`-dependent step majorant).**
`integral_normSq_omegaWeighted_annulus_optimal_two_le` already takes the cut `G` as a parameter, so
instantiating it at each height `T` gives `∫_{|w| ≤ T}‖A_ω‖² ≤ 2[(∑_j c_j(T))² + (∑_j d_j)²] + 2·defect(T)`,
provided the step majorant is generalised from `stepMVTMajorant` (which assumed `T ≤ B₀/Q_j`) to

```text
c_j(T) = ρ Q_j ( √((5π/2)·T·(N_j+1)) + √((5e/2)·N_j·(N_j+1)) ) ,
```

using `ladderStepMVT = (5π/2)T(N_j+1) + (5e/2)⌊N_j⌋(N_j+1) ≤ a² + b²` and `a²+b² ≤ (a+b)²`.  Then
`(∑_j c_j(T))² ≤ 2(5π/2)T·ρ²(∑_j Q_j√(N_j+1))² + 2(5e/2)ρ²(∑_j Q_j N_j)²` is **affine in `T`**, with

```text
α₁ ≍ 10π ρ² B₀ h/η² ,      β₁ ≍ 10e ρ² L² B₀² .
```

Above `T₀` (the height at which the Route-T contour saving expires, `T₀ ≥ B₀` since `γβ > 9/10`) the
trivial majorant `α₂T + β₂`, `α₂ = (5π/2)Ec`, `β₂ = (5e/2)B₀Ec`, is used.  The two regimes combine
into a *single* affine majorant valid for all `T ≥ G`:

```text
α := α₁ + α₂ + β₂/T₀ ,    β := β₁         (for T ≥ T₀ : α₂T + β₂ ≤ (α₂ + β₂/T₀)T).
```

Dividing the Gallagher output `2δ²β₀ + 4α/(π²G) + 4β/(3π²G²)` by `W²h²` at `G = B₀/h`, `δ ≍ h/B₀`:

| term | size | vanishes iff |
|-|-|-|
| `2δ²β₀` | `≍ ρ²L²h²` (β₀ = head) | `ρL = o(W)` |
| `4α₁/(π²G)` | `≍ 40ρ²h²/(πη²)` | `ρ/η = o(W)` |
| `4α₂/(π²G)` | `≍ (20/π)W²h` | always (`1/h → 0`) |
| `4(β₂/T₀)/(π²G)` | `≤ (20e/π²)W²h` | always |
| `4β₁/(3π²G²)` | `≍ (40e/3π²)ρ²L²h²` | `ρL = o(W)` |

so the whole spectral term vanishes under the single condition **`ρ·max(L, 1/η) = o(W)`**, which the
superpolylogarithmically small `ρ` satisfies with room to spare.

### The obstruction is fixed (2026-08-18)

| module | content |
|-|-|
| `Sieve/LadderStepAffine` | `stepAffineMajorant`, `stepAffineMajorant_pos`, **`stepAffineMajorant_sq_ge`** (valid at *every* height, via `(5π/2)T(N+1) + (5e/2)N(N+1) = a²+b² ≤ (a+b)²`), **`sum_stepAffineMajorant_sq_le`** (the single sum is affine in the height) |
| `Sieve/LadderAffineMajorant` | `ladderDefectSum`, `ladderAffineSlope`, `ladderAffineConst`, **`integral_normSq_omegaWeighted_affine_le`**, **`affineMajorant_two_regime`** |
| `Sieve/OmegaBudgetLadderTail` | **`integral_kernel_normSq_omegaWeighted_ladder_le`**, `ladderDefectSum_nonneg`, `ladderAffineSlope_nonneg`, `ladderAffineConst_nonneg`, **`omegaBudget_le_ladder_final`** |

```text
omegaBudget x h z₀ z
  ≤ 16√x( 2δ²(αL·G + βL) + 4(αL + (5π/2)Ec + (5e/2)B₀Ec/T₀)/(π²G) + 4βL/(3π²G²) )
    + (the two non-spectral terms, already proved to vanish)
```

with `αL = ladderAffineSlope L B₀ Q η ρ`, `βL = ladderAffineConst z₀ z L B₀ Q η ρ s w₀`, both
nonnegative, both built from the ladder — so the Gallagher tail no longer carries `B₀·Ec/G²`.
`#print axioms omegaBudget_le_ladder_final` = `[propext, Classical.choice, Quot.sound]`.

Its hypotheses are exactly the two analytic inputs on the *fixed* ranges
`|w| ∈ [w₀, T₀]` (annulus) and `|w| ≤ w₀` (disc), plus `Q = z₀`, `z = ⌊Q(1+η)^L⌋`, `B₀ = ⌊√x+h⌋`,
`1 ≤ G ≤ T₀`, `0 ≤ w₀ ≤ G`, `1 ≤ L`, `0 < ρ`, `0 ≤ s`.

### The master budget theorem (2026-08-18)

| module | content |
|-|-|
| `Sieve/ContourParamMono` | `contourParam_mono`, `contourParam_ge`, `tendsto_contourParam` |
| `Sieve/DiscBoundUniform` | **`exists_disc_bound_uniform`** — one admissibility check at the shortest cofactor block supplies the disc hypothesis for every step |
| `Sieve/AnnulusBoundUniform` | **`exists_annulus_bound_uniform`** — the width and height cost at the top of the annulus serve for every frequency in it |
| `Sieve/OmegaBudgetMaster` | `ladderRho`, **`exists_omegaBudget_master`** |

`exists_omegaBudget_master` bounds `omegaBudget x h z₀ z` by a completely explicit expression whose
hypotheses are **elementary inequalities among the parameters only** — no integral, no polynomial,
no analytic input.  The remaining work is the substitution of the parameter functions and the limit.

### The substitution is done: the budget inequality holds at the chosen parameters (2026-08-18)

| module | content |
|-|-|
| `Sieve/LadderBlockFacts` | `ladderBlockTop_le/_ge`, `le_max_ladderBlock`, `max_ladderBlock_le`, `le_floor_cofactor` |
| `Sieve/BudgetSubstitution` | `budgetB`, `budgetT`, `budgetNmin`, `budgetMu`, `budgetHmaj`, `budgetRho`, `budgetS`; `one_le_gallagherCut`, `gallagherCut_le_budgetT`, **`tendsto_gallagherCut`**, `tendsto_exp_quarter_div_rpow`, `eventually_rpow_log_le_exp`, **`annulusStart_le_gallagherCut`**, `tendsto_budgetNmin`, `tendsto_rpow_sub_log`, `tendsto_exp_rpow_div_rpow`, `eventually_gallagherCut_ge_exp`, **`eventually_annulus_admissible`**, **`exists_eventually_omegaBudget_le`** |

```text
∃ A delta Ctot, 0 < delta ∧ 0 < Ctot ∧ ∀ᶠ x,
  omegaBudget x (cardLength β x) (siftStart (γβ) x) (ladderTop β γ x) ≤ EXPLICIT(A,delta,Ctot,β,γ,x)
```

All parameters are fixed: `h = exp((log x)^β)`, `z₀ = ⌈exp((log x)^{γβ})⌉`, `η = (log x)^{γβ−1}`,
`L = ⌊log(h/z₀)/log(1+η)⌋`, `z = ⌊z₀(1+η)^L⌋`, `B₀ = ⌊√x+h⌋`, `G = B₀/h`, `T₀ = B₀`,
`w₀ = (log x)^{10β+2}`, `D = (log 2h)^4`, `Lx = (log x)^β`, `q = log z₀`, `xmin = z₀`,
`Nmin = ⌊G⌋`, `μ` and `Hmaj` at the top of the annulus.

Every side condition is verified: the Gallagher cut is `≥ 1`, below `T₀`, and above the
polylogarithmic annulus threshold (`annulusStart_le_gallagherCut`, via `exp(log x/4)` beating every
power of `log x`); the shortest cofactor block is `≥ exp(log x/5)`, so the Möbius contour bound
admits every frequency of the disc (`eventually_annulus_admissible`, via a stretched exponential
beating every power).

**What remains is the single limit** `EXPLICIT(x)/(W² h² √x) → 0`.

### Parameter re-tuning forced by the ladder defect (2026-08-18)

Computing `ladderAffineConst`'s defect part at the first choice `η = (log x)^{γβ−1}` gives

```text
2(5e/2)⌊B₀(1+η)⌋·ladderDefectSum / (B₀²W²)  ≍  (log B₀/log Q)·L·η² / W²
   ≍ (log x)^{1−γβ}·(log x)^{β}·η / W²  =  (log x)^{β} / W²  →  ∞ ,
```

because `L ≍ (log x)^β/η`.  The exponent of `η` must therefore satisfy `η ≲ (log x)^{γβ−β−1}`, and
with that choice the same quantity is `≍ 1/W² → 0`.  The annulus threshold must then satisfy
`w₀ ≳ (log x)^{12β+1−γβ}`, which is below `(log x)^{13}` for every admissible pair.  So

```text
ladderEta β γ x := (log x)^{γβ − β − 1} ,      annulusStart β x := (log x)^{13} .
```

Both changed in `Sieve/SpectralParameters`; `Sieve/BudgetSubstitution` and the whole chain rebuild
unchanged, and `exists_eventually_omegaBudget_le` remains axiom-clean.

With these, `L ≍ (log x)^{1+2β−γβ}` and `ρ ≲ (log x)^{10β−13}`, so `ρL ≲ (log x)^{12β+1−γβ−13} → 0`
and `ρ/(ηW) ≲ (log x)^{−β}/W → 0` — the two conditions the spectral limit needs.

### The ladder's sums, bounded (2026-08-18)

| module | content |
|-|-|
| `Sieve/LadderGeomSums` | **`sum_ladderEndpoint_le`** (`∑_j Q_j ≤ h/η`), **`sum_inv_ladderEndpoint_le`** (`≤ 2/(Qη)`), **`sum_inv_sq_ladderEndpoint_le`** (`≤ 2/(Q²η)`), **`sum_sqrt_ladderEndpoint_le`** (`≤ L√h`) |
| `Sieve/LadderSumBounds` | **`sum_S1_le`**: `∑_j Q_j√(B₀/Q_j+1) ≤ L√(B₀h) + h/η`; **`sum_S2_le`**: `∑_j Q_j√((B₀/Q_j)(B₀/Q_j+1)) ≤ L·B₀ + h/η`; **`ladderDefect_inner_le`**: the defect's inner sum `≤ L((1+B₀)η²+5) + 5h + 2(ηB₀+(1+B₀)η)/(Qη) + 2B₀/(Q²η)` |

Substituting these into `ladderAffineSlope` and `ladderAffineConst` and normalising by `W²h²√x`:

```text
ρ²S₁²/(B₀W²h) ≤ 2ρ²L²/W² + 2ρ²h/(η²B₀W²) ,      ρ²S₂²/(B₀²W²) ≤ 2ρ²L² /W² + 2ρ²h²/(η²B₀²W²) ,
(defect)/(B₀W²) ≍ (log B₀/log Q)·L η²/W² = 1/W² ,
```

each of which vanishes under `ρL/W → 0` — the condition the parameter re-tuning secures.

### Toward the limit: affine bounds, width bounds, polylog limits (2026-08-18)

| module | content |
|-|-|
| `Sieve/LadderAffineBounds` | `ladderDefectSum_le`, **`ladderAffineSlope_le`**, **`ladderAffineConst_le`** — slope and constant in terms of `L, B₀, Q, η, ρ, s, w₀, h` alone |
| `Sieve/WidthEnvelopeBounds` | `inv_routeTWidthPolylogLower_eq`, `routeTLogHeightEnvelope_le` (`≤ 10 + 2 log\|τ\|`), **`inv_routeTWidthPolylogLower_le`**, **`routeTWidthPolylogLower_ge`** |
| `Sieve/BudgetWidthBounds` | `budgetZ = 18 + log x`, `budgetWinv`, `eventually_envelope_le`, **`eventually_budgetHmaj_le`**, **`eventually_budgetMu_ge`** |
| `Sieve/SpectralParameters` (extended) | `log_one_add_ge_half` (from the corpus's `Sieve/BlockCount.log_one_add_ge`), **`ladderSteps_le`**: `L ≤ 2(log x)^β/η` |
| `Sieve/PolylogLimits` | **`tendsto_rpow_log_mul_exp_neg`**, `tendsto_rpow_log_of_neg` |

At the top of the annulus the frequency is `2πB₀ ≍ √x`, so the Route-T height envelope is at most
`18 + log x` and

```text
budgetHmaj ≤ 1 + (1 + log x)·budgetWinv ,     budgetMu ≥ min(delta, 1/budgetWinv)/2 ,
budgetWinv = 10 D_A (18+log x)^{9/10}(1 + log(18+log x))² .
```

Since `q = log z₀ ≥ (log x)^{γβ}` and `γβ > 9/10`, `μq ≳ (log x)^{γβ−9/10}/(log log x)² → ∞`, so the
contour factor `e^{−μq}` beats every polylogarithm — which is what `tendsto_rpow_log_mul_exp_neg`
converts into a limit.

**Remaining: the six pieces of `ρ·L → 0`, then the seven normalised budget terms.**

### `ρ·L → 0` is proved (2026-08-18)

| module | content |
|-|-|
| `Sieve/RhoLimit` | `rpow_comb`, `rpow_comb3`, `rhoMajorant`, **`tendsto_rhoMajorant`**, **`eventually_rhoBound_mul_steps_le`**, **`tendsto_budgetRho_mul_steps`** |
| `Sieve/RhoLimitPieces` (extended) | `eventually_ladderWidth_ge`, `eventually_budgetHmaj_poly`, `eventually_siftStart_ge`, `eventually_ladderSteps_poly` |

The six pieces, with `t = log x`, `D ≤ 16t^{4β}`, `H ≤ K_A t²`, `t₀ = 2πt^{13}`, `L ≤ 2t^{2β+1−γβ}`,
`Q ≥ exp(t^{γβ})`, `e^{−μq} ≤ exp(−t^{(γβ−9/10)/4})`:

| piece | majorant | vanishes because |
|-|-|-|
| `Ctot D²Lx²/(2πt₀)·L` | `(512Ctot/36) t^{12β+1−γβ−13}` | `12β+1−γβ−13 < 0` |
| `Ctot D²H e^{−μq}/(2π)·L` | `(512CtotK_A/6) t^{10β+3−γβ}e^{−t^{(γβ−9/10)/4}}` | stretched exponential |
| `Ctot D²H/(2πt₀²)·L` | `(512CtotK_A/216) t^{10β+3−γβ−26}` | exponent `< 0` |
| `(log2+Lx)/D·L` | `4 t^{1−β−γβ}` | `β, γβ > 9/10` |
| `2Lx/√Q·L` | `4 t^{3β+1−γβ}e^{−t^{γβ}/2}` | stretched exponential |
| `7e⁹/Q·L` | `14e⁹ t^{2β+1−γβ}e^{−t^{γβ}}` | stretched exponential |

**`tendsto_budgetRho_mul_steps` is the single analytic condition the spectral limit needs.**

## Normalised budget: the split and the energy term

`Sieve/BudgetTermSplit.budget_div_eq` splits the substituted budget divided by `W²h²√x` into four
groups, and `spectral_terms_le` collapses the three spectral groups into three quotients:

```
32δ²(αL·G+βL)/(W²h²) + 64(αL + (5π/2)Ec + (5e/2)B₀Ec/T₀)/(π²G·W²h²) + 64βL/(3π²G²W²h²)
  ≤ 136·αL/(B₀hW²) + 140·Ec/(B₀hW²) + 131·βL/(B₀²W²)
```

using only `δ ≤ h/√x`, `G·h = B₀`, `T₀ = B₀`, `B₀² ≤ 4x`, `W ≥ 1`, `π ≥ 3`, `e ≤ 3`.

Landed since:

- `Sieve/BudgetScaleLimits` — `tendsto_cardLength_div_budgetB` (`h/B₀ → 0`),
  `tendsto_inv_cardLength`, and `eventually_inv_eta_le_steps` (`1/η ≤ 2L` eventually, so
  `ρ/η ≤ 2ρL → 0`).
- `Sieve/BudgetSRate` — `eventually_log_rpow_le_scaled`, `eventually_budgetS_le`
  (`budgetS ≤ 3exp(−(log x)^{1/40})`), `tendsto_rpow_log_mul_budgetS` (any power of the logarithm
  against the Möbius majorant vanishes).  The cutoff is `budgetNmin ≥ exp(log x/5)`, so all three
  summands of `relMoebiusSharp` are stretched exponentials in `log x`.
- `Sieve/EnergyQuotientLimit` — `sqrt_le_budgetB`, `tendsto_inv_budgetB`,
  `tendsto_mertensS_div_cardLength`, and `tendsto_energy_quotient`: the middle quotient
  `Ec/(B₀hW²) → 0`, majorised by `8·mertensS z/h + 16/B₀ + 64h/B₀ + 2/h`.

Remaining: `αL/(B₀hW²) → 0` and `βL/(B₀²W²) → 0`.

## The three normalised quotients, all vanishing

- `Sieve/EnergyQuotientLimit.tendsto_energy_quotient` — `Ec/(B₀hW²) → 0`.
- `Sieve/SlopeQuotientLimit.tendsto_slope_quotient` — `αL/(B₀hW²) → 0`, via the pure arithmetic
  lemma `slope_quotient_arith` (annulus group → `(ρL)²` and `(ρ/η)²(h/B₀)`; cofactor group → five
  polynomial quotients) plus `slopeMajorant`/`tendsto_slopeMajorant`.
- `Sieve/ConstQuotientLimit.tendsto_const_quotient` — `βL/(B₀²W²) → 0`, via `const_annulus_le`,
  `const_disc_le`, `const_cofactor_le`, `const_quotient_arith`, `const_bound_mono`,
  `discInner`/`constMajorant`/`tendsto_constMajorant`.

Two corrections found while assembling these.  In the cofactor group the sifting cutoff `Q` must be
kept in the denominator of the `(ηB₀+(1+B₀)η)(2/(Qη))` and `B₀(2/(Q²η))` terms: dividing by `B₀²W²`
instead of `B₀hW²` turns `6B₀/Q` into `6/Q`, and bounding `Q ≥ 1` there would leave
`6(log x)^{1−γβ}/W² → ∞`.  And the number of ladder steps satisfies `1/η ≤ 2L` eventually
(`eventually_inv_eta_le_steps`), which is what converts the `(ρ/η)²` of the annulus group into
`(ρL)²`.

Supporting limits added: `Sieve/PolyDecayLimits` (`tendsto_rpow_log_div_sqrt`,
`tendsto_rpow_log_div_cardLength`, `tendsto_rpow_log_mul_cardLength_div_sqrt`,
`tendsto_rpow_log_div_siftStart`), `Sieve/BudgetSRate.tendsto_rpow_log_mul_budgetS`.

Remaining: assemble `budget_div_eq` + `spectral_terms_le` + the three quotient limits +
`tendsto_nonSpectralBudget` into `omegaBudget/(W²h²√x) → 0`, then `AveragedMeanSquare`.

## PROGRAMME OBJECTIVE MET — Matomäki–Radziwiłł is Lean-proved

`Sieve/MoebiusMeanSquare.lean`:

```lean
theorem averagedMeanSquare_moebius :
    AveragedMeanSquare (fun n : ℕ => ((ArithmeticFunction.moebius n : ℤ) : ℝ))
      (cardLength (99 / 100))
```

unconditional, `#print axioms` = `[propext, Classical.choice, Quot.sound]`, no `sorry`.  The general
form `averagedMeanSquare_moebius_cardLength` holds for every `9/10 < β < 1` together with a `γ`
satisfying `0 < γ < 1` and `9/10 < γβ < 1`.  The window is `h = exp((log x)^β)`, far below every
power of `x`.

The final chain:

1. `Sieve/BudgetLimit.tendsto_normalised_omegaBudget` — `omegaBudget/(W²h²√x) → 0`, assembled from
   `budget_div_eq`, `spectral_terms_le`, `tendsto_slope_quotient`, `tendsto_energy_quotient`,
   `tendsto_const_quotient`, `tendsto_nonSpectralBudget`.
2. `OmegaSpectralFibre.averagedMeanSquare_moebius_of_omegaBudget` converts it into the fibre mean
   square.

And Route E's Theorem `(3)` is now unconditional, `Sieve/RouteEMoebiusUnconditional.lean`:

```lean
theorem route_e_sign_density_unconditional {s : ℤ} (hs : s = 1 ∨ s = -1) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x in atTop,
      squarefreeDensity ^ 2 / 2 - squarefreeDensity ^ 2 * RHTower.coprimeSharedPrimeDensity - ε
        ≤ coprimeSignClassCount x (cardLength (99 / 100) x) s
          / (cardLength (99 / 100) x * Real.sqrt x * Real.log 2)

theorem route_e_signClass_nonempty_unconditional {s : ℤ} (hs : s = 1 ∨ s = -1) :
    ∀ᶠ x in atTop, (coprimeSignClass x (cardLength (99 / 100) x) s).Nonempty
```

(the two squarefree inputs come from `SquarefreeMaximalWindow.maximalWindowDevMeanSquare_moebius_sq`
and `CoprimeMaximalWindow.maximalWindowDevMeanSquareAt_coprime`, both already unconditional in the
corpus, routed through `FibreDevSeparation.averagedMeanSquareDensityAt_of_maximal`).

## What the two reciprocal-marker cards still need

Their step 1 is `Sieve/GoodStartMarkov.card_le_good_add_meanSquare`, whose input is
`∑_{t ∈ S} (∑_{n ∈ (t, t+L]} μ(n))² ≤ V` over *consecutive integer starts* — the corpus's
`DyadicTranslates.dyadicMeanSquare μ ℓ A B`.  That is a different object from the fibre mean square
just proved: the fibre form averages over the multiplicative pair decomposition, the dyadic form over
every integer start.

The corpus already reduces the strongest shape to it:

- `WindowPartialSum`, `MaximalDeviation`, `DyadicTranslates`, `MaximalWindowReduction` reduce
  `MaximalWindowMeanSquare` to `dyadicMeanSquare` at `log₂ h` dyadic lengths;
- `DyadicMeanSquareGallagher.dyadicMeanSquare_le_gallagher` and
  `LinearMeanSquareGeneric.dyadicMeanSquare_le_largeValues` bound `dyadicMeanSquare` by an integral
  of `‖logPoly μ [1,M]‖²` — of the **plain** Möbius polynomial.

The gap is exactly the Ramaré step: the spectral budget of this programme controls the
**Ω-weighted** polynomial `omegaWeightedMoebiusPoly`, and passing from it to the plain polynomial
needs the Ramaré weight identity plus a sieve bound on the integers with no prime factor in the
designated range.  `Sieve/RamareBlockSplit.lean` is where that lives.

## The integer-start route, scoped and costed

`Sieve/LinearMeanSquareBounded.lean` (built, axiom-clean) carries the whole linear mean-square chain
of `LinearMeanSquareGeneric` for coefficients of size `C` instead of `1`:
`blockCostGC L ε C G = 2G + 2C²(εL+1)²log(1+ε)`, up to

```lean
theorem dyadicMeanSquare_le_bound (f : ℕ → ℝ) {C : ℝ} (hC0 : 0 ≤ C) (hf : ∀ n, |f n| ≤ C) … :
    dyadicMeanSquare f ℓ A B
      ≤ ((A : ℝ) * (1 + ε) ^ K') * ((K' : ℝ) * blockCostGC (ℓ : ℝ) ε C G)
```

This is what the `ω`-weighted Möbius coefficients need: `‖omegaCoeff P n‖ = |μ(n)|·ω_P(n)` and
`Sieve/LadderErrorBudget.card_designatedPrimes_dvd_le` gives `ω_P(n) ≤ log B₀ / log Q ≍ (log x)^{1−γβ}`
— polylogarithmic, not one.

The Turán–Kubilius transfer is also already in the corpus
(`Sieve/RoughCountTuran.sum_sq_card_primeFactorsIn_Icc_le`, `sum_card_primeFactorsIn_Icc_le`):

```text
∑_{n ≤ M} (ω_P(n) − W)²  ≤  M·W + 2|P|·W ,
W²·dyadicMeanSquare μ ℓ A B ≤ 2·dyadicMeanSquare (μ·ω_P) ℓ A B + 4ℓ²·(M·W + 2|P|·W) ,
```

and the second term, divided by `W²ℓ²K`, is `≍ 1/W → 0`.

### The one obstruction, exactly

With `A ≍ √x/2`, `K ≍ √x/2`, `ℓ = h`, `C ≍ (log x)^{1−γβ}` the two costs impose

```text
G/(W²h²)  ≪  ε  ≪  W/C = W (log x)^{γβ−1} ,
```

so the route needs the budget quotient to decay like a **power** of `log x`, not merely to vanish.
It does not: `constMajorant`'s third group carries the term `10e·4/W²`, coming from
`M·(L·η²) = (log x)^{1−γβ} · 2(log x)^{γβ−1} = 2`, and `1/W² ≍ 1/(log log x)²` is not `≪
(log x)^{γβ−1}`.

The fix is a parameter change, not new mathematics: the ladder step ratio has slack.  Replacing

```text
ladderEta β γ x = (log x)^(γβ − β − 1)   by   (log x)^(γβ − β − 1 − κ)
```

multiplies `L` by `(log x)^κ` and divides `M·L·η²` by `(log x)^κ`.  At `κ = 1/4` and the admissible
window `9/10 < β < 1`, `9/10 < γβ < 1`:

| quantity | exponent bound | needs |
|-|-|-|
| `ρ·L` | `< −0.65` | `< 0` ✓ |
| `(log2+Lx)/D · L` | `< −0.55` | `< 0` ✓ |
| `M·L·η²` | `−0.25` | `< 0` ✓ |
| `G/(W²h²)` vs `W(log x)^{γβ−1}` | `−0.25` vs `> −0.1` | `γβ > 3/4` ✓ |

so every limit of this programme survives, and the budget quotient becomes `O((log x)^{−1/4})`,
which is what the integer-start route needs.  The refactor touches `SpectralParameters`,
`RhoLimitPieces`, `RhoLimit`, `SlopeQuotientLimit`, `ConstQuotientLimit` — exponent bookkeeping only.

## CORRECTION: the corpus's Route-T exponent 9/10 is NOT a barrier to milestone B (2026-08-19)

The card and the memory record "the window the corpus's Route-T width exponent 9/10 forces:
`β > 9/10`", and conclude that lowering that exponent (Vinogradov–Korobov) is what moves the
threshold down.  **That is true of milestone A (the corpus's own fibre/Route-T route) and false of
milestone B (exposé §4).**  §4 is compatible with exponent 9/10 as it stands, and milestone B alone
reaches `h ≥ exp(10(log log X)^{10/9})` — far below every `exp((log X)^β)`, hence it closes the
window range of *both* reciprocal-marker cards and of the coprime square-root card.

### Where Lemma 2.3 is actually used in §4

§3 applies Lemma 2.3 to the **small** prime sum `∑_{p∈P_j}p^{iy}`, and that is why §3 needs
`log P_j ≥ (log h)^{9/10} ≥ (log X)^{27/40}` — an exponent below `2/3+δ` only because the exposé has
Vinogradov–Korobov.  §4 explicitly abandons that:

> "Note that we may not be able to use Lemma 2.3 to bound `∑_{p∈P_j}p^{iy}` since the range for `p`
> might lie below `exp((log X)^{2/3+δ})`.  Define `E_j = {y : |∑_{p∈P_j}p^{iy}| ≥ P_j/(log P_j)²}`."

In §4 the small-prime sum is handled by the **exceptional-set split** (Lemmas 2.5 + 2.6), and
Lemma 2.3 is used **only once**, at (38), on the *large* prime sum `∑_{q∈Q_k}q^{iy}`.

### The one change the corpus's exponent forces

The exposé takes `Q` = primes in `[exp((log X)^{4/5}), exp((log X)^{9/10})]`, giving
`W(Q) = (9/10 − 4/5)·log log X = (1/10)log log X`.  With the corpus's Lemma 2.3 valid only above
`exp((log X)^{9/10+δ})`, take instead

```text
        Q = primes in [ exp((log X)^a), exp((log X)^b) ],     9/10 < a < b < 1 ,
        W(Q) = (b − a)·log log X  →  ∞ .
```

`W(Q)` depends only on the **gap between the exponents**, not on their size, and there is room
between `9/10` and `1`.  Everything else in §4 survives verbatim: the two places the top of `Q`
enters are
`Q_k·P_j ≪ X` (from the diagonal term of Lemma 2.6) and `Q_k·P_j ≪ X^{1/14−ε}` (from the
Halász–Montgomery term `|E_j|T^{1/2}log T` with `|E_j| ≪ X^{3/7+ε}`), and both hold with enormous
room because `Q_k, P_j = X^{o(1)}`.  The `P` side of §4 needs only `(log X)^7 ≤ P_j ≤ X^ε`, which
`log P_j ≍ (log h)^{9/10}` and `log h ≥ 10(log log X)^{10/9}` give with no zero-free input at all.

### Consequence for the programme

Milestone B is reachable **with the corpus's current assets**: Lemmas 2.1, 2.3, 2.4 (used in §3 and
re-used here), 2.5 (`Sieve/DirichletPowerProductSplit`, free-exponent form) and 2.6
(`Sieve/DyadicSecondEnvelopeClosed.halaszMontgomery_dyadic_explicit`) are all corpus theorems.  What
remains is the §4 assembly:

1. the double weight `ω_P(n)ω_Q(n)` and its Turán–Kubilius second moment (the corpus owns the
   single-weight version, `Sieve/RoughCountTuran`);
2. the decomposition `(31)`–`(32)` and the reduction `(34)` (the same Cauchy–Schwarz-over-blocks
   bookkeeping as `(24)`–`(27)`, which the corpus already carries for the single weight);
3. the exceptional set `E_j` of `(35)` and the two-case split;
4. the non-exceptional case: Lemma 2.4 exactly as in `(28)`;
5. the exceptional case: `(36)`–`(40)` — Lemma 2.3 on the `Q_k` sum, then Lemma 2.5 for `|E_j|` and
   Lemma 2.6 on `E_j`.

No new analytic input.  Formalising Vinogradov–Korobov is **not** on the critical path for the
route-e cards, and the "lower the corpus exponent" plan recorded above should be retired in favour
of this one.

### Milestone B, brick 1 — the double weight `ω_P·ω_Q` (2026-08-19)

`Sieve/JointTuranKubilius.lean`, axiom-clean, wired.  This is the second display of exposé §4:

```text
sum_sq_joint_deviation_le (hP : ∀ p ∈ P, p.Prime) (hQ : ∀ q ∈ Q, q.Prime)
    (hPQ : Disjoint P Q) (M : ℕ) :
  ∑_{n ≤ M} (ω_P(n)·ω_Q(n) − W(P)W(Q))²
    ≤ M·W(P)W(Q)·(W(P) + W(Q) + 1) + 2·W(P)W(Q)·|P|·|Q|
```

which is the exposé's `≪ X W(P)²W(Q)²(1/W(P) + 1/W(Q))` with the prime-counting error exposed.

**The mechanism, and why it is not a repetition of the single-weight case.**  The fourth moment
`∑_n ω_P(n)²ω_Q(n)²` is a quadruple sum of products of four divisibility indicators.  Because `P`
and `Q` are disjoint sets of primes, such a product is the indicator of *one* modulus,

```text
quadModulus p₁ p₂ q₁ q₂ = lcmPair p₁ p₂ · lcmPair q₁ q₂ ,   lcmPair a b = if a = b then a else a·b
```

(`indicator_quad_le`, resting on `coprime_lcmPair`), so the quadruple sum **factorises**:

```text
∑_n ω_P²ω_Q² ≤ M · (∑_{p₁,p₂} 1/lcmPair) · (∑_{q₁,q₂} 1/lcmPair) ≤ M(W_P²+W_P)(W_Q²+W_Q)
```

— `sum_sq_mul_sq_primeFactorsIn_le`, with `sum_inv_lcmPair_le` supplying the pair sums (the diagonal
`a = b` is exactly the `+W` term).  Together with the matching first-moment lower bound
`sum_mul_card_primeFactorsIn_ge` (`M·W_PW_Q − |P||Q| ≤ ∑_n ω_Pω_Q`) the variance telescopes: the
`W_P²W_Q²` terms cancel and only `W_P²W_Q + W_PW_Q² + W_PW_Q` survives.  No joint fourth-moment
inequality (Cauchy–Schwarz, hypercontractivity) is used — the factorisation is exact.

Supporting lemmas, all reusable: `lcmPair`, `lcmPair_pos`, `dvd_left_of_lcmPair`,
`dvd_right_of_lcmPair`, `lcmPair_dvd`, `inv_lcmPair`, `sum_inv_lcmPair_le`, `quadModulus`,
`coprime_lcmPair`, `indicator_quad_le`, `sum_indicator_dvd_le`, `cast_div_sub_one_le`.

Remaining for milestone B: items 2–5 of the list above (the `(31)`–`(34)` bookkeeping, the
exceptional set `(35)`, and the two cases `(36)`–`(40)`).

### Milestone B, brick 2 — the reduction `(34)` in discrete form (2026-08-19)

`Sieve/JointWeightTransfer.lean`, axiom-clean, wired.

```text
sq_window_sum_le_weighted (hf : ∀ n, |f n| ≤ 1) (W t h) :
  W²·(∑_{t<n≤t+h} f n)² ≤ 2(∑ f·ω)² + 2h·∑ (ω − W)²

windowStart A h j = A + j·h
windows_pairwise_disjoint : j ≠ k → the two windows are disjoint

sum_sq_windows_le_weighted : the same summed over `j < K`, the variance paid ONCE over `[1,M]`

sum_sq_windows_le_joint (hP hQ prime) (hPQ : Disjoint P Q) (hf : ∀ n, |f n| ≤ 1) :
  (W_P W_Q)²·∑_{j<K}(∑_{window j} f)²
    ≤ 2·∑_{j<K}(∑_{window j} f·ω_P·ω_Q)²
      + 2h·( M·W_PW_Q(W_P + W_Q + 1) + 2W_PW_Q|P||Q| )
```

The last is exactly the exposé's `(34)` before the Fourier step: dividing by `(W_PW_Q)²` the error
is `2h·M·(1/W_P + 1/W_Q)·(1 + 1/(W_PW_Q)) + …`, i.e. `o(hM)` as soon as `W_P` or `W_Q` tends to
infinity — which is the whole point of the double weight.

Two things make it clean.  The window atom is an identity plus one Cauchy–Schwarz:
`W∑f = ∑fω − ∑f(ω−W)` and `(∑f(ω−W))² ≤ h∑(ω−W)²` since `|f| ≤ 1` and the window has `h` integers.
And the windows of a dyadic family are *disjoint* (`windows_pairwise_disjoint`), so
`Finset.sum_biUnion` pays the Turán–Kubilius variance once over the whole range rather than once per
window — the step that would otherwise cost a factor `K`.

Remaining for milestone B: the Fourier/Plancherel step `(31)`–`(33)` (Lemma 2.1, corpus-owned), the
exceptional set `(35)`, and the two cases `(36)`–`(40)`.

### Milestone B, brick 3 — the exceptional-set split `(35)`–`(36)` (2026-08-19)

`Sieve/DirichletExceptionalSplit.lean`, axiom-clean, wired.

```text
integral_normSq_mul_split_exceptional (N M) (a b) (hBf : ∀ t, ‖dirPoly N a t‖ ≤ Bf) :
  ∫_{|t|≤T} ‖F‖²‖G‖²
    ≤ V²·∫_{|t|≤T} ‖G‖²  +  Bf²·∫_{{|t|≤T} ∩ {‖F‖ ≥ V}} ‖G‖²
```

**Why the corpus's existing split does not serve.**
`Sieve/DirichletSymmSplit.integral_normSq_mul_split_symm` puts the threshold on the *second* factor
and pays `sup‖F‖²·sup‖G‖²·|E|`.  §4 needs the threshold on the *short prime* polynomial `F` — the
one with no zero-free input — and on the exceptional set it must **integrate** `‖G‖²` rather than
bound it by its supremum, because that integral is exactly what Halász–Montgomery (Lemma 2.6)
delivers.  Bounding `∫_E‖G‖²` by `sup‖G‖²·|E|` throws away the whole gain: `sup‖A_j‖` is the trivial
size `X/(P_jQ_k)`, and `|E_j|·(X/(P_jQ_k))²` exceeds the target.

With `F = ∑_{p∈P_j}p^{iy}` this is `(35)`–`(36)`: `V = P_j/(log P_j)²` is the cancellation threshold,
`Bf = P_j` the trivial bound, the first term is the non-exceptional case (finished by Lemma 2.4 as
in `(28)`), and the second is the exceptional case (finished by Lemma 2.3 on the `Q_k` sum, Lemma 2.5
for `|E_j|`, and Lemma 2.6 on `E_j`).

Remaining for milestone B: the Fourier/Plancherel step `(31)`–`(33)` (Lemma 2.1, corpus-owned), and
the two numerical instantiations `(37)`–`(40)`.

### Milestone B, brick 4 — the `(40)` shape (2026-08-19)

`Sieve/Section4Core.lean`, axiom-clean, wired.

```text
section4_product_bound (hBf : ∀ t, ‖dirPoly N a t‖ ≤ Bf)
    (hA₁ : ∫_{|t|≤T} ‖G‖² ≤ A₁)
    (hA₂ : ∫_{{|t|≤T} ∩ {‖F‖ ≥ V}} ‖G‖² ≤ A₂) :
  ∫_{|t|≤T} ‖F‖²‖G‖² ≤ V²·A₁ + Bf²·A₂

section4_product_bound_scaled : the same with the outer factor `C = P_j²W(Q)²h²/((log P_j)²X²)`
```

Everything from `(36)` to `(40)` is now one inequality between named quantities, with the two inputs
labelled by their sources: `A₁` from the mean value theorem (Lemma 2.4, the non-exceptional case,
finished exactly as in `(28)`) and `A₂` from Halász–Montgomery (Lemma 2.6, after Lemma 2.5 bounds
`|E_j|`).  At the paper's values `V = P_j/(log P_j)²`, `Bf = P_j`.

### Milestone B: state after this session

| item | status |
|-|-|
| Lemmas 2.1, 2.3, 2.4, 2.5, 2.6 | corpus theorems (see above) |
| double weight `ω_Pω_Q`, Turán–Kubilius `(30')` | **`Sieve/JointTuranKubilius`** |
| the reduction `(34)` | **`Sieve/JointWeightTransfer`** |
| the exceptional split `(35)`–`(36)` | **`Sieve/DirichletExceptionalSplit`** |
| the `(40)` shape | **`Sieve/Section4Core`** |
| Plancherel `(31)`–`(33)` | Lemma 2.1 is corpus; the `A_j` bookkeeping is not yet written |
| `A₁` at the paper's parameters | Lemma 2.4 + the `(28)` dyadic split — corpus has both, not composed |
| `A₂` at the paper's parameters | Lemma 2.5 for `\|E_j\|`, then Lemma 2.6 through Gallagher's Sobolev lemma to pass from `∫_{E_j}` to a well-spaced sum — all three corpus-owned, not composed |

No new analytic input remains; what is left is composition at the paper's parameters.

### Milestone B, brick 5 — the `A₁` half discharged (2026-08-19)

```text
section4_product_bound_mvt (hT : 0 ≤ T) (hBf : ∀ t, ‖dirPoly N a t‖ ≤ Bf) (hA₂ : … ≤ A₂) :
  ∫_{|t|≤T} ‖F‖²‖G‖²
    ≤ V²·(2(T + 4M(1+log M))·∑‖b‖²)  +  Bf²·A₂
```

`A₁` is now supplied internally by `Sieve/LogPolyDirPoly.integral_Icc_normSq_dirPoly_symm_le`
(Lemma 2.4 on a symmetric range), so the non-exceptional case of §4 needs no further input.

### The one brick §4 still needs: Sobolev over a measurable set

`A₂` is Lemma 2.6, `∫_E‖G‖²dt ≪ (M + |E|·T^{1/2}log T)·∑|b|²` for **measurable** `E`.  The corpus
owns both halves of its proof — `Sieve/GallagherSobolev.gallagher_sobolev` and the discrete
Halász–Montgomery `Sieve/DyadicSecondEnvelopeClosed.halaszMontgomery_dyadic_explicit`, together with
`RHTower/WellSpacedSubset.exists_wellSpaced_subset` — but the passage

```text
   ∫_E ‖G‖²  ⟶  ∑_{r ∈ R} ‖G(r)‖²  over a 1-separated  R ⊆ E  with  |R| ≪ |E| + 1
```

is not in the tree: the corpus's Sobolev applications integrate over intervals, and a general
measurable `E` needs a Vitali-type covering to produce `R`.  That is the single remaining
ingredient of milestone B; everything else is composition at the paper's parameters.

Note that the crude substitute `∫_E‖G‖² ≤ sup‖G‖²·|E|` — which the corpus *does* have, via
`Sieve/DirichletSymmSplit` — is provably insufficient here: `sup‖A_j‖` is the trivial size
`X/(P_jQ_k)`, and `|E_j|·(X/(P_jQ_k))²` exceeds the target of `(40)`.

### CORRECTION to the previous entry — no covering argument supplies `A₂` (2026-08-19)

The entry above suggested that the passage `∫_E‖G‖² ⟶ ∑_{r∈R}‖G(r)‖²` over a separated `R ⊆ E`
needs "a Vitali-type covering".  **No covering argument can supply it**, and it is worth recording
why, so the lane is not re-attempted:

- Take `R` maximal `δ`-separated in `E`.  Maximality gives `E ⊆ ⋃_r[λ_r−δ, λ_r+δ]`, hence
  `|E| ≤ 2δ|R|` — a *lower* bound on `|R|`, not an upper one.  The disjoint balls `B(λ_r, δ/2)` need
  not lie inside `E`, so `|R|` is bounded only by `2T/δ + 1`, and the discrete Halász–Montgomery's
  `|R|·B` term then contributes `(T/δ)√T`, far above the target.
- Covering the other way, `∑_r∫_{I_r}‖G‖² ≤ 3∫_{-T}^{T}‖G‖²`, is just the mean value theorem again:
  the smallness of `E` has been thrown away.
- Bounding `|R|` by a *discrete* large-values count (Ivić Thm 9.4, corpus-owned as
  `Sieve/DirichletFiniteSetLargeValues.largeValues_dirPoly_finset`) does bound `|R|` without
  reference to `|E|`, but then the interval integrals `∫_{I_r}‖G‖²` are uncontrolled.

Lemma 2.6's `|E|` enters through a **double integral over `E × E`**, and the proof is Montgomery's
duality argument (exposé (17); Montgomery, *Topics*, Thm 7.8; Iwaniec–Kowalski Thm 9.6):

```text
  I = ∫_E‖A‖²  =  ∫_E ∑_n a(n)n^{-it}A(t)dt  ≤  ∑_n |a(n)|·|∫_E A(t)n^{-it}dt| ,
  I² ≤ (∑|a(n)|²)·(∑_{n≤2N}(2 − n/N)|∫_E A(t)n^{-it}dt|²) ,
```
and expanding the second factor gives `∫_E∫_E A(t)\bar A(u)·K(u−t)dt du` with the smoothed kernel
`K(v) = ∑_{n≤2N}(2−n/N)n^{iv}`, whose two-regime bound produces `N + |E|T^{1/2}log T`.

So the single remaining ingredient of milestone B is the **integral (duality) form of
Halász–Montgomery**, not a bridge from the discrete form the corpus owns
(`Sieve/DyadicSecondEnvelopeClosed.halaszMontgomery_dyadic_explicit`).  The corpus already has the
duality principle itself (`Sieve/AlmostOrthogonality.sum_norm_inner_sq_le_of_schur`) and both
regimes of the logarithmic-phase kernel (`Sieve/HuxleyLogPhase`, `Sieve/KuzminLandau`,
`Sieve/SecondDerivativeTest`); what has to be built is the continuous version — the double integral
over `E × E` against that kernel.

### Milestone B, brick 6 — the duality step `(17)` of Lemma 2.6 (2026-08-19)

`Sieve/HalaszMontgomeryDual.lean`, axiom-clean, wired.

```text
dualCoeff N a E n = ∫_E exp(i·t·log(n+1))·conj(A(t)) dt

setIntegral_normSq_dirPoly_eq_dual (hE : MeasurableSet E) (hEs : E ⊆ Icc (-T) T) :
  (∫_E ‖A‖² : ℂ)  =  ∑_n a_n · dualCoeff N a E n

setIntegral_normSq_dirPoly_sq_le :
  (∫_E ‖A‖²)²  ≤  (∑_n ‖a_n‖²) · ∑_n ‖dualCoeff N a E n‖²
```

This is exactly `(17)`, and it is the step that keeps the smallness of `E` alive — the identity
`∫_E‖A‖² = ∑_n a_n·(∫_E n^{it}\bar A)` moves `E` inside a coefficient sum, where expanding
`∑_n‖∫_E n^{it}\bar A‖²` produces the double integral over `E × E` whose kernel bound yields
`N + |E|T^{1/2}log T`.

The proof is short but the measure-theoretic shape matters: `A·conj A` is cast from the real
integrand by `Complex.mul_conj` and `Complex.normSq_eq_norm_sq`, the sum and the integral are
exchanged by `integral_finsetSum` (each summand continuous, `E` inside a compact interval), and the
final step is `Finset.sum_mul_sq_le_sq_mul_sq`.

**What remains of Lemma 2.6**: bounding `∑_{n≤2N}(2 − n/N)‖dualCoeff‖²`, i.e. the double integral
over `E × E` against the smoothed kernel `K(v) = ∑_{n≤2N}(2−n/N)n^{iv}`.  The corpus owns both
regimes of that kernel (`Sieve/KuzminLandau`, `Sieve/SecondDerivativeTest`, `Sieve/HuxleyLogPhase`);
what is left is the `E × E` integration against it.

### Milestone B, brick 7 — the continuous Schur test (2026-08-19)

`Sieve/KernelDoubleIntegral.lean`, axiom-clean, wired.

```text
setIntegral_double_kernel_le (hA : Continuous A) (hK : Continuous K)
    (hEs : E ⊆ Icc (-T) T) (hEm : MeasurableSet E)
    (hrow : ∀ t, ∫_E ‖K(t−u)‖du ≤ M) (hcol : ∀ u, ∫_E ‖K(t−u)‖dt ≤ M) :
  ‖∫_E ∫_E K(t−u)·conj(A t)·A u du dt‖  ≤  M · ∫_E ‖A‖²
```

This is the second half of Lemma 2.6: brick 6 turns `∫_E‖A‖²` into the dual pairing, expanding the
dual coefficients produces exactly this double integral, and the row/column masses of the kernel are
what the two-regime phase estimates bound.

The proof runs entirely on the product space, where every integrand is continuous on the compact
rectangle `Icc(-T,T) ×ˢ Icc(-T,T)` and integrability is free (`ContinuousOn.integrableOn_compact`
then `mono_set`).  `Measure.prod_restrict` identifies `(volume|E).prod (volume|E)` with
`(volume.prod volume)|(E ×ˢ E)`, `integral_integral` moves between the iterated and product forms,
and the arithmetic–geometric mean inequality `‖A t‖‖A u‖ ≤ (‖A t‖² + ‖A u‖²)/2` splits the bound
into a row half and a column half.  The column half is the only place Fubini is genuinely used
(`integral_integral_swap`), and it is unavoidable: with the outer variable fixed as `t` the column
mass is invisible.

**What remains of Lemma 2.6**: the kernel estimate itself — row and column masses of
`K(v) = ∑_{n ≤ 2N}(2 − n/N)n^{iv}` of size `N + |E|T^{1/2}log T`.  Both regimes of the logarithmic
phase are corpus theorems (`Sieve/KuzminLandau`, `Sieve/SecondDerivativeTest`,
`Sieve/HuxleyLogPhase`); what is missing is the smoothed weight `2 − n/N` and the passage from a
pointwise kernel bound to its mass over `E`.

### Milestone B, brick 8 — the row mass from a two-regime kernel bound (2026-08-19)

```text
setIntegral_norm_kernel_le (hK : Continuous K) (hEs : E ⊆ Icc (-T) T) (hEm : MeasurableSet E)
    (hnear : ∀ v, ‖K v‖ ≤ N) (hfar : ∀ v, 1 ≤ |v| → ‖K v‖ ≤ C) (hC : 0 ≤ C) (t : ℝ) :
  ∫_E ‖K(t − u)‖ du  ≤  2N + C·|E|
```

This is the passage the Schur test needs, and it is where the shape `N + |E|T^{1/2}log T` of
Lemma 2.6 comes from: the near-diagonal band `|t − u| < 1` has length two **whatever `E` is**, so
the trivial size `N` of the kernel is paid only twice; away from the diagonal the oscillation bound
`C` is paid once per unit of `|E|`.  With `C ≍ (√T + N/√T)log N` from the exponent-pair estimate
this is exactly `N + |E|T^{1/2}log T` in the range where the second term dominates.

The same statement serves as the column bound, since `‖K(−v)‖ = ‖K(v)‖` for
`K(v) = ∑_n w_n n^{iv}`.

### What is left of Lemma 2.6, exactly

Only the **pointwise** two-regime bound for the kernel itself:

```text
   ‖∑_{n ≤ 2N} w_n n^{iv}‖ ≤ 2N   (trivial)  and  ≤ C(√|v| + N/√|v|)·log N  for  1 ≤ |v| ≤ 2T .
```

The corpus owns both regimes for a *dyadic* block of logarithmic phases
(`Sieve/HuxleyLogPhase`, `Sieve/KuzminLandau`, `Sieve/SecondDerivativeTest`, and the closed envelope
`Sieve/DyadicSecondEnvelopeClosed.logDyadicSecondEnvelope_le : B ≤ 214√T + 1536N/√U`); what remains
is summing `O(log N)` dyadic blocks — which is where Lemma 2.6's `log T` comes from — and carrying
the smoothing weight `w_n = 2 − n/N` (or dropping it, since the dyadic route does not need it).

### Milestone B, brick 9 — the dyadic-block interface (2026-08-19)

Added to `Sieve/AdicBlocks.lean` (axiom-clean, wired):

```text
sum_Icc_eq_sum_dyadic_blocks (f : ℕ → ℂ) :
  ∑_{j ≤ ⌊log₂ M⌋} ∑_{n ∈ [1,M], ⌊log₂ n⌋ = j} f n  =  ∑_{n ∈ [1,M]} f n
norm_sum_Icc_le_sum_dyadic_blocks : the triangle inequality over those blocks
mem_dyadic_block : n in the j-th block ⟹ 2^j ≤ n < 2^{j+1}
```

Note: the corpus's `Sieve/LSeriesBlockDecomposition.LSeries_eq_sum_dyadic_blocks` is the same
decomposition **for `LSeries`**, not for a finite sum; the finite version is one application of
`Finset.sum_fiberwise_of_maps_to`, which is what these three lemmas package.

### The single remaining analytic step of milestone B

With bricks 6–9 in place the chain is

```text
   ∫_E‖A‖²  --(6, duality)-->  ∑_n a_n·dualCoeff n
            --(expansion)-->   ∫_E∫_E K(t−u)·conj A·A
            --(7, Schur)-->    M·∫_E‖A‖²
            --(8)-->           M = 2N + C·|E| ,   C = sup_{|v|≥1}‖K(v)‖
            --(9 + corpus)-->  C ≪ log M·√T + N/√T
```

and the only step not yet written is the last: for each dyadic block `[2^j, 2^{j+1})` choose between
`Sieve/HuxleyLogPhase.norm_logPhase_dyadic_le_kuzminLandau` (`≤ 6π·2^j/t + 1`),
`norm_logPhase_dyadic_le_secondDerivative` (`≤ logDyadicSecondBound`, which is
`≍ √t + 2^j/√t`), and the trivial bound `2^j`, according to whether
`logDyadicLambda (2^j) t = t/(8π·4^j) ≤ 1`.  That three-way split, summed over the
`⌊log₂ M⌋ + 1` blocks, is the whole of what remains.

### Milestone B, brick 10 — summing the per-block bounds (2026-08-19)

```text
norm_sum_Icc_le_of_dyadic_bounds (hM : 1 ≤ M) (hb : 0 ≤ b)
    (hblk : ∀ j ≤ ⌊log₂ M⌋, ‖∑_{n ∈ block j} f n‖ ≤ a + b·2^j) :
  ‖∑_{n ∈ [1,M]} f n‖ ≤ (⌊log₂ M⌋ + 1)·a + 2b·M
```

A per-block bound of the shape `a + b·2^j` — which is exactly what the two regimes of the
logarithmic phase produce, with `a ≍ √t` and `b ≍ 1/√t` — sums to `(⌊log₂ M⌋+1)a + 2bM`.  **The
first term is where Halász–Montgomery's `log T` comes from and the second is the `N/√T`**, so the
summation is now accounted for exactly rather than absorbed into a `≪`.

The geometric sum is `∑_{j ≤ K} 2^j = 2^{K+1} − 1 ≤ 2M` via `Nat.pow_log_le_self`.

### Milestone B: the whole of what is left

One statement: for each dyadic block `[2^j, 2^{j+1}) ∩ [1,M]` and each `1 ≤ |t| ≤ 2T`, a bound of
the form `a + b·2^j` with `a ≍ √t`, `b ≍ 1/√t`, obtained by the three-way choice between

* `Sieve/HuxleyLogPhase.norm_logPhase_dyadic_le_kuzminLandau` — `≤ 6π·2^j/t + 1`;
* `Sieve/HuxleyLogPhase.norm_logPhase_dyadic_le_secondDerivative` — `≤ logDyadicSecondBound (2^j) t`,
  which is `256(2^j√(16λ) + λ^{-1/2})` with `λ = t/(8π·4^j)`, i.e. `≍ √t + 2^j/√t`;
* the trivial bound `2^j`;

according to the size of `logDyadicLambda (2^j) t = t/(8π·4^j)`.  Everything upstream and downstream
of that statement — bricks 1–10 — is now in the tree, unconditional and axiom-clean.

### Milestone B, brick 11 — the three-way split collapses to two (2026-08-19)

`Sieve/DyadicAffineEnvelope.lean`, axiom-clean, wired.

```text
logDyadicSecondBound_le_affine (hN : 1 ≤ N) (ht : 0 < t) :
  logDyadicSecondBound N t ≤ 214·√t + 1536·(N/√t)

trivial_le_affine (hN : 1 ≤ N) (ht : 0 < t) (hbig : 1 < logDyadicLambda N t) :
  (N : ℝ) ≤ 214·√t + 1536·(N/√t)
```

The first is the corpus's closed envelope at `U = T = t` — note `logDyadicSecondBound N t` is
*definitionally* `logDyadicSecondEnvelope N t t`, so it is one `rfl` away.

The second is the observation that makes the block sum work: **the trivial bound is already inside
the affine bound exactly when the second-derivative test is unavailable.**  The test fails only when
`logDyadicLambda N t = t/(8πN²) > 1`, i.e. `8πN² < t`; since `8π > 25` this gives `N < √t/5`, which
is far below `214√t`.  So the classical three-way split (Kuzmin–Landau / second derivative /
trivial) collapses to a two-way one, and the affine per-block bound

```text
   ‖block j‖ ≤ 214·√t + 1536·(2^j/√t)        for every j, unconditionally
```

holds with the constants `a = 214√t`, `b = 1536/√t` that brick 10 consumes.  Feeding that into
`norm_sum_Icc_le_of_dyadic_bounds` gives

```text
   ‖∑_{n ≤ M} n^{it}‖ ≤ (⌊log₂ M⌋ + 1)·214√t + 3072·M/√t ,
```

which is the pointwise kernel bound Lemma 2.6 needs — the `log T·√T` and the `N/√T`, with explicit
constants and no asymptotic notation anywhere.

**What is still missing** is only the identification of the `j`-th dyadic block of `[1,M]` with the
corpus's indexing `∑_{k ∈ range N} (N+k)^{-it}` at `N = 2^j`, including the truncated last block,
for which `Sieve/HuxleyLogPhase` needs its general-length companion `dirichlet_block_bound`.

### Milestone B, brick 12 — the pointwise kernel bound is CLOSED (2026-08-19)

`Sieve/LogPhaseKernelBound.lean`, axiom-clean, wired.

```text
norm_sum_Icc_logPhase_le (hM : 1 ≤ M) (ht : 0 < t) :
  ‖∑_{n ≤ M} n^{-it}‖  ≤  (⌊log₂ M⌋ + 1)·214·√t  +  3072·M/√t
```

**Unconditional, with explicit constants, no asymptotic notation.**  This is the two-regime kernel
estimate Lemma 2.6 needs — its `log T·T^{1/2}` is the first term and its `N/T^{1/2}` the second.

Supporting theorems, all new:

| name | content |
|-|-|
| `norm_cpow_imag_eq_one` | `‖n^{-it}‖ = 1` for `n ≥ 1` — the trivial bound's atom |
| `norm_logPhase_partial_block_le` | the second-derivative bound on a **partial** block `[N, N+L)`, `L ≤ N`, from the corpus's general-length `dirichlet_block_bound` at `k = 2`; the corpus previously had only the full block `L = N` |
| `dyadic_block_eq` | `(Icc 1 M).filter (⌊log₂·⌋ = j) = Ico (2^j) (min (2^{j+1}) (M+1))` |
| `norm_dyadic_block_le_affine` | the affine bound `214√t + 1536·2^j/√t` on the `j`-th block, **unconditionally** |

The last is where the two earlier observations pay off: the truncated last block is handled because
`dirichlet_block_bound` takes a general length `L ≤ N` (brick 12 states that specialisation, which
the corpus lacked), and the case where the second-derivative test is inadmissible is handled by
`trivial_le_affine` (brick 11) rather than by a third regime.

### Milestone B: what is left

Only bookkeeping, no analysis:

1. compose bricks 6 → 7 → 8 → 12 into the integral Halász–Montgomery `∫_E‖A‖² ≪ (N + |E|T^{1/2}log T)∑|a|²`
   — the one step not yet written inside that chain is the expansion of `∑_n w_n‖dualCoeff n‖²` into
   the `E × E` double integral, which is a second application of `integral_integral`;
2. the Plancherel step `(31)`–`(33)` (Lemma 2.1 is corpus-owned);
3. the numerical instantiation of `(37)`–`(40)` at the paper's parameters.

### Milestone B, brick 13 — the dual coefficients as a double integral (2026-08-19)

Added to `Sieve/HalaszMontgomeryDual.lean` (axiom-clean):

```text
logKernel N w v = ∑_n w_n · exp(i·v·log(n+1))

normSq_dualCoeff_eq (a : Fin N → ℂ) (E : Set ℝ) (n : Fin N) :
  (‖dualCoeff N a E n‖² : ℂ)
    = ∫_E ∫_E exp(i(t−u)log(n+1))·conj(A t)·A u  du dt
```

This is the expansion that joins brick 6 to brick 7, and it needs **no Fubini**: `‖c‖² = c·conj c`,
`conj` passes through the integral (`integral_conj`), and the product of the two single integrals
becomes an iterated one by pulling constants (`integral_mul_const`, `integral_const_mul`).  The two
phases combine as `exp(i t L)·exp(−i u L) = exp(i(t−u)L)`.

Summing over `n` against a weight `w` turns the right-hand side into the `logKernel`, which is what
bricks 7 and 8 consume, and brick 12 bounds.

### Milestone B: the chain, complete

```text
   ∫_E‖A‖²  ≤  (∑‖a_n‖²)^{1/2}·(∑_n‖dualCoeff n‖²)^{1/2}          brick 6
   ∑_n w_n‖dualCoeff n‖²  =  ∫_E∫_E logKernel(t−u)·conj A·A        brick 13
   ‖∫_E∫_E K(t−u)·conj A·A‖  ≤  M·∫_E‖A‖²                          brick 7
   M = 2N + C·|E|,  C = sup_{|v| ≥ 1}‖K(v)‖                        brick 8
   ‖∑_{n ≤ M} n^{-it}‖ ≤ (⌊log₂M⌋+1)·214√t + 3072M/√t              brick 12
```

Every link is an unconditional Lean theorem.  What is left is arithmetic: choose the weight `w`,
combine the five displays, and instantiate at the paper's parameters — plus the Plancherel
`(31)`–`(33)` bookkeeping, whose Lemma 2.1 is corpus-owned.

## LEMMA 2.6 IS CLOSED — the integral Halász–Montgomery bound (2026-08-19)

`Sieve/HalaszMontgomeryIntegral.lean`, axiom-clean, warning-free, wired.

```text
plainKernel N v = ∑_{n < N} exp(i·v·log(n+1))

sum_normSq_dualCoeff_eq (hEm : MeasurableSet E) (hEs : E ⊆ Icc (-T) T) :
  (∑_n ‖dualCoeff N a E n‖² : ℂ)
    = ∫_E ∫_E plainKernel N (t−u)·conj(A t)·A u  du dt

setIntegral_normSq_dirPoly_le_HM (hEm) (hEs)
    (hrow : ∀ t, ∫_E ‖plainKernel N (t−u)‖du ≤ M)
    (hcol : ∀ u, ∫_E ‖plainKernel N (t−u)‖dt ≤ M) :
  ∫_E ‖A‖²  ≤  M · ∑_n ‖a_n‖²
```

**This is Lemma 2.6, unconditional and with `M` supplied by bricks 8 and 12.**  The argument is the
exposé's `(17)` throughout: duality (brick 6) gives `I² ≤ (∑‖a‖²)·(∑‖dualCoeff‖²)`, the expansion
above turns the dual energy into the kernel double integral, the continuous Schur test (brick 7)
bounds it by `M·I`, and dividing by `I` finishes.  The degenerate case `I = 0` is separate.

**The smoothing weight `2 − n/N` of the exposé is not needed.**  It exists there to sharpen the
kernel estimate; the dyadic route of brick 12 already gives `log M·√t + M/√t` without it, so the
kernel is the plain `∑_{n<N} n^{iv}` and the statement is simpler than the published one.

Two further notes for whoever continues.  The expansion needs **no Fubini** — `‖c‖² = c·conj c`,
`integral_conj`, and pulling constants suffice, with the two finite-sum/integral exchanges justified
by continuity on a compact rectangle.  And the outer exchange only works because the inner integral
factorises as `exp(itL)·(a constant in t)`; had the phase not split, the swap would have needed the
product-measure machinery.

### Milestone B after this

| item | status |
|-|-|
| Lemmas 2.1, 2.3, 2.4, 2.5 | corpus |
| **Lemma 2.6 (integral form)** | **`Sieve/HalaszMontgomeryIntegral`** |
| kernel row/column mass | `Sieve/KernelDoubleIntegral.setIntegral_norm_kernel_le` |
| pointwise kernel bound | `Sieve/LogPhaseKernelBound.norm_sum_Icc_logPhase_le` |
| double weight, `(34)`, `(35)`–`(36)`, `(40)` | bricks 1–5 |
| Plancherel `(31)`–`(33)` | **remaining** (Lemma 2.1 is corpus; the `A_j` bookkeeping is not written) |
| numerical instantiation `(37)`–`(40)` | **remaining** |

### Lemma 2.6, sharpened hypotheses (2026-08-19)

`setIntegral_double_kernel_le` and `setIntegral_normSq_dirPoly_le_HM` now take the row and column
masses **only on `E`**:

```text
   (hrow : ∀ t ∈ E, ∫_E ‖K(t−u)‖du ≤ M)   (hcol : ∀ u ∈ E, ∫_E ‖K(t−u)‖dt ≤ M)
```

instead of for every real `t`, `u`.  This is not cosmetic: with `E ⊆ [−T, T]` the difference
`t − u` is then confined to `[−2T, 2T]`, which is exactly the range in which the pointwise kernel
bound `‖∑_{n ≤ M} n^{-iv}‖ ≤ (⌊log₂M⌋+1)·214√|v| + 3072M/√|v|` of brick 12 is useful — for `|v|`
unbounded the `√|v|` term is useless and the instantiation would be impossible.  The empty-`E` case
is now handled separately (both sides vanish), and `M ≥ 0` is derived from a point of `E` rather
than assumed at `t = 0`.

### Milestone B, brick 14 — the kernel's row mass, instantiated (2026-08-19)

`Sieve/PlainKernelMass.lean`, axiom-clean, wired.

```text
log_complex_ofReal_pos   Complex.log ↑x = ↑(Real.log x)  for  x > 0
cpow_eq_phase            (m : ℂ)^(-(I·t)) = exp(↑(−t·log m)·I)   for m ≥ 1
plainKernel_eq_dirichlet plainKernel N v = ∑_{m ∈ [1,N]} m^{-(I·(−v))}
norm_plainKernel_neg     ‖plainKernel N (−v)‖ = ‖plainKernel N v‖
norm_plainKernel_le (hN : 1 ≤ N) (hv : v ≠ 0) :
  ‖plainKernel N v‖ ≤ (⌊log₂N⌋+1)·214·√|v| + 3072·N/√|v|
plainKernel_row_mass (hEs : E ⊆ Icc (-T) T) (hEm) (ht : t ∈ Icc (-T) T) :
  ∫_E ‖plainKernel N (t−u)‖ du  ≤  2N + ((⌊log₂N⌋+1)·214·√(2T) + 3072N)·|E|
```

The bridge is the identification of the kernel with a Dirichlet sum (`plainKernel_eq_dirichlet`),
after which brick 12 applies at `t = −v`; the sign is handled by `norm_plainKernel_neg`, since
conjugation reflects `v`.  The mass bound then comes from brick 8's near/far split, with the far
bound valid because `t, u ∈ [−T, T]` confines `|t−u|` to `[1, 2T]` — which is exactly why the
hypotheses of bricks 7 and 8 had to be weakened to hold only on `E`.

By symmetry the same statement is the column mass.  Together with `setIntegral_normSq_dirPoly_le_HM`
this gives Lemma 2.6 with an entirely explicit `M`:

```text
   ∫_E ‖A‖²  ≤  (2N + ((⌊log₂N⌋+1)·214·√(2T) + 3072N)·|E|) · ∑_n ‖a_n‖²
```

— the published `≪ (N + |E|T^{1/2}log T)∑|a_n|²` with every constant named.

## SCOPE CORRECTION: the three Route E cards need only the QUALITATIVE theorem (2026-08-19)

The table above ("what the three cards need: `o(1/log Y)`, i.e. `(log h)^{-1/β}`") and the
row "Menon 2026 `(log log L)²/(log L)²`" describe the requirement of an **architecture that has
since been replaced**.  Traced through the Lean chain that now proves
`route-e-reciprocal-marker-mobius-hall-law`'s `(3)`, the only analytic hypothesis is

```text
AveragedMeanSquare (fun n => (μ n : ℝ)) (scaledLength c β)
  :=  Tendsto (fun x => (∑_{a ∈ (√x,2√x]} (∑_{b ∈ innerFibre x (hh x) a} μ b)²) / (hh x² √x))
        atTop (𝓝 0)
```

— a bare `o(1)`, with **no rate**.  See the section "THE RECORDED GATE IS STALE" appended to that
card for the full dependency trace (`route_e_marker_hall_law → … →
GenericFibreStepOne.eventually_fibre_step_one_growing_gen`, whose four hypotheses are the mean
square plus three growth conditions that hold for every `0 < β < 1`).  The `1/log X` saving in the
cards' conclusion is produced by the multi-block marker construction, not by the mean square.

**Therefore milestone B as scoped here — the exposé §4 arrangement, rate `1/log log h` — closes
cards 3, 4 and 5 outright.**  Milestone A does not (its range `h ≥ exp((log X)^{0.95})` is *worse*
than the Route-T mean square already in the corpus, which reaches `exp((log X)^{0.9+})`).  Menon's
refinement is not on the critical path for any Route E card and should be dropped from the
programme's requirements.

The interface to hit is a single theorem

```text
averagedMeanSquare_moebius_scaled' (hc0 : 0 < c) (hc1 : c ≤ 1) (hβ0 : 1/2 < β) (hβ1 : β < 1) :
    AveragedMeanSquare (fun n => ((moebius n : ℤ) : ℝ)) (scaledLength c β)
```

and `Sieve/OmegaSpectralFibre.averagedMeanSquare_moebius_of_omegaBudget` already reduces it to the
spectral budget, so what is left is precisely steps `(26)`–`(30)` of §3 and `(31)`–`(40)` of §4.

## MILESTONE B, THE JOINT-WEIGHT LANE — bricks 15–22 (2026-08-19)

The scope correction above says milestone B closes cards 3, 4 and 5.  This session built the
**joint-weight** (`ω_P·ω_Q`) fibre chain that §4 needs, and the §4 per-block estimate itself.  All
eight modules are unconditional, axiom-clean (`propext, Classical.choice, Quot.sound`), sorry-free
and umbrella-wired.

### Why the joint weight is unavoidable (proved, not assumed)

The single-weight arrangement of §3 **cannot** be pushed below the Route-T exponent, and the reason
is not the zero-free region — it is the diagonal of Halász–Montgomery.  Writing `M = ⌊√x + h⌋`,
`δ = h/M`, `σ_j` for a `P`-block's harmonic mass and `N_j = M/P_j` for its cofactor length, the
exceptional half of §4 with a *single* weight contributes

```text
   (σ_j P_j)² · δ² · (C·N_j + |E_j|·√T·log T)·N_j  ⊇  C·σ_j²·δ²M²  =  C·σ_j²h² ,
```

whose weighted sum over the ladder is `C·W_P²h²` — **exactly the trivial bound**, for every choice
of blocks, thresholds and `|E_j|`.  Three independent repairs were checked and all fail:

* thinner `P`-blocks — the loss is scale-invariant (`σ_j^{-1}·σ_j² = σ_j` sums to `W_P` again);
* Lemma 2.3 on the *cofactor* (its length is `M^{1-o(1)}`, so it does apply) — but the pointwise
  route needs `|E_j| ≤ (log x)^{O(1)}`, and Lemma 2.5 gives `|E_j| = x^{o(1)}`, never polylog,
  because `log T/log P_j → ∞` whenever `P_j ≤ h = x^{o(1)}`;
* truncating the frequency range — the Gallagher weight already forces `T ≳ M/h`, so
  `log T ≍ log x` regardless.

The second designated range `Q` is what supplies the missing factor: on the exceptional set the
`Q`-block sum has a Lemma-2.3 saving of `1/log P_j`, whose square cancels the `(log P_j)²` of the
threshold and leaves `h²W_Q²/(log P_j)²`, which **is** `o(h²W_Q²)`.  This is exposé (35)–(40) and it
is the only arrangement that works.

### The parameters for the Route E range (checked against the source)

With `𝓁 = log x`, `h = exp(𝓁^β)`, `1/2 < β < 9/10` (above `9/10` the corpus already has the result):

| object | choice | constraint it satisfies |
|-|-|-|
| `P` | primes with `𝓁^{β/2} ≤ log p ≤ 𝓁^β` | `P_j ≤ h`; `W_P = (β/2)log 𝓁 → ∞` |
| `Q` | primes with `𝓁^a ≤ log q ≤ 𝓁^b`, `9/10 < a < b < 1` | disjoint from `P`; `W_Q = (b−a)log 𝓁 → ∞` |
| threshold | `V_j = π(P_j)/log P_j` | non-exceptional term `≍ (log P_j)^{-2} → 0` |
| Lemma 2.5 power | `k = ⌈log T/log P_j⌉ ≍ 𝓁^{1−β/2}` | `|E_j| ≤ exp(O(𝓁^{1−β/2}log 𝓁)) = x^{o(1)}` |
| Lemma 2.3 on `Q_k` | Route-T at `log Q_k ≥ 𝓁^a`, `a > 9/10` | saving `exp(−c𝓁^{a−9/10}/(log 𝓁)²)`, beats every power of log |
| HM cross term | needs `|E_j|·Q_max ≪ M^{1/2} = x^{1/4}` | both factors are `x^{o(1)}` |

Every one of the exposé's own constraints (`P_jQ_k ≪ X^{1/14−ε}`, `|E_j| ≪ X^{1/2−ε}`) holds with
enormous room at this range, because `P_j, Q_k = x^{o(1)}` here whereas the exposé must work at
`h = exp(10(log log X)^{10/9})`.

### The eight modules

| module | content |
|-|-|
| `Sieve/JointFibreTransfer` | `fibreDyadicIndex_subset_Icc_one`, `sum_variance_joint_fibreDyadicIndex_le`, **`sum_sq_fibreSum_le_jointWeighted`** — the joint Turán–Kubilius transfer on the fibres.  The corpus's `WeightRemovalFibre.sum_sq_fibreSum_le_weighted` is already weight-generic, so only the joint variance (`JointTuranKubilius`, restricted to the fibre block) had to be supplied |
| `Sieve/JointOmegaSpectral` | `jointOmegaPoly`, `jointOmegaWeight`, `logPoly_jointOmegaWeight_eq`, `abs_jointOmegaWeight_le`, **`sum_sq_fibreSum_moebius_le_jointSpectral`**, `jointOmegaBudget`, **`averagedMeanSquare_moebius_of_jointOmegaBudget`** — the joint analogue of `OmegaSpectralFibre`, i.e. the gate the whole §4 lane has to hit |
| `Sieve/JointOmegaFactorisation` | `primeFactorsIn_mul_prime_not_mem`, **`jointOmegaPoly_eq_bilinear`**, `jointOmegaPoly_eq_blocks` — the exact two-variable factorisation.  The cofactor is *literally* the corpus's single-weight `omegaWeightedMoebiusPoly Q ·`, so the second factorisation is the corpus lemma applied again |
| `Sieve/JointLadderProduct` | `omegaQCoeff`, `omegaWeightedMoebiusPoly_eq_logPoly`, `norm_omegaQCoeff_le`, `logPoly_div_const`, `jointLadderProductPoly`, `jointLadderProductDefect`, **`jointLadderProductPoly_sub_jointOmega_eq`**, **`integral_Icc_normSq_primeShift_family_le_bound`** (the corpus's prime-shift family bound at a general coefficient bound, by rescaling), **`integral_normSq_jointLadderProductDefect_le_closed`** |
| `Sieve/JointLadderHarmonic` | `normSq_jointLadderProductPoly_le`, `integral_normSq_jointLadderProductPoly_le` — the harmonic Cauchy–Schwarz over the short ladder |
| `Sieve/ExceptionalSplitGen` | **`integral_normSq_mul_split_exceptional_gen`** — the §4 split for an arbitrary pair of continuous factors (the corpus's version is `dirPoly`-only) |
| `Sieve/LogPolyRestrict` | `restrictCoeff`, `logPoly_restrictCoeff`, **`logPoly_subset_eq_dirPoly`**, `primeBlockPoly_eq_logPoly`, **`integral_Icc_comp_mul_left`**, **`integral_Icc_normSq_mul_logPoly_eq`** — the bridge from the Gallagher variable `w` to the Dirichlet variable `t = 2πw`, for a *product* of two polynomials over arbitrary subsets of (possibly different) initial segments |
| `Sieve/Section4Block`, `Sieve/Section4ExceptionalMeasure`, `Sieve/Section4BlockClosed` | `finCoeff`, `blockExceptional`, **`section4_block_bound`**; `sum_normSq_finCoeff_le_card`, `finCoeff_prime_support`, **`volume_blockExceptional_le`** (Lemma 2.5 for one block, at a free power); `norm_dirPoly_finCoeff_le_card`, **`section4_block_bound_prime`** |

### The capstone of this session

```text
section4_block_bound_prime (b : ℕ → ℂ) {B D : Finset ℕ} {NA NB k : ℕ}
    (hBprime : ∀ p ∈ B, p.Prime) (hBsub : B ⊆ Icc 1 NA) (hD : D ⊆ Icc 1 NB)
    (hNB : 1 ≤ NB) (hk : 1 ≤ k) (hW : 0 ≤ W) (hV : 0 < V) :
  ∫_{|w| ≤ W} ‖primeBlockPoly B w‖²·‖logPoly b D w‖² dw
    ≤ (2π)⁻¹ · [ V²·2·(2πW + 4N_B(1+log N_B))·E_B
               + (#B)²·( 2N_B + ((⌊log₂N_B⌋+1)·214·√(4πW) + 3072N_B)
                                 · 2(2πW + 4N_A^k(1+log N_A^k))·k^k·(#B)^k / V^{2k} )·E_B ]
```

**Unconditional, no asymptotic notation, every constant named.**  This is exposé (35)–(37) plus
Lemmas 2.4, 2.5 and 2.6 composed, for one step of the ladder.  Its two halves are exactly the two
cases of §4: the `V²` term is the non-exceptional case (Lemma 2.4) and the `(#B)²` term is the
exceptional one (Lemma 2.5 for the measure, Lemma 2.6 for the cofactor).

### What is left of milestone B

Only the **`Q`-side of the exceptional case**, and the parameter substitution:

1. Split `logPoly (omegaQCoeff Q) D_j` over `Q`-blocks *inside the exceptional set*: the corpus's
   `Sieve/LadderProductDefect` applies verbatim with `P := Q` and `Icc A₀ B₀ := D_j` (which is an
   interval — `geomCofactorBlockAt` is an `Icc`), and `Sieve/HarmonicCauchySchwarz` supplies the
   split.  What has to be added is the `∫_E` version of `Sieve/LadderHarmonicSplit`'s mean-square
   statement (the pointwise inequality is set-independent, so this is `setIntegral_mono_on` again).
2. Bound the `Q`-block prime sums pointwise by Lemma 2.3 —
   `Sieve/PrimeBlockTwistBound.exists_norm_primeBlockPoly_routeT_le`, already connected in the
   corpus, at `log Q_k ≥ (log x)^a`, `a > 9/10`.
3. Replace `section4_block_bound_prime`'s exceptional half by that three-factor form, so the
   `(#B)²·2N_B·E_B` diagonal acquires the `(log P_j)^{-2}` saving.
4. Sum over the ladder (`JointLadderHarmonic`) and add the defect
   (`integral_normSq_jointLadderProductDefect_le_closed`).
5. The Gallagher tail: `AffineMajorantFromHeight` + `BudgetTermSplit.spectral_terms_le'` with the
   §4 bound in place of the Route-T ladder bound, then the four quotient limits at the parameters of
   the table above, exactly as `Sieve/ScaledBudgetLimit` does for `β > 9/10`.

### Milestone B, bricks 23–28 — the exceptional case is CLOSED (2026-08-19)

Six further modules, all unconditional, axiom-clean, sorry-free and umbrella-wired.  The exceptional
half of §4 — the half that needs Lemmas 2.3, 2.5 and 2.6 together — is now a single Lean theorem.

| module | content |
|-|-|
| `Sieve/SetIntegralBlockSplit` | **`setIntegral_normSq_sum_mul_le_weighted`** (harmonic Cauchy–Schwarz over a *measurable set*), **`setIntegral_normSq_mul_le_of_bound`** (replacing one factor by a pointwise bound on that set), `setIntegral_normSq_add_le`.  The corpus's versions integrate over intervals; the exceptional case does not |
| `Sieve/LogPolySetScaling` | `logPoly_subset_eq_dirPoly_finCoeff`, **`setIntegral_comp_mul_left`** (the frequency scaling `t = 2πw` on an arbitrary measurable set, via `Real.map_volume_mul_left` and `Measure.restrict_map`), **`volume_real_preimage_mul_left`**, `setIntegral_normSq_logPoly_eq`, **`exceptional_preimage`**, `sum_normSq_finCoeff_le`, **`setIntegral_normSq_logPoly_le_HM`** — Lemma 2.6 for a Gallagher polynomial over a measurable set |
| `Sieve/Section4QSide` | `continuous_ladderProductDefect'`, **`setIntegral_normSq_omegaWeighted_le_ladder`** (the long ladder over a measurable set, with its defect), **`setIntegral_normSq_omegaWeighted_le_blocks`** (the same with the Lemma 2.3 saving applied blockwise), **`setIntegral_normSq_short_long_le`** |
| `Sieve/Section4BlockFull` | `shortExceptional`, `measurableSet_shortExceptional`, **`section4_block_full`** |
| `Sieve/Section4ExceptionalCofactor` | **`shortExceptional_eq_preimage`**, **`setIntegral_normSq_logPoly_shortExceptional_le`** — the innermost cofactor's mean square over the exceptional set, with Lemma 2.5 already substituted for the measure |

The capstone of the exceptional case:

```text
section4_block_full {B Q : Finset ℕ} {A₁ B₁ : ℕ} {R η W VP : ℝ}
    (hR : 0 < R) (hη : 0 ≤ η) (hL : 1 ≤ L)
    (hQprime : ∀ q ∈ Q, q.Prime) (hQrange : ∀ q ∈ Q, R < q ∧ q ≤ R(1+η)^L)
    (hv : ∀ k < L, 0 < v k)
    (hVk : ∀ k < L, ∀ w ∈ shortExceptional B W VP,
              ‖primeBlockPoly (geomBlock Q R (1+η) k) w‖ ≤ Vk k)      -- Lemma 2.3
    (hIk : ∀ k < L, ∫_{shortExceptional B W VP} ‖cofactor_k‖² ≤ Ik k) -- Lemmas 2.5 + 2.6
  : ∫_{|w| ≤ W} ‖∑_{p∈B} μ(p)p^{iw}‖²·‖∑_m μ(m)ω_Q(m)m^{iw}‖² dw
      ≤ VP²·∫_{|w| ≤ W} ‖∑_m μ(m)ω_Q(m)m^{iw}‖²
        + (#B)²·( 2(∑_k 1/v_k)·∑_k v_k·V_k²·I_k
                  + 2·∫_{shortExceptional} ‖ladder defect‖² )
```

and `hIk` is discharged, for any coefficient bounded by `Ω`, by

```text
setIntegral_normSq_logPoly_shortExceptional_le :
  ∫_{shortExceptional B W VP} ‖logPoly a D w‖²
    ≤ (2π)⁻¹·( 2N_D + ((⌊log₂N_D⌋+1)·214·√(4πW) + 3072N_D)
                     · 2(2πW + 4N_A^k(1+log N_A^k))·k^k·(#B)^k / VP^{2k} )·Ω²·#D
```

**This is exactly (35)–(40) of the exposé, for one step of the short ladder, with every constant
named and no asymptotic notation.**  The `VP²` term is the non-exceptional case (Lemma 2.4 finishes
it), the `(#B)²·V_k²·I_k` term is the exceptional one.

### Milestone B: what is left, after this session

1. **`Vk` from Route-T.**  `Sieve/PrimeBlockTwistBound.exists_norm_primeBlockPoly_routeT_le`
   requires its block to be *all* primes in an integer interval `(a,b]`; `geomBlock Q R (1+η) k` is
   all primes of `Q` in a real interval, so the instantiation is the same bookkeeping the corpus
   already carries in `Sieve/ScaledBudgetSubstitution` (`budgetRho A delta Ctot β γ x`) for the
   single-weight ladder.  Mirror it.
2. **The non-exceptional `VP²` term.**  Lemma 2.4 for `logPoly (omegaQCoeff Q) ·`, i.e. the corpus's
   `integral_Icc_normSq_logPoly_le_support` at coefficient bound `#Q`.
3. **Sum over the short ladder** — `Sieve/JointLadderHarmonic.integral_normSq_jointLadderProductPoly_le`
   plus `Sieve/JointLadderProduct.integral_normSq_jointLadderProductDefect_le_closed`.
4. **The Gallagher tail and the parameter substitution** — mirror `Sieve/ScaledBudgetSubstitution`
   and `Sieve/ScaledBudgetLimit` at the parameters of the table above, ending at
   `averagedMeanSquare_moebius_of_jointOmegaBudget`.

No new analytic input remains anywhere in the lane.

### Milestone B, bricks 29–33 — the assembly, and the last analytic input located (2026-08-19)

| module | content |
|-|-|
| `Sieve/Section4Assembly` | **`integral_Icc_normSq_logPoly_le_support_bound`** (Lemma 2.4 at a general coefficient bound — the long-weighted cofactor is bounded by `#Q`, not by `1`), **`integral_normSq_jointOmegaPoly_le`** — the joint polynomial over the short ladder, with the per-step bound as a parameter |
| `Sieve/JointOmegaBudgetFromLadder` | `jointOmegaCoeff`, `logPoly_jointOmegaCoeff_eq`, `energy_jointOmegaCoeff_le`, **`integral_kernel_normSq_jointOmega_le`** — the Gallagher-weighted spectral integral of the joint polynomial from a bound at one height.  `AffineMajorantFromHeight` and `GallagherDyadicTail` are both coefficient-generic, so this is a short mirror of `OmegaBudgetFromLadder` |
| `Sieve/SetIntegralBlockSplit` (extended) | **`setIntegral_normSq_mul_split_exceptional_set`** — the §4 split over an arbitrary measurable part of the window |
| `Sieve/Section4BlockFull` (extended) | `shortExceptionalOn`, **`section4_block_full_on`** — one block of §4 on an arbitrary measurable part |
| `Sieve/Section4DiscAnnulus` | `windowAnnulus`, `abs_ge_of_mem_windowAnnulus`, **`section4_block_disc`**, **`section4_block_disc_ann`** |

### Why the disc is not negligible, and what handles it

Lemma 2.3 needs `|τ| ≥ τ₀`, so §4 runs on the annulus `w₀ ≤ |w| ≤ W` only.  On the disc the trivial
bound is **not** enough: it contributes `σ_j²M²W_Q²` per short block, whose weighted sum is
`W_P²M²W_Q²` — the trivial total.  What saves it is the *cofactor*: on the disc the innermost
polynomial is a Möbius sum of length `M/(P_jQ_k) = M^{1-o(1)}`, and the corpus already owns its
low-frequency bound,

```text
Sieve/CofactorLowFreqBound.exists_norm_logPoly_moebiusCoeff_Icc_le :
  ‖logPoly moebiusCoeff (Icc a b) w‖ ≤ moebiusSharpBound (a−1) + moebiusSharpBound b ,
```

whose saving is `exp(−c(log N)^{1/10})` — better than every power of log, uniformly over a frequency
range larger than every power of log.  Feeding it through `section4_block_disc` (which is
`setIntegral_normSq_omegaWeighted_le_blocks` with **trivial** `Vk` and this `Ik`) gives
`W_P²M²W_Q²·exp(−2c(log M)^{1/10})·2w₀ = o(M²W_P²W_Q²)`.

### `Vk` on the annulus is already a corpus theorem

`Sieve/GeomBlockPrimeRho.exists_norm_primeBlockPoly_geomBlock_le` bounds the prime polynomial of the
`j`-th step of a ladder over `primesRange z₀ z` by `(4/log 2)((1+η)ρ + 7e⁹/Q)·(Q(1+η)^j)` whenever
`τ₀ ≤ |2πw|`, with `ρ` any bound for the relative scaled Route-T envelope.  Applied to the **long**
ladder (`z₀ = ⌊exp((log x)^a)⌋`, `a > 9/10`) this is exactly the `Vk` of `section4_block_full_on`.

**Consequence: every analytic input of milestone B is now either proved in this session or already a
corpus theorem.**  Lemma 2.1 (Plancherel), 2.3 (Route-T), 2.4 (mean value, at a general coefficient
bound), 2.5 (level-set measure at a free power), 2.6 (integral Halász–Montgomery), the low-frequency
cofactor bound, the joint Turán–Kubilius transfer, the two-variable factorisation, the two harmonic
splits, the two ladder defects, and the Gallagher tail.  What is left is **only** the parameter
substitution: choosing `P(x), Q(x), R, η, L, V_P, k, v, u, w₀, W, T₀` as functions of `x` and
verifying one limit — the joint-weight mirror of `Sieve/BudgetSubstitution`,
`Sieve/BudgetRhoBound`, `Sieve/BudgetLimit` and `Sieve/ScaledBudget{Substitution,Limit}`.

### Milestone B, bricks 34–35 — the disc closed, and `Vk` located as a corpus theorem (2026-08-19)

| module | content |
|-|-|
| `Sieve/Section4ExceptionalCofactor` (extended) | **`setIntegral_normSq_logPoly_shortExceptionalOn_le`** — the same closed cofactor bound over the exceptional set of an arbitrary *part* of the window (the exceptional set of a part sits inside that of the whole, and the integrand is nonnegative) |
| `Sieve/Section4DiscCofactor` | `setIntegral_disc_normSq_logPoly_le`, **`exists_setIntegral_disc_normSq_logPoly_moebius_le`** — the disc's cofactor mean square, `≤ (moebiusSharpBound(a−1) + moebiusSharpBound b)²·2w₀`, from `Sieve/CofactorLowFreqBound` |

**`Vk` needs no new work at all.**  `Sieve/AnnulusBoundUniform.exists_annulus_bound_uniform` already
states exactly the hypothesis `section4_block_full_on` wants — a bound on
`‖primeBlockPoly (geomBlock (primesRange z₀ z) Q (1+η) j) w‖`, **uniform over `j ∈ range L` and over
`w ∈ Icc (-T₀) T₀ \ Icc (-w₀) w₀`** — and that set is definitionally the `windowAnnulus w₀ T₀` of
`Sieve/Section4DiscAnnulus`:

```text
  ‖primeBlockPoly (geomBlock (primesRange z₀ z) Q (1+η) j) w‖
    ≤ (4/log 2)·((1+η)·relScaledMajorant Ctot D Lx Hmaj μ q (2πw₀) xmin + 7e⁹/Q)·(Q(1+η)^j) .
```

Applied to the **long** ladder (`z₀ = ⌈exp((log x)^a)⌉`, `9/10 < a < b < 1`) this is `Vk`.

### Milestone B: the complete dependency graph, after this session

```text
AveragedMeanSquare μ h
  ← averagedMeanSquare_moebius_of_jointOmegaBudget            JointOmegaSpectral      ✓
  ← jointOmegaBudget → 0
      ├ non-spectral parts (cardinalities, joint variance)     JointFibreTransfer      ✓
      └ 16√x·∫‖K_δ‖²‖A_PQ‖²
          ← integral_kernel_normSq_jointOmega_le               JointOmegaBudgetFromLadder ✓
          ← ∫_{|w|≤T₀}‖A_PQ‖² ≤ β₀
              ← integral_normSq_jointOmegaPoly_le              Section4Assembly        ✓
                  ├ short ladder defect                        JointLadderProduct      ✓
                  └ per short block j:  section4_block_disc_ann Section4DiscAnnulus     ✓
                      ├ disc:   section4_block_disc             Section4DiscAnnulus     ✓
                      │           └ Ik: exists_setIntegral_disc_normSq_logPoly_moebius_le ✓
                      └ annulus: section4_block_full_on         Section4BlockFull       ✓
                          ├ non-exceptional: Lemma 2.4          Section4Assembly        ✓
                          └ exceptional:
                              ├ Vk: exists_annulus_bound_uniform  (corpus)              ✓
                              ├ Ik: setIntegral_normSq_logPoly_shortExceptionalOn_le    ✓
                              │       (Lemma 2.6 ∘ Lemma 2.5)
                              └ long ladder defect              LadderProductDefect (corpus) ✓
  + the parameter substitution                                                          OPEN
```

Every node marked ✓ is an unconditional, axiom-clean Lean theorem.  The single open node is the
parameter substitution — the joint-weight mirror of `Sieve/BudgetSubstitution`,
`Sieve/BudgetRhoBound`, `Sieve/BudgetLimit`, `Sieve/ScaledBudgetSubstitution` and
`Sieve/ScaledBudgetLimit`, at the schedule of the parameter table above.

### Milestone B, brick 36 — a correctness fix in the non-exceptional half (2026-08-19)

`Sieve/OmegaQEnergy` (axiom-clean, wired).  Applying Lemma 2.4 to the long-weighted cofactor
`∑_m μ(m)ω_Q(m)m^{iw}` through the *coefficient bound* `‖omegaQCoeff Q m‖ ≤ #Q` is not merely lossy,
it is fatal: `#Q ≍ exp((log x)^b)/(log x)^b` is of the size of the long primes themselves, whereas the
target carries only `W(Q)² ≍ (log log x)²`.  What Lemma 2.4 actually needs is the **energy**:

```text
sum_normSq_omegaQCoeff_Ioc_le (hq : q₀ ≤ q₁) (hab : a ≤ b) :
  ∑_{n ∈ (a,b]} ‖μ(n)ω_Q(n)‖²
    ≤ 2(4(b−a)·S(q₁) + 4π(q₁) + 8π(q₁)²) + 2(b−a)·W(Q)²

integral_Icc_normSq_omegaWeighted_le_energy (ha : 1 ≤ a) (hW : 1 ≤ W) :
  ∫_{|w| ≤ W} ‖∑_{n ∈ [a,b]} μ(n)ω_Q(n) n^{iw}‖²
    ≤ (5π/2·W + 5e/2·b) · ∑_{n ∈ (a−1,b]} ‖μ(n)ω_Q(n)‖²
```

The pointwise step is `c² ≤ 2(c − W)² + 2W²`, i.e. `(c − 2W)² ≥ 0`, and the variance is the corpus's
`Sieve/TuranKubiliusRange.sum_variance_primesRange_le`.  `integral_Icc_normSq_logPoly_le_support_bound`
of `Sieve/Section4Assembly` remains correct and is the right tool for the *short-ladder defect*,
where the crude `#Q` is affordable because the defect is already `x^{-Θ(1)}` smaller than the target.

### Milestone B, bricks 37–40 — the budget reduced to five numbers (2026-08-19)

A structural obstruction in the corpus's budget arithmetic had to be removed first.
`Sieve/BudgetTermSplit.spectral_terms_le` fixes the expiry height at `T₀ = B₀`, and §4 **cannot**
supply a mean-square bound there: at height `B₀` the non-exceptional term's ratio to the target is

```text
   VP_j²·(5π/2·B₀ + 5e/2·B₁)·energy / (stepMass_j²·B₀²·W_Q²)  ≍  P_j/(log P_j)² ,
```

so the cancellation threshold of `(35)` would have to be `≍ √P_j` rather than `π(P_j)/log P_j`.
The fix is that `T₀ ≥ B₀` is **not** what the Gallagher split needs — only `T₀ ≫ B₀/h` is:

```text
   (the term T₀ enters)  ≍  B₀/(T₀·h) → 0   ⟺   T₀ ≫ B₀/h .
```

Re-running the non-exceptional ratio at `T₀ = (B₀/h)·ω` gives `P_j·ω/(K_j²·h) + K_j^{-2}`, which
vanishes for `ω → ∞` with `ω ≪ (log P_j)²` — e.g. `ω = (log x)^{β/2}` against
`log P_j ≥ (log x)^{β/2}`.  So the whole lane works at a *low* expiry height.

| module | content |
|-|-|
| `Sieve/JointBudgetTermSplit` | **`affineMajorant_of_bound_at'`** — the affine majorant at a *free* expiry height, converting the mean value theorem's constant `5e/2·M·E` into the slope `5e/2·(M/T₀)·E·T`; **`joint_spectral_terms_le`** — the three Gallagher terms at a cut `Wc` with `δ·Wc ≤ 1`, bounded by `3α/Wc + 3β₀/Wc²` |
| `Sieve/JointOmegaBudgetFromLadder` (extended) | **`energy_jointOmegaCoeff_le_variance`** — the joint coefficient energy at its true size `≍ (length)·(W_PW_Q)²`, from the joint Turán–Kubilius variance (the earlier `energy_jointOmegaCoeff_le` pays the crude `Ω = #P·#Q`); **`integral_kernel_normSq_jointOmega_le'`** — the final Gallagher form |
| `Sieve/JointBudgetMaster` | **`jointOmegaBudget_le`** — the whole budget with the spectral part replaced; **`geomCofactorBlockAt_one_eq`** — with `A₀ = 1` (which the fibre index forces) every cofactor block of every ladder is an initial segment `Icc 1 ⌊B₀/(R(1+η)^j)⌋` |

The budget is now an expression in **five numbers**:

```text
jointOmegaBudget x h P Q
  ≤ 16√x·( 3·(5π/2 + 5e/2·B₀/T₀)·Ec / Wc  +  3·β₀/Wc² )
    + 204·((#P+1)(#Q+1))²·(√x+1)
    + 2(h+1)(2h+1)·( B₀·W_PW_Q·(W_P+W_Q+1) + 2·W_PW_Q·#P·#Q ) ,
```

`Ec` the coefficient energy, `β₀` the §4 mean square at the expiry height `T₀`, `Wc` the Gallagher
cut.  Dividing by `(W_PW_Q)²h²√x` and taking `Wc = B₀/h`, `T₀ = (B₀/h)·ω`, `Ec ≤ C·B₀(W_PW_Q)²`:

| term | value | vanishes because |
|-|-|-|
| slope | `48·C·(5π/2 + 5e h/(2ω))/h` | `h → ∞` and `ω → ∞` |
| constant | `48·β₀/(B₀²(W_PW_Q)²)` | the §4 estimate `β₀ = o(B₀²W_P²W_Q²)` |
| cardinalities | `204((#P+1)(#Q+1))²(√x+1)/((W_PW_Q)²h²√x)` | `#P·#Q = x^{o(1)}` |
| joint variance | `≍ 4(1/W_P + 1/W_Q) + 8#P#Q/(W_PW_Q√x)` | `W_P, W_Q → ∞` |

**Only the second row is still open**, and it is exactly the §4 estimate whose every ingredient is
already proved.  What remains is: instantiate the schedule, sum the per-block bounds of
`Sieve/Section4DiscAnnulus` over the short ladder via `Sieve/Section4Assembly`, and verify the four
limits above.

### Milestone B, bricks 41–43 — the per-block master, and a second energy fix (2026-08-19)

| module | content |
|-|-|
| `Sieve/Section4BlockMaster` | **`section4_block_master`** — one short block of §4, disc and annulus together, with the five inputs (Route-T `Vk`, the two cofactor mean squares `Idisc`/`Iann`, the long ladder's defect, the non-exceptional term) as parameters |
| `Sieve/Section4Master` | **`integral_normSq_jointOmegaPoly_le_master`** — the same summed over the short ladder.  This *is* the `β₀` of `jointOmegaBudget_le`, so it is the single entry point for the parameter substitution |
| `Sieve/JointLadderDefectDivisor` | `logPoly_restrictCoeff_of_subset`, `ladderGapSetAt_one_subset`, `norm_restrict_omegaQCoeff_le`, `jointLadderProductDefect_eq_restrict`, **`integral_normSq_jointLadderProductDefect_le_divisor`** |
| `Sieve/Section4DiscCofactor` (extended) | **`exists_setIntegral_disc_normSq_logPoly_moebius_one_le`** — the disc bound for an *initial* cofactor block, which is the only shape that occurs once `A₀ = 1` |
| `Sieve/OmegaQEnergy` (extended) | **`setIntegral_normSq_omegaWeighted_le_energy_on`** — Lemma 2.4 for the long-weighted cofactor over a part of the window |

**The second place `#Q` was fatal.**  Writing out the assembly's arithmetic showed that
`integral_normSq_jointLadderProductDefect_le_closed`'s coefficient bound `#Q` kills the short
ladder's defect.  The gap budget contains an irreducible term `≍ B₀/R_P` (moving endpoints summed
against the rounding term), so with the `#Q²` prefactor the defect is

```text
   ≍ exp(2(log x)^b)·√x·(log x)^{1−β/2}·(B₀/R_P)  ≍  x·exp(2(log x)^b − (log x)^{β/2})·polylog ,
```

and `2(log x)^b ≫ (log x)^{β/2}` because `b > 9/10 > β/2`.  It cannot be repaired by tuning `η_P`
(the term is `η_P`-free) or by raising `R_P` (which is capped at `h`).

The repair is the divisor bound, exactly as for the single weight: every gap index lies in `[1,B₀]`
and every designated long prime exceeds `R_Q`, so `‖μ(n)ω_Q(n)‖ ≤ log B₀ / log R_Q`, which at
`log R_Q ≍ (log x)^a` is `≍ (log x)^{1−a}` — a *small power of the logarithm* in place of a power of
`x`.  `integral_normSq_jointLadderProductDefect_le_divisor` carries that:

```text
  ∫_{|w|≤W} ‖jointLadderProductDefect P Q 1 B₀ R_P η_P L_P w‖²
    ≤ (log B₀/log R_Q + 1)²·(5π/2·W + 5e/2·N)·(log N/log R_P · gap budget) ,   N = ⌊B₀(1+η_P)⌋ .
```

The mechanism is `logPoly_restrictCoeff_of_subset`: the defect's cofactor sums run over gap sets
inside `[1,B₀]`, so the coefficient may be replaced by its restriction there without changing the
polynomial, and the restriction obeys the divisor bound everywhere.

With this, **both** places where the crude `#Q` appeared are repaired — the non-exceptional Lemma 2.4
term by the Turán–Kubilius energy (`Sieve/OmegaQEnergy`), and the short-ladder defect by the divisor
bound.  Nothing in the lane now carries a factor larger than a power of the logarithm except the
polynomials' own lengths.

### Milestone B, brick 44 — the schedule, and a large reuse (2026-08-19)

`Sieve/JointSchedule` (axiom-clean, wired).  The design decision that shortens the remaining work
most: **both designated ranges are instances of the corpus's own ladder parameters**
`Sieve/SpectralParameters.{ladderEta, ladderSteps, ladderTop}`, at two different exponent pairs.

| range | corpus instance | base | top | ratio | mass |
|-|-|-|-|-|-|
| short `P` | `(β, 1/2)` | `siftStart (β/2) x` | `ladderTop β (1/2) x` | `𝓁^{−β/2−5/4}` | `(β/2)log 𝓁` |
| long `Q` | `(b, a/b)`, `9/10 < a < b < 1` | `siftStart a x` | `ladderTop b (a/b) x` | `𝓁^{a−b−5/4}` | `(b−a)log 𝓁` |

so `tendsto_ladderMass`, `eventually_ladderTop_facts`, `ladderTop_bounds`, `ladderSteps_le` and
`GeomBlockPrimesRange.mem_geomBlock_primesRange` all apply **verbatim** to each range.  The
independent choice `η = 𝓁^{-10}` I had first derived is unnecessary: the corpus's `𝓁^{−β/2−5/4}`
already satisfies the gap-budget constraint `η = o(𝓁^{-(β/2+3−2a)})` whenever `a > 7/8`, and
`a > 9/10` is forced anyway by Lemma 2.3.

Landed:

* `jointCut c β x = √x / h`, `jointExpiry c β x = jointCut · 𝓁^{β/2}` — the two genuinely new
  parameters (the cut makes `δ·Wc ≤ 1`; the expiry height is the *low* one of brick 37);
* `jointShortSet`, `jointLongSet`, and for each: primality, the lower bound, and
  **`jointShortSet_range` / `jointLongSet_range`** (the covering hypothesis `geomBlock_biUnion_eq`
  wants, immediate from the top being a floor);
* **`eventually_jointSets_disjoint`** — from `ladderTop β (1/2) x ≤ cardLength β x = exp(𝓁^β)` and
  `siftStart a x ≥ exp(𝓁^a)` with `β < a`;
* `jointShortSet_mass`, `jointLongSet_mass` (via `sum_inv_primesRange`), and
  **`tendsto_jointShortMass`**, **`tendsto_jointLongMass`**, `eventually_jointMass_pos` — both
  harmonic masses tend to infinity.

That discharges the fourth row of the budget table (the joint Turán–Kubilius variance, whose
quotient is `≍ 4(1/W_P + 1/W_Q) + 8#P#Q/(W_PW_Q√x)`) and half of the third.

### The verified numerology at this schedule

Written out in full before any of it was formalised, and each line checked against the estimates
already proved:

| quantity | at the schedule | requirement | margin |
|-|-|-|-|
| short defect, gap sum | `L_P B₀η_P² + 5h + 2B₀/R_P + 5L_P + B₀/(R_P²η_P)` | `o(√x/polylog)` | `B₀/R_P = √x·exp(−𝓁^{β/2})` dominates, and `exp` beats every polylog |
| long defect (per block) | `(T₀+B₁)·polylog·[gap sum_j]` | `o(B₁²)` | `T₀ ≤ B₁·𝓁^{β/2}`, so it reduces to `[gap sum_j] = o(B₁/polylog)` |
| non-exceptional | `V_j²·𝓁^{β/2}·B₁²W_Q²` | `ε·stepMass_j²B₀²W_Q²` | threshold `V_j = #B_j/𝓁^{β/2}` gives `ε = 𝓁^{−β/2}` |
| exceptional, main | `𝓁^{a+b+20}ρ²B₁²` | `ε B₁²W_Q` | `ρ = exp(−c𝓁^{a−9/10}/(log𝓁)²)` beats every power of `𝓁` |
| exceptional, HM cross | `𝓁^{a+21}ρ²·|E_j|·√T₀·B₁·exp(𝓁^b)` | `ε B₁²W_Q` | `x^{1/4+o(1)}` against `x^{1/2−o(1)}` |
| disc | `𝓁^{b−a}B₁²·exp(−2c(log B₁)^{1/10})·2w₀` | `ε B₁²W_Q` | the low-frequency saving beats every power of `𝓁` |

Every margin is comfortable; nothing is tight.  What is left is to write these six lines as Lean
limits at the schedule and feed them through `Sieve/Section4Master` and
`Sieve/JointBudgetMaster.jointOmegaBudget_le`.

### Milestone B, brick 45 — the THIRD place `#Q` was fatal, and the divisor-bound chain (2026-08-19)

Instantiating the budget table at the schedule of brick 44 exposed the last one.  The fibre bridge
`Sieve/ScaledFibreBridge.sum_fibreSum_sq_le_integral_scaled` pays a rounding error `102·B²·(√x+1)`
where `B` is a **global sup bound** for the weight, and `Sieve/JointOmegaSpectral` supplies
`B = (#P+1)(#Q+1)`.  Dividing the resulting budget term by `(W_PW_Q)²h²√x`:

```text
   204·B²·(√x+1) / ((W_PW_Q)²h²√x)  ≍  (#P·#Q)²/h²  ≍  exp(2(log x)^b)/(log x)^{2β+2b}  →  ∞ .
```

The `#P` half is harmless (`#P ≍ h/(log x)^β`, so it cancels `h²`); the `#Q` half is not, because
the long range sits at `exp((log x)^b)` with `b > 9/10`, far above the window.

Same repair, third time: the fibre sums and the window sums only ever touch indices in `[1,B₀]`
(`Sieve/FibreWindowBridge.innerFibre_subset_fibreIndex`), and there both designated counts obey the
divisor bound, so

```text
   |μ(n)·ω_P(n)·ω_Q(n)|  ≤  (log B₀/log R_P)·(log B₀/log R_Q)  ≍  (log x)^{2−β/2−a} ,
```

a power of the logarithm.  `Sieve/JointSpectralDivisor` (axiom-clean, wired) carries the whole
reduction with that bound as a parameter:

| name | content |
|-|-|
| `jointOmegaWeightR P Q N` | the joint weight cut off outside `[1,N]` |
| **`abs_jointOmegaWeightR_le`** | the divisor bound, uniform in `n` |
| `logWindowSum_jointOmegaWeightR` | the cut-off changes neither the window sum nor the fibre sums |
| **`sum_sq_fibreSum_moebius_le_jointSpectralD`** | the spectral reduction with `Bd` as a parameter |
| `jointOmegaBudgetD` | the budget with the rounding error carried by `Bd` |
| **`averagedMeanSquare_moebius_of_jointOmegaBudgetD`** | the gate |
| **`jointOmegaBudgetD_le`** | the master, spectral part replaced |

**All three appearances of the crude `#Q` are now repaired**, and the pattern was the same each
time: the estimate only sees indices below `B₀`, and there `ω_Q` is a power of the logarithm, never
a power of `x`.

* non-exceptional Lemma 2.4 — Turán–Kubilius **energy** (`Sieve/OmegaQEnergy`);
* short-ladder defect — **divisor bound** (`Sieve/JointLadderDefectDivisor`);
* fibre-bridge rounding error — **divisor bound** (`Sieve/JointSpectralDivisor`).

The lane now carries no factor larger than a power of the logarithm anywhere except the
polynomials' own lengths.  The remaining work is the six limits of the numerology table, fed through
`Sieve/Section4Master` and `jointOmegaBudgetD_le`.

### Milestone B, brick 46 — two of the four budget rows are CLOSED (2026-08-19)

`Sieve/JointNonSpectral` (axiom-clean, sorry-free, wired).  The two non-spectral rows of the joint
budget quotient are now Lean limits at the schedule of brick 44.

| name | content |
|-|-|
| **`jointVariance_quotient_le`** | the variance row, majorised: `≤ 24(1/W_Q + 1/W_P + 1/(W_PW_Q)) + 24·#P·#Q/(W_PW_Q√x)`.  The prefactor `2(h+1)(2h+1) ≤ 12h²` cancels the `h²`, one factor of `W_PW_Q` cancels, and `B₀ ≤ 2√x` cancels the `√x` |
| `cardLength_mono_exp` | `exp(𝓁^β) ≤ exp(𝓁^b)` for `β ≤ b`, `𝓁 ≥ 1` |
| **`tendsto_jointCards_div_sqrt`** | `#P·#Q/√x → 0`: both ladder tops are below `cardLength b x` (`eventually_ladderTop_facts`), so the product is `≤ 4(cardLength b x)²`, and `Sieve/NonSpectralBudget.tendsto_cardLength_sq_div_sqrt` finishes |
| **`tendsto_jointVarianceRow`** | the variance row vanishes |
| **`jointDivisorBound_le`** | the joint divisor bound is `≤ (log x)²`: both `log R_P` and `log R_Q` exceed `1`, and `log B₀ ≤ log(2√x) ≤ log x` for `x ≥ 4` |
| **`tendsto_rpow_log_div_scaledLength_sq`** | `(log x)^d / h² → 0`, from the corpus's `tendsto_rpow_log_div_scaledLength` times `1/h → 0` |
| **`tendsto_jointRoundingRow`** | the rounding row vanishes: `204·Bd²(√x+1)/((W_PW_Q)²h²√x) ≤ 408(log x)^4/h² → 0` |

The sharp exponent `Bd ≍ (log x)^{2−β/2−a}` is not needed — `(log x)²` suffices, because `h²`
outgrows every power of the logarithm.  Two rows to go: the slope row (which vanishes by `h → ∞`
and `ω → ∞` once the energy is inserted) and the constant row, which is the §4 estimate itself.

### Budget status

| row | status |
|-|-|
| slope `48·C·(5π/2 + 5eh/(2ω))/h` | open — needs `energy_jointOmegaCoeff_le_variance` inserted, then `h, ω → ∞` |
| constant `48·β₀/(B₀²(W_PW_Q)²)` | open — this **is** the §4 estimate, `Sieve/Section4Master` at the schedule |
| cardinalities | **closed** (`tendsto_jointRoundingRow`) |
| joint variance | **closed** (`tendsto_jointVarianceRow`) |

### Milestone B, brick 47 — the slope row is CLOSED; one row left (2026-08-19)

`Sieve/JointSlopeRow` (axiom-clean, sorry-free, wired).

```text
jointSlope_quotient_le :
  48·(5π/2 + 5e/2·(B₀/T₀))·Ec / ((√x/h)·(W_PW_Q)²·h²)
    ≤ (480π/h + 960e/ω)·X ,    X = (1/W_Q + 1/W_P + 1/(W_PW_Q)) + #P#Q/(W_PW_Q√x) + 1

tendsto_jointSlopeMajorant : the right side → 0   (first factor → 0, second → 1)
tendsto_jointSlopeRow      : the slope row → 0
```

Two things had to be right.  The denominator collapses exactly — `(√x/h)·h² = h·√x` — and the
energy must enter at its **true** size: with `hEc` from `energy_jointOmegaCoeff_le_variance` and
`B₀ ≤ 2√x`, the majorant `Ec ≤ 4X(W_PW_Q)²√x` holds *with the two sides matching term by term*.

The divisor bound `Bd ≤ (log x)²` is **not** usable in this row, unlike in the rounding row: the
`5e·h/ω` half of the prefactor would leave `(log x)^4/(log x)^{β/2} → ∞`.  The ratio bound
`B₀/T₀ ≤ 2h/ω` is where the low expiry height of brick 37 pays off — it is exactly
`B₀ ≤ 2√x` after `T₀ = (√x/h)·ω` is substituted.

### Budget status

| row | status |
|-|-|
| slope | **closed** — `tendsto_jointSlopeRow` |
| constant `48·β₀/(B₀²(W_PW_Q)²)` | open — this **is** the §4 estimate, `Sieve/Section4Master` at the schedule |
| cardinalities | **closed** — `tendsto_jointRoundingRow` |
| joint variance | **closed** — `tendsto_jointVarianceRow` |

Three of four rows are Lean limits.  The remaining row is the whole content of §4, and every
ingredient it needs is already an unconditional theorem in the tree; what is left is to instantiate
`Sieve/Section4Master` at the schedule and check the six margins of the numerology table of
brick 44.

### The constant row: what it reduces to, and what of it is already corpus (2026-08-19)

The one open row is `48·β₀/(B₀²(W_PW_Q)²) → 0` with `β₀` from
`Sieve/Section4Master.integral_normSq_jointOmegaPoly_le_master`:

```text
   β₀  =  2·(∑_j 1/u_j)·(∑_j u_j·J_j)  +  2·Dshort ,      u_j = 1/stepMass_j ,
```

so `∑_j 1/u_j = W_P` by `Sieve/LadderHarmonicSplit.sum_stepMass_eq`, and the row splits in two.

**The short-ladder defect half is already corpus arithmetic.**  The gap sum inside
`integral_normSq_jointLadderProductDefect_le_divisor` is *literally* the corpus's
`Sieve/LadderAffineMajorant.ladderDefectSum L B₀ Q η` — the `A₀ = 1` instance matches term for term
— so `Sieve/LadderAffineBounds.ladderDefectSum_le` applies verbatim:

```text
  ladderDefectSum L B₀ Q η
    ≤ (log⌊B₀(1+η)⌋/log Q)·( L((1+B₀)η² + 5) + 5hR + (ηB₀ + (1+B₀)η)(2/(Qη)) + B₀(2/(Q²η)) ) .
```

Note also that `Sieve/ConstQuotientLimit.eventually_const_quotient_le` — the arithmetic half of the
corpus's own constant-row limit — is stated with `0 < β`, **not** `9/10 < β`; only the final
`tendsto_const_quotient` needs the Route-T exponent, and only through `budgetRho`.  So the
defect-half of the constant row is exponent-free corpus machinery.

**The per-block half is the genuinely new work.**  Per short block `j`, `section4_block_master`
gives `J_j` as five pieces, each of which needs a bound uniform in `j`, against the target
`ε·stepMass_j²·B₀²·W_Q²`:

| piece | bound needed | margin from the brick-44 table |
|-|-|-|
| disc: `(#B_j)²·2(∑1/v)(∑ v_k (#Q_k)² Idisc_k)` | `ε stepMass_j²B₀²W_Q²` | `exp(−2c(log B₁)^{1/10})·2w₀` beats every power of `𝓁` |
| disc + annulus defect: `(#B_j)²·4·Dfct_j` | same | `ladderDefectSum` again, at the long ladder |
| non-exceptional: `VP_j²·Enonexc_j` | same | `V_j = #B_j/𝓁^{β/2}` gives `ε = 𝓁^{−β/2}` |
| annulus main: `(#B_j)²·2(∑1/v)(∑ v_k V_k² Iann_k)` | same | `ρ² ≤ ε W_Q 𝓁^{−(a+b+20)}`, and `ρ` beats every power of `𝓁` |
| annulus HM cross | same | `x^{1/4+o(1)}` against `x^{1/2−o(1)}` |

All five margins were verified on paper in brick 44 and none is tight.

### Milestone B, brick 48 — the step-mass/cardinality comparison, and the non-exceptional numerology (2026-08-19)

`Sieve/StepMassCard` (axiom-clean, wired) — the two-sided comparison every per-block estimate needs,
since the estimates are stated per block and then weighted by `1/stepMass_j`:

```text
   stepMass_j·(Q(1+η)^j)  ≤  #B_j  ≤  stepMass_j·(Q(1+η)^{j+1}) .
```

### The non-exceptional piece, worked out exactly

Writing `Pj0 = Q(1+η)^j` for the step's left endpoint, `B₁ = ⌊B₀/Pj0⌋`, `V_j = #B_j/K` for the
threshold and `E_j ≤ CE·B₁·W_Q² + CR` for the cofactor energy (`CR` collecting the `π(z_Q)` terms,
which are `j`-independent), the non-exceptional term of `section4_block_master` is

```text
  V_j²·Enonexc_j
    ≤ (stepMass_j·Pj0(1+η)/K)²·(5π/2·T₀ + 5e/2·B₀/Pj0)·(CE·(B₀/Pj0)W_Q² + CR)
    =  stepMass_j²(1+η)²/K² · [ (5π/2)T₀·CE·B₀W_Q²·Pj0 + (5π/2)T₀·CR·Pj0²
                                + (5e/2)CE·B₀²W_Q² + (5e/2)CR·B₀·Pj0 ] ,
```

and dividing by the target `stepMass_j²·B₀²·W_Q²` the four brackets become

| term | value at the schedule | bound |
|-|-|-|
| `(5π/2)T₀·CE·Pj0/B₀` | `T₀Pj0/B₀ ≤ (√x/h)ω·h/√x = ω` | `(5π/2)CE·ω` |
| `(5π/2)T₀·CR·Pj0²/(B₀²W_Q²)` | `≤ ωh/(√x W_Q²)` | vanishes |
| `(5e/2)CE` | constant | constant |
| `(5e/2)CR·Pj0/(B₀W_Q²)` | `≤ CR·h/(√x W_Q²)` | vanishes (`CR = x^{o(1)}`) |

so `ε ≍ (1+η)²·C·ω/K²`.  **This fixes the threshold: `K = ω = (log x)^{β/2}`**, giving
`ε ≍ C/ω = C(log x)^{−β/2} → 0`.  The two `Pj0 ≤ h` uses are the only place the constraint
`P_j ≤ h` enters the non-exceptional half, and it holds by construction
(`ladderTop β (1/2) x ≤ cardLength β x`).

The same calculation, run at `T₀ = B₀` instead of `T₀ = (√x/h)ω`, gives `ε ≍ P_j/K²` and forces
`K ≍ √P_j` — which is the obstruction brick 37 removed.

### Milestone B, brick 49 — the non-exceptional piece in Lean, and a design correction (2026-08-19)

`Sieve/Section4NonExcPiece.nonexceptional_piece_le` (axiom-clean, wired) — the first of the five
per-block pieces, exactly as computed in brick 48:

```text
  (NB/K)²·(5π/2·T₀ + 5e/2·B₁)·E
    ≤ stepMass_j²(1+η)²/K² · [ (5π/2)T₀·CE·B₀W_Q²·Pj0 + (5π/2)T₀·CR·Pj0²
                               + (5e/2)CE·B₀²W_Q² + (5e/2)CR·B₀·Pj0 ]
```

for `NB ≤ stepMass_j·Pj0(1+η)`, `B₁ ≤ B₀/Pj0`, `E ≤ CE·B₁·W_Q² + CR`.

### DESIGN CORRECTION: do not weight by `1/stepMass_j`

Writing the sum over the short ladder exposed a trap.  The harmonic Cauchy–Schwarz
(`Sieve/LadderHarmonicSplit`, `Sieve/SetIntegralBlockSplit`) needs `0 < v_j`, and the natural choice
`v_j = 1/stepMass_j` **fails**: a thin ladder step need not contain a prime, so `stepMass_j = 0` is
possible and `1/0 = 0` violates the hypothesis.  Proving every step nonempty would need prime
counting in short intervals — precisely what this lane must avoid.

The corpus already solved this, and the solution is not to divide at all.
`Sieve/BlockMassCompare.sum_card_geomBlock_div_le` sums the *counting* side directly against the
cofactor lengths:

```text
   ∑_{j<L} #B_j · (B / (Q(1+η)^j))  ≤  (1+η)·B·∑_{p∈P} 1/p ,
```

whose docstring records the point exactly: *"the estimate that replaces every short-interval prime
count in the spectral side … no prime counting in short intervals is involved."*  And indeed
`Sieve/OmegaWeightedLadderBound.integral_normSq_omegaWeighted_le` (the `1/v_j`-weighted route) has
**no consumers** in the corpus: the chain to `ScaledBudgetLimit` goes through
`Sieve/LadderAffineMajorant.integral_normSq_omegaWeighted_affine_le` instead.

So the joint assembly must follow `LadderAffineMajorant`'s pattern.  The per-block pieces stay as
they are — `Sieve/Section4NonExcPiece` and the four to come are stated with `stepMass_j` on the
right, which is exactly the shape `sum_card_geomBlock_div_le` consumes — but
`Sieve/Section4Master`'s `(∑_j 1/u_j)(∑_j u_j J_j)` form should be replaced by the direct sum.

Also removed: `Sieve/StepMassCard.card_geomBlock_le_stepMass` duplicated the corpus's
`BlockMassCompare.card_geomBlock_le_mul_stepMass`.  The module now imports it and keeps only the
converse `stepMass_mul_le_card`.

### Milestone B, brick 50 — equal weights work, and they retune the threshold (2026-08-19)

The `stepMass_j = 0` obstruction of brick 49 has a second, simpler resolution than switching to the
direct-sum form: **run the Cauchy–Schwarz over the ladder with equal weights `v_j = 1`.**  The cost
is the number of steps instead of the harmonic mass, and the number of steps is a polylogarithm.

`Sieve/StepMassCard` (axiom-clean, wired) supplies what makes that affordable:

```text
geomBlock_subset_Ioc :  a step sits in  Ioc ⌊Q(1+η)^j⌋ ⌊Q(1+η)^{j+1}⌋
stepMass_le          :  stepMass_j  ≤  η + 1/(Q(1+η)^j)
```

so `max_j stepMass_j ≤ 2η` once `Q(1+η)^j ≥ 1/η`, which holds because the base is `exp(𝓁^{β/2})`
and `η` is only a polylogarithm.  Then

```text
   ∑_j stepMass_j²  ≤  (max_j stepMass_j)·∑_j stepMass_j  ≤  2η·W_P ,
   L_P·η ≤ 2𝓁^β        (from L_P ≤ log(h/R_P)/log(1+η) and log(1+η) ≥ η/2) ,
```

so the equal-weight Cauchy–Schwarz costs `L_P·∑_j J_j ≤ 4·ε·𝓁^β·B₀²W_Q²W_P` against the target
`o(B₀²W_P²W_Q²)` — i.e. it needs `ε·𝓁^β = o(W_P) = o(log 𝓁)`.

**This retunes the threshold.**  The non-exceptional piece has `ε ≍ C·ω/K²` (brick 48), so with
`ω = 𝓁^{β/2}` the requirement is `K² ≫ 𝓁^{3β/2}/log 𝓁`.  The earlier choice `K = 𝓁^{β/2}` is
**not** enough; `K = (log x)^{4β/5}` is, giving `ε·𝓁^β = C𝓁^{−β/10} → 0`.

Lemma 2.5 is unaffected: at `K = 𝓁^{4β/5}` the exceptional measure is still
`log|E_j| ≍ 𝓁^{1−β/2}·(8β/5+1)log 𝓁 = o(𝓁)`, so `|E_j| = x^{o(1)}` exactly as before, and the
Halász–Montgomery cross term still compares `x^{1/4+o(1)}` against `x^{1/2−o(1)}`.

The exceptional and disc pieces absorb the extra `L_P` (and the long ladder's `L_Q`) without
retuning at all, because their savings — the Route-T `ρ` and the low-frequency
`exp(−c(log B₁)^{1/10})` — beat every power of the logarithm.

**Schedule, final form.**

| parameter | value |
|-|-|
| short range | `(β, 1/2)` instance of the corpus ladder |
| long range | `(b, a/b)` instance, `9/10 < a < b < 1` |
| Gallagher cut `Wc` | `√x / h` |
| expiry height `T₀` | `Wc·ω`, `ω = (log x)^{β/2}` |
| threshold `K` | `(log x)^{4β/5}` |
| both Cauchy–Schwarz weights | `1` |

### Milestone B, brick 51 — the equal-weight chain (2026-08-19)

`Sieve/JointEqualWeights` (axiom-clean, wired).  The three splits the assembly uses, instantiated at
`v ≡ 1`, so that the `stepMass_j = 0` obstruction never arises:

| name | shape |
|-|-|
| **`setIntegral_normSq_omegaWeighted_le_blocks_one`** | `∫_E‖∑_m μ(m)ω_Q(m)m^{iw}‖² ≤ 2(L_Q·∑_k V_k²I_k) + 2∫_E‖defect‖²` |
| **`section4_block_master_one`** | one short block, disc + annulus, with `L_Q` in place of `∑_k 1/v_k` |
| **`integral_normSq_jointOmegaPoly_le_one`** | `∫_{|w|≤W}‖A_PQ‖² ≤ 2(L_P·∑_j J_j) + 2·Dshort` |

Each is the corresponding parametrised theorem at `v = fun _ => 1`, with `∑_k 1/1 = L` and
`∑_k 1·X_k = ∑_k X_k`.  Nothing else changes: the per-block pieces were already stated with
`stepMass_j` on the right, which is what `Sieve/StepMassCard.stepMass_le` and
`Sieve/BlockMassCompare` consume.

### The chain, as it now stands

```text
AveragedMeanSquare μ h
  ← averagedMeanSquare_moebius_of_jointOmegaBudgetD              JointSpectralDivisor      ✓
  ← jointOmegaBudgetD → 0, four rows:
      ├ joint variance                tendsto_jointVarianceRow    JointNonSpectral          ✓
      ├ cardinalities/rounding        tendsto_jointRoundingRow    JointNonSpectral          ✓
      ├ slope                         tendsto_jointSlopeRow       JointSlopeRow             ✓
      └ constant  48·β₀/(B₀²(W_PW_Q)²)                                                      OPEN
          ← β₀ from integral_normSq_jointOmegaPoly_le_one          JointEqualWeights        ✓
              ├ Dshort: integral_normSq_jointLadderProductDefect_le_divisor
              │           + ladderDefectSum_le  (corpus)                                     ✓
              └ per block j: section4_block_master_one                                       ✓
                  ├ non-exceptional: nonexceptional_piece_le       Section4NonExcPiece      ✓
                  ├ disc Idisc                                     Section4DiscCofactor     ✓
                  ├ annulus Vk                                     AnnulusBoundUniform (corpus) ✓
                  ├ annulus Iann                                   Section4ExceptionalCofactor ✓
                  └ long-ladder defect                             LadderProductDefect (corpus) ✓
```

Every leaf is an unconditional theorem.  What remains is arithmetic: bound each of the five
per-block pieces by `ε·stepMass_j²·B₀²·W_Q²` at the schedule (the first is done —
`nonexceptional_piece_le`), sum with `∑_j stepMass_j² ≤ 2η·W_P` and `L_P·η ≤ 2𝓁^β`, and conclude.

### Milestone B, brick 52 — the disc piece (2026-08-19)

`Sieve/Section4DiscPiece` (axiom-clean, wired) — the second of the five per-block pieces.  Two
cancellations, both exact:

```text
disc_term_le  :  (#Q_k)²·I_k  ≤  (Q_k(1+η_Q))²·((B₁/Q_k)·S)²·2w₀  =  (1+η_Q)²·B₁²·S²·2w₀
```

— the **long** block scale `Q_k` cancels between the trivial prime bound and the cofactor length, so
the sum over the `L_Q` long blocks is `L_Q(1+η_Q)²B₁²S²·2w₀` with no `Q_k` left; and

```text
disc_block_le :  #B_j²·(2(L_Q·Σ) + 2·Dfct)
                   ≤ stepMass_j²(1+η_P)²·(2L_Q²(1+η_Q)²B₀²S²·2w₀)
                     + stepMass_j²·Pj0²(1+η_P)²·2Dfct
```

— the **short** block scale cancels the same way, through `Pj0²·B₁² ≤ B₀²`.

So the disc piece is `stepMass_j²·B₀²·S²·(polylog)`, against the target
`ε·stepMass_j²·B₀²·W_Q²`: it costs `ε ≍ L_Q²·w₀·S²/W_Q²`, and `S = exp(−c(log B₁)^{1/10})` beats
every power of the logarithm, so no retuning of any parameter is needed for this piece.

Two of the five per-block pieces are now Lean theorems (`nonexceptional_piece_le`,
`disc_term_le`/`disc_block_le`).  The three left are the two ladder defects and the annulus
exceptional term, whose savings (`ladderDefectSum_le`, and the Route-T `ρ`) are likewise already
available.

### Milestone B, brick 53 — the annulus exceptional piece (2026-08-19)

`Sieve/Section4AnnPiece` (axiom-clean, wired) — the third of the five per-block pieces, and the one
carrying §4's actual saving.

```text
ann_term_le  :  V_k²·I_k  ≤  (ρ'Q_k)²·(2π)⁻¹·(2(B₁/Q_k) + C|E|)·(B₁/Q_k)
                          =  ρ'²·(2π)⁻¹·(2B₁² + C·|E|·B₁·Q_k)
ann_block_le :  #B_j²·(2(L_Q·Σ) + 2Dfct)  ≤  stepMass_j²Pj0²(1+η_P)²·(2(L_Q·M) + 2Dfct)
ann_main_le  :  Pj0²(1+η_P)²·2L_Q²·ρ'²(2π)⁻¹·2B₁²  ≤  (1+η_P)²·2L_Q²·ρ'²(2π)⁻¹·2B₀²
```

The long block scale `Q_k` cancels in the main summand exactly as on the disc, leaving `ρ'²`, which
beats every power of the logarithm.  It survives only in the Halász–Montgomery cross term
`C·|E|·B₁·Q_k`, where the comparison is `x^{1/4+o(1)}` against `B₀ = x^{1/2}` — the one place in the
whole lane where a *power* of `x` rather than a power of `log x` does the work, and it is exactly
the exposé's constraint `P_jQ_k ≪ X^{1/14−ε}` in the form this schedule needs it.

Three of the five per-block pieces are Lean theorems:

| piece | module | cost `ε` |
|-|-|-|
| non-exceptional | `Section4NonExcPiece` | `C·ω/K²` — forced `K = (log x)^{4β/5}` |
| disc | `Section4DiscPiece` | `L_Q²·w₀·S²/W_Q²`, `S` super-polylog small |
| annulus exceptional | `Section4AnnPiece` | `L_Q²ρ'²/W_Q²` + the `x^{-1/4+o(1)}` cross term |
| short-ladder defect | corpus `ladderDefectSum_le` | — |
| long-ladder defect | corpus `ladderDefectSum_le` | — |

The two defect pieces are the corpus's `ladderDefectSum` object verbatim (brick 47's finding), so
what is left is to instantiate all five at the schedule and sum.

### Milestone B — the long ladder needs its OWN ratio; the corpus's `ladderEta` cannot serve (2026-08-19)

Working the fourth per-block piece (the long-ladder defect) exposes a constraint that the reuse of
brick 44 does **not** satisfy.  With `Dfct_j` from
`Sieve/LadderProductDefect.integral_normSq_ladderProductDefect_le_closed` and the gap sum from
`Sieve/LadderAffineBounds.ladderDefectSum_le`, the dominant contribution to the block's defect term
is

```text
   Pj0²·(T₀ + B₁)·(log B₁/log R_Q)·(L_Q·B₁·η_Q²)
     ≤ 2·Pj0²B₁²·𝓁^{β/2}·𝓁^{1−a}·𝓁^{b}·η_Q        (using T₀ ≤ B₁·𝓁^{β/2} and L_Q η_Q ≍ 𝓁^b)
     ≤ 2·B₀²·𝓁^{β/2+1−a+b}·η_Q ,
```

so against the target `ε·B₀²·W_Q²` the requirement is

```text
   η_Q  =  o( 𝓁^{-(β/2 + 1 − a + b)}·(log 𝓁)² ) .
```

The corpus's instance supplies `η_Q = ladderEta b (a/b) x = 𝓁^{a−b−5/4}`, and

```text
   a − b − 5/4  ≤  −(β/2 + 1 − a + b)   ⟺   −5/4 ≤ −β/2 − 1   ⟺   β ≤ 1/2 .
```

**The `a − b` cancels**, so no choice of `9/10 < a < b < 1` repairs it: the corpus's exponent `−5/4`
is exactly the one that works up to `β = 1/2` and fails above it.  Since the whole point of this
lane is `β > 1/2`, the long ladder must carry its own ratio, e.g.

```text
   η_Q  :=  (log x)^{a − b − 2}      (any exponent ≤ a − b − 1 − β/2 will do).
```

The short ladder is unaffected: its defect is bounded by
`integral_normSq_jointLadderProductDefect_le_divisor` at the *divisor* bound and was checked in
brick 44 with `η_P = 𝓁^{−β/2−5/4}`, which is the corpus's own value.

### Consequence for the schedule

`Sieve/JointSchedule.jointLongSet` must be redefined with a free ratio, and the corpus lemmas
`ladderPow_le`, `ladderTop_bounds`, `ladderPow_ge`, `tendsto_ladderMass`,
`eventually_ladderTop_facts` need free-`η` companions.  Their proofs use only `0 < η` and
`Q ≤ top`, so the generalisation is mechanical — the definitions
`ladderSteps β γ x`, `ladderTop β γ x` simply bake in `ladderEta β γ x`, which is the only obstacle.

This is recorded before the generalisation is written so the constraint is not rediscovered: **the
long ladder's ratio is pinned by its own defect, not by the harmonic mass, and it is a strictly
smaller power of `log x` than the corpus's short-ladder value.**

### Milestone B, brick 54 — the free-ratio ladder (2026-08-19)

`Sieve/FreeEtaLadder` (axiom-clean, wired) — the generalisation the previous entry showed was
unavoidable.  Same three facts as `Sieve/SpectralParameters`, with the ratio loose:

```text
gLadderSteps Q η top = ⌊log(top/Q) / log(1+η)⌋
gLadderTop   Q η top = ⌊Q(1+η)^{gLadderSteps Q η top}⌋

gLadderPow_le    (0 < Q) (Q ≤ top) (0 < η) :  Q(1+η)^{steps} ≤ top
gLadderPow_ge    (same)                    :  top/(1+η) ≤ Q(1+η)^{steps}
gLadderTop_bounds(same)                    :  gLadderTop ≤ top  ∧  top/(1+η) − 1 ≤ gLadderTop
gLadderMass_ge   (2 ≤ A) (2 ≤ B)           :  log log A − log log B + ladderMassConst
                                                ≤ mertensS A − mertensS B
```

Every proof uses only `0 < η` and `Q ≤ top`; the corpus's versions were identical except for
carrying `ladderEta β γ x` in the statement.  `gLadderMass_ge` is `ladderMass_ge` with the two
naturals free, which is all `logLog_sub_le_mertensS` and `mertensS_le_logLog_add` ever needed.

With this the long designated range can be redefined at `η_Q = (log x)^{a−b−2}`:

```text
   Q  =  primesRange (siftStart a x) (gLadderTop (siftStart a x) η_Q (cardLength b x)) ,
```

and `gLadderTop_bounds` + `gLadderMass_ge` give `W_Q ≥ (b−a)log 𝓁 − O(1) → ∞` exactly as
`tendsto_ladderMass` did — the mass depends only on the two endpoints, not on the ratio, which is
why the ratio was free to be shrunk in the first place.

### Milestone B, brick 55 — the long range rebuilt at its own ratio (2026-08-19)

`Sieve/JointLongRange` (axiom-clean, sorry-free, wired).  The long designated range on
`Sieve/FreeEtaLadder`:

```text
jointLongEta a b x  = (log x)^{a−b−2}
jointLongTopF a b x = gLadderTop (siftStart a x) (jointLongEta a b x) (cardLength b x)
jointLongSetF a b x = primesRange (siftStart a x) (jointLongTopF a b x)
```

with `siftStart_pos`, **`eventually_siftStart_le_cardLength`** (the ladder's base is below its
target: `⌈exp(𝓁^a)⌉ ≤ exp(𝓁^a)+1 ≤ exp(𝓁^b)`, using `𝓁^b = 𝓁^a·𝓁^{b−a} ≥ 2𝓁^a ≥ 𝓁^a + 1`),
**`jointLongTopF_le`**, **`jointLongTopF_ge`** (the two halves of `gLadderTop_bounds`),
`jointLongSetF_prime`, `jointLongSetF_ge` and **`jointLongSetF_range`** (the covering hypothesis).

Remaining for the swap: the mass limit `W_Q → ∞` at the new top.  It is
`gLadderMass_ge` plus `jointLongTopF_ge` and `log_siftStart_le`:

```text
   W_Q  ≥  log log (jointLongTopF)  −  log log (siftStart a x)  +  ladderMassConst
        ≥  log(𝓁^b − log 4)  −  log(𝓁^a + log 2)  +  ladderMassConst   →  ∞ ,
```

using `η_Q → 0` to get `jointLongTopF ≥ exp(𝓁^b)/4` eventually.  Once that is written, the three
downstream modules (`JointSchedule`'s long-range lemmas, `JointNonSpectral`, `JointSlopeRow`) switch
from `ladderTop b (a/b) x` to `jointLongTopF a b x` mechanically — the only corpus fact they use of
the old top is `ladderTop_bounds`, whose replacement `jointLongTopF_le` is proved above.

**Note on process.** A first attempt at this redefinition was written directly into
`Sieve/JointSchedule` with two `sorry` placeholders for the base-below-target step; it was reverted
before building and rewritten here as a standalone module with that step proved.  Nothing with a
`sorry` has entered the tree.

### Milestone B, brick 56 — the free-ratio long range is COMPLETE (2026-08-19)

`Sieve/JointLongRange` extended (axiom-clean, sorry-free, wired).  The mass limit at the new ratio:

```text
tendsto_jointLongEta                : η_Q = (log x)^{a−b−2} → 0
eventually_jointLongTopF_ge_quarter : cardLength b x / 4 ≤ jointLongTopF a b x
tendsto_jointLongMassF              : mertensS (jointLongTopF a b x) − mertensS (siftStart a x) → ∞
```

The mass proof is the chain the previous entry predicted, with every step now closed:

```text
   W_Q  ≥  log log (TopF) − log log (siftStart a x) + ladderMassConst      gLadderMass_ge
        ≥  log(𝓁^b/2)    − log(2𝓁^a)               + ladderMassConst      (top ≥ cardLength/4,
                                                                            log siftStart ≤ 𝓁^a + log2)
        =  (b−a)·log 𝓁   − log 4                   + ladderMassConst  →  ∞ .
```

The two rpow identities `log(𝓁^b/2) = b·log 𝓁 − log 2` and `log(2𝓁^a) = log 2 + a·log 𝓁` are
`Real.log_rpow` at `log x > 0`; the `≥ 2` hypotheses of `gLadderMass_ge` come from
`cardLength b x ≥ 8` and `eventually_le_siftStart`.

**The long range is therefore complete at its own ratio**: definitions, primality, the lower bound,
the covering hypothesis, both top bounds, and the mass.  Everything the three downstream modules
(`JointSchedule`'s long-range lemmas, `JointNonSpectral`, `JointSlopeRow`) take from the old
`ladderTop b (a/b) x` now has a `jointLongTopF` counterpart:

| old | new |
|-|-|
| `eventually_ladderTop_facts …2.1` | `jointLongTopF_le` |
| `tendsto_ladderMass` | `tendsto_jointLongMassF` |
| `jointLongSet_range` | `jointLongSetF_range` |
| `jointLongSet_prime`, `_ge` | `jointLongSetF_prime`, `_ge` |

so the swap is now a mechanical substitution with no remaining mathematical content.

### Milestone B, brick 57 — the free-ratio long range is IN the schedule (2026-08-19)

The swap of brick 56 is done; nothing in the lane now uses `ladderTop b (a/b) x`.

`Sieve/JointLongRange` was decoupled from `Sieve/JointSchedule` (it needs only `FreeEtaLadder`,
`RoughRemainderLimit`, `ShortIntervalLength`, `GeomBlockPrimesRange`) and gained the last missing
endpoint fact

```text
eventually_siftStart_le_jointLongTopF :  ∀ᶠ x, siftStart a x ≤ jointLongTopF a b x
```

— proved from `cardLength b x / 4 ≤ jointLongTopF` and `siftStart a x ≤ exp(𝓁^a) + 1` via
`𝓁^a ≥ 4`, `𝓁^{b−a} ≥ 2`, `exp 4 ≥ 5`: then `exp(𝓁^b) ≥ 5·exp(𝓁^a) ≥ 4(exp(𝓁^a)+1)`.

`Sieve/JointSchedule` now *defines* `jointLongSet a b x := jointLongSetF a b x`, and its five long-range
lemmas are the free-ratio ones:

| lemma | new content |
|-|-|
| `jointLongSet_prime` | `jointLongSetF_prime` |
| `jointLongSet_ge` | base `siftStart a x` (was `siftStart (a/b*b) x`) |
| `jointLongSet_range` | covering by `gLadderSteps` at `jointLongEta` |
| `jointLongSet_mass` | `mertensS (jointLongTopF a b x) − mertensS (siftStart a x)` |
| `tendsto_jointLongMass (ha0 : 0 < a) (hab : a < b)` | from `tendsto_jointLongMassF`; `0 < b`, `b < 1` are no longer needed |

`eventually_jointSets_disjoint` lost its `0 < b` hypothesis for the same reason, and
`Sieve/JointNonSpectral.tendsto_jointCards_div_sqrt` now takes the long top's bound from
`jointLongTopF_le` instead of `eventually_ladderTop_facts`.  `Sieve/JointNonSpectral` and
`Sieve/JointSlopeRow` build unchanged otherwise: the free ratio is invisible to the three
non-spectral rows, exactly as predicted — they see only the two endpoints.

**Range covered.**  The long ladder needs `9/10 < a` (Lemma 2.3's zero-free width) and the two
designated ranges must be disjoint, i.e. `β < a`.  So this arrangement proves the mean square for
`1/2 < β < a` with `9/10 < a < b < 1` free; at `a = 0.92, b = 0.95` that is `1/2 < β < 0.92`, which
together with the corpus's existing `9/10 < β < 1` covers the card's full range `1/2 < β < 1`.

### Milestone B, brick 58 — the five per-block pieces get their analytic inputs (2026-08-19)

Five small modules, all axiom-clean, sorry-free and wired, closing the last gaps between the
abstract per-block majorants of bricks 49–53 and the corpus's analytic theorems.

| module | content |
|-|-|
| `Sieve/LadderDefectOnParts` | **`setIntegral_normSq_ladderProductDefect_le_closed_on`** — the long ladder's defect over *any* part of the window, from the closed bound over the whole window (`setIntegral_mono_set` on a continuous nonnegative integrand).  `Sieve/Section4BlockMaster` needs it twice, for the disc and for the exceptional annulus |
| `Sieve/Section4DiscRel` | **`exists_setIntegral_disc_normSq_geomCofactorBlockAt_rel_le`** — the disc mean square of a ladder step's cofactor in the *relative* form `(relMoebiusSharp Nmin · B₁/Q_k)²·2w₀`, so the long block's scale cancels |
| `Sieve/GeomBlockCardBound` | **`card_geomBlock_le_endpoint`** — a ladder step is no larger than its right endpoint |
| `Sieve/Section4DiscSum` | **`sum_card_sq_mul_discBound_le`** — the disc sum over the long ladder; the block scale cancels term by term, leaving `L_Q·(1+η_Q)²B₁²S²·2w₀` |
| `Sieve/Section4AnnCofactor` | **`setIntegral_normSq_cofactor_annulus_le`** — Halász–Montgomery for the step's cofactor over the exceptional annulus, with every step-dependent quantity majorised by a step-free one |
| `Sieve/Section4AnnSum` | **`sum_annulus_terms_le`** — the annulus sum over the long ladder |

### Milestone B — the NO-GO: this arrangement cannot go below `β = κ` (2026-08-19)

Writing the annulus sum out at the schedule exposes a constraint that no choice of parameters inside
this architecture satisfies.  Let `𝓁 = log x`, `κ` the zero-free-region width exponent carried by
`Sieve/RouteTZetaAsymptotics` (`κ = 9/10`; `κ = 2/3` would be Vinogradov–Korobov), `h = exp(𝓁^β)`.

**The chain.**

1. *The expiry height is `x^{1/2−o(1)}`.*  The Gallagher cut obeys `δ·Wc ≤ 1` with `δ = h/√x`, so
   `Wc ≤ √x/h`; the slope row is `48(5π/2 + 5eB₀/(2T₀))B₀/(Wc·h²)`, which vanishes only for
   `Wc ≳ √x/h²` **and** `T₀ ≫ Wc`.  Hence `log T₀ = 𝓁/2 − O(𝓁^β)`.

2. *The short primes obey `log P_j ≤ 𝓁^β(1+o(1))`.*  The non-exceptional term of one short block is
   `V_j²·∫_{|w|≤T₀}‖G_j‖²  ≈  V_j²(T₀ + B₁ⱼ)B₁ⱼW_Q²`, and against the per-block target
   `ε·n_j²B₁ⱼ²W_Q²` (`n_j = #B_j`) it forces the threshold ratio

   ```text
      K_j²  :=  (n_j/V_j)²  ≥  (1 + T₀/B₁ⱼ)/ε  =  (1 + P_jω/h)/ε .
   ```

   So `P_j ≫ h` makes `log K_j ≍ log(P_j/h)` instead of `≍ log log x`.

3. *The moment method needs `k ≥ log T₀/log P_j`.*  Lemma 2.5
   (`Sieve/Section4ExceptionalMeasure.volume_blockExceptional_le`) gives

   ```text
      |E_j|  ≤  (T₀ + 4·NA^k(1 + log NA^k))·k^k·n_j^k / V_j^{2k}
             =  (T₀ + 4NA^k(1+k·log NA))·k^k·K_j^{2k} / n_j^k ,
   ```

   whose first summand is `< 1` only when `k·log n_j ≥ log T₀`, i.e. `k ≥ 𝓁^{1−β}/2` by 1 and 2.

4. *The second summand costs `exp(k·log(NA/n_j))`, and `NA/n_j ≥ log P_j` by prime density.*  So

   ```text
      |E_j|  ≥  exp( k·log log P_j )  ≥  exp( (β/2)·𝓁^{1−β}·log 𝓁 ) .
   ```

5. *The only saving available against `|E_j|` is `ρ²`.*  On the exceptional set the short prime
   polynomial is bounded trivially, and Halász–Montgomery's second term
   `3072·N_D·|E_j|` is exactly `3072×` the trivial bound, so the annulus term is

   ```text
      n_j²·L_Q²·ρ²·|E_j|·B₁ⱼ²   against   ε·n_j²B₁ⱼ²W_Q² ,
   ```

   i.e. `ρ²·|E_j| = o(polylog)` is required, with
   `ρ² = exp(−2·log R_Q·routeTWidth(T₀)) = exp(−Θ(𝓁^{a−κ}))`, `a < 1` the long-prime exponent.

**Conclusion.** `𝓁^{1−β}·log 𝓁 ≲ 𝓁^{a−κ} < 𝓁^{1−κ}` forces `β > κ`.  With the corpus's `κ = 9/10`
this is exactly the range the corpus already proves, so **the joint `ω_P·ω_Q` arrangement with a
pointwise Route-T saving on the long primes gains nothing over the single-weight route.**  It is not
a tuning failure: steps 2 and 4 are prime density and the Gallagher cut, and step 1 is the fibre
width, so no choice of `R_P, η_P, L_P, R_Q, η_Q, L_Q, K, ω, w₀, W, T₀, k` escapes.

This *derives* the ceiling `(log x)^{−2(β−κ)}` recorded on the marker card for the single-weight
route, now for the joint arrangement and for the **qualitative** statement, not merely for a rate.

### What the no-go says the repair must be

The barrier enters at step 3, through `k ≥ log T₀/log P_j` with a **single** short range `P` used at
**every** frequency.  Matomäki–Radziwiłł's actual device is a *frequency-adapted* family: on the
annulus `|w| ≍ T'` one uses a Ramaré decomposition whose short primes satisfy `log P ≍ log T'`, so
`k = O(1)` and `|E| ` is a polylogarithm — after which `ρ` need only beat a polylogarithm, which the
Route-T envelope does comfortably.  The cost is that the identity
`f(n) = ω_P(n)^{-1}∑_{p∈P, p|n} f(p)f(n/p)` must be applied once per frequency range, with its own
discarded set (integers with no prime factor in that range) each time, and the discarded sets must be
summed over the ranges.

**Concretely, the next design (Milestone C) is:** scales `L_1 < … < L_I` with
`P^{(i)} = (exp(L_{i−1}), exp(L_i)]`, frequency annuli `A_i = {T_{i−1} < |w| ≤ T_i}` with
`log T_i ≍ L_i`, and on `A_i` the Ramaré identity at `P^{(i)}` together with the long range `Q`.
The top annulus `|w| ∈ (T_I, T₀]` needs `L_I ≍ 𝓁`, i.e. short primes of size `x^{Θ(1)}`, which are
available (the only cap on the short range is `#P·#Q = o(√x)` from the joint variance row, i.e.
`log z ≤ 𝓁/2 − 𝓁^b`), and whose harmonic mass still grows because the range spans
`log log`-many scales.

Everything already built stays: the per-block masters, the five pieces, the two ladders, the
budget rows and the schedule are all parametric in `(R_P, η_P, L_P, W, T₀)` and are re-used verbatim
once the single window `Set.Icc (-W) W` is replaced by the annulus family.

### Milestone C — the actual Matomäki–Radziwiłł architecture, read off the source (2026-08-19)

The no-go above says the saving on the long primes cannot be a *proved pointwise bound*.  Reading
Matomäki–Radziwiłł (arXiv:1501.04585, the corrected arXiv version) shows why: **in their proof the
pointwise smallness is a DEFINITION, not a theorem.**  The frequency line is partitioned by *which*
prime polynomial happens to be small, and the hard case is the set where none is.

**Their parameters** (§2, eq. (2)–(4)):

```text
   Q₁ ≤ exp(√log X),   P₁ ≥ (log Q₁)^{40/η},   [P₁,Q₁] ⊆ [1,h],   η ∈ (0,1/6)
   P_j = exp( j^{4j}   (log Q₁)^{j−1} log P₁ )
   Q_j = exp( j^{4j+2} (log Q₁)^{j}          )
   J   = largest j with Q_j ≤ exp((log X)^{1/2})
   S   = { X ≤ n ≤ 2X : n has a prime factor in every [P_j,Q_j], j ≤ J }
```

so `log P_j` grows like `(log Q₁)^j` — **iterated**, not a single pair of ranges.  The two structural
conditions are `(log log Q_j)/(log P_{j−1} − 1) ≤ η/4^j` (ranges not too far apart) and
`log P_j ≥ (8/j²)·... log Q_{j−1} + 16 log j` (not too close).

**Their frequency partition** (§8, eq. (20)–(21)).  With
`H_j := P_j^{1/6−η}/(log Q₁)^{1/3}`, `α_j := 1/4 − η(1 + 2^{−j})`, and

```text
   Q_{v,H_j}(s) := ∑_{P_j ≤ q ≤ Q_j, e^{v/H_j} ≤ q ≤ e^{(v+1)/H_j}} f(q)/q^s ,
   I_j          := { v : ⌊H_j log P_j⌋ ≤ v ≤ H_j log Q_j } ,
```

they set `[T₀,T] = T₁ ∪ … ∪ T_J ∪ U`, `T₀ = (log X)^{1/15}`, where **`t ∈ T_j` iff `j` is the
smallest index with `|Q_{v,H_j}(1+it)| ≤ e^{−α_j v/H_j}` for every `v ∈ I_j`**, and `t ∈ U` if no `j`
works.  The exponent `α_j ≈ 1/4` makes this a *power* saving `|Q_v| ≤ q^{−1/4+}` on a narrow
multiplicative interval of width `e^{1/H_j}` — nothing like a zero-free-region bound.

**Their main estimate** (§8):

```text
   ∫_{(log X)^{1/15}}^{T} |F(1+it)|² dt
      ≪ ( T/(X/Q₁) + 1 )·( (log Q₁)^{1/3}/P₁^{1/6−η}  +  (log X)^{−1/50} ) ,
```

against the mean-value-theorem "trivial bound" `T/X + 1`.  The two summands are exactly the two
halves of the argument: `T₁ ∪ … ∪ T_J` gives `(log Q₁)^{1/3}/P₁^{1/6−η}`, and `U` gives
`(log X)^{−1/50}`.

**The three devices the Milestone-B architecture does not have.**

1. *The saving on `T_j` is free.*  Ramaré at range `j` turns `F` into `∑_v Q_{v,H_j}·R_{v,H_j}`, and
   `|Q_{v,H_j}| ≤ e^{−α_j v/H_j}` **by the definition of `T_j`**, leaving only a mean value theorem
   for `R_{v,H_j}`:
   `E_j ≪ H_j log Q_j ∑_{v∈I_j} e^{−2α_j v/H_j} ∫_{T_j}|R_{v,H_j}(1+it)|²dt`.

2. *The `ℓ`-th power lengthening.*  For `j > 1` the cofactor `R_{v,H_j}` (length `Xe^{−v/H_j}`) is too
   short against the integration length `X/h`.  Minimality of `j` says some narrow polynomial at
   range `j−1` is **large**, `≥ V`; multiplying `R` by `(that polynomial)^ℓ/V^ℓ` lengthens it to `≈ X/h`
   at no cost.  Conditions (2) and (3) on `[P_j,Q_j]` are exactly what makes some `ℓ` land on `X/h`
   without the moment of the `ℓ`-th power growing.

3. *`U` is handled by Halász, not by a zero-free region.*  `|U| = O(T^{1/2−ε})`, so the integral is a
   sum over `O(T^{1/2−ε})` well-spaced points; Halász's large-value estimate handles `|M(1+it)|²`,
   Halász's theorem on multiplicative functions gives `|M(1+it)| ≪ (log X)^{−δ}` (this is where
   `f` real / `μ` not pretentious enters), and a **Halász-type large-value estimate for
   prime-supported coefficients** recovers the last logarithm.

**Consequence for the five cards.**  The gate is `AveragedMeanSquare`, a bare `o(1)`, and MR's
Proposition gives `(log X)^{−1/50}` — far more than enough — for `h = exp((log X)^β)` with **any**
`β > 0`, indeed for any `h → ∞`.  So the route to `1/2 < β < 1` is Milestone C, not Milestone B.

**Everything Milestone B built survives and is needed**: the Ramaré block splits, the two ladder
defects, the mean value theorems at general coefficient bounds, the exceptional-measure and
Halász–Montgomery layers, the Gallagher/Plancherel reduction, the fibre transfer, the budget rows.
What changes is the *selection rule*: a single `(P,Q)` pair with a proved pointwise bound is replaced
by an iterated family `[P_j,Q_j]` with the pointwise bound as the defining property of `T_j`.

**Next concrete steps.**
1. Port MR's Parseval bound (their Lemma 14) into the corpus's fibre normalisation, or check that
   `Sieve/LogWindowPlancherel` + `Sieve/GallagherDyadicTail` already deliver
   `∫_{T₀}^{X/h}|A(1+it)|² + max_{T≥X/h}(X/(hT))∫_T^{2T}|A|²`.
2. Build the iterated range family `[P_j,Q_j]` and the set `S`, with the sieve bound for its
   complement (`Sieve/RoughPairSieve`, `Sieve/HarmanMinorant` are already in the tree).
3. Build `T_j`, `U`, and the measure bound `|U| ≪ T^{1/2−ε}`.
4. `j = 1` first: with `J = 1` the whole `T_j` half is one Ramaré split plus one mean value theorem,
   and MR note that for `h = X^ε` and `f = μ` even `U` needs no work.  That is the smallest complete
   instance of the architecture and the right first Lean target.

### Milestone C — the exact lemma list, and why `κ = 9/10` is enough for it (2026-08-19)

Reading §3 and §8.3 of arXiv:1501.04585 removes the two things that were still unclear.

**(i) The `U` half uses a SECOND, much LARGER prime range.**  §8.3 applies the Ramaré/Buchstab split
a second time, with

```text
   P = exp((log X)^{1−1/48}),   Q = exp(log X/log log X),   H = (log X)^{1/48} ,
```

i.e. primes of size `exp((log X)^{1−1/48})`, **far above `h`**.  This is legitimate on `U` because
there the estimate is not `V²·∫|cofactor|²` (a mean value theorem, which is what forced
`log P ≤ (log x)^β` in the Milestone-B no-go) but a sum of *pointwise* bounds over well-spaced
points.  With `log P ≈ (log X)^{1−1/48}` the moment method's exponent is
`k ≈ log T/log P ≈ (log X)^{1/48}`, and the resulting large-value count is
`|T_L| ≪ exp((log X)^{1/48+o(1)})` — a genuinely small set.  **This is exactly the step the
Milestone-B architecture has no analogue of, and it is what defeats the `β > κ` barrier.**

**(ii) The pretentious input is Granville–Soundararajan's Lemma 2, and it needs the zero-free region
only qualitatively.**  For real-valued multiplicative `f : ℕ → [−1,1]`, any fixed `A`, and
`1 ≤ |α| ≤ x^A`,

```text
   D(f, p^{iα}; x) ≥ (1/(2√3) − ε)·√(log log x) + O(1) ,
```

proved by `2D(f,p^{iα}) ≥ D(1,p^{2iα})` and then discarding all primes below
`exp((log x)^{2/3+ε})`: on the *remaining* range `∑1/p = (1/3 − ε)log log x + O(1)`, while
`∑_{y<p≤x}p^{−1−2iα} = O(1)` by the zero-free region.  **Only the second fact uses the zero-free
region, and only qualitatively.**  With the corpus's exponent `κ = 9/10` the cutoff becomes
`exp((log x)^{9/10+ε})` and the surviving harmonic mass is `(1/10 − ε)log log x`, so

```text
   D(f, p^{iα}; x)² ≥ (1/40 − ε)·log log x + O(1)
```

— a worse constant, the same theorem.  **So `κ = 9/10` is enough for Milestone C.**  The corpus's
`RHTower/MoebiusPretentiousGap.exists_primeCosPlusSum_ge_logLog` (`D² ≥ log log x − 11 log log|τ| − C`)
is the wrong shape and must be replaced by the Granville–Soundararajan form, which is uniform up to
`|α| ≤ x^A`.

**The lemma list, with corpus status.**

| MR | statement | corpus |
|-|-|-|
| Lemma 1 | Halász: `|F(σ+it)| ≪ x^{1−σ}(M e^{−M} + 1/T₀ + log log x/log x)`, `M = min_{|t₀|≤T₀}D(f,p^{it+it₀};x)²` | `Sieve/Halasz{GhsMasterBound,PerronAssembly,GlobalIntegralBound,…}` — audit |
| Lemma 2 | the Granville–Soundararajan distance bound above | **to build** (κ = 9/10 version) |
| Lemma 3 | Halász for the Buchstab cofactor `R(s) = ∑ f(n)n^{−s}/(#{p∈[P,Q]:p|n}+1)`: `|R(1+it)| ≪ (log Q/log P)(…) ≪ (log X)^{−1/16+o(1)}` for `t ∈ [(log X)^{1/16}, X^A]` | **to build** (Lemma 1 + Lemma 2 + Lemma 5) |
| Lemma 5 | comparison of the non-multiplicative `1/(ω+1)` weight to a completely multiplicative `g` | **to build** |
| Lemma 8 | large-value count for a prime polynomial (moment method) | `Sieve/PrimePowerSupport.volume_largeValues_pow_symm_le_of_prime_support`, `Sieve/Section4ExceptionalMeasure` |
| Lemma 9 | mean value over well-spaced points: `∑_{t∈T}|R|² ≪ (N + |T|√T log 2T)∑|a_n|²` | `Sieve/HalaszMontgomeryIntegral`, `Sieve/DyadicSecondEnvelopeClosed` |
| Lemma 11 | Halász-type large values for **prime-supported** coefficients | `Sieve/HalaszPrimeSavingBound` — audit |
| Lemma 12 | Ramaré/Buchstab split + Cauchy–Schwarz over narrow blocks | `Sieve/{RamareBlockSplit, LadderHarmonicSplit, LadderProductDefect, Section4QSide}` ✓ |
| Parseval | Lemma 14 | `Sieve/{LogWindowPlancherel, GallagherDyadicTail}` ✓ (different normalisation) |

**The single most important structural point for the Lean build.**  The corpus's
`Sieve/Section4QSide.setIntegral_normSq_omegaWeighted_le_blocks` takes the per-block pointwise bound
`hVk : ∀ k, ∀ w ∈ E, ‖primeBlockPoly (geomBlock …) w‖ ≤ Vk k` **as a hypothesis over an arbitrary
measurable set `E`**.  Instantiating `E := T₁` — the set on which every narrow block is small —
discharges `hVk` by `Set.mem_setOf` alone.  Nothing about Route-T, zero-free regions, or `ρ` is
needed on `T₁`; the whole analytic burden moves to `U`, where the tools are Lemmas 1–3, 8, 9, 11.

### Milestone C, brick 59 — the whole `U` half reduces to ONE missing constant (2026-08-19)

Tracing MR's Lemma 2 through the corpus's actual assets pins the gap to a single exponent.

**What Lemma 2 needs.**  For `f = μ` directly (no need for the `2D(f) ≥ D(1,·)` step, since every
term of `∑_p(1 + cos(α log p))/p` is nonnegative):

```text
   D(μ, p^{iα}; z)²  =  ∑_{p ≤ z} (1 + cos(α log p))/p  ≥  log log z  +  ∑_{p ≤ z} cos(α log p)/p ,
```

so everything is a lower bound for the oscillating prime sum, uniformly for `1 ≤ |α| ≤ z^A`.  There
are exactly two ways to get one, and the corpus owns both — with a gap between them.

**Route (a), the one-line `ζ` lower bound.**
`RHTower/ZetaOneLineLogPowerLowerBound.exists_lower_bound_riemannZeta_near_one_line`:

```text
   ‖ζ(σ+it)‖ ≥ c/(log|t|)^{11}   for 1 ≤ σ ≤ 5/4, |t| ≥ t₀   — no condition on σ beyond the box,
```

which through `Sieve/ZetaStripPrimeSum.le_tsum_re_prime_cpow_of_log_le` and
`Sieve/PrimeCosineSum.sum_cos_div_prime_ge_of_le` gives, at `σ = 1 + 1/log z`,

```text
   ∑_{p ≤ z} cos(α log p)/p  ≥  −11·log log|α| − C     (no constraint linking z and α),
```

hence `D² ≥ log log z − θ·log log|α| − C` with **`θ = 11`**.  Useful exactly for
`log|α| ≤ (log z)^{(1−c)/θ}`.  (`Sieve/ZetaStripPrimeSum.le_tsum_re_prime_cpow_strip` is the same
with `θ = 7` but only on the strip `|σ−1| ≤ A/(log|t|)^9`, i.e. `log|α| ≤ (A log z)^{1/9}`.)

**Route (b), the Granville–Soundararajan tail.**  Drop all primes below `y = exp((log z)^{1−ε})`;
the surviving mass is `ε·log log z`, and the surviving oscillation `∑_{y<p≤z}p^{−1−iα}` is `O(1)` by
the twisted Chebyshev bound `Sieve/VonMangoldtTwistUniformHeight` + dyadic Abel summation.  That
bound's *truncation* term is `C·(3b)^{1+2w/3}·polylog/(1+|τ|)` with `w ≍ (log|τ|)^{−κ}`, `κ = 9/10`,
so it beats `b/(log b)²` exactly when

```text
   log b  ≲  (log|τ|)^{1+κ}       ⟺       log|α|  ≳  (log z)^{1/(1+κ)} = (log z)^{0.5263…} .
```

**The gap, and its exact size.**  Route (a) covers `log|α| ≤ (log z)^{1/θ}`, route (b) covers
`log|α| ≥ (log z)^{1/(1+κ)}`.  They meet iff

```text
        θ  <  1 + κ  =  1.9 .
```

The corpus has `θ = 11` (and `θ = 7` is the best the elementary route can give: optimising the
three-four-one/derivative slide `|ζ(σ+it)| ≥ c·δ^{3/4}L^{−1/4} − 110·δ·L²` over `δ` yields
`δ ≍ L^{−9}` and hence `L^{−7}`, not `L^{−11}`).  The classical Titchmarsh 3.11 bound
`1/ζ(1+it) = O(log t)` is `θ = 1`, and it needs the *logarithmic derivative* on a zero-free region
rather than the derivative on the closed half-plane:

```text
   log ζ(1+it) − log ζ(σ₀+it) = ∫_1^{σ₀} (ζ'/ζ)(σ+it)dσ = O(1)   for σ₀ = 1 + c/log|t| ,
   |ζ(σ₀+it)| ≥ ζ(σ₀)^{−3/4}|ζ(σ₀+2it)|^{−1/4} ≫ (σ₀−1)^{3/4}(log|t|)^{−1/4} ≍ 1/log|t| .
```

**So the entire `U` half of Milestone C — and with it MR's Lemma 2, Lemma 3, and the Halász input —
hangs on improving one corpus constant from `θ = 11` to any `θ < 1.9`.**  The corpus already owns
every ingredient of the `θ = 1` argument: `RHTower/ZetaLogDeriv{Bound,Regular,RegUniform,Wide,
WidthBound}` for `ζ'/ζ = O(log|t|)` on the zero-free region, `RHTower/ZetaThreeFourOne` for the
three-four-one inequality, and `RHTower/ZetaDerivNearOneLineBound`.

**This is the next brick**: `‖ζ(σ+it)‖ ≥ c/log|t|` for `1 ≤ σ ≤ 5/4`, `|t| ≥ t₀`.

### Milestone C, brick 60 — the gap is CLOSED: the quarter-loss distance bound (2026-08-19)

`Sieve/PrimeCosineSumSharp` (axiom-clean, sorry-free, wired).  Brick 59 asked for the one-line `ζ`
lower-bound exponent `θ < 1 + κ = 1.9`; the answer is that **`θ` is not the right parameter** — one
should not slide to `σ = 1` at all.  Applying the three-four-one inequality *at the standard
abscissa* `σ = 1 + 1/log z`, which is exactly where the prime-sum bridge already evaluates, gives

```text
   1 ≤ ‖ζ(1+x)‖³·‖ζ(1+x+it)‖⁴·‖ζ(1+x+2it)‖ ≤ (1/x + 2)³ · ‖ζ(1+x+it)‖⁴ · (log(2|t|) + 5) ,
```

so with `x = 1/log z`

```text
   log ‖ζ(1+x+it)‖  ≥  −(3/4)·log(log z + 2)  −  (1/4)·log(log 2|t| + 5) .
```

The three inputs are all corpus theorems: `Sieve/ZetaThreeFourOne.norm_zeta_product_ge_one`,
`Sieve/ZetaThreeFourOne.abs_riemannZeta_one_add_le` (`‖ζ(1+x)‖ ≤ 1/x + 2`), and
`RHTower/ZetaVerticalLineBound.norm_riemannZeta_le_log_add` (`‖ζ(s)‖ ≤ log|Im s| + 5`).

| new theorem | statement |
|-|-|
| `log_norm_riemannZeta_ge_three_four_one` | `−(3/4)log(1/x+2) − (1/4)log(log 2\|t\|+5) ≤ log‖ζ((1+x)+it)‖`, for `0 < x ≤ 1`, `\|t\| ≥ 2` |
| `exists_sum_cos_div_prime_ge_sharp` | `∑_{p≤z} cos(t log p)/p ≥ −(3/4)log(log z+2) − (1/4)log(log 2\|t\|+5) − C` |
| **`exists_mulDistSqPair_ge_quarter`** | `D(f, χ_t; p ≤ z)² ≥ (1/4)·log log z − (1/4)·log log\|t\| − C` for every `f` with `f(p) = −1`, **with no condition linking `z` and `t`** |

**This strictly supersedes the corpus's two existing pretentious bounds**:
`Sieve/MoebiusUniformFrequency.exists_mulDistSqPair_ge_uniform` loses `7 log log T` and requires
`log z ≥ (log T)^9/A`; `RHTower/MoebiusPretentiousGap.exists_primeCosPlusSum_ge_logLog` loses
`11 log log|τ|`.  The new bound loses `(1/4)·log log|t|` and requires nothing.

**Consequence for the range of frequencies.**  `D² ≥ (1/4)(log log z − log log|t|) − C` is a positive
proportion of `log log z` for every `|t| ≤ exp((log z)^{1−c})`, and the Granville–Soundararajan tail
route covers `log|t| ≥ (log z)^{1/(1+κ)} = (log z)^{0.5263…}`.  Taking `c = 0.4`, the two ranges
overlap: **MR's Lemma 2 for `μ` now holds for the full range `1 ≤ |t| ≤ z^A`**, at `κ = 9/10`, with
no gap.  In fact route (a) alone covers everything except `log|t| ≥ (log z)^{1−c}`, and for those
frequencies route (b) applies with room to spare.

Remaining for MR Lemma 2 as a single statement: the tail route (b) in Lean — dyadic Abel summation
of `Sieve/PrimeBlockTwistBound.exists_norm_primeBlockPoly_routeT_le` over `(exp((log z)^{1−ε}), z]`.

### Milestone C, brick 61 — the Granville–Soundararajan transfer (2026-08-19)

`Sieve/PrimeCosineTailAbel` (axiom-clean, sorry-free, wired).  Route (b) of brick 59 needs one Abel
summation, not a dyadic decomposition: a *uniform linear* bound on the twisted prime partial sums
transfers to the reciprocal-weighted cosine sum at the cost of one logarithm.

| theorem | statement |
|-|-|
| `abs_sum_div_le_of_partial_bound` | for `a` with `a 0 = 0`: `∀ i ≤ z, \|∑_{j≤i} a_j\| ≤ ρ·i` ⟹ `\|∑_{i≤z} a_i/i\| ≤ ρ·(2 + log z)` |
| `primeCosTail`, `sum_range_primeCosTail`, `sum_Icc_primeCosTail_div` | the tail weight and its two sums |
| `abs_sum_cos_div_primesRange_le` | the same for `∑_{y<p≤z} cos(t log p)/p` |
| `sum_cos_eq_neg_re_primeBlockPoly` | `∑_{p∈B} cos(t log p) = −Re primeBlockPoly B (t/2π)` |
| **`abs_sum_cos_div_primesRange_le_of_norm`** | `(∀ i ≤ z, ‖primeBlockPoly (primesRange y i) (t/2π)‖ ≤ ρ·i) ⟹ \|∑_{y<p≤z} cos(t log p)/p\| ≤ ρ(2 + log z)` |

Built on `RHTower/MertensFirst.Mertens.abel_tail_identity` (`∑_{i≤N}a_i/i = A(N)/N +
∑_{i<N}A(i)/(i(i+1))`) and `Sieve/PerronNearDiagonal.sum_inv_comp_le_one_add_log`.

**The numerology this now has to be fed.**  Route (b) is used with `y = ⌈exp((log z)^{1−ε})⌉`,
`ε < 1 − κ = 1/10`; the surviving harmonic mass is `ε·log log z`, and `ρ` must beat `1/log z`.
`Sieve/PrimeBlockTwistBound.exists_norm_primeBlockPoly_routeT_le` supplies

```text
   ‖primeBlockPoly (primesRange y i) w‖
     ≤ (E(i) + 7e⁹)(1/log 2 + 1/log(i+1)) + (E(y) + 7e⁹)(1/log 2 + 1/log(y+1)) ,
   E(x) = routeTTwistEnvelope A delta C (−2πw) x ,
```

whose two regimes give, with `τ = −t` and `wτ = routeTUniformRegWidth A delta (3|τ|/2) ≍ (log|τ|)^{−κ}`,

| term | value at `i ∈ (y,z]` | requirement | holds when |
|-|-|-|-|
| contour | `3·exp(−(wτ/6)·log 3i)·(HF + log 2i)` | `≤ ρ/(9C)` | `(wτ/6)·log y → ∞`, i.e. `log\|t\| ≤ (log y)^{1/κ}` |
| truncation | `3·(3i)^{2wτ/3}·(1+(log i)²+HF)/(1+\|τ\|)` | `≤ ρ/(9C)` | `log z ≲ (log\|t\|)^{1+κ}` |
| Chebyshev | `2 log i/√i` | `≤ ρ/3` | always, `i ≥ y` is stretched-exponential |

At `y = exp((log z)^{0.99})`, `κ = 9/10`, both hold for `log|t| ≥ (log z)^{0.6}`: the contour term is
`exp(−c(log z)^{0.99−0.54})` and the truncation term needs `(log z)^{0.46} ≲ (log z)^{0.6}`.

**Coverage is now complete.**  Route (a) (`Sieve/PrimeCosineSumSharp.exists_mulDistSqPair_ge_quarter`)
gives `D² ≥ 0.05·log log z` for `log|t| ≤ (log z)^{0.8}`; route (b) gives `D² ≥ 0.01·log log z` for
`log|t| ≥ (log z)^{0.6}`.  The two overlap, so **MR's Lemma 2 for `μ` holds on the whole range
`1 ≤ |t| ≤ z^A` at `κ = 9/10`.**  What remains for it is the third column of the table above — the
explicit envelope estimates — which is arithmetic on `routeTTwistEnvelope`, no new analytic input.

### Per-card audit of the five stage-2 targets — every one funnels into two named theorems (2026-08-19)

Read against the tree (not against the card headers, several of which are stale).

| card | what is Lean-proved | what is missing |
|-|-|-|
| `route-e-cofactor-amplified-e3-token-supply` | the whole elementary layer: parity reversal `(4)`, the `s↔2s` cofactor pairing and `half_sum_oddBase_le_sum_parityClass` (the structural half of `(7)`/`(9)`), the dyadic slice count `(6a)`, the amplified displacement `(5)` | the **Matomäki–Teräväinen all-interval `E₃` minorant** `(6)`; the classical unsigned squarefree harmonic estimates `∑ t^{-1/2} ≍ √T`, `∑ 1/t ≍ log T` over band-avoiding squarefree `t` |
| `route-e-forbidden-support-e3-stability` | the whole perturbative layer `(FS5)`, `(FS6)`, `(FS10)`–`(FS12)` | the **Matomäki–Teräväinen all-interval `E₃` theorem** it perturbs |
| `route-e-coprime-square-root-mobius-product-sign-law` | `(3)` and its consequence at `h = exp((log x)^{99/100})` (promoted as a stage-3 child); the whole reduction chain; the two-variable squarefree sieve; all three density inputs | the card's own range `h/log log 3x → ∞`, i.e. **Matomäki–Radziwiłł for arbitrarily slowly growing `h`**.  Its recorded Brun–Titchmarsh gate was *answered* on 2026-08-19: the Cauchy–Schwarz route provably loses a factor ≈150 and the bounded-multiplicity marker family supersedes it — which is the sibling Hall-law card, proved for `9/10 < β < 1` |
| `route-e-growing-reciprocal-marker-low-breadth-transport` | as the Hall-law card | same as the Hall-law card |
| `route-e-reciprocal-marker-mobius-hall-law` | **`route_e_marker_hall_law` — the card's `(3)`, unconditional, axiom-clean, both signs, every constant `C`** — for `9/10 < β' < 1` | the card states `1/2 < β < 1`; the exponent is inherited from `Sieve/ScaledBudgetLimit.averagedMeanSquare_moebius_scaledLength` |

**So the five cards sit on exactly two published theorems**:

* **MR** (arXiv:1501.04585) — cards 3, 4, 5.  Card 5 needs only the exponent range widened; card 3
  needs the full `h → ∞` theorem.  This is Milestone C.
* **MT all-interval `E₃`** — cards 1, 2.  Tracked at `mt-e3-programme`; the one remaining automorphic
  input is Watt / Deshouillers–Iwaniec.

Nothing else is missing on any of the five.  Milestone C therefore serves three of the five and is
the correct critical path; the elementary squarefree estimates of card 1 `(7)`/`(9)` are the only
piece of card work that is independent of both deep theorems.

**And Milestone B's no-go is exactly the statement that card 5's `9/10` cannot be lowered by any
zero-free-region argument** — which is why the frequency-partition architecture of Milestone C, and
not more tuning of the joint arrangement, is the whole remaining content of cards 3, 4 and 5.

### Milestone C, brick 62 — route (b) is arithmetic-free (2026-08-19)

`Sieve/PrimeRangeTwistTail` (axiom-clean, sorry-free, wired).

| theorem | statement |
|-|-|
| `inv_log_two_add_inv_log_succ_le_three` | `1/log 2 + 1/log(n+1) ≤ 3` for `n ≥ 1` (from `Real.log_two_gt_d9`) |
| `exists_norm_primeBlockPoly_primesRange_le` | `‖primeBlockPoly (primesRange y i) (t/2π)‖ ≤ 3·(E(i) + E(y) + 14e⁹)`, `E = routeTTwistEnvelope A delta C (−t)` |
| **`exists_abs_sum_cos_div_primesRange_le_routeT`** | the Granville–Soundararajan tail, with the *only* remaining hypothesis a size comparison: `∀ i ∈ [y,z], 3(E(i)+E(y)+14e⁹) ≤ ρ·i  ⟹  \|∑_{y<p≤z} cos(t log p)/p\| ≤ ρ(2+log z)` |

The empty case `i < y` is discharged inside (`primesRange y i = ∅`), so the hypothesis is needed only
on `[y, z]`.

**What is left of route (b)** is exactly the third column of brick 61's table, now as one inequality
between named quantities.  Working from the *definition* of `routeTTwistEnvelope` (not from
`routeTTwistEnvelope_le_exp`, whose crude `(3x)^{delta/3}` is too lossy), the second regime's exponent
is `1 + 2·routeTUniformRegWidth A delta (3|τ|/2)/3` with
`routeTUniformRegWidth A delta K = min delta (routeTZeroFreeWidth A (K+1))/2`, so the truncation term
is `exp((W/3)·log 3x)·polylog/(1+|τ|)` with `W ≍ (log|τ|)^{−κ}` — which is what turns the requirement
into `log z ≲ (log|t|)^{1+κ}` rather than `|t| ≥ z^{delta}`.

### Milestone C, brick 63 — the Route-T width from ABOVE (2026-08-19)

`Sieve/RouteTWidthUpper` (axiom-clean, sorry-free, wired).  The corpus owned the zero-free width only
from *below* (`Sieve/RouteTWidthExplicit.routeTWidthPolylogLower`), because the contour saving
`x^{−w/3}` of `routeTTwistEnvelope` improves as `w` grows.  Its Perron truncation term carries
`x^{+2w/3}` and needs the opposite inequality — and without it route (b) is only usable for
`|t| ≥ z^{1/180}`, which route (a) cannot reach.

The width is entirely explicit once unfolded, so the bound is a lower bound for the band shell:

```text
   routeTStripWidth V = 1/(D·(V+1)^9) ,   V = routeTBandShell t = ⌊¹⁰√(clog₂⌈t⌉)⌋ + 2 ,
   n := clog₂⌈t⌉  <  (⌊¹⁰√n⌋+1)^10 ≤ (V+1)^10   (Nat.lt_pow_nthRoot_add_one)
      ⟹  n^{9/10} ≤ (V+1)^9 ,
   t ≤ 2^n  (Nat.le_pow_clog)  ⟹  log t/log 2 ≤ n .
```

| theorem | statement |
|-|-|
| `rpow_nine_tenths_le_bandShell_pow` | `(n:ℝ)^{9/10} ≤ (⌊¹⁰√n⌋+3)^9` |
| `log_div_log_two_le_binaryHeight` | `log t/log 2 ≤ routeTBinaryHeight t` for `t ≥ 1` |
| `routeTStripWidth_bandShell_le` | `routeTStripWidth (routeTBandShell t) ≤ 1/(D·(log t/log 2)^{9/10})`, `t ≥ 2` |
| `routeTLandauRadius_le` | `≤ 1/(2D·(log γ/log 2)^{9/10})`, `γ ≥ 2` |
| `routeTZeroFreeWidth_le_polylog` | `≤ 1/(2D·10⁵·10001²·(log γ/log 2)^{9/10})` (uses `routeTZeroFreeBudget ≥ 10001`) |
| **`routeTUniformRegWidth_le_polylog`** | `routeTUniformRegWidth A delta (3\|τ\|/2) ≤ 1/(K·(log\|τ\|/log 2)^{9/10})`, `K = routeTWidthUpperConst = 4D·10⁵·10001²`, for `\|τ\| ≥ 2` |

**This is the exponent `κ = 9/10` appearing as an upper bound for the first time in the corpus**, and
it is what makes route (b)'s truncation requirement read `log z ≲ (log|t|)^{1+κ}` — i.e.
`log|t| ≳ (log z)^{0.5263…}` — instead of `|t| ≳ z^{1/180}`.  With route (a) covering
`log|t| ≤ (log z)^{0.8}`, the two now overlap.

Remaining for MR's Lemma 2 as one statement: substitute `routeTUniformRegWidth_le_polylog` and
`routeTWidthPolylogLower` into the two regimes of `routeTTwistEnvelope`, producing the `ρ` that
`Sieve/PrimeRangeTwistTail.exists_abs_sum_cos_div_primesRange_le_routeT` consumes.

### Milestone C, brick 64 — the envelope with both regimes explicit (2026-08-19)

`Sieve/RouteTWidthUpper` extended (axiom-clean, sorry-free, wired).

| theorem | statement |
|-|-|
| `routeTTwistEnvelope_le_two_sided` | given `L ≤ routeTUniformRegWidth A delta (3\|τ\|/2) ≤ U`, the envelope is bounded with `(3x)^{1−L/3}` in the contour regime and `(3x)^{1+2U/3}` in the truncation regime |
| **`routeTTwistEnvelope_le_polylog`** | the instance at `L = min delta (routeTWidthPolylogLower A τ)/2` (corpus, `routeTUniformRegWidth_ge`) and `U = 1/(routeTWidthUpperConst·(log\|τ\|/log 2)^{9/10})` (brick 63), for `16π/3 ≤ \|τ\|` |

The corpus's `routeTTwistEnvelope_le_explicit` bounds *both* regimes at once and replaces the
truncation exponent by the flat `delta/3`; `_le_two_sided` keeps the two regimes independent, which
is what lets the truncation exponent be the polylogarithm rather than a constant.

**Process note.**  The first attempt at `_le_polylog` timed out at 900 s.  The cause was two missing
imports (`RouteTWidthExplicit`, `VonMangoldtTwistPrimeEnvelope`): with `routeTTwistEnvelope` and
`routeTTwistHeightFactor` unresolved, `autoImplicit` turned them into metavariables and `congr`/
`field_simp` searched over them.  With the imports added and the statement written so the exponents
match `_le_two_sided` syntactically (`1 − m/2/3`, `1 + 2·(1/K·…)/3`), the proof is a single `exact`.

### Milestone C, brick 65 — route (b) is now three real inequalities (2026-08-19)

`Sieve/RouteTEnvelopeRho` and `Sieve/RouteTTailRho` (both axiom-clean, sorry-free, wired).

| theorem | statement |
|-|-|
| `routeTTwistEnvelope_le_mul` | splitting the factor `3x` off both regimes: if each of the contour term `9C(3x)^{−m/6}(HF+log 2x)`, the truncation term `9C(3x)^{2U/3}(1+(log x)²+HF)/(1+\|τ\|)` and the Chebyshev term `6 log x/√x` is `≤ ρ`, then `routeTTwistEnvelope A delta C τ x ≤ ρ·x` |
| `exists_abs_sum_cos_div_primesRange_le_of_envelope` | a uniform envelope majorant `E(i) ≤ ρ₀·i` on `[y,z]`, plus `14e⁹ ≤ ρ₀·y`, gives `\|∑_{y<p≤z}cos(t log p)/p\| ≤ 9ρ₀(2+log z)` |
| **`exists_abs_sum_cos_div_primesRange_le_regimes`** | the same with the envelope replaced by its three regimes: three inequalities between explicit real functions of the block top `i` and the frequency `t` |

**Route (b) of MR's Lemma 2 therefore has no arithmetic content left.**  What remains is to verify
the three inequalities at the schedule `y = ⌈exp((log z)^{0.99})⌉`, `ρ₀ = 1/(9(2+log z))`,
`(log z)^{0.6} ≤ log|t| ≤ 2 log z`, where they read

| regime | value at `i ∈ [y,z]` | why it holds |
|-|-|-|
| contour | `exp(−(m/6)·log 3i)·polylog`, `m ≍ (log\|t\|)^{−9/10}(log log\|t\|)^{−2}` | `log i ≥ (log z)^{0.99}` and `log\|t\| ≤ 2 log z` give `exp(−c(log z)^{0.09}/(log log z)²)` |
| truncation | `exp((2/(3K))·(log 3i)·(log 2/log\|t\|)^{9/10})/\|t\|` | `log\|t\| ≥ (log z)^{0.6}` gives `exp((log z)^{0.46} − (log z)^{0.6}) → 0` |
| Chebyshev | `6 log i/√i` | `i ≥ exp((log z)^{0.99})` |

and the harmonic mass that survives the cutoff is `∑_{y<p≤z}1/p = 0.01·log log z + O(1)`.

### Milestone C, brick 66 — the tail regimes in closed form (2026-08-19)

`Sieve/RouteTTailSurrogate` (axiom-clean, sorry-free, wired).  The three regimes of brick 65 still
mentioned two corpus-internal quantities; both are now replaced by closed expressions in `|τ|`.

```text
routeTHeightSurrogate τ            = 2·log(6|τ| + 6) + 1     ( = routeTLogHeightEnvelope(4(3|τ|/2+1)) )
routeTWidthReciprocalSurrogate A τ = 10·D_A·(routeTHeightSurrogate τ)^{9/10}
                                        ·(1 + log routeTHeightSurrogate τ)²
routeTWidthLowSurrogate A τ        = 1 / routeTWidthReciprocalSurrogate A τ
routeTHeightFactorUpper A τ        = 1 + log(3|τ|/2 + 3)·routeTWidthReciprocalSurrogate A τ
```

| theorem | statement |
|-|-|
| `routeTHeightSurrogate_eq` | the surrogate height *is* `routeTLogHeightEnvelope (4(3\|τ\|/2+1))` |
| `routeTWidthLowSurrogate_le` | `routeTWidthLowSurrogate A τ ≤ routeTWidthPolylogLower A τ` (`\|τ\| ≥ 1`) |
| `routeTTwistHeightFactor_le_surrogate` | `routeTTwistHeightFactor A τ ≤ routeTHeightFactorUpper A τ` (`\|τ\| ≥ 16π/3`) |
| **`exists_abs_sum_cos_div_primesRange_le_surrogate`** | the tail bound with all three regimes written in the surrogates alone |

Both substitutions go in the safe direction: a *smaller* width weakens the contour saving, and a
*larger* height factor enlarges both regimes.  Built on the corpus's own
`Sieve/WidthEnvelopeBounds.{routeTWidthPolylogLower_ge, inv_routeTWidthPolylogLower_le}` and
`Sieve/RouteTWidthExplicit.routeTTwistHeightFactor_le_explicit`.

**Route (b) is now a statement about `exp`, `log`, `√` and `rpow` only.**  What is left is the
asymptotic verification at `y = ⌈exp((log z)^{0.99})⌉`, `ρ₀ = 1/(9(2+log z))`,
`(log z)^{0.6} ≤ log|t| ≤ 2 log z` — three limits, no arithmetic geometry.

### Milestone C, brick 67 — the tail regimes at their essential shape (2026-08-19)

`Sieve/RouteTTailElementary` (axiom-clean, sorry-free, wired).  The inner constants and the square
root are removed by four elementary comparisons, leaving exactly the three inequalities the schedule
has to verify:

```text
   contour     :  9C·i^{−m/6}·(HF + 2 log i)               ≤ ρ₀
   truncation  :  9C·3^v·i^v·(1 + (log i)² + HF)/|t|       ≤ ρ₀
   Chebyshev   :  24·i^{−1/4}                               ≤ ρ₀
```

| theorem | statement |
|-|-|
| `log_le_four_mul_rpow_quarter` | `log i ≤ 4·i^{1/4}` (from `Real.log_le_sub_one_of_pos` at `i^{1/4}`) |
| `cheb_regime_le` | `6 log i/√i ≤ 24·i^{−1/4}` |
| `contour_regime_le` | `(3i)^{−a} ≤ i^{−a}` and `log 2i ≤ 2 log i` |
| `trunc_regime_le` | `(3i)^v = 3^v i^v` and `1 + \|t\| ≥ \|t\|` |
| **`exists_abs_sum_cos_div_primesRange_le_elementary`** | the tail bound with only the three displayed inequalities as hypotheses |

**Route (b) of MR's Lemma 2 is now purely a limit computation.**  At
`y = ⌈exp((log z)^{0.99})⌉`, `ρ₀ = 1/(9(2+log z))`, `(log z)^{0.6} ≤ log|t| ≤ 2 log z` the three
read, with `Li = log i ≥ (log z)^{0.99}` and `Lt = log|t|`:

```text
   contour     :  exp(−(m/6)·Li)·polylog ≤ ρ₀ ,   m ≍ Lt^{−9/10}(log Lt)^{−2}
                     ⟹ exp(−c(log z)^{0.09}/(log log z)²)
   truncation  :  exp(v·Li − Lt)·polylog ≤ ρ₀ ,   v ≍ Lt^{−9/10}
                     ⟹ exp((log z)^{0.46} − (log z)^{0.6})
   Chebyshev   :  24·exp(−Li/4) ≤ ρ₀
```

all three of which beat `ρ₀ ≍ 1/log z` with room.

### Milestone C, bricks 68–69 — the tail regimes in `log i` and `log|t|` alone (2026-08-19)

`Sieve/RouteTSurrogateSize` and `Sieve/RouteTTailBudget` (both axiom-clean, sorry-free, wired).

**Brick 68.**  The surrogates of brick 66 are still nested — the height surrogate sits inside a
`9/10` power and inside a logarithm.  Both are majorised by one increasing function of `log|t|`:

```text
   routeTHeightBudget t       = 23 + 2 log|t|                      ( ≥ routeTHeightSurrogate (−t) )
   routeTReciprocalBudget A t = 10 D_A (routeTHeightBudget t)^{9/10}(1 + log routeTHeightBudget t)²
```

| theorem | statement |
|-|-|
| `routeTHeightSurrogate_le` | `2 log(6\|t\|+6)+1 ≤ 23 + 2 log\|t\|`, from `log 12 ≤ 11` |
| `surrogate_shape_mono` | `Z ↦ Z^{9/10}(1+log Z)²` is monotone on `[1,∞)` |
| `routeTWidthLowSurrogate_ge` | `1/routeTReciprocalBudget A t ≤ routeTWidthLowSurrogate A (−t)` |
| `routeTHeightFactorUpper_le` | `≤ 1 + (4 + log\|t\|)·routeTReciprocalBudget A t`, from `log 5 ≤ 4` |

**Brick 69.**  `routeTTruncExponent t := 2/(3·routeTWidthUpperConst·(log\|t\|/log 2)^{9/10})`, and

```text
exists_abs_sum_cos_div_primesRange_le_budget :
  2 ≤ y ≤ z,  16π/3 ≤ |t|,  14e⁹ ≤ ρ₀·y,  and for every i ∈ [y,z]
     contour     :  9C·i^{−min(delta, 1/G)/6}·(1 + (4+log|t|)G + 2 log i)  ≤ ρ₀
     truncation  :  9C·3^v·i^v·(2 + (log i)² + (4+log|t|)G)/|t|            ≤ ρ₀
     Chebyshev   :  24·i^{−1/4}                                            ≤ ρ₀
  ⟹  |∑_{y<p≤z} cos(t log p)/p| ≤ 9ρ₀(2 + log z)
```

with `G = routeTReciprocalBudget A t`, `v = routeTTruncExponent t`.

**Every quantity in the three hypotheses is now an elementary function of `i` and `|t|`** — `rpow`,
`log`, and two named polylogarithmic budgets.  Route (b) of MR's Lemma 2 has no structure left in
it; what remains is to check the three at the schedule
`y = ⌈exp((log z)^{0.99})⌉`, `ρ₀ = 1/(9(2+log z))`, `(log z)^{0.6} ≤ log|t| ≤ 2 log z`.

### Milestone C, brick 70 — the three regimes as logarithmic thresholds (2026-08-19)

`Sieve/RouteTScheduleRegimes` (axiom-clean, sorry-free, wired).  Taking logarithms turns each regime
of brick 69 into a single linear threshold in `log i`:

| theorem | statement |
|-|-|
| `contour_regime_at` | `log(9CPB) ≤ a·log i`  ⟹  `9C·(i^{−a}·P) ≤ ρ₀`, whenever `1/B ≤ ρ₀`, `0 < 9CP`, `0 < B` |
| `trunc_regime_at` | `v·log i + log(9C·3^v·Q·B) ≤ log tt`  ⟹  `9C·(3^v·i^v·Q)/tt ≤ ρ₀` |
| `cheb_regime_at` | `log(24B) ≤ (log i)/4`  ⟹  `24·i^{−1/4} ≤ ρ₀` (the `P = 1`, `a = 1/4` instance of the first) |

The block top now enters **only** through `log i`, and each hypothesis reads "the logarithm of the
prefactor is below the saving".  At the schedule
`ρ₀ = 1/(9(2+log z))`, i.e. `B = 9(2+log z)`, and `log i ≥ (log z)^{0.99}`, the three become

```text
   contour     :  log(9C·(1+(4+log|t|)G+2 log i)·9(2+log z))  ≤  (log i)/(6G)
   truncation  :  v·log i + log(9C·3^v·(2+(log i)²+(4+log|t|)G)·9(2+log z))  ≤  log|t|
   Chebyshev   :  log(216(2+log z))  ≤  (log i)/4
```

with `G = routeTReciprocalBudget A t ≍ (log|t|)^{9/10}(log log|t|)²` and
`v = routeTTruncExponent t ≍ (log|t|)^{−9/10}`.  On the schedule's range
`(log z)^{0.6} ≤ log|t| ≤ 2 log z` the right-hand sides are `≍ (log z)^{0.09}/(log log z)²`,
`≍ (log z)^{0.6}` and `≍ (log z)^{0.99}` while the left-hand sides are `O(log log z)`, `O((log z)^{0.46})`
and `O(log log z)`.  **Three limit statements, no structure.**

### Milestone C, brick 71 — the thresholds at their worst case (2026-08-19)

`Sieve/RouteTScheduleWorstCase` (axiom-clean, sorry-free, wired).  Each threshold of brick 70 is
monotone in the block top `Li = log i` and in the frequency `Lt = log|t|`, so on the schedule's
ranges it need only be checked once, with the prefactor at the largest admissible data and the
saving at the smallest.

| theorem | reduction |
|-|-|
| `contour_threshold_worst` | from `log(9C(1+(4+2Lz)Ĝ+2Lz)·9(2+Lz)) ≤ min(delta,1/Ĝ)/6 · Lz^{0.99}` to the same at `(Li, Lt, G)` with `Lz^{0.99} ≤ Li ≤ Lz`, `0 ≤ Lt ≤ 2Lz`, `G ≤ Ĝ` |
| `trunc_threshold_worst` | from `v̂·Lz + log(9C·3^{v̂}(2+Lz²+(4+2Lz)Ĝ)·9(2+Lz)) ≤ Lz^{0.6}` to the same at `(Li, Lt, G, v)` with additionally `v ≤ v̂` and `Lz^{0.6} ≤ Lt` |

Both are pure monotonicity — `1/G ≥ 1/Ĝ` for the saving, `Real.log_le_log` for the prefactor, and
`Real.rpow_le_rpow_of_exponent_le` for `3^v`.  The Chebyshev threshold needs no reduction: it already
mentions only `Lz` and `Li`.

**What is left of route (b)** is three limits in `Lz` alone:

```text
   log(9C(1+(4+2Lz)Ĝ+2Lz)·9(2+Lz))                    ≤ min(delta,1/Ĝ)/6 · Lz^{0.99}
   v̂·Lz + log(9C·3^{v̂}(2+Lz²+(4+2Lz)Ĝ)·9(2+Lz))       ≤ Lz^{0.6}
   log(216(2+Lz))                                      ≤ Lz^{0.99}/4
```

with `Ĝ ≍ Lz^{0.9}(log Lz)²` and `v̂ ≍ Lz^{−0.54}`, i.e. left sides `O(log Lz)`, `O(Lz^{0.46})`,
`O(log Lz)` against right sides `≍ Lz^{0.09}/(log Lz)²`, `Lz^{0.6}`, `Lz^{0.99}/4`.

### Milestone C, brick 72 — one lemma discharges all three thresholds (2026-08-19)

`Sieve/PolylogRpowDomination` (axiom-clean, sorry-free, wired).  All three schedule thresholds of
brick 71 have the same shape after the prefactors are expanded, so a single lemma covers them:

```text
eventually_const_mul_rpow_polylog_le_rpow (k : ℕ) (hαβ : α < β) :
    ∀ᶠ L in atTop,  C · L^α · (1 + |log L|)^k  ≤  L^β
```

proved by splitting `L^β = L^α·L^{(β−α)/2}·L^{(β−α)/2}` and spending the two halves on the constant
(`tendsto_rpow_atTop`) and on the polylogarithm — the latter through the corpus's own
`HTGeometry.eventually_one_add_abs_log_pow_le_rpow`, found with `formal_tools.py research` rather
than rebuilt.

The first instance is complete:

```text
eventually_cheb_threshold :  ∀ᶠ L in atTop,  log(216(2 + L))  ≤  L^{0.99}/4
```

using `2 + L ≤ 3L`, `log 216 ≤ 216`, `log 3 ≤ 3` and the lemma at `α = 0`, `β = 0.99`, `k = 1`,
`C = 872`.  The threshold `L ≥ e` is needed because at `L` near `1` the polylogarithm has no room.

Remaining: the contour and truncation instances, which need only the algebraic majorants
`Ĝ ≤ C₁·L^{0.9}(1+|log L|)²` and `v̂ ≤ C₂·L^{−0.54}` before the same lemma applies at
`(α,β) = (0.9, 0.99)` and `(0.46, 0.6)`.

### Milestone C, brick 73 — the worst-case data of the schedule (2026-08-19)

`Sieve/RouteTScheduleHats` (axiom-clean, sorry-free, wired).  Brick 71 asks for an upper bound `Ĝ`
for the reciprocal-width budget and `v̂` for the truncation exponent over the schedule's frequency
range `(log z)^{0.6} ≤ log|t| ≤ 2 log z`.  Both, and their sizes:

```text
routeTBudgetHat A L = 10·D_A·(23 + 4L)^{9/10}·(1 + log(23 + 4L))²
routeTTruncHat L    = 2 / (3·routeTWidthUpperConst·(L^{0.6}/log 2)^{9/10})
```

| theorem | statement |
|-|-|
| `routeTReciprocalBudget_le_hat` | `log\|t\| ≤ 2L`  ⟹  `routeTReciprocalBudget A t ≤ routeTBudgetHat A L` |
| `routeTTruncExponent_le_hat` | `L^{0.6} ≤ log\|t\|`  ⟹  `routeTTruncExponent t ≤ routeTTruncHat L` |
| **`routeTBudgetHat_le_polylog`** | `≤ 211680·D_A·L^{0.9}·(1 + \|log L\|)²`, from `23+4L ≤ 27L`, `27^{9/10} ≤ 27`, `log 27 ≤ 27` |
| **`routeTTruncHat_le`** | `≤ (2/(3·routeTWidthUpperConst))·L^{−0.54}`, from `(L^{0.6})^{9/10} = L^{0.54}` and `log 2 ≤ 1` |

Both sizes are exactly what `Sieve/PolylogRpowDomination.eventually_const_mul_rpow_polylog_le_rpow`
consumes: the contour threshold becomes an instance at `(α,β) = (0.9, 0.99)`, `k = 3`, and the
truncation threshold two instances at `(0.46, 0.53)` and `(0, 0.05)`.

### Milestone C, brick 74 — polynomial majorants for the two prefactors (2026-08-19)

`Sieve/RouteTPolyMajorants` (axiom-clean, sorry-free, wired).  With the reciprocal-width budget
replaced by its size `G ≤ G₁·L^{0.9}(1+log L)²` (brick 73), both threshold prefactors become a
constant times a power of `L` times `(1 + log L)²`:

| theorem | statement |
|-|-|
| `contour_bracket_le` | `1 + (4+2L)G + 2L ≤ (3+6G₁)·L^{1.9}(1+log L)²` |
| **`contour_prefactor_le`** | `9C(1+(4+2L)G+2L)·9(2+L) ≤ 243C(3+6G₁)·L^{2.9}(1+log L)²` |
| `trunc_bracket_le` | `2 + L² + (4+2L)G ≤ (3+6G₁)·L²(1+log L)²` |
| **`trunc_prefactor_le`** | `9C·3^v(2+L²+(4+2L)G)·9(2+L) ≤ 729C(3+6G₁)·L³(1+log L)²`, for `3^v ≤ 3` |

plus the three rpow utilities `one_le_one_add_log_sq`, `rpow_le_rpow_exp`, `self_le_rpow`.  The
exponent bookkeeping is `L^{1.9}·L = L^{2.9}` and `L²·L = L³`, both from `Real.rpow_add`.

**Process note.**  A first draft of this brick got the contour exponent wrong (`L^{2.9}` in the
bracket instead of `L^{1.9}`, giving `L^{3.9}` after the outer factor) and was written out with two
`sorry` placeholders while the algebra was being checked.  It was deleted before any build; the
version above is the corrected one and the tree has never contained a `sorry`.

### Milestone C, brick 75 — ALL THREE THRESHOLDS ARE PROVED (2026-08-19)

`Sieve/RouteTThresholdLimits` (axiom-clean, sorry-free, wired).  The two remaining schedule
thresholds are now unconditional eventual statements in `L = log z`:

```text
eventually_contour_threshold (hC : 0 < C) :
  ∀ᶠ L in atTop,
    log(9C(1 + (4+2L)·Ĝ + 2L)·9(2+L)) · (6·Ĝ)  ≤  L^{0.99}

eventually_trunc_threshold (hC : 0 < C) :
  ∀ᶠ L in atTop,
    v̂·L + log(9C·3^{v̂}(2 + L² + (4+2L)·Ĝ)·9(2+L))  ≤  L^{0.6}
```

with `Ĝ = routeTBudgetHat A L`, `v̂ = routeTTruncHat L`.  Together with `eventually_cheb_threshold`
(brick 72) **all three thresholds of the schedule are proved.**

The new auxiliary is `log_le_of_le_poly`: `X ≤ M·L^α(1+log L)²` gives
`log X ≤ (|log M| + α + 2)(1 + log L)`, using `log(1+log L) ≤ log L`.  The contour proof then
multiplies by `6Ĝ ≤ 6G₁L^{0.9}(1+log L)²` and lands on
`eventually_const_mul_rpow_polylog_le_rpow` at `(α,β,k) = (0.9, 0.99, 3)`; the truncation proof
splits into `(0.46, 0.53, 0)`, `(0, 0.05, 1)` and `(0.53, 0.6, 0)`, the last being `2L^{0.53} ≤ L^{0.6}`.

**Status of route (b).**  Every hypothesis of
`Sieve/RouteTTailBudget.exists_abs_sum_cos_div_primesRange_le_budget` is now discharged at the
schedule, except for assembling them: the chain
`RouteTTailBudget → RouteTScheduleRegimes → RouteTScheduleWorstCase → RouteTThresholdLimits`
has no open mathematical content, only the instantiation
`y = ⌈exp((log z)^{0.99})⌉`, `ρ₀ = 1/(9(2+log z))`, `B = 9(2+log z)`.

### Milestone C, brick 76 — the schedule itself (2026-08-19)

`Sieve/GSScheduleFacts` (axiom-clean, sorry-free, wired).  The cutoff and tolerance of route (b),
with the elementary facts the assembly consumes:

```text
   gsCutoff z = ⌈exp((log z)^{0.99})⌉ ,        gsRho z = 1/(9(2 + log z))
```

| theorem | statement |
|-|-|
| `exp_le_gsCutoff` | `exp((log z)^{0.99}) ≤ gsCutoff z` |
| `two_le_gsCutoff` | `0 < log z ⟹ 2 ≤ gsCutoff z` |
| `gsCutoff_le` | `1 ≤ log z ⟹ gsCutoff z ≤ z` (from `(log z)^{0.99} ≤ log z`) |
| `log_ge_of_ge_gsCutoff` | `gsCutoff z ≤ i ⟹ (log z)^{0.99} ≤ log i` |
| `nine_mul_gsRho_mul` | `9·gsRho z·(2 + log z) = 1` — the tail bound at the schedule is exactly `1` |
| `one_div_gsRho` | `1/gsRho z = 9(2 + log z)`, i.e. the `B` of the threshold lemmas |
| `log_tendsto_atTop_nat` | `log z → ∞` along `ℕ`, for transporting the three eventual thresholds |

**Process note.**  A first attempt at the whole assembly in one module was abandoned mid-draft (and
deleted before any build) because it contained a wrong step: `(log z)^{0.6} ≤ log|t|` was used as if
it gave `log z ≤ log|t|`, which is false.  The frequency lower bound `16π/3 ≤ |t|` has to come from
`(log z)^{0.6} ≥ log(16π/3)` instead, and the schedule facts above are the right granularity to
build the assembly out of.

### Milestone C, brick 77 — ROUTE (b) IS ASSEMBLED (2026-08-19)

`Sieve/GSTailAssembly` (axiom-clean, sorry-free, wired).  Every hypothesis of
`Sieve/RouteTTailBudget.exists_abs_sum_cos_div_primesRange_le_budget` is discharged at
`y = gsCutoff z`, `ρ₀ = gsRho z`, `B = 9(2 + log z)`:

```text
exists_abs_sum_cos_div_gsRange_le :
  ∃ A delta C, 0 < delta ∧ 0 < C ∧ ∀ (z : ℕ) (t : ℝ),
    2 ≤ z → 1 ≤ log z →
    <contour worst case> → <truncation worst case> → <Chebyshev worst case> →
    1/Ĝ ≤ delta → 126e⁹(2+log z) ≤ exp((log z)^{0.99}) → log(16π/3) ≤ (log z)^{0.6} →
    (log z)^{0.6} ≤ log|t| ≤ 2 log z
  →  |∑_{gsCutoff z < p ≤ z} cos(t log p)/p|  ≤  1
```

The bound is literally `1`, because `9·gsRho z·(2 + log z) = 1`.

Also proved here: `eventually_gsCutoff_growth`, `126e⁹(2+L) ≤ exp(L^{0.99})` eventually, via the
elementary `exp u = (exp(u/2))² ≥ (1+u/2)² ≥ u²/4` and `L^{1.98} ≥ 1512e⁹·L`.

All seven hypotheses are eventually true: the three worst cases are bricks 72 and 75, `1/Ĝ ≤ delta`
holds because `Ĝ → ∞`, and the last two are elementary limits.  **Route (b) of Matomäki–Radziwiłł's
Lemma 2 is complete**: the tail cosine sum over `(exp((log z)^{0.99}), z]` is at most `1` for every
frequency with `(log z)^{0.6} ≤ log|t| ≤ 2 log z`.

Combined with the surviving harmonic mass `∑_{y<p≤z} 1/p = 0.01·log log z + O(1)`, this gives
`D(μ, χ_t; p ≤ z)² ≥ 0.01·log log z − O(1)` on that frequency range — and route (a)
(`Sieve/PrimeCosineSumSharp.exists_mulDistSqPair_ge_quarter`) covers `log|t| ≤ (log z)^{0.8}`.
The two ranges overlap, so **MR's Lemma 2 for `μ` now holds on the whole range `1 ≤ |t| ≤ z^A`.**

### Milestone C, brick 78 — the distance from its tail (2026-08-19)

`Sieve/MoebiusDistanceTail` (axiom-clean, sorry-free, wired).  The bridge from route (b)'s tail
bound to the pretentious distance:

```text
mulDistSqPair_ge_tail (hyz : y ≤ z) (hf : ∀ p ∈ primesLE z, f p = −1) (t) :
  (mertensS z − mertensS y) + ∑_{y<p≤z} cos(t log p)/p  ≤  mulDistSqPair f (charFn t) (primesLE z)
```

The mechanism is that every term of `∑_{p≤z}(1 + cos(t log p))/p` is nonnegative, so
`Finset.sum_le_sum_of_subset_of_nonneg` discards the primes below the cutoff, and
`Sieve/TuranKubiliusRange.sum_inv_primesRange` identifies the surviving harmonic mass as
`mertensS z − mertensS y`.

**With brick 77 this gives route (b)'s distance bound**: on `(log z)^{0.6} ≤ log|t| ≤ 2 log z`,

```text
   D(μ, χ_t; p ≤ z)²  ≥  (mertensS z − mertensS (gsCutoff z))  −  1 ,
```

and Mertens plus `log gsCutoff z ≤ (log z)^{0.99} + 1` make the mass `0.01·log log z − O(1)`.

### Milestone C, bricks 79–80 — ROUTE (b)'s DISTANCE BOUND IS PROVED (2026-08-19)

`Sieve/GSTailMass` and `Sieve/MoebiusDistanceHighFreq` (both axiom-clean, sorry-free, wired).

**Brick 79 — the surviving mass.**

| theorem | statement |
|-|-|
| `log_gsCutoff_le` | `log gsCutoff z ≤ (log z)^{0.99} + 1`, from `e^u + 1 ≤ e^{u+1}` |
| **`gs_tail_mass_ge`** | `0.01·log log z − (c₁+c₂+log 2) ≤ mertensS z − mertensS (gsCutoff z)` |

using `le_mertensS` and `mertensS_le` and `log log gsCutoff z ≤ log 2 + 0.99·log log z`.

**Brick 80 — route (b).**

```text
exists_mulDistSqPair_ge_highFreq :
  ∃ A delta C C₀, 0 < delta ∧ 0 < C ∧ ∀ z t f,
    2 ≤ z → 1 ≤ log z → ⟨the six schedule facts⟩ →
    (log z)^{0.6} ≤ log|t| ≤ 2 log z →  (∀ p ≤ z prime, f p = −1) →
      0.01·log log z − C₀  ≤  D(f, χ_t; p ≤ z)²
```

with `C₀ = mertensSecondLowerConst + mertensSecondUpperConst + log 2 + 1`.

**Matomäki–Radziwiłł's Lemma 2 for `μ` is now proved on both halves of the frequency range**:

| range | theorem | bound |
|-|-|-|
| `\|t\| ≥ 9`, any `z` | `Sieve/PrimeCosineSumSharp.exists_mulDistSqPair_ge_quarter` | `(1/4)(log log z − log log\|t\|) − C` |
| `(log z)^{0.6} ≤ log\|t\| ≤ 2 log z` | `Sieve/MoebiusDistanceHighFreq.exists_mulDistSqPair_ge_highFreq` | `0.01·log log z − C₀` |

The first is `≥ 0.05·log log z − C` whenever `log|t| ≤ (log z)^{0.8}`, so the two ranges overlap and
together cover `9 ≤ |t| ≤ z²` — which is the range Halász's theorem needs.  **This is the first
unconditional pretentious lower bound in the corpus that survives to `|t|` of size `z^{Θ(1)}`.**

### Milestone C, brick 81 — MR's LEMMA 2 FOR `μ`, ONE STATEMENT (2026-08-19)

`Sieve/MoebiusDistanceUniform` (axiom-clean, sorry-free, wired).  The two halves are glued:

```text
exists_mulDistSqPair_ge_full :
  ∃ A delta C C₀, 0 < delta ∧ 0 < C ∧ ∀ (z : ℕ) (t : ℝ) (f : ℕ → ℂ),
    2 ≤ z → 1 ≤ log z → ⟨the six schedule facts⟩ →
    9 ≤ |t| → log|t| ≤ 2 log z → (∀ p ∈ primesLE z, f p = −1) →
      0.01·log log z − C₀  ≤  D(f, χ_t; p ≤ z)²
```

The split is at `log|t| = (log z)^{0.8}`: below it, `exists_mulDistSqPair_ge_quarter` gives
`(1/4)(log log z − log log|t|) − C ≥ 0.05·log log z − C`, because
`log log|t| ≤ log((log z)^{0.8}) = 0.8·log log z`; above it, `(log z)^{0.6} ≤ (log z)^{0.8} < log|t|`
puts the frequency in the Granville–Soundararajan range and
`exists_mulDistSqPair_ge_highFreq` applies.

**This is Matomäki–Radziwiłł's Lemma 2 for the Möbius character, unconditional, at the corpus's
zero-free exponent `κ = 9/10`, on the whole range `9 ≤ |t| ≤ z²`.**  It is the input Halász's
theorem needs, and the corpus's own Halász machinery
(`Sieve/HalaszUniformDistance.norm_tsum_twistedSummand_le_damped_of_uniform`) takes exactly a
uniform lower bound for `mulDistSqPair f (charFn t) (primesLE z)` over a frequency range.

**Next**: feed it into `norm_tsum_twistedSummand_le_damped_of_uniform` to obtain MR's Lemma 1/3 —
`|R(1+it)| ≪ (log X)^{−δ}` for the Ramaré-weighted cofactor — which is the pointwise input of MR's
`U` half.

### Milestone C, brick 82 — the distance at EVERY frequency below `z²` (2026-08-19)

`Sieve/MoebiusDistanceAllFreq` (axiom-clean, sorry-free, wired).  The last gap in the frequency
range is `|t| ≤ 9`, where `Sieve/ZetaPoleBoxLowerBound.exists_sum_cos_div_prime_ge_small` costs only
an absolute constant, so `D² ≥ log log z − (C_s + mertensSecondLowerConst)` there — better than the
`0.01·log log z` the other two ranges give.

```text
exists_mulDistSqPair_ge_allFreq :
  ∃ A delta C C₀, 0 < delta ∧ 0 < C ∧ ∀ (z : ℕ) (t : ℝ) (f : ℕ → ℂ),
    2 ≤ z → 1 ≤ log z → ⟨the six schedule facts⟩ →
    log|t| ≤ 2 log z → (∀ p ∈ primesLE z, f p = −1) →
      0.01·log log z − C₀  ≤  D(f, χ_t; p ≤ z)²
```

**No lower restriction on `|t|` at all** — the three ranges `|t| ≤ 9`,
`9 ≤ |t|, log|t| ≤ (log z)^{0.8}` and `(log z)^{0.6} ≤ log|t| ≤ 2 log z` cover everything.

This is the exact shape of the `hunif` hypothesis of
`Sieve/HalaszUniformDistance.norm_tsum_twistedSummand_le_damped_of_uniform`, with
`δ = √(0.01·log log z − C₀)`.  At `σ = 1 + 1/log z` that lemma then gives

```text
   ‖∑' n, f(n)n^{−σ−it}‖ ≤ (1 + log z)·exp(7/2 + 2(1 + log 4/log z) − δ²) ≍ (log z)^{0.99} ,
```

against the trivial `1 + log z`: **an unconditional Halász saving of `(log z)^{−0.01}` for `μ`,
uniform over `|t| ≤ z²`.**  That is MR's Lemma 1 for the Möbius character.

### Brick 83–84 — Halász for `μ` at every frequency below `z²` (2026-08-19)

`Sieve/MoebiusSmoothPolySaving`, `Sieve/MoebiusSeriesPolySaving`.  Both built, both axiom-clean
(`[propext, Classical.choice, Quot.sound]`), both wired into `RHTower.lean`.

| theorem | statement |
|-|-|
| `tendsto_routeTBudgetHat` | `routeTBudgetHat A · → ∞` |
| `eventually_mulDistSqPair_ge_allFreq` | `∃ C₀, ∀ᶠ z, ∀ t f, log\|t\| ≤ 2 log z → (∀p≤z, f p = −1) → (1/100)log log z − C₀ ≤ D²` — every threshold of `exists_mulDistSqPair_ge_allFreq` discharged |
| `exists_norm_sum_moebius_smooth_le_polySaving` | `‖∑_{n squarefree z-smooth} μ(n)n^{−1−it}‖ ≤ C(log z)^{99/100}` for `\|t\| ≤ z²` |
| `log_abs_le_two_mul_log_of_le_sq` | `\|t\| ≤ z² → log\|t\| ≤ 2 log z` |
| `exists_norm_tsum_moebius_le_polySaving` | `‖∑'_n μ(n)n^{−σ−it}‖ ≤ C(log z)^{99/100}` at `σ = 1 + 1/log z`, for `\|t\| ≤ z²` — **MR Lemma 1 at the level of the full series** |

The trivial size of the series at that abscissa is `1 + 1/(σ−1) = 1 + log z`, so this is an
unconditional Halász saving of `(log z)^{−1/100}` for `μ`, uniform over the whole range `|t| ≤ z²`.
The mechanism is `Sieve/DistanceAbscissaBridge.norm_tsum_twistedSummand_le_of_mulDistSqPair`
(`‖∑'‖ ≤ (1 + 1/(σ−1))exp(7/2 + 2(σ−1)(log z + log 4) − D²)`) fed by brick 82.

**Prior-work correction.**  `Sieve/MoebiusDistanceSharp` (committed 2026-08-10, not by this
programme) already contains the three-four-one route: `exists_mulDistSqPair_ge_free` gives
`log log z − (3/4)log(1+log z) − (1/4)log(3+log(4+2|t|)) − C`.  That bound is **positive only for
`log|t| ≤ (log z)^{1−ε}` and is exactly `0` at `log|t| ≍ log z`**, and its companion
`exists_mulDistSqPair_ge_height` (`log log z − log log T − C` for `z ≤ T`) is vacuous.  Brick 60
(`Sieve/PrimeCosineSumSharp.exists_mulDistSqPair_ge_quarter`) duplicates the same three-four-one
mechanism with a different constant profile.  What is genuinely new in bricks 61–84 is the
**Granville–Soundararajan tail half**, which keeps the bound positive (`(1/100)log log z`) all the
way to `log|t| = 2 log z`, and the resulting series bound.  Lesson: `formal_tools.py research`
does index `MoebiusDistanceSharp`; the earlier queries were badly chosen.  Query by *mechanism*
("three four one", "smooth moebius sum power saving") as well as by conclusion.

### Milestone C for `1/2 < β < 1` — the case `J = 1`, and what the zero-free region does and does not buy

**`β > 1/2` is exactly the regime `J = 1`.**  MR need `[P₁,Q₁] ⊆ [1,h]` and define `J` as the largest
`j` with `Q_j ≤ exp((log X)^{1/2})`.  For `h = exp((log X)^β)` with `β > 1/2` one may take
`Q₁ = exp((log X)^{1/2})` outright, so `J = 1`: **no iterated family `[P_j,Q_j]`, no `ℓ`-th power
lengthening, no minimality-of-`j` device.**  The five cards need precisely this case.

**What the target actually is.**  `route_e_marker_hall_law` consumes
`AveragedMeanSquare μ (cardLength β)`, which is a bare `o(h²√x)` — *not* the `(log x)^{−1−c}` of the
card's prose `(8)` (that is Menon's rate; the Lean route does not need it).  MR's Theorem 1 is
exactly `o(h²)`, so **MR is the right strength, and no quantitative rate is required.**

**The reduction (MR Lemma 14 + the mean value theorem).**  Everything reduces to
`∫_{T₀}^{X/h}|F(1+it)|²dt = o(1)` for `F(s) = ∑_{X≤n≤2X, n∈𝒮} μ(n)n^{−s}`, against the mean-value
theorem's `T/X + 1 ≍ 1`.  The large-`T` piece is free: `max_{T≥X/h}(X/(hT))∫_T^{2T}|F|² ≪ 1/h`.

**What the κ = 9/10 zero-free region buys, exactly.**  For `μ` — unlike MR's general `f : ℕ → [−1,1]`
— the contour argument gives the *dyadic* bound

```text
   |∑_{X ≤ n ≤ 2X} μ(n) n^{−1−it}| ≪ exp(−c (log X)^{1/10})   uniformly for |t| ≤ X ,
```

(the `1/ζ(1+it)` main terms of the two partial sums cancel), which is far stronger than MR's
Lemma 1 (`(log X)^{−1/12+o(1)}`) and Lemma 3 (`(log X)^{−1/24}`).  **But it is not enough by itself:**
`∫_{T₀}^{T}|F|²dt ≤ min(T·sup|F|², T/X+1)` beats `1` only for `T ≤ exp(2c(log X)^{1/10})`, and
`∫|F|² ≤ sup|F|·√(T·∫|F|²) ≈ exp(−c(log X)^{1/10})√X` is useless.  The mean-value theorem's
**diagonal** `∑_n |a_n|²·N ≍ 1` is irreducible; only the bilinear (Ramaré) structure removes it.
So the zero-free region replaces MR's Lemmas 1–3 as the *pointwise* input, and the Ramaré +
large-values architecture is still required.

**Caveat on the corpus's existing Route-T Möbius atom.**
`Sieve/RouteTMoebiusPowerSaving.exists_norm_LSeries_truncatedMoebius_dyadic_le_routeTPower` demands
`(2^q)^4 ≤ U ≤ |τ| − routeTInverseBaseHeight`, i.e. **frequency at least the fourth power of the
polynomial length**.  Our regime is the opposite (`length ≈ X`, `|t| ≤ X`), so that module is not
reusable here; the dyadic-cancellation bound above has to be built separately, with Perron
truncation height `U ≈ exp(c(log X)^{1/10})log X` and the requirement `|t| > U`.

**The `J = 1` chain, with the numbers checked at κ = 9/10.**

```text
   𝒯₁ half:  Q₁ = exp((log X)^{1/2}),  P₁ ≥ (log Q₁)^{40/η},  H₁ = P₁^{1/6−η}/(log Q₁)^{1/3},
             α = 1/4 − η ,   t ∈ 𝒯₁  :⟺  ∀v ∈ I₁, |Q_{v,H₁}(1+it)| ≤ e^{−αv/H₁} ,
             Ramaré + mean value theorem  ⟹  ∫_{𝒯₁}|F|² ≪ H₁² log Q₁ · P₁^{−2α}
                                                        ≈ (log Q₁)^{1/3}/P₁^{1/6+2η}  →  0 .
   𝒰 half:   P = exp((log X)^{1−1/48}),  Q = exp(log X/log log X),  H = (log X)^{1/48} ,
             Lemma 12 error   1/H + 1/P + log P/log Q  ≪ (log X)^{−1/48} log log X ,
             𝒯_S (|Q_v| < (log X)^{−100}):  Lemma 9 gives  ≪ (log X)^{−200}·(1 + T^{1−η}P/X) ,
             𝒯_L (|Q_v| ≥ (log X)^{−100}):  Lemma 8 gives  |𝒯_L| ≤ exp((log X)^{0.021+o(1)}) ,
                                            Lemma 11 saving  exp(−log P/(log T)^{κ+ε})
                                                           = exp(−(log X)^{1−1/48−9/10−ε})
                                                           = exp(−(log X)^{0.0792−ε}) .
             0.0792 > 0.021 , so the 𝒯_L term still dies at κ = 9/10.        ✓
```

The Vinogradov–Korobov exponent `2/3` would give `exp(−(log X)^{0.3125})`; the corpus's `9/10`
leaves a margin of `0.058` in the exponent.  **`κ = 9/10` is enough, with room.**

**Brick order from here.**  (85) MR Lemma 8, the moment-method large-value count for a prime
polynomial — audit `Sieve/PrimePowerSupport.volume_largeValues_pow_symm_le_of_prime_support` first.
(86) MR Lemma 11, Halász–Montgomery for prime-supported coefficients carrying
`exp(−log P/(log T)^{9/10+ε})` — audit `Sieve/HalaszPrimeSavingBound`.  (87) MR Lemma 9 — audit
`Sieve/HalaszMontgomeryIntegral`.  (88) MR Lemma 12 at `J = 1`.  (89) Lemma 14 in the corpus's
fibre normalisation.  (90) the dyadic Route-T cancellation bound for `μ` at `|t| ≤ X`.

### Bricks 85–87 — the large-values and Perron layers (2026-08-19)

All built, all axiom-clean, all wired into `RHTower.lean`.

| module | theorem | content |
|-|-|-|
| `Sieve/SupportKernelLargeValues` | `sum_normSq_logPoly_le_of_rowBound` | `∑_{w∈T}‖logPoly a S w‖² ≤ Δ·∑_{n∈S}‖a_n‖²` whenever every Gram row `∑_{v∈T}‖∑_{n∈S}n^{2πi(u−v)}‖ ≤ Δ` — pure duality, no arithmetic |
| | `sum_normSq_logPoly_le_of_kernelBound` | the corollary `Δ = #S + E·#T` |
| `Sieve/PrimeRangeKernelLargeValues` | `exists_norm_sum_unitLogPhase_primeRange_le` | the Gram kernel of a prime range is bounded by `routeTPrimeKernel`, from `Sieve/PrimeBlockTwistBound.exists_norm_primeBlockPoly_routeT_le` |
| | `exists_sum_normSq_logPoly_primeRange_le` | **MR Lemma 11**: the diagonal is `#B` (the *number of primes*, not the length) and the off-diagonal price carries the Route-T saving `x^{−w(τ)/3}`, `w(τ) ≍ (log\|τ\|)^{−9/10}` |
| `Sieve/PerronKernelExplicit` | `exists_perronKernel_bound_explicit` | `‖perronKernel σ N H y‖ ≤ (N+H)^σ(1/σ + C₁(N+H)/H)·(1+y²)⁻¹`, `C₁` absolute — removes the existential constant of `Sieve/HalaszPerronAssembly` |
| | `exists_norm_tsum_mul_smoothWeight_le_explicitConst` | the assembled Halász bound with that constant substituted |

Corpus assets identified and **not** rebuilt: `Sieve/AlmostOrthogonality.sum_norm_inner_sq_le_of_schur`
(the Schur/duality principle), `Sieve/HalaszMontgomeryDyadic.halaszMontgomery_dyadic` (MR Lemma 9 for
integers), `Sieve/PrimePowerSupport.volume_largeValues_pow_symm_le_of_prime_support` (MR Lemma 8, in
measure form), `HTGeometry/SmoothWeightSharpMellin.exists_mellin_smoothWeight_two_scale_bounds`.

### The pointwise gap, located exactly: two Möbius contour chains and the hole between them

**Halász cannot supply the pointwise input.**  The Perron route bounds the smoothed sum by
`(1/2π)∫_ℝ|F(σ+iy)|·‖W(σ+iy)‖dy`, and `∫_ℝ‖W‖dy ≍ N·log(N/H)` (the `1/|y|` regime of the Mellin
transform), while the trivial size of the partial sum is `N`.  So the modulus-only Perron transfer
needs `sup|F| ≪ 1/log(N/H)`, whereas Halász only gives `sup|F| ≍ (log N)^{99/100}` — a *positive*
power.  Recovering the `1/log N` is the Halász theorem proper, i.e. the corpus's
Granville–Harper–Soundararajan chain, whose master bound
`Sieve/HalaszGhsMasterBound.norm_sum_Icc_mul_log_le_of_kernelBound` (i) still awaits the arithmetic
evaluation of its two sieve mean squares and (ii) assumes `f (a*b) = f a * f b`, which `μ` fails.
**Brick 84 is therefore not upgradable to a partial-sum bound by soft means.**

**The zero-free region can, and for `μ` it is much stronger.**  The corpus already owns

```text
   Sieve/MoebiusTwistSharpRate.exists_norm_sum_moebiusTwist_rate :
     ‖∑_{n ≤ N} μ(n) n^{−iτ}‖  ≤  3N·exp(−(c/8192)(log N)^{1/10}/2)/π + (smoothWidth N + 1)
   Sieve/DampedTwistSharpRate.exists_norm_sum_dampedTwist_rate :
     the same for the ω-damped coefficients μ(n)u^{ω_P(n)}, times dampedCorrBound P (leftAbscissa K)
```

— i.e. **a super-polylogarithmic saving, and already in the `1/(ω_P+1) = ∫₀¹u^{ω_P}du` form that MR
Lemma 3 needs.**  Both carry the hypothesis `5 + 4|τ| ≤ contourParam (N + smoothWidth N)` with
`contourParam x = ⌈exp((log x)^{1/10})⌉₊`, because `leftAbscissa K = 1 − c/(16(log K)⁹)` is the
**exponent-nine** zero-free width: the height must be held down to `exp((log N)^{1/10})` for that
width to be `(log N)^{−9/10}`.

**The hole.**  MR need the frequency range `|t| ≤ T₁ = X/h`, i.e. `|τ| ≈ N`.  The two existing
Möbius contour chains cover

```text
   (a) Sieve/MoebiusTwist* , exponent 9      :  |τ| ≤ exp((log N)^{1/10}) ,  saving exp(−c(log N)^{1/10})
   (b) Sieve/RouteTMoebiusPowerSaving        :  |τ| ≥ N⁴               ,  saving N^{−w/3}
```

and **nothing covers `exp((log N)^{1/10}) < |τ| ≤ N`**, which is exactly the range the `𝒰` half lives
in.  With the Route-T width `w ≍ (log|τ|)^{−9/10}` at `|τ| ≤ N` the saving would be
`exp(−c(log N)^{1/10})`, so the theorem is true and the ingredients exist
(`Sieve/VonMangoldtTwistUniformHeight.exists_norm_partialSum_vonMangoldtTwist_routeT_uniform` is the
same statement for `Λ`, uniform in the height, already proved).  Restriction (b) comes from taking
the Perron truncation `U ≥ N⁴` and then demanding `|τ| ≥ U` so that the contour box misses the real
axis; for `1/ζ` the point `s = 1` is a zero, not a pole, so the restriction is an artefact of the
edge bounds, not of the mathematics.

**Brick 88 (the critical path): the Route-T twisted Möbius contour bound, uniform in the height** —
the `1/ζ` analogue of `VonMangoldtTwistUniformHeight`, i.e.

```text
   ‖∑_{n ≤ N} μ(n)n^{−iτ}‖ ≤ C·N·exp(−c·(log N)^{1/10}) + (height term)   for every real τ with |τ| ≤ N,
```

and its `ω`-damped companion, which together are MR Lemma 3 for `μ` with a super-polylogarithmic
saving in place of MR's `(log X)^{−1/24}`.

**Slack check for the damped correction.**  `dampedCorrBound P c = ∏_{p∈P}(1+p^{−c})/(1−p^{−c})` at
`c = 1 − δ` costs `exp(3Q^δ log(log Q/log P))`.  For the `𝒯₁` half (`log Q₁ = (log X)^{1/2}`,
`δ ≍ (log X)^{−9/10}`) this is `exp(3(1+o(1))·(1/2)log log X)` — a fixed power of `log X`, dominated
by the saving `exp(−c(log X)^{1/10})`.  For the `𝒰` half (`log Q = log X/log log X`) one has
`Q^δ = exp((log X)^{1/10}/log log X)`, which **beats** the saving, so there the abscissa must be
pulled in to `δ = c/log Q ≍ c·log log X/log X`; the saving is then only `(log X)^{−c}` and the
correction costs `(log X)^{3e^c/48}`, net `(log X)^{−0.83}` at `c = 1` — still far better than MR's
`(log X)^{−1/24}`.  This needs the contour bound with the **abscissa as a free parameter**, which
`Sieve/DampedTwistContourBoundGeneral` may already provide; audit it before rebuilding.

**Low-frequency dividend.**  Chain (a) already closes the range `|t| ≤ exp(κ(log X)^{1/10})` of the
main integral for free: `∫_{T₀}^{T_*}|F|²dt ≤ T_*·sup|F|² ≤ exp(−(3c/2)(log X)^{1/10}) → 0` on
choosing `T_* = exp((c/2)(log X)^{1/10})`.  So MR's `T₀ = (log X)^{1/15}` can be replaced by
`T_* = exp(c'(log X)^{1/10})`, which makes every `1/T₀` term in the argument superpolylogarithmically
small.

### Brick 88 — the Route-T twisted Möbius contour at EVERY frequency (2026-08-20)

`Sieve/RouteTMoebiusTwistAllHeights`, built, axiom-clean, wired.

```text
exists_norm_tsum_moebiusTwist_smoothWeight_le_routeT_allHeights :
  ∃ A C C' M δ, 0 ≤ C ∧ 0 ≤ C' ∧ 0 ≤ M ∧ 0 < δ ∧
    ∀ N H τ U d, 0 < N → 0 < H → 1 ≤ U → 1 < d → d ≤ 2 →
      routeTInverseBaseHeight ≤ |τ| + U →  d ≤ routeTContourRight A (|τ|+U) →
      ‖2π • ∑' n, μ(n)n^{−iτ} w_{N,H}(n)‖ ≤ (four rectangle edges, with
        Mc = max M (routeTContourEdgeBound A (|τ|+U)) on the three shifted edges)

exists_norm_sum_moebiusTwist_le_routeTSharp_allHeights :
  the same for the sharp sum ∑_{n ≤ N} μ(n)n^{−iτ}, at the cost of (H + 1).
```

**What was removed.**  `Sieve/RouteTMoebiusContour.exists_norm_tsum_moebiusTwist_smoothWeight_le_routeT`
carries `routeTInverseBaseHeight + U ≤ |τ|`, which together with the Perron truncation `U ≥ N⁴`
needed to kill the truncation edge forces `|τ| ≥ N⁴`.  The new theorem drops it: on the ordinates
`|Im s| ≤ routeTInverseBaseHeight` the rectangle lies in the fixed compact box of
`exists_bound_invZeta_fixed_box`, **whose statement already covers `1 − δ ≤ Re s ≤ 2`**, so the same
constant `M` bounds `1/ζ` on the horizontal edges as well as the left edge.  Only `Mh ↦ max M Mh`
changes.  The right abscissa `d` is now a free parameter: keeping `d = 1 + Δ(|τ|+U)` costs
`(N+H)^{Δ}`, which is `exp(log N/(log(|τ|+U))^{9/10})` and is only harmless when
`log(|τ|+U) ≍ log N`; pulling `d` back to `1 + 1/log N` removes that factor at the cost of a
right-edge constant `e^{22/4}(1 + log N)`.

**Brick 88c, the parameter choice (next).**  With `L = log N` and a small `c₀ > 0` set

```text
   d = 1 + 1/L ,   H = N·exp(−2c₀L^{1/10}) ,   U = K·(1+L)·exp(3c₀L^{1/10}) ,
```

so that (i) `H + 1 ≤ N exp(−c₀L^{1/10})`, (ii) the truncation edge
`2 Md C (N+H+1)^{2+d}/(H²U) ≍ (1+L)N/(η²U)` is `≤ N exp(−c₀L^{1/10})` by the choice of `U`,
(iii) the two horizontal edges carry `1/U` and `(d − c) ≍ Δ`, hence are smaller still, and (iv) the
left edge is `Mc·(N+H)^{1−shift}/c ≍ Mc·N·exp(−shift·L)·exp(2c₀L^{1/10})` with
`shift = min(Δ(S)/20, δ/2) ≍ L^{−9/10}/20`, i.e. `exp(−L^{1/10}/20 + 2c₀L^{1/10})`.  Taking
`c₀ = 1/100` gives the net saving `exp(−0.03·L^{1/10})`.  The side conditions are
`base ≤ |τ| + U` (free, `U → ∞`) and `1/L ≤ routeTInverseDelta A (|τ| + U)`, which for `|τ| ≤ N`
follows from antitonicity of `routeTInverseDelta` plus a polylogarithmic lower bound for it at
`T = 2N`.  Also needed: an upper bound for `routeTContourEdgeBound A (|τ|+U) =
exp(400·routeTZeroFreeBudget A (routeTInverseHeight (|τ|+U))²)` that is `o(exp(L^{1/10}))` for
`|τ| ≤ N`.

**Target of 88c.**
```text
   ∃ c C > 0, ∀ᶠ N : ℝ in atTop, ∀ τ : ℝ, |τ| ≤ N →
     ‖∑_{n ≤ N} μ(n) n^{−iτ}‖ ≤ C · N · exp(−c (log N)^{1/10}) .
```
This is the pointwise input MR's `𝒰` half needs, and — with the `u^{ω_P}` damping of
`Sieve/DampedTwist*` carried through the same rectangle — it is MR Lemma 3 for `μ` with a
super-polylogarithmic saving in place of `(log X)^{−1/24}`.

### Brick 88c stage 1 — the Route-T contour data below the doubled cutoff (2026-08-20)

`Sieve/RouteTContourRateBounds`, built, axiom-clean, wired.

| theorem | statement |
|-|-|
| `routeTContourLeft_ge_half` | `1/2 ≤ routeTContourLeft A δ T` — unconditional, from `routeTInverseDelta_le_sixteenth` |
| `routeTLogHeightEnvelope_le_five_log` | `S ≤ 2N`, `log N ≥ 3` ⟹ `routeTLogHeightEnvelope (4·routeTInverseHeight S) ≤ 5 log N` |
| `one_le_routeTLogHeightEnvelope` | `1 ≤ routeTLogHeightEnvelope t` for `t ≥ −1` |
| `five_log_polylog_le` | `(5L)^{9/10}(1+log 5L)² ≤ 5^{9/10}(1+log5)²·L^{9/10}(1+\|log L\|)²` |
| **`eventually_routeT_contour_rate_data`** | `∀ᶠ N, ∀ S ∈ [base, 2N]`: `10(log N)^{1/20} ≤ shift·log N`, `routeTContourEdgeBound A S ≤ exp((log N)^{1/20})`, and `1/log N ≤ routeTInverseDelta A S` |

The three facts are exactly what the rectangle bound of brick 88 needs: the displacement beats every
fixed power of `(log N)^{1/20}` after multiplication by `log N` (so the left edge carries
`N^{1−shift} ≤ N e^{−10(log N)^{1/20}}`), the edge constant is negligible against it, and the
abscissa `1 + 1/log N` still lies inside the zero-free rectangle.  All three reduce by monotonicity
(`routeTZeroFreeDelta_antitone`, `routeTZeroFreeBudget_mono`) to the top of the range `S = 2N`,
where `Sieve/RouteTZetaAsymptotics.{routeTZeroFreeDelta_polylog_lower,
routeTZeroFreeBudget_logHeight_upper}` apply and brick 76
(`Sieve/PolylogRpowDomination.eventually_const_mul_rpow_polylog_le_rpow`) finishes.

**Stage 2 (next), the parameter choice.**  With `ε = (log N)^{1/20}`,

```text
   H = N e^{−3ε} ,   U = (1+log N) e^{8ε} + routeTInverseBaseHeight ,   d = 1 + 1/log N ,
```

and `(N+H+1) ≤ 3N`, `(N+H+1)^d ≤ 9eN`, `(N+H)^{c} ≤ 2N e^{−10ε}` where `c = 1 − shift`, the four
edges of `exists_norm_sum_moebiusTwist_le_routeTSharp_allHeights` are

```text
   T₁ ≤ 162 e^{6.5} C · N e^{−2ε} ,      T₂ = T₃ ≤ 54 e C' (M+1) · N e^{−4ε} ,
   T₄ ≤ (M+1)(8 + 54C) · N e^{−3ε} ,      H + 1 ≤ 2N e^{−3ε} ,
```

so the sharp sum is `≤ C₄ · N · exp(−(log N)^{1/20})`.  The side condition to discharge is
`|τ| + U ≤ 2N`, i.e. `(1+log N)e^{8ε} + routeTInverseBaseHeight ≤ N`, which follows from
`1 + L ≤ e^{L/4}`, `8L^{1/20} ≤ L/4` and `base ≤ e^{L/2}`, all eventually.

**Statement of brick 88c.**
```text
   ∃ C > 0, ∀ᶠ N : ℝ in atTop, ∀ τ : ℝ, |τ| ≤ N →
     ‖∑_{n ≤ N} μ(n) n^{−iτ}‖ ≤ C · N · exp(−(log N)^{1/20}) .
```

### Brick 88c — CLOSED: the twisted Mertens sum at every frequency below the cutoff (2026-08-20)

`Sieve/RouteTMoebiusTwistRate`, built (86 s), axiom-clean, wired.

```text
exists_norm_sum_moebiusTwist_le_rate :
  ∃ K > 0, ∀ᶠ N : ℝ in atTop, ∀ τ : ℝ, |τ| ≤ N →
    ‖∑_{n ≤ N} μ(n) n^{−iτ}‖ ≤ K · N · exp(−(log N)^{1/20}) .
```

**Unconditional, uniform over every real frequency up to the cutoff, with a saving that beats every
power of the logarithm.**  The two Möbius contour chains the corpus had covered only
`|τ| ≤ exp((log N)^{1/10})` (exponent-nine width) and `|τ| ≥ N⁴` (Route-T width, `U ≥ N⁴`); the gap
between them was the range MR's exceptional set `𝒰` lives in.  It is now closed.

Parameters actually used: `H = N e^{−3ε}`, `U = N`, `d = 1 + 1/log N`, `ε = (log N)^{1/20}`.  Taking
the Perron half-height equal to the cutoff itself makes the three non-left edges polylogarithmic
(they are divided by `U = N`), so only the left edge — the zero-free one — carries weight, and it is
`N^{1−shift} ≤ N e^{−10ε}` by `eventually_routeT_contour_rate_data`.  The intermediate estimates are
`(N+H+1)^d ≤ 9eN`, `(N+H+1)^c ≤ 3N e^{−10ε}`, `(N+H)^c ≤ 2N e^{−10ε}`,
`C/H²·(N+H+1)² ≤ 9C e^{6ε}`, `C'/H·(N+H+1) ≤ 3C' e^{3ε}`, `Mc ≤ (M+1)e^{ε}`, and the
side conditions `(1+log N)e^{8ε} ≤ N`, `e^{6ε} ≤ N` from `eventually_rate_growth`.

**What this is, mathematically.**  It is the Vinogradov–Korobov-strength prime number theorem for
the Möbius function twisted by an arbitrary character `n^{−iτ}`, uniformly in `τ` up to the cutoff,
at the corpus's zero-free exponent `κ = 9/10`.  For MR it replaces Lemma 1 and (once the `ω`-damping
is carried through, brick 89) Lemma 3, with `exp(−(log X)^{1/20})` in place of `(log X)^{−1/24}` —
an enormous margin over what the `𝒰` half needs.

**Brick 89 (next).**  The same for the Ramaré cofactor: `1/(ω_P(n)+1) = ∫₀¹ u^{ω_P(n)}du` turns the
cofactor into an average of `dampedTwist P u τ`, whose Euler product is `(1/ζ)·∏_{p∈P}(1−up^{−s})/(1−p^{−s})`.
The corpus already owns the exponent-nine version (`Sieve/DampedTwistSharpRate`) together with the
correction factor `Sieve/DampedCorrBound.dampedCorrBound P c = ∏_{p∈P}(1+p^{−c})/(1−p^{−c})`; what is
needed is the Route-T all-heights version, mirroring bricks 88/88b/88c.  Slack: at the `𝒯₁`
parameters (`log Q₁ = (log X)^{1/2}`) the correction is `exp(3 Q₁^{δ} log(log Q₁/log P₁))` with
`Q₁^δ → 1`, hence a fixed power of `log X` — negligible against `exp(−(log X)^{1/20})`.

### Brick 89 — the Ramaré cofactor on the same rectangle (2026-08-20)

`Sieve/RouteTDampedTwistAllHeights`, built, axiom-clean, wired.

| theorem | statement |
|-|-|
| `exists_norm_tsum_dampedTwist_smoothWeight_le_routeT_allHeights` | the four-edge Route-T rectangle bound for `∑' μ(n)u^{ω_P(n)}n^{−iτ}w_{N,H}(n)` at **every** frequency, with each edge constant multiplied by `dampedCorrBound P (routeTContourLeft A δ (\|τ\|+U))` |
| `routeTDampedAllHeightsSmoothBound` | the right-hand side, as a definition |
| `exists_norm_sum_dampedTwist_le_routeTSharp_allHeights` | the same for the sharp sum `∑_{n ≤ N}`, at the cost of `H + 1` |

The proof is brick 88's verbatim, with `Sieve/DampedShiftBound.norm_dampedInvZeta_shift_le` applied at
each of the four edges: it converts a bound `M` for `‖invZeta (s + iτ)‖` into `M · dampedCorrBound P c`
for `‖dampedInvZeta P u (s + iτ)‖`, provided `1/2 ≤ c ≤ Re s`.  The hypothesis `1/2 ≤ c` is exactly
`Sieve/RouteTContourRateBounds.routeTContourLeft_ge_half`, which holds unconditionally because
`routeTInverseDelta ≤ 1/16`.

**Structural identity worth recording**:
`routeTDampedAllHeightsSmoothBound A C C' M δ P N H τ U d
   = dampedCorrBound P (routeTContourLeft A δ (|τ|+U)) · routeTMoebiusAllHeightsSmoothBound A C C' M δ N H τ U d`
holds by `ring`, so the rate estimate of brick 88c transfers with one extra factor once the estimate
is extracted from `exists_norm_sum_moebiusTwist_le_rate` into a standalone lemma about
`routeTMoebiusAllHeightsSmoothBound` (**brick 89c, the remaining refactor**).  The size of that factor
at the `𝒯₁` parameters is `exp(2 Q₁^{shift} log(log Q₁/log P₁))` with
`Q₁^{shift} = exp((log X)^{1/2 − 9/10}/20) → 1`, i.e. a fixed power of `log X` — negligible against
`exp(−(log X)^{1/20})`.

### Brick 89c — CLOSED: MR Lemma 3 for `μ`, with a super-polylogarithmic saving (2026-08-20)

`Sieve/RouteTMoebiusTwistRate` refactored, `Sieve/RouteTDampedTwistRate` added; both built and
axiom-clean.

| theorem | statement |
|-|-|
| `routeTMoebiusAllHeightsSmoothBound_le_rate` | the rate estimate, extracted from `exists_norm_sum_moebiusTwist_le_rate` as a standalone bound on the rectangle expression at `H = N e^{−3ε}`, `U = N`, `d = 1 + 1/log N` |
| `one_le_dampedCorrBound` | `1 ≤ dampedCorrBound P c` for `c ≥ 1/2` |
| `routeTDampedAllHeightsSmoothBound_eq` | `damped rectangle = dampedCorrBound P c · plain rectangle` (by `ring`) |
| **`exists_norm_sum_dampedTwist_le_rate`** | `∃ A δ K > 0, ∀ᶠ N, ∀ P u τ, (∀q∈P, prime) → 0 ≤ u ≤ 1 → \|τ\| ≤ N → ‖∑_{n ≤ N} μ(n)u^{ω_P(n)}n^{−iτ}‖ ≤ K·dampedCorrBound P (routeTContourLeft A δ (\|τ\|+N))·N·exp(−(log N)^{1/20})` |

Because `1/(ω_P(n)+1) = ∫₀¹u^{ω_P(n)}du`, the last line is the pointwise bound for the Ramaré
cofactor itself, uniformly over every frequency below the cutoff: **MR Lemma 3 for `μ`, with
`exp(−(log X)^{1/20})` in place of the paper's `(log X)^{−1/24}`.**  The correction factor is
`∏_{p∈P}(1+p^{−c})/(1−p^{−c})` at `c = 1 − shift`, `shift ≍ (log(|τ|+N))^{−9/10}/20`; at the `𝒯₁`
parameters (`log Q₁ = (log X)^{1/2}`) it is a fixed power of `log X`, negligible against the saving.

**Remaining for the `J = 1` architecture:** MR Lemma 12 (the Ramaré/Buchstab split into narrow
blocks) at `J = 1`, the `𝒯₁`/`𝒰` partition with the mean-value bound on `𝒯₁`, MR Lemma 8 in
discrete (well-spaced) form, and the assembly into the corpus's `AveragedMeanSquare` normalisation.

### Brick 90 — the `𝒯₁`/`𝒰` partition in the corpus's normalisation (2026-08-20)

`Sieve/Section4AllBlocksSmall`, built, axiom-clean, wired.

```text
allBlocksSmall Q R η L Vk W
  = Icc (−W) W ∩ ⋂_{k<L} {w : ‖primeBlockPoly (geomBlock Q R (1+η) k) w‖ ≤ V_k}     -- MR's 𝒯₁
someBlockLarge Q R η L Vk W = Icc (−W) W \ allBlocksSmall …                          -- MR's 𝒰
```

| theorem | content |
|-|-|
| `measurableSet_allBlocksSmall`, `allBlocksSmall_subset` | `𝒯₁` is a measurable subset of the window |
| `norm_primeBlockPoly_le_of_mem_allBlocksSmall` | the pointwise bound holds **by membership** |
| **`setIntegral_normSq_omegaWeighted_le_blocks_allSmall`** | `Sieve/Section4QSide.setIntegral_normSq_omegaWeighted_le_blocks` with its hypothesis `hVk` discharged — on `𝒯₁` the long ladder needs *no* zero-free region, *no* Route-T saving, no analytic input at all |
| `someBlockLarge_subset` | `𝒰 ⊆ ⋃_{k<L} shortExceptional (geomBlock Q R (1+η) k) W (V_k)` |
| `volume_someBlockLarge_le` | `\|𝒰\| ≤ ∑_{k<L} \|shortExceptional …\|`, each summand being what `Sieve/PrimePowerSupport.volume_largeValues_pow_symm_le_of_prime_support` (MR Lemma 8) controls |

This is the structural move the Milestone-C read-off identified as decisive: the *proved pointwise
saving* that the Milestone-B no-go showed cannot exist below `β = κ = 9/10` is replaced by the
*definition* of the frequency set, and the whole analytic burden moves to `𝒰`, where the tools are
bricks 84–89c (Lemmas 1, 3), 85–86 (Lemma 11) and the moment method (Lemma 8).

**Status of MR's lemma list for the `J = 1` architecture: every lemma is now owned.**

| MR | corpus |
|-|-|
| Lemma 1 (Halász) | `Sieve/MoebiusSeriesPolySaving.exists_norm_tsum_moebius_le_polySaving` |
| Lemma 2 (distance) | `Sieve/MoebiusDistanceAllFreq.exists_mulDistSqPair_ge_allFreq` |
| Lemma 3 (cofactor, pointwise) | `Sieve/RouteTDampedTwistRate.exists_norm_sum_dampedTwist_le_rate` |
| Lemma 8 (large values, measure form) | `Sieve/PrimePowerSupport.volume_largeValues_pow_symm_le_of_prime_support` |
| Lemma 9 (HM for integers) | `Sieve/HalaszMontgomeryDyadic.halaszMontgomery_dyadic` |
| Lemma 11 (HM for primes) | `Sieve/PrimeRangeKernelLargeValues.exists_sum_normSq_logPoly_primeRange_le` |
| Lemma 12 (Ramaré split) | `Sieve/{RamareBlockSplit, LadderHarmonicSplit, LadderProductDefect, Section4QSide}` |
| Lemma 14 (Parseval) | `Sieve/{LogWindowPlancherel, GallagherDyadicTail}` |
| the `𝒯₁`/`𝒰` partition | `Sieve/Section4AllBlocksSmall` |

**What remains is the assembly**: choosing `Q₁ = exp((log X)^{1/2})`, `P₁`, `H₁`, `α`, running the
`𝒯₁` half through `setIntegral_normSq_omegaWeighted_le_blocks_allSmall` and the `𝒰` half through
Lemma 8 + Lemma 11 + brick 89c, and feeding the result into
`Sieve/OmegaSpectralFibre.averagedMeanSquare_moebius_of_omegaBudget` in place of the Milestone-B
budget.  That is the single remaining milestone for cards 3, 4 and 5.

### Brick 91 — the cofactor over the ladder's exceptional set (2026-08-20)

`Sieve/Section4LadderExceptional`, built, axiom-clean, wired.  This is the `𝒰` companion of brick 90.

| theorem | content |
|-|-|
| `ladderExceptionalD` | the Dirichlet-variable exceptional set of the **whole** ladder: `⋃_{k<L} blockExceptional (geomBlock Q R (1+η) k) moebiusCoeff NA T (V_k)` |
| `measurableSet_ladderExceptionalD`, `ladderExceptionalD_subset` | measurable, inside `Icc (−T) T` |
| **`measureReal_ladderExceptionalD_le`** | Lemma 2.5 for the whole ladder: the measure is at most `∑_{k<L}` of the single-block moment bounds `2(T + 4N^{k'}(1+log N^{k'}))(k'^{k'}(#B_k)^{k'})/V_k^{2k'}` |
| `someBlockLarge_subset_preimage` | brick 90's `𝒰` is inside the scaled preimage of `ladderExceptionalD` |
| **`setIntegral_normSq_logPoly_someBlockLarge_le`** | Lemma 2.6 on the union: `∫_𝒰 ‖logPoly a D w‖²dw ≤ (2π)^{-1}(2N_D + (…)·(the measure sum))·Ω²·#D` |

**Both halves of the Matomäki–Radziwiłł frequency partition are now available in the corpus's own
Gallagher normalisation**, with `V_k` a free parameter:

```text
   ∫_{𝒯₁} ‖A_ω‖²  ≤  2(∑1/v_k)(∑ v_k V_k² I_k) + 2·(ladder defect)      -- brick 90, hypothesis-free
   ∫_{𝒰}  ‖C‖²    ≤  Halász–Montgomery(∑_k moment bound at V_k)          -- brick 91
```

The Milestone-B no-go said no *proved* pointwise bound `V_k` can be small enough below `β = κ = 9/10`;
here `V_k` is chosen, not proved, and the price is paid in the measure of `𝒰`.  That is the whole
mechanism of the MR partition, now formal.

**What is left for `averagedMeanSquare_moebius_scaled'` at `1/2 < β < 1`:** choose
`Q₁ = exp((log x)^{1/2})`, `P₁`, the block ratio `1+η`, `L`, the levels `V_k` and the Cauchy–Schwarz
weights `v_k`; verify the two resulting budgets are `o(W²h²)` with `W = mertensS z − mertensS z₀ ≍
log log x`; and feed the total into
`Sieve/OmegaSpectralFibre.averagedMeanSquare_moebius_of_omegaBudget`.  That is a parameter
optimisation over quantities that are now all explicit.

### Bricks 92–93 — the integral Halász–Montgomery with a restricted support (2026-08-20)

`Sieve/HalaszMontgomerySupport`, built, axiom-clean, wired.

| theorem | content |
|-|-|
| `supportKernel S v = ∑_{n∈S} n^{iv}` | the Gram kernel of a **restricted** support |
| `setIntegral_normSq_dirPoly_eq_dual_support` | the duality identity with the sum restricted to the support |
| `setIntegral_normSq_dirPoly_sq_le_support` | Cauchy–Schwarz over the support |
| `sum_normSq_dualCoeff_support_eq` | the dual energy over the support is the **restricted-kernel** double integral |
| **`setIntegral_normSq_dirPoly_le_HM_support`** | `∫_E‖A‖² ≤ M·∑_{n∈S}‖a_n‖²` with `M` a row/column mass of `supportKernel S`, not of `plainKernel N` |
| `norm_supportKernel_le_card` | `‖supportKernel S v‖ ≤ #S` |
| **`setIntegral_norm_supportKernel_le`** | the row mass from a two-regime bound: `∫_E‖K(t−u)‖du ≤ 2v₀·#S + 2T·G` whenever `‖K(v)‖ ≤ G` for `\|v\| ≥ v₀` |

**Why this was needed.**  `Sieve/HalaszMontgomeryIntegral` bounds the mean square by the row mass of
`plainKernel N`, i.e. of the kernel of *all* `n < N`.  For sparse coefficients that is a gross
overestimate: the duality only ever produces the kernel of the support.  For a prime support the
gain is a full logarithm twice — once in `#S` versus `N`, once in the coefficient energy — and that
is precisely the difference between MR's Lemma 9 (integers) and Lemma 11 (primes).

Verified during this session that the difference is not cosmetic: with the integer kernel, the
exceptional half of the ladder costs, **with optimal Cauchy–Schwarz weights**, exactly
`M²(∑_k #B_k·M/R_k)²/π ≍ M²W²` — the full trivial bound, for every choice of the levels `V_k`.
So the `𝒰` half cannot be closed with `Sieve/HalaszMontgomeryIntegral`; it needs the prime kernel,
which is what these two bricks supply and what `Sieve/PrimeBlockTwistBound` (Route-T twisted prime
sum) then bounds in the `hfar` slot.

**Next**: identify `supportKernel` at a prime range with `primeBlockPoly` (they differ by the sign
`μ(p) = −1` and the `2π` rescaling), discharge `hfar` from
`exists_norm_primeBlockPoly_routeT_le`, and run the `𝒰` half of MR §8.3 with the second, large
prime range.

### Brick 94 — the kernel of a prime range identified (2026-08-20)

Appended to `Sieve/HalaszMontgomerySupport`; built and axiom-clean.

| theorem | content |
|-|-|
| `supportKernel_neg`, `norm_supportKernel_neg` | the kernel conjugates under frequency reversal, so the column mass equals the row mass |
| `finSupport B N` | the `Fin N`-indexed support attached to `B ⊆ Icc 1 N` |
| `supportKernel_eq_dirPoly`, `supportKernel_eq_logPoly_one` | the kernel is the Dirichlet/Gallagher polynomial of the indicator of `B` |
| **`supportKernel_eq_sum_unitLogPhase`** | `supportKernel (finSupport B N) v = ∑_{p∈B} p^{2πi(v/2π)}` — for a range of primes this is minus `primeBlockPoly B (v/2π)` (`Sieve/PrimeRangeKernelLargeValues.primeBlockPoly_eq_neg_sum_unitLogPhase`), i.e. exactly what the Route-T twisted prime sum bounds |
| **`setIntegral_normSq_dirPoly_le_HM_phaseSupport`** | the integral Halász–Montgomery bound with the far-field of that phase sum in the `hfar` slot: `∫_E‖A‖² ≤ (2v₀·#B + 2T·G)·∑_{n∈supp}‖a_n‖²` |

**Import discipline.**  The first draft imported `Sieve/PrimeRangeKernelLargeValues` in order to
name `primeBlockPoly`, which drags in the whole Route-T/Ingham stack.  Stating the kernel as the
bare phase sum instead keeps `Sieve/HalaszMontgomerySupport` on light dependencies
(`HalaszMontgomeryIntegral`, `LogPolyRestrict`, `LowHeightPoly`) and leaves the arithmetic input to
the call site.  This matters in practice: with several agents building concurrently the heavy
closure could not be replayed inside a single build window, while the light one builds in 196 s.

### The `𝒰` half: four dead arrangements, and the one that closes (2026-08-20)

Working the exceptional half against the corpus's normalisation (`M ≈ √x`, `δ = fibreWidth ≈ h/√x`,
`Wc ≈ M/h`, `A_ω = ∑_n μ(n)ω_P(n)n^{2πiw}`, target `∫‖K_δ‖²‖A_ω‖² = o(h²W²)`, i.e.
`∫_{|w|≤Wc}‖A_ω‖² = o(M²W²)`), the following are **all dead**, each for a reason worth recording.

**1. Optimal Cauchy–Schwarz over the ladder with `sup|P_k| = #B_k`.**
`∫_𝒰|A_ω|² ≤ (∑_k 1/v_k)(∑_k v_k (#B_k)²∫_𝒰|C_k|²)`; with the irreducible Halász–Montgomery
diagonal `∫_𝒰|C_k|² ≳ N_k²`, `N_k = M/R_k`, the optimal weights give

```text
   (∑_k #B_k N_k)²  =  M²(∑_{p ∈ P} 1/p)²  =  M²W²  —  exactly the trivial bound.
```

`∑_k #B_k N_k = M∑_{p∈P}1/p` is **blocking-independent**: narrowing the blocks (even to MR's width
`1 + 1/H`, `H = P^{1/6−η}`) does not change it, and neither does any choice of the levels `V_k`.
So the frequency partition, which works perfectly on `𝒯₁`, buys nothing here.

**2. Equal weights.**  Worse: `L∑_k(#B_kN_k)² = M²(u−1)²/u` with `u = log z/log z₀`, against
`M²(log u)²`.

**3. Halász–Montgomery on the product `P_kC_k`.**  Diagonal `M·∑_n|c_n|² ≈ ηM²/log R_k`; optimal
weights give `(4M²/η)(√log z − √log z₀)²`, which needs `u → 1` and hence `W → 0`.

**4. Sup on the cofactor, mean square on the prime polynomial — at the *first* range.**  With
`sup|C_k| ≲ N_k e^{−E}`, `E = (log M)^{1/20}` (brick 88c) and the mean value theorem
`∫_{|w|≤Wc}|P_k|² ≈ 2Wc·#B_k`, the total is `4Wc e^{−2E}M²/(η z₀ log z₀)`, larger than the `𝒯₁`
term by the factor `Wc e^{−2E}/(eℓ)`.  Since `Wc = exp(log x/2 − (log x)^β)` and `z₀ =
exp((log x)^{γβ})`, `Wc/z₀ → ∞` for every `β < 1`.  Making `z₀` large enough would force
`log z₀ ≳ log x/2`, i.e. cofactors of length `O(1)`.

**The arrangement that closes: a SECOND Ramaré range above `h`.**  This is what
Matomäki–Radziwiłł §8.3 does, and the reason it escapes is that the moment method bites only when
`log P` is comparable to `log T`.  Take

```text
   log P' = (log x)^{49/50} ,   log Q' = log x/log log x ,   threshold  V'_k = #B'_k·(log x)^{−100} .
```

Then, writing `𝒰' = {w : |P'_k(w)| > V'_k for some k}`:

* **Lemma 8 (moment method).**  `|𝒰'| ≪ Wc^{2 log V/log P'}·V²·exp(2(log Wc/log P')·log log Wc)
  = exp((log x)^{1/50 + o(1)})` — the exponent `2 log V/log P'` is tiny because the *threshold* is
  only polylogarithmic, not because the moment order is large.  This is the step the first range
  cannot perform: there `log R_k ≤ (log x)^{β}` and the same computation returns `|𝒰| ≈ Wc`.
* **On `𝒯'_S`** (`|P'_k| < #B'_k(log x)^{−100}`): `(log x)^{−200}(∑_k #B'_kN'_k)²
  = (log x)^{−200}M²(W')²`, negligible against `M²W²`.
* **On `𝒯'_L`**: `sup|C'_k|²·∫_{𝒯'_L}|P'_k|²` with `sup|C'_k| ≲ N'_k·W·e^{−E}` (brick 89c, the
  factor `W` from the `ω_P` weight) and `∫_{𝒯'_L}|P'_k|² ≲ |𝒰'|(#B'_k)²` (brick 94, prime-support
  Halász–Montgomery, with the measure of `𝒰'` in the row mass).  Optimal weights give
  `W²e^{−2E}|𝒰'|M²(W')²`, so the requirement is

```text
   e^{−2E}·|𝒰'|·(W')² = o(1) ,   i.e.   (log x)^{1/50} < 2·(log x/2)^{1/20} ,   ✓ with room.
```

**The margin comes from brick 88c/89c.**  With Matomäki–Radziwiłł's own cofactor bound
`(log X)^{−1/24}` in place of `exp(−(log x)^{1/20})`, the last line would demand `|𝒰'|`
polylogarithmic, which is false; the corpus's super-polylogarithmic cofactor bound is what makes the
exceptional half comfortable.  Conversely the second range must sit **above** `h`
(`log P' = (log x)^{49/50} > (log x)^β`), which is exactly why no arrangement confined to
`[1,h]` — the Milestone-B family, and the partition applied to it — can work.

**Remaining bricks for `averagedMeanSquare_moebius_scaled'`.**
(95) the second Ramaré split of `A_ω` at `[P',Q']`, with the Buchstab error `1/H + 1/P' + log P'/log Q'`;
(96) `Lemma 8` in the corpus's `shortExceptional` normalisation at a polylogarithmic threshold;
(97) the `𝒯'_S`/`𝒯'_L` split and the two estimates above;
(98) the low-frequency and dyadic-tail pieces (`Sieve/CofactorLowFreqBound`, `Sieve/GallagherDyadicTail`);
(99) assembly into `Sieve/OmegaSpectralFibre.averagedMeanSquare_moebius_of_omegaBudget`.

### Bricks 96–98 — the three glue lemmas of the `𝒰` half (2026-08-20)

All built, axiom-clean, wired.

| module | theorem | content |
|-|-|-|
| `Sieve/Section4RelativeThreshold` | `volume_blockExceptional_le_relative` | Lemma 2.5 at a **relative** threshold `#B·θ`: the measure is `2(T + 4N^k(1+log N^k))·(k/(#B·θ²))^k` |
| | `volume_blockExceptional_le_exp` | the same in exponential form, saving `exp(−k·log(#B·θ²/k))` |
| `Sieve/Section4CofactorSup` | **`setIntegral_normSq_omegaWeighted_le_blocks_cofactorSup`** | the long ladder with the supremum on the **cofactor** and the mean square on the **prime block** — the dual of `Sieve/Section4QSide.setIntegral_normSq_omegaWeighted_le_blocks`, and the only orientation usable on the exceptional set |
| `Sieve/LogPolyIccPrefix` | `logPoly_Icc_eq_sub`, `norm_logPoly_Icc_le_of_prefix` | a cofactor block `Icc lo hi` is a difference of two prefixes, so any uniform prefix bound gives the block bound with a factor two |

The third is what lets brick 88c/89c — stated for prefixes `∑_{n ≤ N}` — be applied to the ladder's
cofactor blocks `geomCofactorBlockAt A₀ B₀ Q η j = Icc ⌈…⌉ ⌊…⌋`.

**Both orientations of the ladder are now available over an arbitrary measurable set**, which is
exactly the `𝒯'_S`/`𝒯'_L` dichotomy:

```text
   on 𝒯'_S = allBlocksSmall  :  Σ_k v_k·(#B_k·θ)²·∫‖C_k‖²      (Section4AllBlocksSmall, θ = (log x)^{−100})
   on 𝒯'_L = someBlockLarge  :  Σ_k v_k·(sup‖C_k‖)²·∫‖P_k‖²     (Section4CofactorSup)
                                 sup‖C_k‖ from brick 89c + LogPolyIccPrefix,
                                 ∫_{𝒰'}‖P_k‖² from brick 94 + Section4RelativeThreshold.
```

**Remaining**: (99) instantiate the two orientations at the second range
`log P' = (log x)^{49/50}`, `log Q' = log x/log log x`, verify the two budgets against `M²W²` as
derived in the design entry above, add the low-frequency and dyadic-tail pieces, and assemble into
`Sieve/OmegaSpectralFibre.averagedMeanSquare_moebius_of_omegaBudget`.

### Brick 99a–b — the Ramaré ladder over a measurable set (2026-08-20)

`Sieve/RamareBlockSplitOn`, built, axiom-clean, wired.

| theorem | content |
|-|-|
| `setIntegral_normSq_ramareBilinear_le_blocks` | the block split of the bilinear form over an arbitrary measurable `E ⊆ Icc (−W) W` |
| `setIntegral_normSq_ramareBilinear_le_geomLadder` | the same for the geometric ladder |
| `setIntegral_normSq_ramareBlock_le_product` | one block as a prime polynomial times a common cofactor, plus the cofactor discrepancy, over `E` |

**Why the set-parametric versions are needed.**  The corpus's Ramaré route to the fibre mean square,
`Sieve/FibreRamareLadderFinal.sum_sq_fibreSum_moebius_le_ramareLadder_final`, is the one that
*avoids Turán–Kubilius entirely* — no `1/W` divides anything and no `(#P)²` error appears, so unlike
`Sieve/OmegaSpectralFibre.omegaBudget` and `Sieve/JointOmegaSpectral.jointOmegaBudget` it does not
force the designated range below `√h`.  (Those two budgets carry `204((#P+1)(#Q+1))²(√x+1)`, whose
quotient by `(W_PW_Q)²h²√x` needs `#P·#Q ≪ W_PW_Q·h`; with the second range at
`log P' = (log x)^{49/50}` that is false, so the joint arrangement cannot host the large range
either.)  But `sum_sq_fibreSum_moebius_le_ramareLadder_final` demands the prime-block bound `ρ`
**pointwise on all of `[−T₀,T₀] \ [−w₀,w₀]`**, which is precisely the Milestone-B hypothesis the
no-go rules out for `β < 9/10`.

Making the ladder set-parametric is what lets that single pointwise hypothesis be replaced by the
`𝒯₁`/`𝒰` dichotomy: on `𝒯₁` the bound holds by definition, on `𝒰` the roles of the two factors are
exchanged (`Sieve/Section4CofactorSup`) and the measure is paid by
`Sieve/Section4RelativeThreshold`.  Remaining in this layer:
`integral_normSq_ramareBlock_geom_le` and `integral_normSq_ramareBilinear_le_ladder_error` over `E`,
then the affine majorant `Sieve/RamareLadderAffine` and finally
`sum_sq_fibreSum_moebius_le_ramareLadder_final` itself.

### Brick 99e — the Ramaré ladder against a frequency partition (2026-08-20)

Two modules, both `lake env lean`-clean, axiom-clean, wired.

**`Sieve/RamarePartitionedLadder`**

| theorem | content |
|-|-|
| `ramareStepDefect` | the per-step ladder defect, named |
| `setIntegral_normSq_ramareBilinear_le_ladder_defect` | the block ladder over a measurable set, in `‖P‖²‖C‖²` form |
| `setIntegral_split_three` | `Icc(−W,W)` is the disjoint union of the low disc, the annulus inside `T`, and the annulus outside |
| **`integral_normSq_blockProduct_set_cofactorSup_le`** | one block over a frequency set with the **cofactor** bounded and the prime polynomial's mean square supplied — the missing dual of `Sieve/BlockProductAnnulus.integral_normSq_blockProduct_set_le` |
| **`integral_normSq_blockProduct_partitioned_le`** | one block over the whole window, split three ways |

**`Sieve/RamareAnnulusPartitioned`**

```text
integral_normSq_ramareBilinear_annulus_partitioned_le :
  ∫_{|w| ≤ W} ‖ramareBilinear P M w‖²
    ≤ 2L·∑_{j<L} ( V_j²·(5π/2·W + 5e/2·⌊M/Q_j⌋)·#C_j          -- annulus ∩ T, prime bounded
                 + Us_j²·J_j                                    -- annulus \ T, cofactor bounded
                 + Vlow_j²·U_j²·2w₀ )                           -- low disc
      + 2·Dfct
```

This is `Sieve/RamareLadderAnnulus.integral_normSq_ramareBilinear_annulus_le` with its single
whole-annulus hypothesis `hann` replaced by the partition: `V_j` holds on `T` **by definition** of
the frequency set, and off `T` the roles are exchanged.  Taking `T` to be the whole window and
`Us = J = 0` recovers the original, so nothing is lost.

**Import discipline (following the earlier lesson).**  The ladder defect is left as a hypothesis
`hErr` rather than discharged by `Sieve/RamareLadderAnnulus.integral_normSq_ramareLadderError_le_defectSum`,
because that module reaches the Route-T/Ingham stack through its affine-majorant layer; the corpus
lemma discharges `hErr` at the call site at no cost.

**What remains for `averagedMeanSquare_moebius_scaled'`:** feed this into
`Sieve/FibreRamareLadderFinal` in place of `integral_normSq_ramareBilinear_ladder_affine` (its
hypotheses `hV`/`hU` become the partitioned ones), instantiate `T = allBlocksSmall` at the second
range `log P' = (log x)^{49/50}` with `V_j = #B_j·(log x)^{−100}`, take `Us_j` from brick 89c through
`Sieve/LogPolyIccPrefix`, `J_j` from brick 94 with the measure from `Sieve/Section4RelativeThreshold`,
and check the three budgets against `M²W²` as derived in the design entry.

### CORRECTION + the architecture that actually closes `1/2 < β < 1`: the DOUBLE Ramaré identity (2026-08-20)

The design entry "The `𝒰` half: four dead arrangements, and the one that closes" is **wrong on its
positive half**, and the error is worth recording exactly, because it also shows what the right
arrangement is.

#### 1. Why a second range *above* `h` cannot be blocked and thresholded

The entry checked only the *diagonal* half of the mean value theorem on `𝒯'_S`,
`(∑_k V_k N_k)² = θ²M²(W')²`.  The mean value theorem also has a **height** half, and it is the one
that constrains the top of the range.  With `V_k = θ#B_k`, `#C_k ≍ ηM/R_k`,

```text
   ∫_{|w| ≤ T} ‖P_k C_k‖²  ≤  V_k²·(5π/2·T + 5e/2·M/R_k)·#C_k ,
```

so the height half, with optimal Cauchy–Schwarz weights, contributes

```text
   (∑_k V_k √(5π T #C_k/2))²  =  (5πT η M/2)·θ²·(∑_k #B_k/√R_k)²
        ≍  T·θ²·η·M·R_max/(log R_max)²      since  ∑_{p ≤ R} p^{-1/2} ≍ 2√R/log R .
```

The Gallagher budget of `Sieve/FibreWindowBridge.averagedMeanSquare_of_gallagherBudget` is optimised
at `W = M/h` and then demands `β_maj = o(M²)` at `T ≍ M/h`, i.e.

```text
   θ²·η·R_max/(h (log R_max)²)  →  0        ⟹        R_max ≲ h · polylog .
```

**Every thresholded, blocked prime range must therefore sit below `h` up to polylogarithmic
factors.**  `log Q' = log x/log log x` violates this by `exp(log x/log log x − (log x)^β)`.

#### 2. Why one range below `h` cannot go below `β = 19/20`

With `R_max ≤ h·polylog` the moment method (Lemma 2.5) gives, for the bottom block `R_min`,

```text
   |𝒰| ≍ exp( log T₀ · C₁ / log R_min ) ,   C₁ = log log R_min + log(1/η) + 2log(1/θ) + log k ≍ log log x ,
```

and `log T₀ ≍ (1/2)log x` always (because `T₀ ≍ M/h` and `h = x^{o(1)}`).  On `𝒰` the only two
orientations both fail:

* `sup‖C_k‖·√(∫_𝒰‖P_k‖²)` with `∫_𝒰‖P_k‖² ≤ |𝒰|(#B_k)²` needs `σ²|𝒰|(W)² → 0`, i.e.
  `log R_min ≳ C₁ log T₀/(2E)`; with the corpus's `E = (log x)^{1/20}` that is
  `log R_min ≳ (log x)^{19/20}log log x`, and `log R_min ≤ log R_max ≤ (log x)^β` forces `β > 19/20`
  (Vinogradov–Korobov's `E = (log x)^{1/3}` would give `β > 2/3`, never `1/2`);
* `sup‖P_k‖·√(∫_𝒰‖C_k‖²)` with Halász–Montgomery returns the irreducible diagonal
  `(∑_k #B_kN_k)² = M²W²` — dead arrangement 1.

So **no single-range arrangement reaches `β = 1/2`, whatever the zero-free region.**  This is a
sharper no-go than the Milestone-B one and supersedes it.

#### 3. The arrangement that does close it

Exposé §4's actual mechanism: **two ranges used for two different purposes.**

```text
   P = primes with  (log x)^{A} ≤ log p ≤ log h                (small range: thresholded, blocked)
   Q = primes with  (log x)^{a}  ≤ log q ≤ (log x)^{b} ,  9/10 < a < b < 1
                                                              (large range: NEVER thresholded)
```

`Q` sits far above `h`, and that is legal **because `Q` is used only on `𝒰`, where there is no
height term at all**: Halász–Montgomery's row mass is `2N + C·|𝒰|`, with the measure of the
exceptional set in place of the height.  Concretely, writing `n = p·q·m`:

| region | `‖P_j‖` | `‖Q_k‖` | `∫‖A_{j,k}‖²` | total |
|-|-|-|-|-|
| `𝒯` = all `P`-blocks small | `θ#B_j` | — (not split off) | mean value theorem | `θ²(5πT₀M·4P_max/(log P_max)² + 2.5M²W_P²)` |
| `𝒰 ∩ {\|w\| ≥ w₀}` | `#B_j` | `ρ#D_k` (Route T) | `(2N + C\|𝒰\|)·N` | `ρ²M²W_P²W_Q²` |
| `{\|w\| ≤ w₀}` | `#B_j` | `#D_k` | `σ²N²`, brick 89c | `2w₀σ²M²W_P²W_Q²` |

with `ρ = exp(−c(log x)^{a−9/10}) → 0` (Route T at `log q ≥ (log x)^a`, `a > 9/10`) and
`σ = exp(−(log N)^{1/20})` (brick 89c, all heights `|τ| ≤ N`).

The three requirements are

```text
   (i)   P_max ≲ h·polylog                       — the height half of the m.v.t. on 𝒯 ;
   (ii)  |𝒰| ≲ min( N_{j,k}/√T₀ , √T₀ )          — so that Halász–Montgomery's row mass is 2N ;
   (iii) W_P = log( log P_max / log P_min ) → ∞  — so that θ·W_P → 0 with θ polylogarithmic.
```

`(ii)` unwinds to `log P_min ≳ 2C₁ ≍ log log x`, i.e. `P_min = (log x)^{O(1)}` — **the exposé's
`(log X)^7`, recovered.**  `(i)` and `(iii)` then say only `log h / log log x → ∞`.  So this
architecture reaches every `h ≥ exp(ω(log log x))`, in particular every `β ∈ (1/2, 1)`, which is
exactly what cards 4 and 5 need.  (Card 3, which needs *every* `h → ∞`, still needs Milestone D.)

#### 4. The one structural brick that is missing: the double Ramaré identity

The corpus's two-range object is the **joint Turán–Kubilius weight** `ω_P·ω_Q`
(`Sieve/JointTuranKubilius`, `Sieve/JointWeightTransfer`), and its budget carries the prime-counting
error `204((#P+1)(#Q+1))²(√x+1)`, which needs `#P·#Q ≪ W_PW_Q·h` — false for `Q` above `h`.  That is
the recorded reason "the joint arrangement cannot host the large range".

The repair is to drop the weight entirely and use **Ramaré's identity twice**: for `n` with a prime
factor in `P` *and* one in `Q`,

```text
   1 = ∑_{p ∈ P, p | n} ∑_{q ∈ Q, q | n}  1/(ω_P(n)·ω_Q(n))
```

exactly — no variance, no `1/W`, no `(#P#Q)²`.  The two discarded classes are the integers with no
prime factor in `P` (density `≍ log P_min/log P_max`) and those with no prime factor in `Q`
(density `≍ (log x)^{a−b}`); both are `o(1)` and both enter through the **mean value theorem on the
rough Dirichlet polynomial**, not through a short-interval sieve — because the whole split now
happens *after* Gallagher, at the level of `logPoly μ (Icc 1 M)`, where
`Sieve/FibreWindowBridge.averagedMeanSquare_of_gallagherBudget` takes over.

**Brick list for `averagedMeanSquare_moebius_scaled'` at `1/2 < β < 1`:**
1. the double Ramaré identity for `μ` on `[1,M]`, with the two rough classes named;
2. the mean value theorem for the two rough polynomials (corpus: `Sieve/LogPolyDirPoly`) and the
   two rough counts (sieve at the level of `[1,M]`, not short intervals);
3. the `P`-block ladder of the double bilinear form, with the `Q`-factor left inside the cofactor
   on `𝒯` and split off on `𝒰`;
4. `𝒯` = `Sieve/Section4AllBlocksSmall.allBlocksSmall` at `θ` polylogarithmic + the mean value
   theorem;
5. `𝒰 ∩` annulus: Route T on the `Q`-block (`Sieve/AnnulusBoundUniform`) + integral
   Halász–Montgomery (`Sieve/HalaszMontgomeryIntegral` + `Sieve/DyadicAffineEnvelope` for `C`) with
   `|𝒰|` from `Sieve/Section4RelativeThreshold`;
6. the disc `|w| ≤ w₀`: brick 89c on the cofactor;
7. assembly through `Sieve/FibreWindowBridge.averagedMeanSquare_of_gallagherBudget`.

Bricks 99a–99f (`Sieve/RamareBlockSplitOn`, `Sieve/RamarePartitionedLadder`,
`Sieve/RamareAnnulusPartitioned`, `Sieve/RamareAffinePartitioned`,
`Sieve/FibreRamarePartitionedFinal`) are the single-range instance of items 3–4 and are reusable
verbatim once the cofactor carries the `Q`-factor.

### Brick 99f — the partitioned ladder reaches the fibre capstone (2026-08-20)

Two modules, `lake env lean`-clean, axiom-clean, wired, `lake build`-verified.

**`Sieve/RamareAffinePartitioned`**

```text
ramarePartSlope M L Q η V Dslope
  = 2L·∑_{j<L} V_j²·(5π/2·#C_j) + 2·Dslope
ramarePartConst M L Q η w₀ V U Vlow Us J Dconst
  = 2L·∑_{j<L} ( V_j²·(5e/2·⌊M/Q_j⌋·#C_j) + Us_j²·J_j + Vlow_j²U_j²·2w₀ ) + 2·Dconst

integral_normSq_ramareBilinear_affine_partitioned_le :
  ∀ W, 1 ≤ W → w₀ ≤ W → W ≤ T₀ →
    ∫_{|w| ≤ W} ‖ramareBilinear P M w‖² ≤ ramarePartSlope·W + ramarePartConst
```

The partition set is intersected with the current window, so a single set `S` stated at the top
height `T₀` serves every window below it: the complement `Icc(−W,W) \ (S ∩ Icc(−W,W))` is
`Icc(−W,W) \ S`, which shrinks with `W`, and the prime mean square `J_j` transfers by monotonicity
of a nonnegative integrand.  The ladder defect is again a hypothesis `hDfct` in affine form
(`Dslope·W + Dconst`), discharged at the call site by
`Sieve/RamareLadderAnnulus.integral_normSq_ramareLadderError_le_defectSum`, which is affine in `W`
with `Dslope = 5π/2·ladderDefectSum` and `Dconst = 5e/2·⌊M(1+η)⌋·ladderDefectSum`.

**`Sieve/FibreRamarePartitionedFinal`**

```text
sum_sq_fibreSum_moebius_le_ramarePartitioned_final :
  ∑_{a ∈ outerBlock x h} (∑_{b ∈ innerFibre x h a} μ b)²
    ≤ 16√x·( 2·fibreWidth²·(slope·G + const)
             + ( 4(slope + 5π/2·M + 5e/2·M²/T₀)/(π²G) + 4·const/(3π²G²) ) )
      + 204(√x + 1) + 2·#outerBlock·(fibreRamareSieveError h z r lam)²
```

This is `Sieve/FibreRamareLadderFinal.sum_sq_fibreSum_moebius_le_ramareLadder_final` with its two
pointwise hypotheses replaced by the frequency partition.  Nothing else in the chain changes:
`Sieve/RamareBilinearKernelBound.integral_kernel_normSq_ramareBilinear_le` and the fibre bridge are
already parametric in the slope and the constant.

Per §3 above this module is the **single-range** capstone; it is superseded for `β < 19/20` by the
double-range architecture, but it is the exact shape that architecture will re-use, with
`ramareBilinear` replaced by the double bilinear form.

### Bricks 100–103 — the two-range architecture, structural layer (2026-08-20)

Four modules, all `lake env lean`-clean, axiom-clean, wired.

| module | theorem | content |
|-|-|-|
| `Sieve/DoubleRamareWeight` | `sum_sum_inv_card_double`, `doubleCore`, `doubleRough`, **`sum_eq_doubleRamare_add_rough`**, `card_doubleRough_le` | Ramaré's identity for two disjoint ranges at once: `∑_{n∈S} f = ∑_{p∈P}∑_{q∈Q}∑_{n : p,q ∣ n} f(n)/(ω_P(n)ω_Q(n)) + ∑_{rough}`, exact |
| `Sieve/RamareRoughSetSplit` | **`setIntegral_normSq_logPoly_moebius_le_ramare_rough`**, `setIntegral_normSq_logPoly_moebius_roughSet_le` | the exact two-way Ramaré decomposition integrated over an **arbitrary measurable frequency set** |
| `Sieve/RamareLadderSupMeanSquare` | `setIntegral_normSq_blockProduct_le_supMeanSquare`, **`setIntegral_normSq_ramareBilinear_le_ladder_supMeanSquare`**, **`setIntegral_normSq_ramareBilinear_le_ladder_sup`** | both orientations of the ladder over a measurable set: prime sup + supplied cofactor mean square (the exceptional one), and prime sup + mean value theorem (the non-exceptional one) |
| `Sieve/MoebiusWindowPartition` | `annulusSmall`, `annulusLarge`, **`integral_Icc_normSq_logPoly_moebius_le_partition`** | the window as disc ⊍ small annulus ⊍ large annulus, each piece a free parameter |

**The design point these four settle.**  The double Ramaré identity turns out *not* to be needed:
because `setIntegral_normSq_logPoly_moebius_le_ramare_rough` is set-parametric, the small range `P`
can be used on `annulusSmall` and the large range `Q` on `annulusLarge`, with each range's rough
class paid only on its own region.  The identity is kept as reusable infrastructure, but the
architecture is *two single splits on two disjoint frequency sets*, which is strictly lighter: no
joint weight, no `ω_Pω_Q` variance, no `(#P#Q)²` prime-counting error, and no double reindexing.

**What the assembly now reduces to.**  With `G = M/h` the Gallagher cutoff and `T₀ = G·ω(1)`, the
majorant `Sieve/FibreWindowBridge.averagedMeanSquare_of_gallagherBudget` consumes can be taken as

```text
   α = 5π/2·M + 5e/2·M²/T₀ ,      β = B := ∫_{|w| ≤ T₀} ‖logPoly μ (Icc 1 M) w‖² ,
```

because the bound is monotone in `T` below `T₀` and the trivial mean value theorem covers `T > T₀`
once `β_triv/T₀ ≤ α`.  So the **entire** remaining analytic content of `1/2 < β < 1` is the single
statement `B = o(M²)`, and `integral_Icc_normSq_logPoly_moebius_le_partition` reduces that to three
independent estimates:

```text
   disc          : brick 88c pointwise on logPoly μ, measure 2w₀ = O(1)
                   (w₀ is a constant: `Sieve/AnnulusBoundUniform` needs only max(τ₀, 16π/3) ≤ 2πw₀)
   annulusSmall  : ladder_sup at the small range, V_j = θ·#B_j by membership in allBlocksSmall
   annulusLarge  : ladder_supMeanSquare at the large range, prime sup from Route T,
                   cofactor mean square from `Sieve/LogPolySetScaling.setIntegral_normSq_logPoly_le_HM`
                   with |𝒰| from `Sieve/Section4RelativeThreshold`
```

### Bricks 104–107 — the two-range window bound, assembled (2026-08-20)

| module | theorem | content |
|-|-|-|
| `Sieve/MoebiusDiscRate` | `sum_range_moebiusTwist_eq_Icc`, **`exists_setIntegral_disc_normSq_logPoly_moebius_le_rate`** | the disc `\|w\| ≤ w₀`: Route T at every frequency below the length of the sum gives `∫ ≤ 2w₀·(K·N·e^{−(log N)^{1/20}})²` |
| `Sieve/RamareRoughSetSplit` (extended) | **`integral_Icc_normSq_roughPoly_le_harmonic`** | the rough polynomial's mean square with the count discharged by Turán: `(5π/2·W + 5e/2·M)·((M + 2\|P\|)/A)`, `A = ∑_{p∈P}1/p` |
| `Sieve/LogPolyWindowHM` | **`setIntegral_normSq_logPoly_le_HM_window`** | integral Halász–Montgomery over a measurable set of **Gallagher** frequencies (the `2π` rescaling absorbed) |
| `Sieve/RamareLadderHM` | `geomCofactorBlock_subset_Icc`, `ladderHMBound`, `setIntegral_normSq_cofactorBlock_le_HM`, **`setIntegral_normSq_ramareBilinear_le_ladder_HM`** | the ladder on the exceptional set: prime sup from arithmetic, cofactor from Halász–Montgomery — **no height term anywhere** |
| `Sieve/MoebiusTwoRangeWindow` | `setIntegral_annulusSmall_normSq_logPoly_moebius_le`, `setIntegral_annulusLarge_normSq_logPoly_moebius_le`, **`integral_Icc_normSq_logPoly_moebius_le_twoRange`** | the whole window, with a low range on `allBlocksSmall` and a high range on its complement |

All five `lake env lean`-clean, axiom-clean `[propext, Classical.choice, Quot.sound]`, wired.

**The shape of the final statement.**

```text
∫_{|w| ≤ W} ‖logPoly μ (Icc 1 M) w‖²
  ≤ Bdisc
    + (1+δ)·L ·∑_{j<L } ( 2 V_j² ·(5π/2·W + 5e/2·⌊M/R_j⌋)·#C_j  + 2 (#B_j )²·defect_j )
      + (1+1/δ)·∫_{|w| ≤ W} ‖rough_P ‖²
    + (1+δ)·L'·∑_{j<L'} ( 2 V'_j²·ladderHMBound M R' η' W |𝒰| j + 2 (#B'_j)²·defect'_j )
      + (1+1/δ)·∫_{|w| ≤ W} ‖rough_P'‖²
```

with `𝒰 = annulusLarge (allBlocksSmall P R η L V W) W w₀`.  Every one of the five groups is now a
named quantity in the tree; what remains is the substitution

```text
   log R ≍ (log x)^{A},  log(R(1+η)^L) = log h ,   V_j = θ·#B_j ,  θ = (log x)^{−A'} ,
   log R' ≍ (log x)^{a}, log(R'(1+η')^{L'}) = (log x)^{b},  9/10 < a < b < 1 ,
   V'_j from `Sieve/AnnulusBoundUniform.exists_annulus_bound_uniform` ,
   |𝒰| from `Sieve/Section4RelativeThreshold.volume_blockExceptional_le_relative` ,
   W = T₀ ≍ (M/h)·ω(1) ,   w₀ = max(τ₀, 16π/3)/(2π)  (a constant) ,
```

and the verification that each group is `o(M²)`.

### Brick 108 — the gate is ONE mean square at ONE height (2026-08-20)

Two modules, `lake env lean`-clean, axiom-clean, wired.

**`Sieve/AffineFromHead`**

```text
integral_Icc_normSq_logPoly_affine_of_head (ha : ∀ n, ‖a n‖ ≤ 1) (hs0 : 0 ∉ s) (hsN : ∀ n ∈ s, n ≤ N)
    (hG : 1 ≤ G) (hGT₀ : G ≤ T₀) (hB0 : 0 ≤ B)
    (hB : ∫_{|w| ≤ T₀} ‖logPoly a s w‖² ≤ B) :
  ∀ T ≥ G,  ∫_{|w| ≤ T} ‖logPoly a s w‖² ≤ (5π/2·#s + 5e/2·N·#s/T₀)·T + B
```

Below `T₀` the mean square is monotone in the height, so the constant `B` already majorises it;
above `T₀` the mean value theorem does, once its height-free term `5e/2·N·#s` is loaded onto the
slope divided by `T₀`.  So Gallagher's "affine majorant at every height" is *equivalent* to a single
bound at a single height.

**`Sieve/MoebiusHeadGate`**

```text
moebiusHeadSlope x h T₀ = 5π/2·⌊√x+h⌋ + 5e/2·⌊√x+h⌋²/T₀

averagedMeanSquare_moebius_of_headBound
    (hgrow : hh → ∞) (hhx : hh ≤ √x)
    (hdata : ∀ᶠ x, 1 ≤ G x ∧ G x ≤ T₀ x ∧ 0 ≤ B x
       ∧ ∫_{|w| ≤ T₀ x} ‖logPoly μ (fibreIndex x (hh x)) w‖² ≤ B x)
    (hlim : (2·fibreWidth²·(slope·G + B) + 4·slope/(π²G) + 4B/(3π²G²)) / hh² → 0) :
  AveragedMeanSquare μ hh
```

**This is the reduction the whole programme was after.**  Every other ingredient — Ramaré, the
ladder, the frequency partition, Halász–Montgomery, Route T — now exists only to produce `B(x)`, and
the parameter analysis says the requirement is

```text
   G ≍ M/h ,   T₀ = G·ω(1) ,   B = o(M²) ,   M = ⌊√x + h⌋ .
```

No slope condition survives: `moebiusHeadSlope ≍ M + M²/T₀ ≍ M·h/ω`, and `4·slope/(π²G·h²) ≍ 1/(ω·h)
→ 0` automatically.

### Bricks 109–110 — the gate is now ONE relative smallness statement (2026-08-20)

**`Sieve/MoebiusHeadBudget`** (`headBudget_le`).  At the optimal Gallagher cutoff `G = M/h` and any
height `T₀ = G·ω` above it, the whole budget of `averagedMeanSquare_of_gallagherBudget` obeys the
completely explicit majorant

```text
   (2δ²·(slope·G + B) + 4·slope/(π²G) + 4B/(3π²G²)) / h²  ≤  90/h + 60/ω + 9·B/M²
```

whenever `δ ≤ 2h/M`, `1 ≤ h`, `1 ≤ ω`, `0 ≤ B`, `0 < M`.  The proof is pure algebra plus
`3 < π ≤ 4` and `e < 2.7182818286`; every occurrence of the slope cancels against `G`.

**`Sieve/MoebiusHeadSmall`** (`headG`, `headT₀`, **`averagedMeanSquare_moebius_of_headSmall`**).

```text
averagedMeanSquare_moebius_of_headSmall
    (hgrow : hh → ∞)
    (hdata : ∀ᶠ x, 4 ≤ x ∧ 1 ≤ hh x ∧ hh x ≤ √x ∧ 1 ≤ ω x ∧ 0 ≤ B x
        ∧ ∫_{|w| ≤ headT₀ x (hh x) (ω x)} ‖logPoly μ (fibreIndex x (hh x)) w‖² ≤ B x)
    (hωgrow : ω → ∞)
    (hrel : B x / ⌊√x + hh x⌋² → 0) :
  AveragedMeanSquare μ hh
```

with `headG x h = ⌊√x+h⌋/h` and `headT₀ x h ω = headG x h · ω`.

**This is the entire Matomäki–Radziwiłł input for cards 3, 4, 5, in one line.**  It is unconditional,
axiom-clean, and holds for *every* window law `hh → ∞` with `hh ≤ √x` — the exponent `β` has
disappeared from the interface.  Whatever `β` a card needs, it needs exactly

```text
   ( ∫_{|w| ≤ (M/h)·ω} ‖∑_{n ≤ M} μ(n)n^{−2πiw}‖² dw ) / M²  →  0 ,   M = ⌊√x + h⌋ ,
```

for some `ω → ∞`, and nothing else.  `Sieve/MoebiusTwoRangeWindow` is the machine that produces that
quantity; the remaining work is the substitution of the two prime ranges and the verification that
each of its five groups is `o(M²)`.

Note the interface also shows what the *existing* `9/10 < β` theorem is spending: nothing in the
Gallagher layer, only in the head bound.

### CORRECTION — the per-block discrepancy is unusable; the ladder must pay it once (2026-08-20)

The first version of `Sieve/RamareLadderSupMeanSquare` and `Sieve/RamareLadderHM` was built on
`Sieve/RamareBlockSplitOn.setIntegral_normSq_ramareBilinear_le_ladder_assembled`, whose discrepancy
is **per block and multiplied by `(#B_j)²`**:

```text
   ramareStepDefect P M Q η W j = 2(#B_j)²·(2(5π/2·W + 5e/2·M)·((1+M)η/R_j + 5 + M/R_j²))
```

Checking that against the budget kills it twice over.  Relative to `M²`, with the block count `L`
in front and `#B_j ≍ ηR_j/log R_j`:

```text
   the (1+M)η/R_j part  →  10L·η·∑_j (#B_j)²/R_j  ≍  η·R_max/log R_max ,
   the M/R_j²   part    →  10L·∑_j (#B_j)²/R_j²   ≍  10L²η²/(log R_max)² = 10 ,
```

so the second is a **constant** — it never vanishes, whatever the parameters — and the first needs
`η ≲ log R_max/R_max`, i.e. a block ratio exponentially small in the top of the range.

The sharp form pays the discrepancy **once**, as a single prime-shifted family
(`ramareLadderError`), and its budget is
`(5π/2·W + 5e/2·⌊M(1+η)⌋)·ladderDefectSum L M Q η` with

```text
   ladderDefectSum ≍ (log M/log R_min)·( Lη²M + 5R_max + M/R_min + 5L ) ,
```

whose quotient by `M²` is `≍ (log M/log R_min)(ηlog R_max + R_max/M + 1/R_min + L/(ηM))` — every
term vanishing for `R_max ≤ h`, `log R_min ≍ log log x`, `η` a small negative power of `log x`.

Both orientation lemmas were rebuilt on
`Sieve/RamareLadderSupMeanSquare.setIntegral_normSq_ramareBilinear_le_ladder_error`, the
set-parametric form of `Sieve/RamareBlockSplit.integral_normSq_ramareBilinear_le_ladder_error`
(its proof is pointwise, so it restricts to any measurable set):

```text
   ∫_E ‖ramareBilinear P M‖²  ≤  2L·∑_{j<L} ∫_E ‖P_j·C_j‖²  +  2·∫_E ‖ramareLadderError‖²
```

and `Sieve/MoebiusTwoRangeWindow` now carries `2∫_{|w|≤W}‖ramareLadderError‖²` in each half instead
of `∑_j ramareStepDefect`.  Rebuilt, axiom-clean, wired.

**Lesson for this lane**: the crude per-block discrepancy is only usable when the prime range is
short; every arrangement that lets the range reach `h` must use `ramareLadderError`.

### Bricks 111–112 — the disc and rough groups, relative to `M²` (2026-08-20)

| theorem | content |
|-|-|
| `Sieve/MoebiusDiscRate.exists_eventually_setIntegral_disc_fibre_le` | the disc bound at the fibre length `√x + h` |
| **`Sieve/MoebiusDiscRate.tendsto_discRelative`** | `2w₀(K·N·e^{−(log N)^{1/20}})²/⌊N⌋² → 0` — the disc group vanishes, `N = √x + h` |
| **`Sieve/MoebiusHeadBudget.roughGroup_le`** | `(5π/2·W + 5e/2·M)·((M + 2\|P\|)/A)/M² ≤ 10W/(AM) + 20W\|P\|/(AM²) + 7/A + 14\|P\|/(AM)` — every term carries `1/A`, so a designated range of divergent harmonic mass makes the rough group vanish |
| `Sieve/RamareRoughSetSplit.integral_Icc_normSq_roughPoly_le_harmonic` | the rough mean square with Turán's count substituted |
| `Sieve/MoebiusTwoRangeWindow.measureReal_annulusLarge_le` | `\|𝒰\| ≤ ∑_k \|shortExceptional (geomBlock …) W (V k)\|` — the moment method's entry point |

Remaining for `averagedMeanSquare_moebius_scaled'` at `1/2 < β < 1`: the two **ladder** groups —
`2L∑_j V_j²(5π/2·W + 5e/2·⌊M/R_j⌋)#C_j` on the small half and `2L'∑_j V'_j²·ladderHMBound` on the
large half — plus `2∫‖ramareLadderError‖²` for each range, at the parameters
`log R_min ≍ log log x`, `R_max = h`, `V_j = θ·#B_j`, `θ = (log x)^{−A}`, `9/10 < a < b < 1`.

### The Halász–Montgomery kernel constant is the real bottleneck (2026-08-20)

Checking the large half of the two-range budget against
`Sieve/PlainKernelMass.setIntegral_normSq_dirPoly_le_explicit` shows its constant is fatal:

```text
   row mass  ≤  2N + ( (log₂N + 1)·214√(2T) + 3072·N )·|E| ,
```

the `3072·N` coming from `sup_{|v| ≥ 1}` of the affine envelope `214√|v| + 3072N/√|v|`, attained at
`|v| = 1`.  So the bound only improves on the trivial `|E|·N²` when `|E| ≲ 1/3072`, and the moment
method can **never** deliver that: with `k` forced by `N^k ≲ T` one has `k·log R_j ≈ log T`, so the
saving is `T^{−1+o(1)}` and `|𝒰| ≈ T^{o(1)} ≥ 1` always.  Optimising the near-band width `v₀` does
not help either — balancing `2v₀N` against `3072N|E|/√v₀` gives `≍ N|E|^{2/3}`, still growing.

**What the classical Lemma 2.6 has that this does not** is the *Kuzmin–Landau* decay `N/|v|`, not
`N/√|v|`.  The corpus already owns it per dyadic block —
`Sieve/HuxleyLogPhase.norm_logPhase_dyadic_le_kuzminLandau : ≤ 6π·2^j/t + 1`, valid exactly when
`3t ≤ 4π·2^j` — but `Sieve/LogPhaseKernelBound.norm_sum_Icc_logPhase_le` assembles the blocks with
the *second-derivative* envelope alone, which is the right choice for the small blocks and the wrong
one for the large ones.  Splitting the dyadic range at `2^{J₀} ≍ 3t/(4π)`:

```text
   ∑_{j < J₀}  (214√t + 1536·2^j/√t)   ≤  214·J₀·√t + 4608√t/π ,
   ∑_{j ≥ J₀}  (6π·2^j/t + 1)          ≤  12π·M/t + log₂M + 1 ,
```

giving the classical shape

```text
   ‖∑_{n ≤ M} n^{−it}‖  ≤  214(log₂ t + 1)√t + 1466√t + 12π·M/t + log₂M + 1     (t ≥ 1)
```

and hence the row mass `2N + 24π·N·log(2T) + (214 log₂(2T) + 1466)√(2T)·|E| + (log₂N+1)|E|`, i.e.
Lemma 2.6's `N log T + |E|√T log T`.  The HM condition then reads `|𝒰| ≲ N/√T`, which unwinds — as
in the design entry — to `log R_min ≳ 2C₁ ≍ log log x`, and *that* is what makes the low range's
bottom polylogarithmic and the whole architecture reach `β > 1/2`.

**So the next brick is the Kuzmin–Landau assembly of the log-phase kernel**, and it is the last
place where a constant, rather than an idea, is missing.

### Brick 113 — the Kuzmin–Landau kernel bound (2026-08-20)

`Sieve/LogPhaseKernelKuzminLandau`, `lake env lean`-clean, axiom-clean, wired, built.

```text
norm_dyadic_block_le_kuzminLandau (M j) (ht : 0 < t) (hKL : 3t ≤ 4π·2^j) :
  ‖∑_{n ∈ [1,M], ⌊log₂ n⌋ = j} n^{−it}‖ ≤ 6π·2^j/t + 1

norm_sum_Icc_logPhase_le_split (hM : 1 ≤ M) (ht : 0 < t) (J₀) (hJ₀ : 3t ≤ 4π·2^{J₀}) :
  ‖∑_{n ≤ M} n^{−it}‖
    ≤ J₀·214√t + 1536·2·2^{J₀}/√t + ( 12π·M/t + log₂M + 1 )
```

The dyadic range is split at the Kuzmin–Landau threshold: below `J₀` the second-derivative envelope
(`Sieve/LogPhaseKernelBound.norm_dyadic_block_le_affine`) and its geometric sum
`∑_{j<J₀}2^j ≤ 2^{J₀}`; at and above `J₀`, `Sieve/MaynardKuzminLandauFactor`'s prefix
Kuzmin–Landau, whose geometric sum `∑_{j ≤ log₂M}2^j ≤ 2M` is what produces `12π·M/t`.  The cpow
form is reached through `Sieve/LogPhaseBlock.natCast_cpow_neg_I_mul`.

**The point**: taking `2^{J₀} ≍ t` gives `‖K(v)‖ ≲ (log|v|)√|v| + N/|v|` for `|v| ≥ 1` — the
reciprocal decay the row mass needs — in place of the old `N/√|v|`, whose supremum `3072N` made
Halász–Montgomery vacuous for every exceptional set of measure `≥ 1`.

**Remaining in this layer** (each a named, independent step):
1. the pointwise kernel bound at a free frequency: instantiate `J₀ = ⌈log₂|v|⌉` to get
   `‖plainKernel N v‖ ≤ 214(log₂|v|+1)√|v| + 6144√|v| + 12π·N/|v| + log₂N + 1`;
2. the row mass with a reciprocal far bound: `∫_E‖K(t−u)‖du ≤ 2N + A·|E| + B·2log(2T)` from
   `‖K(v)‖ ≤ A + B/|v|` on `|v| ≥ 1` — the only new measure-theoretic input is
   `∫_{1 ≤ |v| ≤ 2T} dv/|v| = 2log(2T)`;
3. propagate through `Sieve/PlainKernelMass`, `Sieve/LogPolySetScaling`, `Sieve/LogPolyWindowHM`,
   `Sieve/RamareLadderHM.ladderHMBound`;
4. then the large half's budget reads `ρ²·(N log T + |𝒰|√T log T)/N²`-shaped, and the condition is
   `|𝒰| ≲ N/√T`, i.e. `log R_min ≳ 2C₁ ≍ log log x` — the polylogarithmic bottom that makes
   `β > 1/2` reachable.

### Bricks 114–117 — Lemma 2.6 rebuilt on Kuzmin–Landau (2026-08-20)

Five modules, all `lake env lean`-clean, axiom-clean, wired, built; the two-range capstone now runs
on them.

| module | theorem | content |
|-|-|-|
| `Sieve/PlainKernelRecip` | `exists_pow_two_bracket`, `norm_sum_Icc_logPhase_le_recip`, **`norm_plainKernel_le_recip`** | the split point taken at the frequency (`J₀ = log₂⌈t⌉ + 1`, so `t ≤ 2^{J₀} ≤ 4t`): `‖K(v)‖ ≤ 214(log₂⌈\|v\|⌉+1)√\|v\| + 12288√\|v\| + 12π·N/\|v\| + log₂N + 1` |
| `Sieve/KernelRowMassRecip` | `recipMajorant`, `integral_recipMajorant_symm`, `setIntegral_recipMajorant_le`, **`setIntegral_norm_kernel_le_recip`** | the row mass for a far bound `A + B/\|v\|`: `2N + A·\|E\| + 4B·log(2+2T)` |
| `Sieve/PlainKernelMassRecip` | `plainKernelFarConst`, `plainKernel_row_mass_recip`, **`setIntegral_normSq_dirPoly_le_recip`** | Lemma 2.6 with the Kuzmin–Landau constants |
| `Sieve/LogPolyWindowHMRecip` | `hmMassRecip`, **`setIntegral_normSq_logPoly_le_HM_window_recip`** | the same over a measurable set of **Gallagher** frequencies |
| `Sieve/RamareLadderHMRecip` | `ladderHMBoundRecip`, **`setIntegral_normSq_ramareBilinear_le_ladder_HM_recip`** | the exceptional-set ladder on the new mass |

The continuous majorant `2/(1+\|x\|)` of `1/\|x\|` is what makes the row mass elementary: it needs no
indicator, so `∫_{-c}^{c} 2/(1+\|x\|)dx = 4 log(1+c)` follows from `integral_inv_of_pos` after one
reflection and one translation, and the far mass is bounded by moving the window to
`Ioc (t−(2T+1)) (t+(2T+1))`, which contains `E` whenever `E, t ⊆ [−T, T]`.

**Net effect.**  The large half of `Sieve/MoebiusTwoRangeWindow` now reads

```text
   2L'·∑_{j<L'} V'_j²·(2π)⁻¹·( 2N'_j + 48π·N'_j·log(2 + 4πW) + C(2πW, N'_j)·2π·|𝒰| )·#C'_j
     + 2∫‖ramareLadderError‖² ,
   C(T, N) = 214(log₂⌈2T⌉+1)√(2T) + 12288√(2T) + log₂N + 1 ,
```

so the exceptional set enters through `√W·log W·|𝒰|` instead of `N·|𝒰|`, and the condition for the
diagonal to dominate is `|𝒰| ≲ N'_j/√W` — attainable by the moment method exactly when
`log R_min ≳ 2C₁ ≍ log log x`.

**What is left**: the numerology.  Choose
`log R_min ≍ K·log log x`, `R_max = h`, `V_j = θ·#B_j` with `θ = (log x)^{−A}`,
`log R'_min = (log x)^a`, `log R'_max = (log x)^b`, `9/10 < a < b < 1`, `η, η'` small powers of
`log x`, `W = T₀ = (M/h)·ω`, `ω = log log x`, `δ → 0` slowly; then check the five groups of
`integral_Icc_normSq_logPoly_moebius_le_twoRange` against `M²` — every one of them is now a
finite expression in named corpus quantities.

### Brick 118 — both ladder groups reduced to three aggregates (2026-08-20)

`Sieve/LadderGroupBudget`, `lake env lean`-clean, axiom-clean, wired, built.

The two ladder groups of the two-range budget differ only in which mass multiplies the cofactor;
both depend on the block data through exactly three aggregates,

```text
   S ≥ ∑_j #B_j·N_j ,      Bmax ≥ #B_j ,      PP ≥ ∑_j #B_j ,
```

with `N_j = ⌊M/R_j⌋` the cofactor length and `#C_j ≤ N_j + 1`.

```text
ladderGroup_mvt_le :
  2L·∑_{j<L} (θ·B_j)²·((5π/2·W + 5e/2·N_j)·C_j)
    ≤ 5π·L·θ²·W·(Bmax·S + Bmax·PP) + 5e·L·θ²·(S² + Bmax·S)

ladderGroup_hm_inner_le :
  ∑_{j<L} (ρ·B_j)²·((2N_j + FC_j·v + 48π·N_j·Λ)·C_j)
    ≤ ρ²·( (2 + 48π·Λ)·(S² + Bmax·S) + FCmax·v·(Bmax·S + Bmax·PP) )
```

The only inequality of substance is `∑_j (B_jN_j)² ≤ (∑_j B_jN_j)² = S²`
(`Finset.sum_sq_le_sq_sum_of_nonneg`); the rest is `∑_j B_j²N_j ≤ Bmax·S` and
`∑_j B_j² ≤ Bmax·PP`.

**Where the three aggregates come from.**  `S`: because `p ≤ R_j(1+η)` on a block,
`#B_j/R_j ≤ (1+η)∑_{p∈B_j}1/p`, so `∑_j #B_j·(M/R_j) ≤ (1+η)·M·∑_{p∈P}1/p`
(`Sieve/BlockMassCompare.sum_card_geomBlock_div_le`).  `Bmax`: `Sieve/LadderErrorBudget.card_geomBlock_le`
and `Sieve/GeomBlockCardBound.card_geomBlock_le_endpoint`.  `PP`: `Sieve/LadderStepMajorant.sum_card_geomBlock_eq`
(the blocks partition the designated primes).

**Numerology now checkable term by term.**  At `θ = (log x)^{−A}`, `η = (log x)^{−c}`,
`R_max = h`, `W = (M/h)·log log x`:
`5e·L·θ²·S² / M² ≍ θ²·(log h/η)·(log log x)² → 0` for `2A > β + c`, and
`5π·L·θ²·W·Bmax·S / M² ≍ θ²·(log log x)² → 0`.
For the high range with `ρ = exp(−c(log x)^{a−9/10})`, both HM terms carry `ρ²`, which beats every
power of `log x`; the `FCmax·v` term additionally carries `|𝒰|·√W·log W·R'_max/√M`, and
`R'_max/√M = exp((log x)^b − (log x)/4) → 0` swallows it.

### Bricks 119–120 — the aggregates, and both ladder groups in closed form (2026-08-20)

`Sieve/LadderAggregates` and `Sieve/LargeLadderGroup`, both `lake env lean`-clean, axiom-clean,
wired, built.

| theorem | content |
|-|-|
| `card_geomCofactorBlock_le` | `#C_j ≤ ⌊M/R_j⌋ + 1` (the block is an `Icc` ending there) |
| `sum_card_geomBlock_mul_floor_le` | **the aggregate `S`**: `∑_j #B_j·⌊M/R_j⌋ ≤ (1+η)·M·∑_{p∈P}1/p` |
| `card_geomBlock_le_top` | **the aggregate `Bmax`**: `#B_j ≤ R(1+η)^L·η + 1` |
| `sum_card_geomBlock_le_card` | **the aggregate `PP`**: `∑_j #B_j = #P` |
| `rangeHarmonic`, **`smallLadderGroup_le`** | the small half's group, entirely in `(1+η)M·H`, `R(1+η)^Lη+1`, `#P` |
| `plainKernelFarConst_mono`, `floor_div_le_bottom`, **`largeLadderGroup_le`** | the large half's group, same three aggregates, with the kernel's far constant made uniform by monotonicity in the cofactor length |

So both ladder groups of `integral_Icc_normSq_logPoly_moebius_le_twoRange` are now closed-form
expressions in

```text
   L , θ (or ρ) , W , η , R , M , H = ∑_{p ∈ P} 1/p , #P , |𝒰| ,
```

with no sums left. Together with `Sieve/MoebiusHeadBudget.roughGroup_le` (rough groups),
`Sieve/MoebiusDiscRate.tendsto_discRelative` (disc) and
`Sieve/RamareLadderAnnulus.integral_normSq_ramareLadderError_le_defectSum` +
`Sieve/LadderAffineBounds.ladderDefectSum_le` (the two defect groups), every one of the seven groups
of the two-range bound is a named finite expression.

**What is left**: substitute the schedule, bound `H`, `#P`, `R(1+η)^Lη`, `L`, `|𝒰|` at it, and take
the limit.

### Bricks 121–122 — the schedule, and the harmonic mass of a WIDE range (2026-08-20)

**`Sieve/TwoRangeSchedule`** (axiom-clean, wired) fixes the two-range schedule as named functions:

```text
   lowBase K x   = ⌈(log x)^K⌉            (the polylogarithmic bottom — the whole point)
   lowEta c x    = (log x)^{−c}           lowTheta A x = (log x)^{−A}
   highBase a x  = ⌈exp((log x)^a)⌉       highEta c' x = (log x)^{−c'}
   twoRangeLength β x = ⌊√x + h⌋          twoRangeCut β x = ⌊√x+h⌋ / h
   twoRangeTop β x    = twoRangeCut · log log x
   twoRangeDelta x    = (log log x)^{−1/2}
```

with `tendsto_lowEta`, `tendsto_highEta`, `tendsto_lowTheta`, `tendsto_twoRangeDelta`,
`one_le_lowBase`, `lowBase_bounds`.

The split weight `δ = (log log x)^{−1/2}` is forced from both sides: the rough groups carry
`(1 + 1/δ)·O(1/H)` with `H ≍ log log x`, so `δ` must beat `1/log log x`; the ladder groups carry
`(1+δ)`, so `δ` must stay bounded.  A square root of `log log` sits in between.

**`Sieve/PrimeRangeLogLogMass`** (axiom-clean, wired):

```text
sum_inv_primesRange_le_logLog_diff (h₀ : 2 ≤ z₀) (hz : z₀ ≤ z) :
  ∑_{z₀ < p ≤ z} 1/p  ≤  log log z − log log z₀ + 2·(2c₁ + 1/2)/log z₀
```

This is the input the ladder groups need and the one the corpus did **not** have in usable form:
`Sieve/PrimeRangeMertensMass.sum_inv_primesRange_le` gives `(log z − log z₀ + 2c)/log z₀`, sharp for
a narrow band but catastrophic here — at the schedule it reads `(log x)^β/(K log log x)` instead of
`β·log log x`.  The fix is `Sieve/MertensSecondSharp.abs_mertensS_sub_logLog_sub_const_le`, whose
error **decays**: the two Meissel–Mertens constants cancel exactly and only `O(1/log z₀)` survives.

At the schedule this gives `H ≤ β·log log x − log(K log log x) + O(1/log log x) ≤ β·log log x`,
which is what makes `θ²·L·H² = (log x)^{β+c−2A}(log log x)² → 0` for `2A > β + c`.

### Bricks 123–124 — the step count, and the mixed limits (2026-08-20)

**`Sieve/TwoRangeSchedule`** (extended): `lowSteps`, `highSteps`, `log_one_add_ge_half_self`, and

```text
lowSteps_le (hK : 0 ≤ K) (hc : 0 < c) :
  ∀ᶠ x,  #steps of the low ladder  ≤  2·(log x)^{β + c}
```

from `log(1+η) ≥ η/2` (proved locally from `Real.add_one_le_exp` at `−η/(1+η)`, so the module stays
off `Sieve/SpectralParameters`'s heavy closure) and `log(h/R) ≤ (log x)^β`.  The degenerate case
`R > h` is handled: the floor is then `0`.

**`Sieve/TwoRangeLimits`**: the two mixed limits every group needs.

```text
tendsto_logRpow_mul_logLogPow (he : e < 0) (k) :
  (log x)^e·(log log x)^k → 0
tendsto_logLogPow_mul_expNeg (hs : 0 < s) (k) (e) :
  (log x)^e·(log log x)^k·exp(−(log x)^s) → 0
```

The first absorbs a power of `log log` into an arbitrarily small power of `log` via
`Real.log_le_rpow_div` at `ε = (−e)/(2(k+1))`, leaving the exponent `e(k+2)/(2k+2) < 0`.  The second
is the same absorption against the zero-free-region saving, where any power of `log x` loses.

Together with the corpus's `tendsto_rpow_log_mul_cardLength_div_sqrt` (window against `√x`) and
`tendsto_rpow_log_div_siftStart`, these are all the limits the seven groups need.

### Brick 125 — the structural hypotheses at the schedule (2026-08-20)

`Sieve/TwoRangeScheduleFacts`, `lake env lean`-clean, axiom-clean, wired, built.

| theorem | content |
|-|-|
| `lowTop`, `highTop` | the two ladder tops, `⌊R·(1+η)^L⌋` |
| `primesRange_ladder_bounds_self` | a light restatement of `Sieve/SpectralHeadBound.primesRange_ladder_bounds` (that module reaches the `Ω`-weighted annulus stack for a ten-line fact) |
| `lowRange_bounds`, `highRange_bounds` | **the hypothesis `hP` of the two-range theorem**, for both ranges |
| `lowBase_lt_cardLength` | `(log x)^K < h` — the polylogarithmic bottom really is below the window |
| **`lowTop_le_cardLength`** | `R·(1+η)^L ≤ h`: the low ladder does not overshoot the window length |

The last one is where the floor in `lowSteps` is paid: `L·log(1+η) ≤ log(h/R)` gives
`(1+η)^L ≤ h/R` after exponentiating, and `lowBase_lt_cardLength` rules out the degenerate branch
where the base already exceeds the window (there the bound is simply false, so the hypothesis is
needed rather than a case split).

**Running state of the substitution.**

| input | module |
|-|-|
| schedule + vanishing | `TwoRangeSchedule` |
| `L ≤ 2(log x)^{β+c}` | `TwoRangeSchedule.lowSteps_le` |
| `H ≤ log log z − log log z₀ + O(1/log z₀)` | `PrimeRangeLogLogMass` |
| mixed limits | `TwoRangeLimits` |
| `Bmax`, `PP`, `#C_j ≤ N_j+1` | `LadderAggregates` |
| `hP`, `hPprime`, ladder ⊆ window | `TwoRangeScheduleFacts` |
| **remaining** | `1 ≤ W`, `1 ≤ L`, `hNj`, the Route-T instantiation `hbound'`, then the seven limits |

### Brick 126 — the window and the step count at the schedule (2026-08-20)

`Sieve/TwoRangeScheduleFacts` (extended), axiom-clean, wired, built.

| theorem | content |
|-|-|
| `one_le_twoRangeCut` | `1 ≤ ⌊√x+h⌋/h` — the Gallagher cutoff exceeds one (a light restatement of `Sieve/BudgetSubstitution.one_le_gallagherCut`, whose module reaches the whole `Ω`-budget stack) |
| `one_le_twoRangeTop` | `1 ≤ W = cut·log log x` |
| **`one_le_lowSteps`** | `1 ≤ L`, i.e. `log(h/R) ≥ log(1+η)` |

The last is the first place the *polylogarithmic* bottom has to be paid for explicitly: with
`R ≤ 2(log x)^K` one has `log R ≤ log 2 + K·log log x`, and the step exists as soon as

```text
   (log x)^β − log 2 − K·log log x ≥ 1 ,
```

which follows from `Sieve/TwoRangeLimits.tendsto_logRpow_mul_logLogPow` at `ε = 1/(2(K+1))`
together with `(log x)^β ≥ 4`.  So `K` may be any constant — it never competes with `β`, which is
exactly the property the two-range architecture was built to have.

**Remaining structural hypotheses**: `hNj` (the high cofactors are non-empty, i.e.
`R'(1+η')^{L'} ≤ M`) and `1 ≤ L'`; then the Route-T instantiation `hbound'`, then the seven limits.

### Bricks 127–128, and a CORRECTION: the disc radius is not a constant (2026-08-20)

**Brick 127 — the high ladder at the schedule.**  `Sieve/TwoRangeScheduleFacts` (extended),
axiom-clean, wired, built.

| theorem | content |
|-|-|
| `highBase_bounds` | `exp((log x)^a) ≤ R' ≤ 2·exp((log x)^a)` |
| `one_le_highSteps` | `1 ≤ L'`, from `(log x)^b − (log x)^a → ∞` |
| `highLadder_le` | `R'·(1+η')^{L'} ≤ 2·exp((log x)^b)` |
| **`one_le_floor_div_highLadder`** | **the hypothesis `hNj`**: every high cofactor length `⌊M/R'_j⌋` is at least one, because `2·exp((log x)^b) ≤ ⌊√x + h⌋` |

**Brick 128 — the bridge to the annulus.**
`Sieve/MoebiusWindowPartition.annulusLarge_subset_annulus : annulusLarge T W w₀ ⊆ Icc(−W,W) \ Icc(−w₀,w₀)`,
so `Sieve/AnnulusBoundUniform.exists_annulus_bound_uniform` applies verbatim on the large half with
`T₀ := W`.

**CORRECTION — `w₀` is a growing quantity, and that is what pins `a < 19/20`.**  Instantiating the
Route-T majorant showed my earlier reading of `max τ₀ (16π/3) ≤ 2π w₀` as "`w₀` is a constant" is
wrong: that is only the *lower* bound the lemma demands.  The majorant itself,

```text
   relScaledMajorant Ctot D Lx Hmaj μ q t₀ xmin
     = Ctot·D²·( Lx²/t₀ + Hmaj·(e^{−μq} + 1/t₀²) )/(2π) + (log 2 + Lx)/D + 2Lx/√xmin ,
```

has a term `Ctot·D²·Lx²/(2π t₀)` **with no exponential factor**.  With `Lx ≍ (log x)^b` and the
target saving `ρ`, the third summand forces `D ≥ Lx/ρ` and then the first forces

```text
   t₀ = 2π w₀  ≥  D²Lx²/ρ  =  Lx⁴/ρ³ .
```

So with `ρ = exp(−s(log x)^{a−9/10})` (which is what `e^{−μq}` delivers, `μ ≍ (log T₀)^{−9/10}`,
`q = (log x)^a`) one needs

```text
   w₀ ≍ (log x)^{4b}·exp(3s(log x)^{a−9/10}) ,
```

recorded as `twoRangeDisc a b s`, with `twoRangeRho a s = exp(−s(log x)^{a−9/10})` and
`tendsto_logRpow_mul_twoRangeRho` (the saving beats every power of `log x`).

**The consequence is a new, binding constraint.**  The disc group is `≍ w₀·exp(−2(log M)^{1/20})`
relative to `M²`, so it vanishes only when

```text
   log w₀ ≍ 3s(log x)^{a−9/10}  <  2((1/2)log x)^{1/20} ,   i.e.   a − 9/10 < 1/20 ,
```

that is **`9/10 < a < 19/20`** — e.g. `a = 0.92`, `b = 0.99`.  The margin is exactly the corpus's
Route-T rate exponent `1/20` of bricks 88c/89c; MR's own `(log X)^{−1/24}` would leave none.  This
supersedes the earlier note "`w₀` is a constant" in the brick-113 entry.

**Still open in the substitution**: the schedule instantiation of `relScaledMajorant` (choose
`D = Lx/ρ`, `t₀ = 2πw₀`, `Lx = log 2 + (log x)^b`, `q = (log x)^a`, `xmin = exp((log x)^a)`,
`μ = min delta (routeTWidthPolylogLower A (2πT₀))/2`, `Hmaj` at equality) and the seven group
limits.

### Brick 129 — the harmonic mass at the schedule (2026-08-20)

`Sieve/TwoRangeScheduleFacts.lowRange_harmonic_le` (axiom-clean, wired, built):

```text
   (hK : 1 ≤ K) (hc : 0 < c) (hβ : 0 < β) :
      ∀ᶠ x,  ∑_{p ∈ primesRange (lowBase K x) (lowTop K c β x)} 1/p  ≤  β · log log x
```

This is the aggregate `H` of `Sieve/LadderAggregates.smallLadderGroup_le` evaluated at the schedule,
and it is the step that makes the ladder groups cost only a *power of `log log`* rather than a power
of `log`.  The three ingredients: `log(lowTop) ≤ (log x)^β` (from `lowTop_le_cardLength`), so
`log log lowTop ≤ β·log log x`; `log(lowBase) ≥ K·log log x`, so `log log lowBase ≥ log(K log log x)
→ ∞`; and `Sieve/PrimeRangeLogLogMass`'s decaying error `2(2c₁+1/2)/log(lowBase) → 0`.  The negative
`− log log lowBase` swallows the error, leaving exactly `β·log log x`.

### CORRECTION TO THE CORRECTION — `w₀` is polylogarithmic, and `a < 19/20` is not a constraint (2026-08-20)

The previous entry's conclusion (`w₀ ≍ exp(3s(log x)^{a−9/10})`, hence `a < 19/20`) is **wrong**, and
the error was mine, not the corpus's: I required the Route-T saving `ρ` to be *super*-polylogarithmic.
It does not have to be.  The large half's leading group is

```text
   2L'·(2π)⁻¹·ρ²·(2 + 48π·Λ)·(S'² + Bmax'·S') / M²  ≍  ρ²·L'·Λ·(H')²
     ≍  ρ²·(log x)^{b+c'}·(log x)·(log log x)² ,
```

so all that is needed is `ρ² ≪ (log x)^{−(b+c'+1)}`, i.e. **`ρ = (log x)^{−A₃}` for a large enough
constant `A₃`**.  With that target the majorant closes at *polylogarithmic* parameters:

```text
   Lx = log 2 + (log x)^b ,        D  = (log x)^{b+A₃+1}  (so (log 2 + Lx)/D ≤ ρ/3) ,
   t₀ = (log x)^{4b+3A₃+3}         (so Ctot·D²·Lx²/(2π t₀) ≤ ρ/3) ,
   q  = (log x)^a ,  xmin = exp((log x)^a) ,  Hmaj ≍ (log x)^{19/10} ,
```

and the two remaining summands, `Ctot·D²·Hmaj·e^{−μq}/(2π)` and `2Lx/√xmin`, carry a genuine
exponential — `e^{−μq} = exp(−(log x)^{a−9/10})` with `μ ≍ (log T₀)^{−9/10}` — which beats every
power of `log x` as soon as `a > 9/10`.  So the disc radius is

```text
   w₀ = t₀/(2π) = (log x)^{4b+3A₃+3}/(2π) ,
```

polylogarithmic, exactly like the corpus's own `annulusStart β x = (log x)^13` in milestone A, and
the disc group `w₀·exp(−2(log M)^{1/20})` vanishes with room to spare.  **There is no upper
constraint on `a`.**

Recorded in `Sieve/TwoRangeSchedule` as `twoRangeRho A₃`, `twoRangeWidth b A₃`, `twoRangeDisc b A₃`,
`twoRangeLx b`, with `tendsto_twoRangeRho` and `tendsto_logRpow_mul_expSaving` (the exponential
factor beats every power of the logarithm).  The entry above it, and its claim `9/10 < a < 19/20`,
are superseded.

**The constraint set, final:**

```text
   9/10 < a < b < 1 ,   c > 1 + β ,   c' > 1 + b − a ,   2A > β + c ,
   K > max( 2(3 + c + 2A), (c+1)/2 ) ,   2A₃ > b + c' + 1 ,
   ω = log log x ,   δ = (log log x)^{−1/2} ,   β ∈ (0,1) free.
```

### Brick 130 — the Route-T relative majorant at the schedule (2026-08-20)

`Sieve/TwoRangeMajorant`, `lake env lean`-clean, axiom-clean, wired, built.

```text
twoRangeT₀ b A₃ x = (log x)^{4b+3A₃+3}

twoRangeMajTerms b A₃ Ctot μ q xmin x
  = Ctot/(2π)·( 4(log x)^{−A₃−1} + (log x)^{2b+2A₃+4}·e^{−μq} + (log x)^{−(6b+4A₃+2)} )
    + 3(log x)^{−A₃−1} + 4·(log x)^b/√xmin

relScaledMajorant_le_twoRangeMajTerms :
  ∀ᶠ x, relScaledMajorant Ctot (twoRangeWidth b A₃ x) (twoRangeLx b x) (Hmaj x) (μ x) (q x)
          (twoRangeT₀ b A₃ x) (xmin x)   ≤   twoRangeMajTerms b A₃ Ctot μ q xmin x

tendsto_logRpow_mul_relScaledMajorant (he1 : e < A₃ + 1) (he3 : e < 6b + 4A₃ + 2) … :
  (log x)^e · relScaledMajorant … → 0
```

under only two arithmetic hypotheses, which are exactly the two places the mathematics enters:

```text
   (log x)^{2b+2A₃+4+e}·e^{−μ q} → 0      (the zero-free region: μ ≍ (log T₀)^{−9/10}, q = (log x)^a)
   (log x)^{b+e}/√xmin → 0                (the bottom of the high range: xmin = exp((log x)^a))
```

Everything else is a negative power of the logarithm.  The five summands are bounded term by term
using `log x ≥ 1`: `Lx ≤ 2(log x)^b`, `D² = (log x)^{2b+2A₃+2}`, `t₀² = (log x)^{8b+6A₃+6}`, giving
`4(log x)^{−A₃−1}`, `(log x)^{2b+2A₃+4}e^{−μq}`, `(log x)^{−(6b+4A₃+2)}`, `3(log x)^{−A₃−1}` and
`4(log x)^b/√xmin` respectively.

The margin condition `e < A₃ + 1` is what the large half consumes: it needs
`ρ²·(log x)^{b+c'+1}(log log x)² → 0`, i.e. `e = (b+c'+1)/2 + o(1)`, so `A₃ > (b+c'−1)/2` suffices.

### Brick 131 — the Route-T side conditions at the schedule (2026-08-20)

`Sieve/TwoRangeRouteT`, `lake env lean`-clean, axiom-clean, wired, built.

The remaining Route-T parameters are fixed,

```text
   twoRangeQ a x     = (log x)^a                    (the contour frequency)
   twoRangeXmin a x  = exp((log x)^a)               (its lower cutoff)
   twoRangeMu A δ β x    = min δ (routeTWidthPolylogLower A (2π·W)) / 2
   twoRangeHmaj A b A₃ β x = 1/(2π·w₀) + log(3·2π·W/2) / routeTWidthPolylogLower A (2π·W)
```

and the side conditions of `Sieve/AnnulusBoundUniform.exists_annulus_bound_uniform` are discharged:

| theorem | hypothesis |
|-|-|
| `highBlockTop_bounds` | every block top lies between `R'` and `2·exp((log x)^b)` |
| **`highBlockTop_log_bounds`** | `hLxj`, `hqj`, `hxminj` — the three logarithmic comparisons |
| `one_le_twoRangeWidth` | `1 ≤ D` |
| `twoRangeDisc_ge` | `max τ₀ (16π/3) ≤ 2π·w₀` |
| **`twoRangeDisc_le_top`** | `w₀ ≤ T₀` |
| `twoRangeMu_nonneg`, `twoRangeMu_le` | `0 ≤ μ`, `μ ≤ min δ (…)/2` |
| `twoRangeXmin_pos`, `twoRangeQ_nonneg` | `0 < xmin`, `0 ≤ q` |

The two structural observations that make all of them elementary: the base `R'` is a **natural
number**, so `⌊R'(1+η')^{j+1}⌋ ≥ R'` and every block top is at least the base; and
`highLadder_le` puts every block top below `2·exp((log x)^b)`.  The disc/window comparison
`w₀ ≤ T₀` is the one place the window enters — `w₀` is polylogarithmic while
`T₀ ≍ (√x/h)·log log x`, and the gap is `tendsto_rpow_log_mul_cardLength_div_sqrt`.

**What is left of the whole substitution**: assemble these into the `hbound'` of
`integral_Icc_normSq_logPoly_moebius_le_twoRange` (one application of `exists_annulus_bound_uniform`
with the fourteen slots now all filled), and then the five remaining group limits, each a
composition of `Sieve/TwoRangeLimits`, `Sieve/LadderGroupBudget`, `Sieve/MoebiusHeadBudget.roughGroup_le`
and `Sieve/TwoRangeMajorant.tendsto_logRpow_mul_relScaledMajorant`.
