# Matomäki–Radziwiłł in Lean — the shared Route-E analytic gate

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
