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
  and the prime analogue.  **This is a hard prerequisite, and the corpus does not have it** — see
  "The Vinogradov–Korobov prerequisite" below.
- **Lemma 2.4 (mean value theorem).** `∫_{-T}^{T}|∑_{n≤N}a(n)n^{it}|²dt ≪ (T+N)∑|a(n)|²`.
  **CORPUS** — `Sieve/DirichletIntegralBound.integral_normSq_dirPoly_le` and the symmetric form
  `Sieve/LogPolyDirPoly.integral_Icc_normSq_dirPoly_symm_le`.
- **Lemma 2.5 (large values for prime polynomials).** `|E| ≪ (V² log T)^{1+log T/log P}`.
  Open; the corpus's sixth-moment layer (`Sieve/DirichletSixthMoment*.lean`) is the same device at a
  fixed exponent and should generalise to the `k`-th power used here.
- **Lemma 2.6 (Halász–Montgomery).** `∫_E|∑_{n≤N}a(n)n^{it}|²dt ≪ (N+|E|T^{1/2}log T)∑|a(n)|²`.
  Open.
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
