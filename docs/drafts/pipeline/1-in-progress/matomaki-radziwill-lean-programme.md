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
