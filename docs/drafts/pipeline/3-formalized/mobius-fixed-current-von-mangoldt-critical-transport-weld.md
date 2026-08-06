# The Mobius multiplier fixed current is critically transport-equivalent to the Euler prime current

- **ID:** `mobius-fixed-current-von-mangoldt-critical-transport-weld`
- **Stage:** 3-formalized
- **Type:** THEOREM (paper) / HT FIXED-CURRENT SOURCE WELD
- **Scientific status:** `[PROVED HERE] [LITERATURE NOVELTY OPEN] [NOT AN RH PROOF]`
- **Parents:**
  - `mobius-critical-fisher-tangent-hilbert-lift.md`
  - `mobius-incidence-clock-gini-fisher-four-unit-law.md`
  - `complementary-packet-critical-gini-isometry.md`
  - `new_scientific_knowledge/charged-scalar-core-fixed-current-torsor.md`
  - `../3-formalized/infinite-mobius-critical-boundary-layer-product.md`
  - `not_new_scientific_knowledge/infinitesimal-euler-leakage-cauchy-energy-threshold.md`
- **Statement:** The logarithmic current of the exact signed all-prime Mobius multiplier is the
  positive von Mangoldt prime-power law.  Its critical logarithmic clock and the squarefree
  Mobius clock converge in `W_1` to the same mean-one exponential law.  Their canonical monotone
  coupling therefore has vanishing critical complementary-packet cost, so the four-unit packet
  geometry transfers to the actual Euler current before Gamma/Sonin completion.

## Two source clocks

Let `sigma>1`, `epsilon=sigma-1`, and

```text
Z(sigma)=sum_d mu(d)^2d^(-sigma)=zeta(sigma)/zeta(2sigma),
P_sigma(d)=mu(d)^2d^(-sigma)/Z(sigma).                    (1)
```

Let

```text
A(s)=-zeta'(s)/zeta(s)=sum_(n>=2)Lambda(n)n^(-s),
nu_sigma(n)=Lambda(n)n^(-sigma)/A(sigma).                 (2)
```

Both `(1)` and `(2)` are probability laws.  Write `H_P=log d` under `P_sigma` and `H_E=log n`
under `nu_sigma`.

The exact moving-aperture signed Mobius multiplier is

```text
tau_sigma(u)
 =zeta(2sigma)/[zeta(sigma)zeta(sigma+u epsilon)],
u>=0.                                                     (3)
```

The parameter `epsilon` is the thermal/escape clock of `(1)`.  A second parameter `alpha` will
denote the normal Suzuki shift.  They must not be identified before taking the normal derivative.

## Exact fixed-current theorem `[PROVED HERE]`

The logarithmic current of `(3)` is

```text
J_sigma(u)
 =partial_u log tau_sigma(u)
 =epsilon A(sigma+u epsilon)
 =epsilon A(sigma) E_nu[exp(-u epsilon H_E)].             (4)
```

This is an exact identity on `sigma>1`.  In particular, scalar factors in `(3)` which are
independent of `u` disappear, while every nonconstant rational or Euler gauge contributes its
own logarithmic current.  Thus `(4)` is canonical under the multiplicative torsor freedom and is
not rational-gauge blind.

Equation `(4)` is the source-specific instance of the fixed-current mechanism proved for charged
scalar HT cores: a multiplicative amplitude has a gauge-invariant logarithmic current.  Here that
current is not abstract.  It is exactly the positive von Mangoldt law `(2)`.

The same current is the normal derivative of Suzuki's packet connection.  If

```text
c_alpha(n)=n^alpha product_(p|n)(1-p^(-2alpha)),          (5)
```

then the already proved coefficient identity gives

```text
partial_alpha c_alpha(n)|_(alpha=0)=2Lambda(n).           (6)
```

Consequently the logarithmic current of the signed multiplier and the normal current of the
complementary packet connection are the same arithmetic object.

## Diagonal-collapse no-go and positive two-clock law

For fixed `Re s>1`, absolute convergence gives

```text
C(alpha,s)=sum_n c_alpha(n)n^(-s)
          =zeta(s-alpha)/zeta(s+alpha),
partial_alpha C(alpha,s)|_(alpha=0)=2A(s).               (7)
```

On the old diagonal `s=1+2alpha`, however,

```text
C(alpha,1+2alpha)
 =zeta(1+alpha)/zeta(1+3alpha) ->3.                      (8)
```

Thus normal differentiation and critical diagonal summation do not commute.  In fact
`[C(alpha,1+2alpha)-1]/(2alpha)` diverges, whereas the correctly ordered normalized derivative is

```text
(epsilon/2) partial_alpha C(alpha,1+epsilon)|_(alpha=0)
 =epsilon A(1+epsilon) ->1.                              (9)
```

**No-go:** tying the normal Suzuki shift to the thermal critical parameter before differentiation
does not recover the von Mangoldt current.

**Positive theorem:** the HT source has two geometrically distinct clocks.  The normal fixed
current is obtained by `alpha->0` at fixed `epsilon`; only then may the escaping thermal limit
`epsilon->0` be taken.  This order is source-forced by `(7)`--`(9)`.

## Common exponential boundary law `[PROVED HERE]`

Set

```text
X_P=epsilon H_P,
X_E=epsilon H_E.                                         (10)
```

For every `u>=0`, the Laplace transforms are

```text
E[exp(-uX_P)]
 =Z(sigma+u epsilon)/Z(sigma) ->1/(1+u),

E[exp(-uX_E)]
 =A(sigma+u epsilon)/A(sigma) ->1/(1+u).                 (11)
```

The first limit is the proved squarefree critical boundary-layer theorem.  For the second, the
simple pole of zeta gives

```text
A(1+x)=1/x+O(1).                                         (12)
```

The limiting transform in `(11)` is that of `Exp(1)`, so both variables converge weakly to the
mean-one exponential law.  Their first moments also converge:

```text
E[X_P]=-epsilon Z'(sigma)/Z(sigma) ->1,
E[X_E]=-epsilon A'(sigma)/A(sigma) ->1.                  (13)
```

For `(13)`, use the residue-unit expansion of `Z` and differentiate `(12)`, which gives
`A'(1+x)=-x^(-2)+O(1)`.  Weak convergence on the half-line plus convergence of first moments is
equivalent to `W_1` convergence.  Therefore

```text
W_1(Law(X_P),Exp(1))->0,
W_1(Law(X_E),Exp(1))->0,
W_1(Law(X_P),Law(X_E))->0.                               (14)
```

Let `pi_sigma` be the monotone quantile coupling of the two laws.  It is determined by `(1)` and
`(2)` alone and satisfies

```text
epsilon E_(pi_sigma)|H_P-H_E|->0.                        (15)
```

The same argument at second order gives more.  The residue expansions imply

```text
E[X_P^2]->2,
E[X_E^2]=epsilon^2 A''(sigma)/A(sigma)->2.               (15a)
```

Hence both laws converge to `Exp(1)` in `W_2`.  For the same monotone coupling,

```text
epsilon^2 E_(pi_sigma)|H_P-H_E|^2->0.                    (15b)
```

In particular their centered thermal scores are coupled in `L2`:

```text
epsilon[(H_P-E H_P)-(H_E-E H_E)]->0                     (15c)
```

in the joint `L2` space.  The fixed-current transport therefore identifies the full critical
Fisher tangent, not only the ground clock distribution and its Gini energy.

## Prime-current four-unit law `[PROVED HERE]`

If `H_E'` is an independent copy of `H_E`, then `W_1` convergence and `(13)` imply uniform
integrability of the pairwise distance.  Hence

```text
epsilon E|H_E-H_E'|->E|Y-Y'|=1,
Y,Y' iid Exp(1).                                         (16)
```

Thus the von Mangoldt current has its own canonical four-unit incidence energy

```text
E^Euler_sigma=4epsilon E|H_E-H_E'|->4.                  (17)
```

This is not a fitted copy of the squarefree law.  It is obtained from the logarithmic current of
the exact signed multiplier `(3)` and independently calibrated by `(16)`.

## Vanishing complementary-packet transport cost `[PROVED HERE]`

Put `omega=epsilon/2` and let `B_h` be the complementary affine packet.  Its squared distance is

```text
||B_h-B_k||_2^2=D_omega(|h-k|),
D_omega(a)<=C+a/(1+omega)^2                              (18)
```

with `C` uniform near `omega=0`.  The monotone coupling `(15)` and `(18)` give

```text
epsilon E_(pi_sigma)||B_(H_P)-B_(H_E)||_2^2->0.          (19)
```

Take two independent copies of the coupling and define the two edge fields

```text
G_P=2(B_(H_P')-B_(H_P)),
G_E=2(B_(H_E')-B_(H_E)).                                 (20)
```

The elementary parallelogram bound and `(19)` imply

```text
epsilon E||G_P-G_E||_2^2->0.                             (21)
```

The squarefree packet theorem gives `epsilon E||G_P||^2->4`; equations `(16)` and `(18)` give the
same limit for `G_E`.  Hence `(21)` is an asymptotic isometry of the complete source packet
fields, not merely equality of two scalar limits.

Entrywise Gamma multiplication has norm tending to one and Sonin compression is contractive.
Applying them to the common coupling preserves `(21)` and the upper budget:

```text
limsup epsilon E||Q_Sonin G_Gamma G_E||_2^2<=4.          (22)
```

Thus the four-unit packet geometry has been transferred to the actual positive Euler current
before any Xi divisor expansion.

## RH contribution and exact remaining seam

The infinitesimal completed source is already known exactly:

```text
partial_alpha Theta_alpha(z)|_(alpha=0)
 =-2 Xi'(s)/Xi(s),
s=1/2-iz,                                                (23)
```

and `(6)` is its prime-power leg before Gamma completion.  Equations `(4)`, `(6)`, and `(19)`--`(22)`
therefore remove two ambiguities from the RH route:

1. the anti-causal normal readout must be the logarithmic fixed current, not an arbitrary
   contraction of the squarefree projection;
2. the metric source presented to that readout can be the Euler prime-current packet field with
   no loss of critical four-unit energy.

The remaining theorem is a single operator statement.  On the common Gamma/Sonin charged graph,
prove that the anti-causal fixed-current codifferential taking the completed Euler packet edge
field to the contour-jump part of `(23)` is closed and nonexpansive.  This is not proved here; its
output is the RH-bearing profile `ell_E`.

## No-go and positive HT consequences

### 1. One-clock diagonalization fails

Equation `(8)` disproves the diagonal shortcut.

**Positive HT statement:** tangential escape and normal constraint response can be independent
clocks even when a one-parameter specialization exists.  The invariant current is recovered only
by the ordered normal derivative.

### 2. Metric orientation is not enough

The squarefree and Euler laws are asymptotically indistinguishable in `W_1` and in packet energy,
but only the Euler law is the fixed current of the source multiplier.

**Positive HT statement:** a critical metric class may contain several asymptotically isometric
realizations, while a logarithmic current selects a distinguished source orientation inside that
class.

### 3. Bounded scalar overlap readouts collapse

The overlap `(3)` is of order `epsilon^2` on the moving aperture, while its logarithmic current has
a nonzero limit.  Extracting the current from the amplitude is therefore singular in the ordinary
Hilbert norm.

**Positive HT statement:** the charged graph is not optional decoration.  It is the natural
rigged norm in which a vanishing multiplicative torsor amplitude retains a finite fixed current.

## Novelty and anti-theatre gate

The ingredients `-zeta'/zeta=sum Lambda(n)n^(-s)`, Laplace-transform convergence, `W_1`
convergence by first moments, monotone coupling, and logarithmic-current invariance are standard
parents.  Targeted external searches found no statement combining the exact Mobius multiplier
current `(4)`, the two-clock noncommutation `(7)`--`(9)`, the squarefree/von-Mangoldt critical
transport `(14)`--`(15)`, and the complementary-packet asymptotic isometry `(19)`--`(22)`.

That negative search is not a novelty declaration.  The card remains `LITERATURE NOVELTY OPEN`.
The theorem is not an RH proof because it does not establish the charged anti-causal
codifferential estimate.

## Gates

- [x] exact Mobius multiplier logarithmic current computed
- [x] current identified with the positive von Mangoldt law
- [x] packet normal derivative identified with the same current
- [x] diagonal one-clock shortcut falsified exactly
- [x] ordered two-clock law proved
- [x] squarefree and Euler critical clocks proved `W_1`-equivalent
- [x] squarefree and Euler critical Fisher scores proved `W_2`-equivalent
- [x] canonical monotone coupling constructed
- [x] prime-current four-unit Gini law proved
- [x] complementary packet transport cost proved vanishing
- [x] Gamma/Sonin upper budget transferred to the Euler current
- [x] formalize the fixed-current identities in Lean
- [x] formalize the transport identities `(14)`--`(22)` in Lean
- [ ] prove the charged anti-causal codifferential is nonexpansive
- [ ] identify its graph limit with `ell_E`
- [ ] independent specialist literature audit
- [ ] RH

## Lean formalization (fixed-current layer)

`formal/GaloisForLFunctions/RHTower/MobiusFixedCurrentVonMangoldt.lean` (imported by
`GaloisForLFunctions.RHTower`; builds clean; every result axiom-clean).

| Card item | Lean name |
|---|---|
| the von Mangoldt current `A(s) = -ζ′/ζ(s)` | `RHTower.vonMangoldtCurrent` |
| the moving multiplier `(3)` `τ_σ(u) = ζ(2σ)/[ζ(σ)ζ(σ+uε)]` | `RHTower.mobiusMovingMultiplier` |
| **`(4)`** the fixed current `∂_u τ = ε·A(σ+uε)·τ`, i.e. `logDeriv τ (u) = ε·A(σ+uε)` | `RHTower.hasDerivAt_mobiusMovingMultiplier`, `RHTower.logDeriv_mobiusMovingMultiplier` |
| the packet series `C(α,s) = ζ(s-α)/ζ(s+α)` | `RHTower.suzukiPacketDirichlet` |
| **`(7)`** `∂_α C(α,s)\|₀ = 2A(s)` on `re s > 1` | `RHTower.hasDerivAt_suzukiPacketDirichlet` |
| **`(8)`** the diagonal collapse `C(α,1+2α) → 3` | `RHTower.tendsto_suzukiPacketDirichlet_diagonal` |
| **`(9)`/`(12)`** `cε·A(1+cε) → 1` for every scale `c > 0` | `RHTower.tendsto_mul_vonMangoldtCurrent_scaled` |
| **`(11)`** `A(1+(1+u)ε)/A(1+ε) → 1/(1+u)` — the mean-one exponential Laplace transform | `RHTower.tendsto_eulerClockLaplace` |
| the derivative residue `(s-1)²A′(s) → -1` | `RHTower.tendsto_sub_one_sq_mul_deriv_vonMangoldtCurrent` |
| **`(13)`** `-εA′(1+ε)/A(1+ε) → 1` — the first moment of the critical Euler clock | `RHTower.tendsto_eulerClockFirstMoment` |
| the second derivative residue `(s-1)³A″(s) → 2` | `RHTower.tendsto_sub_one_cube_mul_deriv2_vonMangoldtCurrent` |
| **`(15a)`** `ε²A″(1+ε)/A(1+ε) → 2` — the second moment of the critical Euler clock | `RHTower.tendsto_eulerClockSecondMoment` |

`(6)` is already in the corpus as `hasDerivAt_suzukiShiftedCoefficient`
(`∂_α c_α(n)\|₀ = 2Λ(n)`), and the squarefree half of `(11)` as
`RHTower.tendsto_squarefreeMobiusBoundaryLayerLaplace`.  The no-go `(8)` and the ordered two-clock
law `(7)`--`(9)` are therefore machine-checked in full.

## Lean formalization (transport layer, in progress)

`formal/GaloisForLFunctions/HTGeometry/HalfLineTransportDistance.lean` (imported by
`GaloisForLFunctions.HTGeometry`; builds clean; every result axiom-clean).

Mathlib carries no Wasserstein distance and no quantile coupling, so the transport layer is being
built from scratch.  The first block is the `W₁` machinery for laws on `[0,∞)`, where the transport
distance is the `L¹` distance of the survival functions.

| Card item | Lean name |
|---|---|
| survival function `S_μ(t) = μ(t,∞)` and its monotonicity/measurability | `HTGeometry.survival`, `antitone_survival`, `measurable_survival` |
| the half-line transport distance `W₁(μ,ν) = ∫₀^∞ \|S_μ - S_ν\|` | `HTGeometry.halfLineW1` |
| layer cake: `∫₀^∞ S_μ = E[X]` for a half-line law | `HTGeometry.integral_survival_eq_mean` |
| integrability of the survival function under a finite mean | `HTGeometry.integrableOn_survival` |
| **the convergence criterion**: pointwise survival convergence + convergence of first moments ⇒ `W₁ → 0` | `HTGeometry.tendsto_halfLineW1_of_tendsto_survival` |
| triangle inequality | `HTGeometry.halfLineW1_triangle` |
| **`(14)`, third line**: two families converging to one limit law have vanishing mutual `W₁` | `HTGeometry.tendsto_halfLineW1_pair` |
| the reference law `Exp(1)`: survival `e^{-t}`, half-line support, finite mean, mean one | `HTGeometry.survival_expMeasure_one`, `expMeasure_one_nonneg_ae`, `integrable_id_expMeasure_one`, `integral_id_expMeasure_one` |

The convergence criterion replaces the usual compactness/uniform-integrability argument by an exact
cancellation: `|S - T| = S + T - 2 min S T`, the minimum is dominated by the limit survival
function, so dominated convergence sends its integral to the limit mean while the two outer
integrals are the two means, and the three limits cancel.  This is the statement the card's `(14)`
needs, in the form that consumes exactly the proved inputs `(11)` and `(13)`.

`formal/GaloisForLFunctions/HTGeometry/QuantileCoupling.lean` builds the coupling half.  Mathlib
carries `cdf` but no quantile function and no inverse-transform sampling, so both are built here.

| Card item | Lean name |
|---|---|
| the quantile (generalized inverse distribution) function | `HTGeometry.quantile` |
| its defining set is nonempty and bounded below | `quantileSet_nonempty`, `quantileSet_bddBelow` |
| the set contains its infimum (right continuity passes the inequality to the boundary) | `le_cdf_quantile` |
| **the Galois connection** `quantile μ p ≤ x ↔ p ≤ cdf μ x` on `0 < p < 1` | `quantile_le_iff` |
| measurability of the quantile | `measurable_quantile` |
| **inverse transform sampling**: the quantile pushes the uniform law on `(0,1)` to the law | `map_quantile_eq` |
| **the monotone coupling `π_σ` of `(15)`** | `HTGeometry.monotoneCoupling` |
| its marginals are the two laws | `map_fst_monotoneCoupling`, `map_snd_monotoneCoupling` |
| the mean as a quantile integral, `∫₀¹ Q_μ = E[X]` | `integral_quantile_eq_mean` |
| **its transport cost** `E_π\|X-Y\| = ∫₀¹ \|Q_μ - Q_ν\|` | `integral_monotoneCoupling_abs_sub`, `lintegral_dist_monotoneCoupling` |

So the canonical monotone coupling of `(15)` now exists in Lean with its correct marginals, and its
cost is expressed as an integral of the two quantile functions — the quantity `(15)` asserts tends
to zero.  That limit is now also proved, conditionally only on the two analytic inputs the card
already supplies:

| Card item | Lean name |
|---|---|
| Scheffé cancellation: nonnegative integrands converging a.e. with converging integrals converge in `L¹` | `tendsto_integral_abs_sub_of_tendsto` |
| the quantile of a half-line law is nonnegative | `quantile_nonneg` |
| a finite mean makes the quantile integrable | `integrableOn_quantile` |
| **`(15)` criterion**: a.e. quantile convergence + convergence of means ⇒ vanishing coupling cost | `tendsto_integral_monotoneCoupling_abs_sub` |
| quantile convergence from distribution convergence at a level of strict increase | `tendsto_quantile_of_tendsto_cdf` |
| the exponential distribution function crosses each level exactly once | `cdf_expMeasure_one_lt_of_lt`, `lt_cdf_expMeasure_one_of_lt` |
| the exponential quantile `Q(p) = -log(1-p)` | `quantile_expMeasure_one` |
| quantile convergence to `Exp(1)` | `tendsto_quantile_expMeasure_one` |
| the exponential law charges no negative half line | `expMeasure_one_Iio_zero` |
| **`(15)` against `Exp(1)`**: distribution convergence to `Exp(1)` + means → 1 ⇒ vanishing monotone-coupling cost | `tendsto_integral_monotoneCoupling_expMeasure_one` |

The last statement is exactly the shape of `(15)`: it consumes pointwise convergence of the two
critical distribution functions to that of `Exp(1)` — which is what `(11)` gives once the Laplace
continuity theorem is available — together with the first-moment convergence `(13)`, already proved
in the fixed-current layer.

`formal/GaloisForLFunctions/HTGeometry/DiscreteHalfLineLaw.lean` builds the carrier for the two
clock laws `(1)` and `(2)`.  Both are weighted point laws: the points are logarithms of integers
and the weights are the normalized Dirichlet coefficients.

| Card item | Lean name |
|---|---|
| the law of a countable weighted point family | `HTGeometry.weightedPointLaw` |
| its measure of a set, and its total mass | `weightedPointLaw_apply`, `weightedPointLaw_univ` |
| total mass one makes it a law | `isProbabilityMeasure_weightedPointLaw` |
| its integrals are weighted sums | `lintegral_weightedPointLaw`, `integral_weightedPointLaw` |
| logarithmic points give a half-line law | `weightedPointLaw_Iio_zero` |
| its survival function | `survival_weightedPointLaw` |
| **its Laplace transform** — a Dirichlet series at a shifted abscissa for logarithmic points | `lintegral_exp_neg_weightedPointLaw`, `integral_exp_neg_weightedPointLaw` |
| **its mean** | `integral_id_weightedPointLaw` |

So `P_σ` of `(1)` and `ν_σ` of `(2)` are now instances of one construction whose Laplace transform
and mean are the weighted sums the card computes; what is left for item 1 is the arithmetic
identification of those sums with `Z(σ+uε)/Z(σ)`, `A(σ+uε)/A(σ)` and their logarithmic derivatives.

`formal/GaloisForLFunctions/HTGeometry/CompactMomentWeakConvergence.lean` builds the compact half
of the Laplace continuity theorem: on a compact interval the moments determine and control a law.

| Card item | Lean name |
|---|---|
| a continuous function on a compact space is integrable against a finite measure | `integrable_continuousMap` |
| integration depends continuously on the law | `continuous_integral_real_continuousMap` |
| the integral is bounded by the uniform norm | `abs_integral_continuousMap_le` |
| polynomial integrals are moment combinations | `integral_polynomial_eq_sum` |
| **moments determine a law on a compact interval** | `probabilityMeasure_ext_of_integral_pow_eq` |
| **moment convergence forces weak convergence** | `probabilityMeasure_tendsto_of_integral_pow_tendsto` |

The density step is used directly rather than through a closed-kernel argument: a continuous
function is uniformly approximated by a polynomial (Stone--Weierstrass, `polynomialFunctions_closure_eq_top`),
and each integral is bounded by the uniform norm, so the difference of the two integral functionals
is below every tolerance.  Weak convergence then follows from compactness of the space of laws on a
compact space together with uniqueness of cluster points.

`formal/GaloisForLFunctions/HTGeometry/ExponentialCompactification.lean` and
`.../LaplaceContinuityHalfLine.lean` close item 2, the Laplace continuity theorem.

| Card item | Lean name |
|---|---|
| the compactification `y = e^{-x}` of the half line | `HTGeometry.expProj`, `continuous_expProj`, `coe_expProj_of_nonneg` |
| the compactified law | `expPush`, `expPushProb` |
| **the Laplace transform at `u = k` is the `k`-th moment of the compactified law** | `integral_pow_expPush` |
| **Laplace convergence compactifies to weak convergence** | `tendsto_expPushProb_of_tendsto_laplace` |
| the exponential law has no atoms | `expMeasure_one_singleton` |
| the tail `(-∞,t]` corresponds to the upper set `{y ≥ e^{-t}}` | `expTailSet`, `expPush_expTailSet` |
| that upper set has a one-point frontier, of zero limit mass | `frontier_expTailSet_subset`, `expPush_frontier_expTailSet` |
| **`(11)` ⇒ distribution convergence**: Laplace convergence at every natural argument forces pointwise convergence of the distribution functions | `tendsto_cdf_expMeasure_one_of_tendsto_laplace` |
| **`(11)` + `(13)` ⇒ `(15)`** | `tendsto_integral_monotoneCoupling_of_tendsto_laplace` |

The last statement is the card's transport claim in closed form: half-line laws whose Laplace
transforms converge to those of `Exp(1)` and whose means converge to one have monotone couplings
with vanishing cost.  Its two hypotheses are exactly `(11)` and `(13)`.

`formal/GaloisForLFunctions/HTGeometry/LogClockLaw.lean` turns an arithmetic weight into a clock.

| Card item | Lean name |
|---|---|
| the clock law of a weight on the integers, placed at logarithmic points | `HTGeometry.logClockLaw` |
| total mass one makes it a law | `isProbabilityMeasure_logClockLaw` |
| it is carried by the half line | `logClockLaw_Iio_zero` |
| **its Laplace transform is the Dirichlet series at the shifted abscissa** | `integral_exp_neg_logClockLaw` |
| **its mean is the logarithmically weighted Dirichlet sum** | `integral_id_logClockLaw` |
| **`(11)` + `(13)` ⇒ `(15)` for arithmetic clocks** | `tendsto_integral_monotoneCoupling_logClock` |

The last statement is the card's transport claim stated directly in arithmetic terms: if the
Dirichlet series of a family of weights converges at every natural shift to the Laplace transform
of `Exp(1)`, and the logarithmically weighted means converge to one, then the monotone couplings of
the clocks with `Exp(1)` have vanishing cost.

`formal/GaloisForLFunctions/HTGeometry/RealDirichletSeries.lean` builds the Euler clock itself.

| Card item | Lean name |
|---|---|
| a real `L`-series at a real abscissa is the real Dirichlet sum | `lseriesTerm_ofReal`, `ofReal_tsum_eq_lseries` |
| summability of the real von Mangoldt Dirichlet series past abscissa one | `summable_vonMangoldt_rpow` |
| **`(2)`/`(4)`: the real von Mangoldt Dirichlet sum is the von Mangoldt current `A(σ) = -ζ′/ζ(σ)`** | `ofReal_tsum_vonMangoldt_eq` |
| positivity of that sum | `tsum_vonMangoldt_rpow_pos` |
| **`(2)`: the Euler clock weight `ν_σ(n) = Λ(n)n^{-σ}/A(σ)` and its total mass one** | `eulerClockWeight`, `tsum_eulerClockWeight` |
| the Euler clock law, a law on the half line | `eulerClockLaw`, `isProbabilityMeasure_eulerClockLaw`, `eulerClockLaw_Iio_zero` |
| **`(11)`: its Laplace transform is `A(σ+u)/A(σ)`** | `integral_exp_neg_eulerClockLaw` |
| integrability against a discrete law is summability of the weighted values | `integrable_weightedPointLaw` |
| summability of the logarithmically weighted von Mangoldt series | `summable_vonMangoldt_logMul_rpow` |
| **the logarithmically weighted von Mangoldt sum is `-A′(σ)`** | `ofReal_tsum_vonMangoldt_logMul_eq` |
| the Euler clock has a finite mean | `integrable_id_eulerClockLaw` |
| **`(13)`: its mean is `-A′(σ)/A(σ)`** | `integral_id_eulerClockLaw` |

The Euler clock of `(2)` therefore exists in Lean as an honest probability law on `[0,∞)`, its
Laplace transform is the ratio of von Mangoldt currents that `(11)` studies, and that current is
identified with `-ζ′/ζ` through mathlib's `L`-series theory.

`formal/GaloisForLFunctions/HTGeometry/SquarefreeClockLaw.lean` generalizes the clock construction
and builds the ground clock `(1)`.

| Card item | Lean name |
|---|---|
| the Dirichlet total, normalized clock weight, and clock law of an arithmetic weight | `dirichletTotal`, `dirichletClockWeight`, `dirichletClockLaw` |
| total mass one, a law on the half line | `tsum_dirichletClockWeight`, `isProbabilityMeasure_dirichletClockLaw`, `dirichletClockLaw_Iio_zero` |
| **its Laplace transform is the ratio of shifted Dirichlet totals** | `integral_exp_neg_dirichletClockLaw` |
| **its mean is the ratio of the logarithmic total to the plain total** | `integrable_id_dirichletClockLaw`, `integral_id_dirichletClockLaw` |
| the squarefree weight `μ(d)²`, bounded by one and vanishing at zero | `squarefreeWeight`, `squarefreeWeight_le_one`, `squarefreeWeight_zero` |
| summability and positivity of its Dirichlet total past abscissa one | `summable_squarefreeWeight_rpow`, `dirichletTotal_squarefreeWeight_pos` |
| summability of its logarithmically weighted series | `summable_squarefreeWeight_logMul_rpow` |
| **`(1)`: the squarefree clock, a law on the half line** | `squarefreeClockLaw`, `isProbabilityMeasure_squarefreeClockLaw`, `squarefreeClockLaw_Iio_zero` |
| **its Laplace transform `Z(σ+u)/Z(σ)` and its mean** | `integral_exp_neg_squarefreeClockLaw`, `integral_id_squarefreeClockLaw` |
| the weight supported on squares reading a weight at its square root | `sqrtWeight`, `sqrtWeight_sq` |
| **square substitution: such a weight has the Dirichlet series of its square root at twice the abscissa** | `tsum_sqrtWeight` |
| the squarefree weight is the indicator of the squarefree integers | `squarefreeWeight_of_squarefree`, `squarefreeWeight_of_not_squarefree`, `squarefreeWeight_eq_indicator` |
| the square part of an integer, and that a square divides it exactly when its root divides the square part | `sqDivisorPart`, `sqDivisorPart_dvd`, `sq_dvd_iff_dvd_sqDivisorPart` |
| the square part is trivial exactly for squarefree integers | `sqDivisorPart_eq_one_iff` |
| the Möbius sum over divisors | `sum_moebius_divisors` |
| **the convolution identity `μ(n)² = ∑_{d²∣n} μ(d)`** | `sum_moebius_sq_dvd` |
| **`∑ n^{-σ} = ζ(σ)` and `∑ μ(n) n^{-σ} = 1/ζ(σ)` as real Dirichlet sums** | `ofReal_tsum_oneWeight_eq`, `ofReal_tsum_moebius_eq` |
| the Möbius function read at square roots, and `μ² = sqrtMoebius ⋆ 1` | `sqrtMoebius`, `sum_divisors_sqrtMoebius` |
| **`(1)`: the squarefree Dirichlet series is `Z(σ) = ζ(σ)/ζ(2σ)`** | `ofReal_dirichletTotal_squarefreeWeight_eq` |

Both clocks of the card therefore exist in Lean as honest laws on `[0,∞)`, each with its Laplace
transform and its mean in closed Dirichlet form.

`formal/GaloisForLFunctions/HTGeometry/HalfLineScaling.lean` reads the two clocks at the thermal
scale `ε = σ - 1`, which is the normalization the card's limits use.

| Card item | Lean name |
|---|---|
| the rescaled law, and that a nonnegative rescaling preserves half-line support | `scaleLaw`, `scaleLaw_Iio_zero`, `instIsProbabilityMeasureScaleLaw` |
| rescaling multiplies the Laplace argument and the mean | `integral_exp_neg_scaleLaw`, `integral_id_scaleLaw`, `integrable_id_scaleLaw` |
| **`X_E = ε H_E` and `X_P = ε H_P` of `(10)`** | `scaledEulerClockLaw`, `scaledSquarefreeClockLaw` |
| **`(11)`: their Laplace transforms are `A(σ+uε)/A(σ)` and `Z(σ+uε)/Z(σ)`** | `integral_exp_neg_scaledEulerClockLaw`, `integral_exp_neg_scaledSquarefreeClockLaw` |
| **`(13)`: their means are `ε·(-A′(σ)/A(σ))` and `ε·(-Z′(σ)/Z(σ))`** | `integral_id_scaledEulerClockLaw`, `integral_id_scaledSquarefreeClockLaw` |

With `σ = 1 + ε` these are literally the expressions `(11)` and `(13)` study, so the two scaled
clocks now expose exactly the quantities whose limits the fixed-current layer has already proved.

`formal/GaloisForLFunctions/HTGeometry/ExponentialLaplaceValue.lean` supplies the boundary value.

| Card item | Lean name |
|---|---|
| the exponential law as a weighted Lebesgue measure | `expMeasure_one_eq_withDensity` |
| the decaying-exponential integral over the half line | `integral_exp_neg_mul_Ioi_zero`, `lintegral_exp_neg_mul_Ioi_zero` |
| **`(11)`: the Laplace transform of `Exp(1)` is `1/(1+u)`** | `lintegral_exp_neg_expMeasure_one`, `integral_exp_neg_expMeasure_one` |
| **transport from the explicit boundary-layer limits** | `tendsto_integral_monotoneCoupling_of_tendsto_laplace_value` |
| mutual transport cost from a common limit law | `tendsto_integral_monotoneCoupling_pair` |
| **`(15)` in closed form: the two-clock critical transport statement** | `tendsto_integral_monotoneCoupling_pair_of_tendsto_laplace_value` |

The last statement is `(15)` in closed form: two families of half-line laws whose Laplace transforms
converge at every natural argument to `1/(1+k)` — exactly what `(11)` produces — and whose means
converge to one are coupled *to each other*, by their monotone coupling, with vanishing transport
cost.  Its hypotheses are precisely the boundary-layer limit `(11)` and the first-moment limit
`(13)`; nothing else enters.

`formal/GaloisForLFunctions/RHTower/MobiusCriticalTransportAssembly.lean` joins the clock to the
boundary layer.

| Card item | Lean name |
|---|---|
| the real von Mangoldt Dirichlet total is the von Mangoldt current | `ofReal_tsum_vonMangoldt_eq_current` |
| **`(11)` for the clock: the scaled Euler clock's Laplace transform tends to `1/(1+k)`** | `tendsto_integral_exp_neg_scaledEulerClockLaw` |
| the `L`-series and the current have the same derivative past abscissa one | `deriv_lseries_vonMangoldt_eq` |
| **`(13)` for the clock: the scaled Euler clock's mean tends to one** | `tendsto_integral_id_scaledEulerClockLaw` |
| the transport layer's squarefree total is the boundary layer's squarefree Möbius total | `dirichletTotal_squarefreeWeight_eq_total` |
| **`(11)` for the ground clock: the scaled squarefree clock's Laplace transform tends to `1/(1+k)`** | `tendsto_integral_exp_neg_scaledSquarefreeClockLaw` |

All four hypotheses the critical transport statement consumes are therefore discharged for the
actual arithmetic clocks rather than assumed: both Laplace limits and both means.

### What remains for the Lean transport layer

Nothing: `(14)`--`(22)` are all compiled unconditionally.  The remaining open gates of the card are
the operator statements of the RH seam, which are not transport statements.

Both clocks exist at the thermal scale with their Laplace transforms and means in the exact form
the card's limits use.  What is left is the final assembly:

1. transporting the corpus's scalar limits `(11)` and `(13)` (stated for `A` and `Z` as analytic
   functions) to the Dirichlet-sum form the clocks expose.  The Euler side is the already-proved
   `ofReal_tsum_vonMangoldt_eq`.  The squarefree side is
   `dirichletTotal squarefreeWeight σ = Z(σ) = ζ(σ)/ζ(2σ)`, which factors as
   `μ² = 1 ⋆ (μ at square roots)` followed by `tsum_sqrtWeight`.  **This is now proved**:
   `ofReal_dirichletTotal_squarefreeWeight_eq`.  Both clocks therefore have their Dirichlet totals
   identified with the analytic functions `A` and `Z` of the fixed-current layer, so what is left
   of item 1 is only to feed the corpus's proved scalar limits `(11)` and `(13)` through
   `tendsto_integral_monotoneCoupling_pair_of_tendsto_laplace_value`.  The Euler Laplace limit is
   now discharged, as are the Euler mean limit and the squarefree Laplace limit; only the squarefree
   mean limit remains, by the same pattern;
2. `(15a)`--`(15c)`, `(16)`--`(17)` and `(18)`--`(22)`, the second-order and packet statements.

- 2026-08-05 — half-line `W₁` layer built: transport distance, layer-cake mean identity, the
  survival/moment convergence criterion, the triangle inequality, the mutual-convergence corollary,
  and the `Exp(1)` reference law.
- 2026-08-05 — quantile/coupling layer built: quantile function, Galois connection, measurability,
  inverse-transform sampling, the monotone coupling with its marginals, and its transport cost as a
  quantile integral.
- 2026-08-05 — the `(15)` limit proved: Scheffé cancellation, quantile nonnegativity and
  integrability, quantile convergence from distribution convergence, the explicit `Exp(1)` quantile,
  and the capstone `tendsto_integral_monotoneCoupling_expMeasure_one`.
- 2026-08-05 — the discrete-law carrier built: weighted point laws with their mass, integrals,
  half-line support, survival function, Laplace transform and mean.  Item 1 is now the arithmetic
  identification of two weighted sums.
- 2026-08-06 — the compact half of Laplace continuity built: moments determine a law on a compact
  interval, and moment convergence forces weak convergence.
- 2026-08-06 — item 2 closed: the exponential compactification carries the Laplace transform to the
  moments, weak convergence follows, and portmanteau at the one-point frontier of the compactified
  tail turns it into distribution-function convergence.  `(11)` + `(13)` ⇒ `(15)` is now a single
  Lean theorem.
- 2026-08-06 — the arithmetic clock built: `logClockLaw` with its Laplace transform (a shifted
  Dirichlet series) and its mean (a logarithmically weighted Dirichlet sum), and the capstone
  `tendsto_integral_monotoneCoupling_logClock`.
- 2026-08-06 — the Euler clock built: the real/complex `L`-series bridge, the identification of the
  real von Mangoldt Dirichlet sum with `-ζ′/ζ`, and the clock law of `(2)` with total mass one and
  Laplace transform `A(σ+u)/A(σ)`.
- 2026-08-06 — the Euler clock's mean closed: integrability against a discrete law as summability,
  summability of the logarithmically weighted von Mangoldt series, its identification with `-A′(σ)`
  via `LSeries_deriv`, and the mean `-A′(σ)/A(σ)`.
- 2026-08-06 — the clock construction generalized to any nonnegative arithmetic weight, and the
  squarefree clock `(1)` built with its Laplace transform and mean.
- 2026-08-06 — both clocks read at the thermal scale `ε = σ - 1`: the rescaled laws of `(10)` with
  their Laplace transforms `(11)` and means `(13)` in exactly the card's form.
- 2026-08-06 — the boundary value computed: the Laplace transform of `Exp(1)` is `1/(1+u)`, so the
  transport capstone now takes the card's own limits as hypotheses.
- 2026-08-06 — `(15)` closed in the general form: the mutual transport cost of two families each
  converging to `Exp(1)` vanishes, so the two-clock statement follows from `(11)` and `(13)` alone.
- 2026-08-06 — square substitution for real Dirichlet series proved (`tsum_sqrtWeight`), the second
  factor of the squarefree identity `∑ μ(d)²d^{-s} = ζ(s)/ζ(2s)`; the squarefree weight identified
  with the squarefree indicator.  The remaining factor is the convolution identity
  `μ(n)² = ∑_{d²|n} μ(d)`, whose multiplicativity route is recorded above.
  `lake build GaloisForLFunctions.HTGeometry` green across all transport modules.
- 2026-08-06 — the convolution identity `μ(n)² = ∑_{d²∣n} μ(d)` proved via the square part
  `sqDivisorPart n = ∏ p^{⌊v_p(n)/2⌋}`: a square divides `n` exactly when its root divides the
  square part, the square part is trivial exactly for squarefree `n`, and the Möbius sum over
  divisors detects that.  Both factors of the squarefree Dirichlet identity are now in hand.

### The second-order, transport-distance and four-unit layers

`[LEAN-PROVED]` `formal/GaloisForLFunctions/HTGeometry/QuadraticTransportCost.lean` carries the
first-order comparison to second order.  Mathlib has no Scheffé lemma in any form, so the `L²`
version is obtained from the `L¹` one by the pointwise inequality `|a-b|² ≤ |a²-b²|` for
nonnegative reals.

| Card item | Lean name |
|---|---|
| `\|a-b\|² ≤ \|a²-b²\|` for nonnegative reals | `sq_abs_sub_le_abs_sq_sub` |
| the quadratic triangle inequality `\|a-c\|² ≤ 2\|a-b\|² + 2\|b-c\|²` | `sq_abs_sub_le_two_mul_add` |
| **quadratic Scheffé cancellation** | `tendsto_integral_sq_sub_of_tendsto` |
| the quadratic cost is the `L²` distance of the quantile functions | `integral_monotoneCoupling_sq_sub` |
| square-integrability and second moment of a quantile function | `integrableOn_quantile_sq`, `integral_quantile_sq_eq_second_moment` |
| **`W₂` convergence criterion** | `tendsto_integral_monotoneCoupling_sq_sub` |
| **`(15b)` mutual form** | `tendsto_integral_monotoneCoupling_pair_sq` |
| the second moment of `Exp(1)` is two (third Gamma integral) | `integral_sq_expMeasure_one`, `integrable_sq_expMeasure_one` |
| **`(15b)` in closed form from the boundary-layer limits** | `tendsto_integral_monotoneCoupling_pair_sq_of_tendsto_laplace_value` |
| the monotone coupling is a probability law | `isProbabilityMeasure_monotoneCoupling` |
| **`(15c)` centered form** | `tendsto_integral_monotoneCoupling_centered_sq` |

`[LEAN-PROVED]` `formal/GaloisForLFunctions/HTGeometry/ClockSecondMoment.lean` supplies the
arithmetic input: the second moment of a Dirichlet clock is the second logarithmic Dirichlet sum,
and that sum is the second derivative of the `L`-series of the weight.

| Card item | Lean name |
|---|---|
| second moment of a logarithmic clock | `integrable_sq_logClockLaw`, `integral_sq_logClockLaw` |
| second moment of a Dirichlet clock | `integrable_sq_dirichletClockLaw`, `integral_sq_dirichletClockLaw` |
| rescaling multiplies the second moment by `c²` | `integral_sq_scaleLaw`, `integrable_sq_scaleLaw` |
| **the squared logarithmic sum is `(LSeries f)″`** | `ofReal_tsum_logSq_mul_eq` |
| convergence of the squared logarithmic series | `summable_logSq_mul_rpow`, `summable_vonMangoldt_logSq_rpow`, `summable_squarefreeWeight_logSq_rpow` |
| **`(15a)` for the clocks** | `integral_sq_scaledEulerClockLaw`, `integral_sq_scaledSquarefreeClockLaw` |

`[LEAN-PROVED]` `formal/GaloisForLFunctions/HTGeometry/PairGiniLaw.lean` computes the mean pairwise
distance of a half-line law from its survival function.

| Card item | Lean name |
|---|---|
| the law of the minimum of two independent variables | `minLaw` |
| **the survival function of a minimum is the product** | `survival_minLaw` |
| **`E\|X-X'\| = E X + E X' - 2∫₀^∞ S S'`** | `integral_abs_sub_prod` |
| `∫₀^∞ S_{Exp(1)}² = 1/2` | `integral_survival_sq_expMeasure_one` |
| **`(16)` for `Exp(1)`: `E\|Y-Y'\| = 1`** | `integral_abs_sub_prod_expMeasure_one` |
| the squared survival integral is continuous in `W₁` | `tendsto_integral_survival_sq` |
| **`(16)` transferred along `W₁`** | `tendsto_integral_abs_sub_prod` |
| **`(17)` the four-unit incidence energy** | `tendsto_four_mul_integral_abs_sub_prod` |

`[LEAN-PROVED]` The assembly file adds the second-order and four-unit statements for the two actual
arithmetic clocks.

| Card item | Lean name |
|---|---|
| the `L`-series and the current have the same second derivative | `deriv_lseries_vonMangoldt_eq_of_one_lt_re`, `deriv2_lseries_vonMangoldt_eq` |
| **`(15a)` for the Euler clock: `ε²A″(1+ε)/A(1+ε) → 2`** | `tendsto_integral_sq_scaledEulerClockLaw` |
| the transport layer's squarefree second moment is the boundary layer's second logarithmic moment | `squarefree_logSqMean_eq_logMoment` |
| **`(15a)` for the squarefree clock** | `tendsto_integral_sq_scaledSquarefreeClockLaw` |
| **`(15)` for the two actual clocks** | `tendsto_integral_monotoneCoupling_criticalClocks` |
| **`(15b)` for the two actual clocks** | `tendsto_integral_monotoneCoupling_sq_criticalClocks` |
| **`(15c)` for the two actual clocks** | `tendsto_integral_monotoneCoupling_centered_sq_criticalClocks` |
| **`(14)` in survival form for both clocks** | `tendsto_halfLineW1_scaledSquarefreeClockLaw`, `tendsto_halfLineW1_scaledEulerClockLaw` |
| **`(16)` for the Euler current** | `tendsto_integral_abs_sub_prod_scaledEulerClockLaw` |
| **`(17)` for the Euler current** | `tendsto_fourUnitEnergy_scaledEulerClockLaw` |
| **`(16)` in the card's variables**: `ε E\|H_E - H_E'\| → 1` | `tendsto_mul_integral_abs_sub_prod_eulerClockLaw` |
| **`(17)` in the card's variables**: `4 ε E\|H_E - H_E'\| → 4` | `tendsto_fourUnitEnergy_eulerClockLaw` |
| the same for the ground clock | `tendsto_mul_integral_abs_sub_prod_squarefreeClockLaw` |
| the quadratic cost scales with the square of the scale | `integral_monotoneCoupling_sq_sub_scaleLaw` |
| **`(15)` in the card's variables**: `ε E_π\|H_P - H_E\| → 0` | `tendsto_mul_integral_monotoneCoupling_criticalClocks` |
| **`(15b)` in the card's variables**: `ε² E_π\|H_P - H_E\|² → 0` | `tendsto_sq_mul_integral_monotoneCoupling_sq_criticalClocks` |
| the centered cost as a quantile integral, and its scaling | `integral_monotoneCoupling_centered_sq_eq`, `integral_monotoneCoupling_centered_sq_scaleLaw` |
| **`(15c)` in the card's variables** | `tendsto_sq_mul_integral_monotoneCoupling_centered_sq_criticalClocks` |
| `(16)`--`(17)` for the squarefree clock | `tendsto_integral_abs_sub_prod_scaledSquarefreeClockLaw`, `tendsto_fourUnitEnergy_scaledSquarefreeClockLaw` |

Equations `(14)`, `(15)`, `(15a)`, `(15b)`, `(15c)`, `(16)` and `(17)` are therefore machine-checked
for the actual arithmetic clocks, with no hypotheses and no added axioms.

- 2026-08-06 — the squarefree mean limit closed and `(15)` proved for the two actual clocks; the
  escape clamp `escape ε = if 0 < ε then 1 + ε else 2` supplies the probability-measure instances
  the transport statement needs at every index while agreeing with `1 + ε` on the filter.
- 2026-08-06 — the second-order layer built: quadratic Scheffé from the first-order one, the
  second moment of `Exp(1)` as the third Gamma integral, the second logarithmic Dirichlet sum as
  `(LSeries f)″`, and `(15a)`--`(15c)` for both clocks.
- 2026-08-06 — `(14)` closed in the card's own survival form for both clocks, and the four-unit
  Gini law `(16)`--`(17)` proved from the survival identity `E|X-X'| = 2EX - 2∫₀^∞ S²` together
  with `W₁` continuity of the squared survival integral.

### The complementary-packet layer

`[LEAN-PROVED]` `formal/GaloisForLFunctions/RHTower/ComplementaryPacketTwoPointDistance.lean`
supplies the missing `L²` link between the affine packet profile and the two-point modulus.

| Card item | Lean name |
|---|---|
| the squared packet distance `‖B_h - B_k‖²` | `RHTower.packetPathDistanceSq` |
| square integrability of the packet difference | `RHTower.integrableOn_packet_difference_Ioc`, `..._Ioi`, `RHTower.integrableOn_packetPathDifference` |
| **`‖B_h - B_k‖² = D_ω(\|h-k\|)`** | `RHTower.packetPathDistanceSq_eq`, `RHTower.packetPathDistanceSq_eq_abs` |
| **`(18)` at the two-point distance** | `RHTower.packetPathDistanceSq_le` |
| **`(20)`** the packet edge field `G = 2(B_{h'} - B_h)` | `RHTower.packetEdgeField` |
| its energy is four times the two-point distance | `RHTower.integral_packetEdgeField_sq` |
| the edge-field distance and its parallelogram bound | `RHTower.packetEdgeFieldDistanceSq`, `RHTower.packetEdgeFieldDistanceSq_le` |
| measurability of the edge-field distance in the four clock values | `RHTower.measurable_packetEdgeFieldDistanceSq` |

`[LEAN-PROVED]` `formal/GaloisForLFunctions/RHTower/MobiusCriticalPacketTransport.lean` closes
`(19)`--`(22)`.

| Card item | Lean name |
|---|---|
| the critical two-clock coupling before rescaling | `criticalClockCoupling` |
| the packet distance is the modulus of the coupled gap, and is integrable | `ae_packetPathDistanceSq_eq`, `integrable_packetPathDistanceSq` |
| **`(19)`: `ε E_π‖B_{H_P} - B_{H_E}‖² → 0`** | `criticalPacketCost`, `tendsto_criticalPacketCost` |
| two independent copies of the coupling | `criticalCouplingSquare` |
| **`(21)`: `ε E‖G_P - G_E‖² → 0`** | `criticalPacketEdgeCost`, `tendsto_criticalPacketEdgeCost` |
| the clamped packet shift and its uniform defect | `packetShift`, `abs_packetModulus_sub_le_uniform` |
| **the Euler edge field carries four units: `ε E‖G_E‖² → 4`** | `criticalEulerEdgeEnergy`, `tendsto_criticalEulerEdgeEnergy` |
| **`(22)`: the Gamma/Sonin budget `limsup ε E‖Q G_Γ G_E‖² ≤ 4`** | `eventually_criticalEulerTransformedEnergy_le` |

The transport layer of the card is therefore complete: `(14)`, `(15)`, `(15a)`--`(15c)`,
`(16)`--`(17)` and `(19)`--`(22)` are machine-checked, with `(18)` supplied by the parent card's
`RHTower.abs_complementaryPacketModulus_sub_le`.  Every statement is unconditional and
axiom-clean (`propext, Classical.choice, Quot.sound`).

- 2026-08-06 — the packet layer closed.  The missing link was the two-point `L²` identity
  `∫₀^∞ (B_h - B_k)² = D_ω(|h-k|)`: translate the base point away, and the half line splits at the
  separation into the incoming-constant branch and the kernel-translate branch, which are exactly
  the two branches of `D_ω`.  With it, `(19)` is the affine bound `(18)` against the vanishing
  transport cost `(15)`, `(21)` is the parallelogram bound under two independent copies of the
  coupling, and `(22)` follows from `ε E‖G_E‖² → 4` — itself the parent card's four-unit packet
  energy law fed by the Gini limit `(16)`.

### The two displayed identities of the fixed-current layer

`[LEAN-PROVED]` Added to `formal/GaloisForLFunctions/RHTower/MobiusCriticalTransportAssembly.lean`.

| Card item | Lean name |
|---|---|
| **`(4)`, second equality**: `A(σ+uε) = A(σ)·E_ν[e^{-uεH_E}]` — the fixed current is the clock's moment generating function | `vonMangoldtCurrent_shift_eq_mul_clockLaplace` |
| **`(9)`, exact form**: `(ε/2)·∂_α C(α,1+ε)\|₀ = ε·A(1+ε)` | `half_mul_deriv_suzukiPacketDirichlet_eq` |
| **`(9)`**: that normalized normal derivative reaches one | `tendsto_half_mul_deriv_suzukiPacketDirichlet` |
| **"the same arithmetic object"**: the multiplier's logarithmic current equals the normalized packet normal derivative | `logDeriv_mobiusMovingMultiplier_eq_half_mul_deriv_suzukiPacketDirichlet` |

The first equality of `(4)` — `∂_u log τ_σ(u) = ε A(σ+uε)` — was already
`RHTower.logDeriv_mobiusMovingMultiplier`.  Its second equality is what ties the fixed current to
the clock: it is the Laplace transform of the thermally scaled Euler clock, so `(4)` and `(11)` are
one identity read at two speeds.  Likewise `(9)` had the packet derivative `(7)` and the residue
limit `(12)` separately; the displayed normalized derivative is now a single statement.

- 2026-08-06 — `(4)`'s Laplace equality and `(9)`'s normalized derivative closed; every displayed
  equation of the card, `(1)`--`(22)`, is now a named unconditional Lean theorem.

### `(23)`: the completed source

`[LEAN-PROVED]` `formal/GaloisForLFunctions/RHTower/CompletedSuzukiPacketNormalDerivative.lean`
(wired into `GaloisForLFunctions/RHTower.lean`; axiom-clean).

The card cites `(23)` as already known.  It is now a theorem of this corpus in its own right, at the
same level of generality as the prime-power leg `(7)`.

| Card item | Lean name |
|---|---|
| the completed packet connection `Θ_α(z) = Ξ(z-α)/Ξ(z+α)` | `RHTower.completedSuzukiPacket`, `.completedSuzukiPacket_zero` |
| **`(23)`** `∂_α Θ_α(z)\|₀ = -2 Ξ'(z)/Ξ(z)` off the completed divisor | `RHTower.hasDerivAt_completedSuzukiPacket`, `RHTower.deriv_completedSuzukiPacket` |
| the archimedean completion factor of `ξ` | `RHTower.archimedeanXiFactor`, `RHTower.xi_eq_archimedean_mul_zeta` |
| **"`(6)` is its prime-power leg before Gamma completion"** | `RHTower.completedSuzukiPacket_eq_archimedean_mul_zeta` |
| **`(7)`, first equality**: the packet connection is the Dirichlet series of the coefficients `(5)` | `RHTower.LSeries_suzukiShiftedCoefficient_eq_suzukiPacketDirichlet`, `.LSeries_suzukiShiftedCoefficient_eq_of_abs_lt` |
| `(5)` as a Dirichlet convolution `n^α ⍟ μ(n)n^{-α}` | `RHTower.suzukiCoeffAF`, `.suzukiCoeffAF_eq_convolution`, `.suzukiCoeffAF_apply` |
| the prime-factor part `∏_{p∣n}(1-p^{-2α})` as a divisor sum | `RHTower.suzukiRadicalFactor`, `.suzukiRadicalFactor_apply`, `.doubleShiftedMoebius_prime_pow` |
| Dirichlet shifts preserve multiplicativity and compose additively | `RHTower.isMultiplicative_dirichletShift`, `.dirichletShift_dirichletShift` |
| **`(6) ⇒ (7)` termwise**: the `α`-derivative of the packet series is the series of the coefficient derivatives `2Λ(n)` | `RHTower.hasDerivAt_LSeries_suzukiShiftedCoefficient` |
| **`(12)`** `A(1+x) = 1/x + O(1)`: the current minus its polar part has a limit at the pole, hence is bounded there | `RHTower.tendsto_vonMangoldtCurrent_sub_pole`, `.exists_bound_vonMangoldtCurrent_sub_pole`, `.exists_bound_vonMangoldtCurrent_one_add_sub_inv` |
| **the second-order residue expansion** `A″(1+x) = 2x^{-3} + O(1)`, with the Laurent form of `A″` | `RHTower.deriv2_vonMangoldtCurrent_of_mem`, `.tendsto_deriv2_vonMangoldtCurrent_sub_pole`, `.exists_bound_deriv2_vonMangoldtCurrent_sub_pole` |
| **the card's Statement line, as one theorem** | `mobiusFixedCurrentTransportWeld` |
| **the card's "positive theorem"**: the ordered two-clock law as one statement — `(9)`, `(8)` and the divergence together | `orderedTwoClockLaw` |
| **`(12)` differentiated**: `A′(1+x) = -x^{-2} + O(1)` | `RHTower.tendsto_deriv_vonMangoldtCurrent_add_pole`, `.exists_bound_deriv_vonMangoldtCurrent_add_pole`, `.exists_bound_deriv_vonMangoldtCurrent_one_add` |
| **`(11)`, exact form, both clocks**: `E[e^{-uX_E}] = A(σ+uε)/A(σ)` and `E[e^{-uX_P}] = Z(σ+uε)/Z(σ)`, for every `u ≥ 0` | `ofReal_integral_exp_neg_scaledEulerClockLaw_eq`, `ofReal_integral_exp_neg_scaledSquarefreeClockLaw_eq` |
| **`(13)`, exact form**: `E[X_E] = -ε·A'(σ)/A(σ)` | `ofReal_integral_id_scaledEulerClockLaw_eq` |
| **`(13)`, exact form, squarefree half**: `E[X_P] = -ε·Z'(σ)/Z(σ)` with `Z(s) = ζ(s)/ζ(2s)` | `ofReal_integral_id_scaledSquarefreeClockLaw_eq`, `ofReal_tsum_squarefreeWeight_logMul_eq` |
| **`(15a)`, exact form**: `E[X_E²] = ε²·A''(σ)/A(σ)` | `ofReal_integral_sq_scaledEulerClockLaw_eq` |
| the von Mangoldt Dirichlet series is the current `(2)` | `RHTower.LSeries_vonMangoldt_eq_current`, `.LSeries_two_mul_vonMangoldt` |

The proof is the completed mirror of `(7)`: the shift is differentiated before any specialization,
the quotient rule contributes `-Ξ'Ξ - ΞΞ'`, and the hypothesis `Ξ(z) ≠ 0` is exactly the statement
that the reading point is off the completed divisor — the logarithmic current is singular precisely
on the zeros the RH seam is about.

- 2026-08-06 — `(23)` proved here rather than inherited: the completed packet connection is defined
  and its normal derivative computed, so `(6)`, `(7)` and `(23)` are now the same construction read
  before and after Gamma completion.

### `(21)` as a genuine asymptotic isometry

`[LEAN-PROVED]` Added to `formal/GaloisForLFunctions/RHTower/MobiusCriticalPacketTransport.lean`.

The card insists that `(21)` "is an asymptotic isometry of the complete source packet fields, not
merely equality of two scalar limits".  That reading needs both edge energies in *one* framing.  The
squarefree side was inherited from the parent card in a different framing
(`RHTower.tendsto_complementaryPacketCriticalEnergy`, modulus at `|x|/(σ-1)` against the squarefree
gap law); it is now also available in the edge-field framing used for the Euler side.

| Card item | Lean name |
|---|---|
| the squarefree edge field energy | `criticalSquarefreeEdgeEnergy`, `criticalSquarefreeEdgeEnergy_eq` |
| **`ε E‖G_P‖² → 4`** in the edge-field framing | `tendsto_criticalSquarefreeEdgeEnergy` |
| **`(21)` as stated**: both energies reach four and the mutual cost vanishes | `criticalPacketFields_asymptotic_isometry` |

- 2026-08-06 — the squarefree edge energy proved in the Euler framing, so `(21)`'s conclusion is a
  single statement about the two packet fields rather than a comparison across two framings.

### `W₂` convergence of each clock to `Exp(1)`

`[LEAN-PROVED]` Added to `formal/GaloisForLFunctions/RHTower/MobiusCriticalTransportAssembly.lean`.

`(15a)` concludes "hence both laws converge to `Exp(1)` in `W₂`".  The mutual statement `(15b)` and
the two second-moment limits were already proved; the two *individual* `W₂` limits — the exact
quadratic analogue of the `W₁` statements `tendsto_halfLineW1_scaled*` — are now stated as well.

| Card item | Lean name |
|---|---|
| **`(15a)`, squarefree half**: the ground clock reaches `Exp(1)` in `W₂` | `tendsto_integral_monotoneCoupling_sq_expMeasure_one_scaledSquarefreeClockLaw` |
| **`(15a)`, Euler half**: the prime current reaches `Exp(1)` in `W₂` | `tendsto_integral_monotoneCoupling_sq_expMeasure_one_scaledEulerClockLaw` |

- 2026-08-06 — the per-clock `W₂` limits added, so `(14)`/`(15a)` now have matching first- and
  second-order statements for each clock separately as well as mutually.

### `(14)`'s third line

`[LEAN-PROVED]` `(14)` displays three limits.  The first two — each clock against `Exp(1)` — were
`tendsto_halfLineW1_scaledSquarefreeClockLaw` and `tendsto_halfLineW1_scaledEulerClockLaw`.  The
third, the mutual distance of the two clocks in the same `W₁`, is now proved from them by the
triangle inequality.

| Card item | Lean name |
|---|---|
| the transport distance is symmetric and nonnegative | `halfLineW1_symm`, `halfLineW1_nonneg` |
| **`(14)`, third line**: `W₁(Law X_P, Law X_E) → 0` | `tendsto_halfLineW1_criticalClocks` |

- 2026-08-06 — `(14)` complete in the survival form: all three displayed limits are named theorems,
  matching the three second-order limits of `(15a)`/`(15b)`.

### `(22)` made applicable, and shown non-vacuous

`[LEAN-PROVED]` Added to `formal/GaloisForLFunctions/RHTower/MobiusCriticalPacketTransport.lean`
and `.../ComplementaryPacketTwoPointDistance.lean`.

The budget theorem originally required its energy bound for **every** input function.  That is
strictly stronger than the card needs and, worse, is not satisfied by the natural model: for a
pointwise contraction `q` supported on a bounded set and a non-square-integrable `f`, the left side
can be positive while the right side is zero by the Bochner convention.  The hypothesis is now asked
only of square-integrable inputs — which is all the proof ever uses, since the packet edge field is
square integrable.

| Card item | Lean name |
|---|---|
| the squared edge field is integrable | `RHTower.integrableOn_packetEdgeField_sq` |
| **`(22)`** with the corrected hypothesis | `eventually_criticalEulerTransformedEnergy_le` |
| the Gamma/Sonin model satisfies that hypothesis | `gammaSoninModel_energy_le` |
| **`(22)` applied to it**: scalar multiplication with norm tending to one, composed with a pointwise contraction, obeys the four-unit ceiling | `eventually_gammaSoninModel_energy_le_four` |

- 2026-08-06 — `(22)`'s hypothesis corrected from "all inputs" to "square-integrable inputs" and a
  Gamma/Sonin model exhibited that satisfies it, so the four-unit ceiling is stated about a transform
  family that exists rather than about a hypothesis that no natural operator meets.

### The divergence between `(8)` and `(9)`

`[LEAN-PROVED]` Added to `formal/GaloisForLFunctions/RHTower/MobiusCriticalTransportAssembly.lean`.

Between `(8)` and `(9)` the card records that the naive normalized difference on the old diagonal,
`[C(α,1+2α) - 1]/(2α)`, *diverges* — this is the sharp form of the no-go, stronger than saying the
two limits differ.  It is now a theorem: by `(8)` the numerator tends to `2`, the denominator
vanishes, and the quotient leaves every bounded set.

| Card item | Lean name |
|---|---|
| doubling preserves the punctured right neighbourhood | `tendsto_two_mul_nhdsGT` |
| **the diagonal shortcut diverges** | `tendsto_norm_diagonalShortcutQuotient_atTop` |

- 2026-08-06 — the divergence claim of the diagonal no-go proved, so the no-go is machine-checked in
  its sharp form and not only as an inequality of limits.

### The second no-go made non-vacuous

`[LEAN-PROVED]` Added to `formal/GaloisForLFunctions/HTGeometry/LogClockLaw.lean` and
`.../SquarefreeClockLaw.lean`.

The card's second no-go — "metric orientation is not enough" — says the two laws are asymptotically
indistinguishable while only the Euler law is the fixed current.  That is a statement about a
*selection inside a class*, so it has content only if the class has more than one member: the two
clocks must actually differ at each finite scale.  They do, and for an exact reason.

| Card item | Lean name |
|---|---|
| the logarithm of a natural number vanishes only at zero and one | `log_natCast_eq_zero_iff` |
| the atom of a logarithmic clock at the origin is the weight of one | `logClockLaw_singleton_zero` |
| the ground clock charges the trivial divisor | `squarefreeClockLaw_singleton_zero` |
| **the two critical clocks differ at every finite scale** | `squarefreeClockLaw_ne_eulerClockLaw` |
| rescaling preserves the atom at the origin | `scaleLaw_singleton_zero` |
| the two *thermally scaled* clocks differ at every finite scale | `scaledSquarefreeClockLaw_ne_scaledEulerClockLaw` |
| **the orientation no-go in one statement**: distinct laws, vanishing transport distance | `criticalClocks_distinct_but_asymptotically_indistinguishable` |

The separating observable is the atom at the origin: the squarefree clock gives mass `1/Z(σ)` to the
trivial divisor `d = 1`, while `Λ(1) = 0` gives the prime current no mass there.  So `(14)`--`(21)`
are genuinely asymptotic statements about two distinct laws, and the fixed current selects one of
them.

- 2026-08-06 — the two clocks proved distinct at every `σ > 1`, so the orientation no-go is about a
  class with more than one member.
- 2026-08-06 — the distinctness carried to the thermally scaled clocks, which are the objects
  `(14)`--`(21)` actually speak about, and the no-go packaged as one statement: at every finite
  scale the two laws differ, while their transport distance vanishes at criticality.
- 2026-08-06 — `(16)` and `(17)` restated in the card's own variables: the escape parameter explicit
  and the clocks unscaled, `ε E|H_E - H_E'| → 1` and `4 ε E|H_E - H_E'| → 4`.  The scaled forms were
  the ones the transport machinery produces; the unscaled forms are the ones the card writes.
- 2026-08-06 — `(15)` and `(15b)` restated in the card's variables as well, completing the pass: the
  escape parameter appears explicitly (to the first power at first order, squared at second) against
  the unscaled clocks, which is how the card writes every transport statement.
- 2026-08-06 — `(15c)` restated in the card's variables, closing the pass: `(14)`, `(15)`,
  `(15b)`, `(15c)`, `(16)` and `(17)` are each available both as the transport machinery produces
  them (thermally scaled clocks) and as the card writes them (escape parameter explicit, clocks
  unscaled).
- 2026-08-06 — the phrase "before Gamma completion" made precise: on the critical rotation the
  completed packet is the ratio of archimedean factors times the ratio of zeta values, so the packet
  Dirichlet series of `(7)` is literally the uncompleted leg of `(23)`.  The factorization needs
  `Γ_ℝ ≠ 0`, which is automatic on the rotation (real part one half) but genuinely fails at the
  trivial-zero points, where mathlib's junk convention sets `Γ_ℝ` to zero.
- 2026-08-06 — the card's sentence "the logarithmic current of the signed multiplier and the normal
  current of the complementary packet connection are the same arithmetic object" is now one
  identity, for every `σ > 1` and every escape parameter, rather than two separate computations that
  happen to land on `A`.
- 2026-08-06 — `(7)`'s first equality proved, closing the last unformalized displayed equation on
  this card.  `suzukiPacketDirichlet` was *defined* as `ζ(s-α)/ζ(s+α)`, while the coefficients `(5)`
  and their derivative `(6)` lived in a separate module with no link, so "the packet Dirichlet
  series" and "the prime-power leg" were two unconnected computations.  They are now one: `c_α` is
  the Dirichlet convolution of `n ↦ n^α` with `n ↦ μ(n)n^{-α}`; pulling the common shift out leaves
  `ζ ⍟ (μ · n^{-2α})`, which is multiplicative with value `1 - p^{-2α}` at every prime power and so
  equals the prime-factor product; the two shifted factors have L-series `ζ(s-α)` and `ζ(s+α)^{-1}`,
  and the convolution theorem gives the identity on `re s > 1 + |α|`.
- 2026-08-06 — the card's `(6) ⇒ (7)` step made a theorem.  The card obtains the normal current by
  differentiating the coefficients and summing; that interchange is not free.  It is not assumed
  here either: the coefficient series equals the packet connection on a whole neighbourhood of
  `α = 0` (every `|α| < re s - 1`), so the packet's already-proved normal derivative transfers to
  the series, and the resulting value is exactly the Dirichlet series of the coefficientwise
  derivatives `2Λ(n)`.
- 2026-08-06 — `(13)` and `(15a)` exposed as identities rather than only as limits.  The card writes
  the Euler clock's moments as exact ratios of derivatives of the von Mangoldt current, `E[X_E] =
  -ε A'(σ)/A(σ)` and `E[X_E²] = ε² A''(σ)/A(σ)`, and only then takes the limit.  Both identities
  were buried inside the limit proofs; they are now named theorems, and the limit proofs are stated
  in terms of them, so the card's displayed equalities are available on their own.
- 2026-08-06 — `(13)`'s squarefree half given in the card's exact form too.  The corpus expressed
  the squarefree mean through the boundary layer's logarithmic moment; the card writes it as
  `-ε Z'(σ)/Z(σ)`.  The denominator is the corpus's own closed form `Z(s) = ζ(s)/ζ(2s)`, and the
  numerator is the derivative of the squarefree `L`-series, obtained from `LSeries_deriv` at the
  abscissa bound the corpus already carried.  Both clocks of `(13)` are now stated as the card
  displays them.
- 2026-08-06 — `(11)`'s two displayed equalities exposed as identities.  The corpus proved the
  Laplace limits, but only at natural arguments and with the moving-ratio identity buried inside the
  limit proofs; the card writes them as exact ratios `A(σ+uε)/A(σ)` and `Z(σ+uε)/Z(σ)` *for every*
  `u ≥ 0`, and only then lets `ε → 0`.  Both are now named theorems at arbitrary nonnegative `u`,
  with the squarefree denominator in the closed form `ζ(s)/ζ(2s)`.
- 2026-08-06 — `(12)` proved in its `O(1)` form.  The corpus had the pole-strength limit
  `cε·A(1+cε) → 1`, which is only `A(1+x) = 1/x + o(1/x)`; the card asserts the sharper
  `A(1+x) = 1/x + O(1)`.  The corpus's own Laurent identity already writes the current as
  `(s-1)^{-1} - logDeriv G(s)` with `G` the analytic residue unit, and `G(1) = 1 ≠ 0` makes
  `logDeriv G` analytic at the pole; so the correction has a *limit* there, which is stronger than
  bounded, and both the complex and the real-escape forms are recorded.
- 2026-08-06 — the differentiated `(12)` proved in the same sharp form.  The card obtains `(13)` by
  differentiating `(12)` to `A′(1+x) = -x^{-2} + O(1)`; the corpus had only the residue limit
  `(s-1)²A′(s) → -1`, which is the weaker `o` statement.  The Laurent identity for the derivative
  was already available, and the correction is the derivative of an analytic function at the pole,
  so it too has a limit; the `O(1)` and real-escape forms follow.
- 2026-08-06 — the "residue expansions" the card invokes for `(15a)` completed at second order.  The
  Laurent form of `A″` was derived inline inside the residue limit; it is now a named identity
  (`A″(s) = 2/(s-1)³ - (logDeriv G)″(s)` on the Laurent set), the residue limit is proved from it,
  and the sharp `A″(1+x) = 2x^{-3} + O(1)` follows because the correction is again analytic at the
  pole.  `A`, `A′` and `A″` now all carry the expansion in the card's `O(1)` form.
- 2026-08-06 — cross-card citation audit re-run after the day's additions.  Every backticked Lean
  name in the four cards was resolved against a fresh index of all corpus declarations (attributes
  and partial namespace prefixes handled).  Two stale citations were found and fixed: this card
  named `(6)`'s coefficient derivative under an `RHTower.` prefix although the module carries no
  namespace, and the Stokes card abbreviated
  `DecoratedStokesCore.RootedRealization.hierarchy_unique`.  All remaining unresolved tokens are
  mathlib names, module names, or prose symbols.
- 2026-08-06 — the section's "positive theorem" packaged as one object.  The card states the ordered
  two-clock law as a single claim — differentiate at fixed escape and only then let the escape
  vanish, because the reversed order gives `3` and the normalized quotient diverges.  Its three
  clauses were separate theorems; `orderedTwoClockLaw` now carries them together, so the forced
  order is a single citable statement rather than a reading of three.
- 2026-08-06 — the card's Statement line compiled as one object.  `mobiusFixedCurrentTransportWeld`
  carries its four clauses together: the signed multiplier's logarithmic current is the escape
  parameter times the positive von Mangoldt law; both critical clocks converge in the half-line
  transport distance to the mean-one exponential law; the canonical monotone coupling has vanishing
  complementary-packet cost, and so do the induced edge fields; and the four-unit packet geometry
  holds of the Euler current itself.  All four cards of this group now carry their headline claim as
  a single citable theorem.
