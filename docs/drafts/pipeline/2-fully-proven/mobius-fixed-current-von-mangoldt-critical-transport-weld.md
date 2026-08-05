# The Mobius multiplier fixed current is critically transport-equivalent to the Euler prime current

- **ID:** `mobius-fixed-current-von-mangoldt-critical-transport-weld`
- **Stage:** 2-fully-proven
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
- [ ] formalize the transport identities `(14)`--`(22)` in Lean
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

`(6)` is already in the corpus as `RHTower.hasDerivAt_suzukiShiftedCoefficient`
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

### What remains for the Lean transport layer

1. Construct the two clock laws `P_σ` of `(1)` and `ν_σ` of `(2)` as measures on `ℝ`, and identify
   their Laplace transforms with `Z(σ+uε)/Z(σ)` and `A(σ+uε)/A(σ)`.
2. Convert the proved Laplace convergence `(11)` into pointwise survival convergence — a continuity
   theorem for Laplace transforms on `[0,∞)`, also absent from mathlib.
3. With `(13)` this gives `(14)` through `tendsto_halfLineW1_of_tendsto_survival`.
4. `W₂` and `(15a)`--`(15c)`, the four-unit Gini law `(16)`--`(17)`, and the complementary-packet
   asymptotic isometry `(18)`--`(22)`.

Item 2 is closed.  Item 1 is reduced to arithmetic: the generic weighted-point-law carrier exists
with its Laplace transform and mean, so what remains is to instantiate it at the two clock weights
and identify the resulting weighted sums with `Z(σ+uε)/Z(σ)`, `A(σ+uε)/A(σ)` and their logarithmic
derivatives — the scalar limits themselves are already proved in the fixed-current layer.  With that
instantiation, `tendsto_integral_monotoneCoupling_of_tendsto_laplace` delivers `(15)` outright.

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
  Lean theorem.  Only item 1, the arithmetic instantiation of the two clock laws, remains.
