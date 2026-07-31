# Squared-Xi completion is a Bose-log cumulant difference

- **ID:** squared-xi-bose-log-cumulant-coordinate
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean 4, fully unconditional) / cancellation-preserving source coordinate
- **Scientific status:** `[PROVED HERE] [NOVELTY UNAUDITED]`
  `[FULLY FORMALIZED IN LEAN, AXIOMS CLEAN]`
- **Parents:** `squared-xi-radial-jet-reverse-bessel-source-alignment.md`; the classical Mellin integral for `Gamma(s) zeta(s)`
- **Statement:** On the live absolute-Euler ray, every completed Xi jet is an exact difference between cumulants of a strictly log-concave Bose-log distribution and half-Gamma polygamma cumulants, with the polar term already absorbed.

## Mellin probability coordinate

Let `a>0`, `s=1+a`, and define

```text
M(a) = integral_0^infinity t^a/(exp(t)-1) dt
     = Gamma(a+1) zeta(a+1).                             (1)
```

The probability measure

```text
d mu_a(t) = [t^a/((exp(t)-1) M(a))] dt                  (2)
```

has all logarithmic moments.  Write `kappa_r(a)` for the order-`r`
cumulant of `log t` under `mu_a`.  Exponential-family differentiation gives

```text
kappa_r(a) = d^r/da^r log M(a),    r>=1.                (3)
```

## Exact completed-Xi theorem `[PROVED HERE]`

The duplication formula for Gamma and `(1)` give

```text
xi(1+a)
  = (1+a) 2^(-a) pi^(-a/2) M(a)/Gamma(a/2).             (4)
```

Therefore, with `L=xi'/xi`,

```text
L(1+a)
  = 1/(1+a) - log(2 sqrt(pi))
    - (1/2) digamma(a/2) + kappa_1(a),                  (5)
```

and, for every `j>=1`,

```text
L^(j)(1+a)
  = (-1)^j j!/(1+a)^(j+1)
    - 2^(-(j+1)) polygamma_j(a/2)
    + kappa_(j+1)(a).                                   (6)
```

Equations `(5)`--`(6)` retain the zeta pole inside the Mellin normalization.
Indeed,

```text
(s-1) zeta(s) = M(a)/Gamma(a),                          (7)
```

so this is the probability form of the already formalized pole-filled zeta
coordinate, not a termwise separation of `1/(s-1)` from `zeta'/zeta`.

## Strict log-concavity `[PROVED HERE]`

For `X=log t`, the density induced by `(2)` is proportional to

```text
exp((a+1)X)/(exp(exp X)-1).                              (8)
```

Its log-density has second derivative

```text
-t * d/dt [t/(1-exp(-t))],    t=exp X.                  (9)
```

The derivative in `(9)` is positive because

```text
1-(1+t)exp(-t) > 0
```

for `t>0`, equivalently `exp(t)>1+t`.  Thus the Bose-log law is strictly
log-concave for every `a>0`.

## Independent-factor interpretation `[PROVED HERE]`

Let `G` have the Gamma distribution of shape `a+1`, and independently let

```text
P(N=m) = m^(-(a+1))/zeta(a+1),    m>=1.                 (10)
```

Then `T=G/N` has law `(2)`.  Hence

```text
kappa_r(log T)
  = polygamma_(r-1)(a+1) + (-1)^r kappa_r(log N),       (11)
```

where the Euler product gives the positive compound-Poisson cumulants

```text
kappa_r(log N)
  = sum_(m>=2) Lambda(m) (log m)^(r-1) m^(-(a+1)) > 0.  (12)
```

Thus the all-order prime sign alignment is also a probability law: it is the
positive cumulant sequence of the zeta-distributed integer.

## Order-fourteen source target

Put `w=a+1/2` and substitute `(5)`--`(6)` into

```text
Q_14(w)=sum_(j=0)^14 (-1)^j b_(14,j) w^j L^(j)(1+a).
```

The live RH-disproof certificate is still `Q_14(w)<0` for some
`0<a<sqrt(8)-1/2`, but it is now a finite inequality between explicit
half-Gamma polygamma terms and cumulants of one strictly log-concave
one-dimensional probability law.  No pole subtraction, zero location, or
numerical evaluation is present.

`[CONJECTURE]` A sharp one-dimensional transport or dispersive-order bound
between the Bose-log law `(8)` and the half-Gamma log law controls this
reverse-Bessel cumulant functional strictly.  The sign must be established,
not inferred from log-concavity alone; ordinary log-concavity has no fixed
sign for cumulants of order three and above.

## Order-fourteen status update

The `[CONJECTURE]` above is settled, in the RH-compatible direction and without any transport
inequality.  `../3-formalized/squared-xi-low-order-complete-monotonicity-protected.md` proves
unconditionally in Lean that `(-1)^n g^(n) y > 0` for every `y > 0` and every `n <= 18`, so
`Q_14(w) > 0` everywhere on the absolute Euler ray and the order-fourteen certificate cannot exist.
The live compact order for this coordinate is therefore nineteen, not fourteen.

## Gates

- [x] exact Mellin probability representation
- [x] pole-filled Xi factorization
- [x] all completed jets expressed as cumulant differences
- [x] strict log-concavity and independent Gamma/Zipf factorization
- [x] find a transport order strong enough for the order-fourteen functional — superseded: the
  order-fourteen sign is proved directly, with no transport inequality
- [x] prove the resulting strict sign, whichever direction it has — it is strictly positive
- [x] formalize the Mellin coordinate `M a = Gamma (a+1) zeta (a+1)`, the pole-filled zeta
  coordinate, the completed-Xi factorization, and strict log-concavity
- [x] formalize the cumulant jet identities `(5)`–`(6)` and the Gamma/Zipf factorization
  `(10)`–`(12)`
- [x] 2 -> 3 formalized
- [ ] 3 -> 4 publication-ready

## Lean status

Axioms `[propext, Classical.choice, Quot.sound]` throughout.

### `GaloisForLFunctions/RHTower/BoseMellinCoordinate.lean`

- `realZetaSeries`, `summable_realZetaTerm`, `ofReal_realZetaSeries`, `one_le_realZetaSeries` —
  the zeta Dirichlet series as a real number at a real abscissa above one.
- `hasSum_boseKernel` — the geometric expansion `1/(exp t - 1) = sum_{n>=1} exp (-n t)` on `t > 0`.
- `boseMellin` — the coordinate `M a = ∫_0^∞ t^a/(exp t - 1) dt`.
- **`ofReal_boseMellin`** — equation `(1)`: `M a = Gamma (a+1) * zeta (a+1)`.  Proved through
  mathlib's `hasSum_mellin`, which supplies the termwise integration from the geometric expansion
  and the summability of `Gamma (a+1)/(n+1)^(a+1)`; no separate interchange argument is needed.
- `boseMellin_eq`, `boseMellin_pos` — the real form and strict positivity.
- **`realZetaSeries_mul_gamma`, `ofReal_poleFilled_zeta`** — equation `(7)`:
  `(s-1) zeta s = M (s-1)/Gamma (s-1)`; the pole sits inside the Mellin normalization.
- `xi_real_factor_identity`, **`xi_ofReal_one_add_eq_boseMellin`** — equation `(4)`:
  `xi (1+a) = (1+a) 2^(-a) pi^(-a/2) M a / Gamma (a/2)`, from Legendre duplication
  `Gamma (a/2) Gamma ((a+1)/2) = Gamma a 2^(1-a) sqrt pi`.

### `GaloisForLFunctions/HTGeometry/BoseLogConcavity.lean`

- `boseGrowth`, `boseGrowthDeriv`, `hasDerivAt_boseGrowth` — the growth factor `g t = t/(1-e^{-t})`
  and its closed-form derivative.
- **`boseGrowthDeriv_pos`** — `g' > 0` on `t > 0`, from the single inequality `exp t > 1 + t`;
  `strictMonoOn_boseGrowth`.
- `boseLogDensity`, `boseLogScore`, `hasDerivAt_boseLogDensity` — equation `(8)` and its score
  `(a+1) - g (exp X)`.
- **`hasDerivAt_boseLogScore`, `boseLogCurvature_neg`** — equation `(9)`: the exact curvature
  `-t g' t` at `t = exp X`, strictly negative.
- **`strictConcaveOn_boseLogDensity`** — strict log-concavity of the Bose-log law on all of `ℝ`,
  for every shift `a`.

### `GaloisForLFunctions/HTGeometry/RealAnalyticTransfer.lean`

- **`contDiffAt_re_comp_ofReal`** — a function holomorphic on an open plane set is real-smooth
  along the real axis inside it.  This is the smoothness supply for `Gamma`, `zeta` and `xi` on
  their pole-free rays: holomorphy plus scalar restriction, no real-variable estimate.

### `GaloisForLFunctions/RHTower/BoseCumulantJets.lean`

Smoothness layer:

- **`contDiffAt_realGamma`**, **`contDiffAt_realZetaSeries`** — `Real.Gamma` is smooth on `x > 0`
  and `realZetaSeries` on `x > 1`.  Neither is in mathlib; both come from holomorphy through
  `contDiffAt_re_comp_ofReal`, with `ContDiffAt.congr_of_eventuallyEq` for zeta (whose real value
  agrees with the complex one only on the ray).
- `contDiffAt_boseMellin`, `contDiffAt_logBoseMellin`, `contDiffAt_logGammaHalf`,
  `contDiffAt_logOneAdd`, `contDiffAt_linear`.

Elementary jets:

- `onePlusJet`, `hasDerivAt_onePlusJet`, **`iteratedDeriv_logOneAdd`** —
  `(d/da)^(j+1) log (1+a) = (-1)^j j!/(1+a)^(j+1)`.
- `iteratedDeriv_const_eq_zero`, `iteratedDeriv_linear_eq_zero` — the affine term dies from order
  two on.

The decomposition and the jet identities:

- `xiRealRay`, `xi_ofReal_one_add_eq_xiRealRay`, `xiRealRay_pos`, `boseXiLogJetBase`,
  **`log_xiRealRay`** — `log (xi (1+a)) = log (1+a) - (log 2 + (log pi)/2) a + log (M a)
  - log (Gamma (a/2))` for `a > 0`.
- **`iteratedDeriv_one_boseXiLogJetBase`** / **`deriv_boseXiLogJetBase`** — equation `(5)`:
  `L (1+a) = 1/(1+a) - log (2 sqrt pi) - (half-Gamma jet) + kappa_1 a`.
- **`iteratedDeriv_boseXiLogJetBase`** — equation `(6)`: for every order `m >= 2`,
  `(d/da)^m log xi (1+a) = onePlusJet (m-1) a + kappa_m a
  - (d/da)^m log (Gamma (a/2))`, the last term being exactly `2^(-m) polygamma_(m-1) (a/2)`.
- **`iteratedDeriv_logBoseMellin`** — equation `(11)`: `kappa_r a =
  (d/da)^r log (Gamma (a+1)) + (d/da)^r log (zeta (a+1))`.

Here `kappa_r a := iteratedDeriv r (fun b => Real.log (boseMellin b)) a` is the exponential-family
definition `(3)` of the Bose-log cumulants, so `(5)`, `(6)` and `(11)` are exactly the card's
identities.

### `GaloisForLFunctions/RHTower/BoseZipfCumulants.lean`

- `vonMangoldtLogSeries`, `vonMangoldtLogTerm_nonneg`, **`summable_vonMangoldtLogTerm`** — the
  log-weighted real von Mangoldt Dirichlet series and its convergence on every ray `s > 1`.  The
  majorant uses `Real.log_le_rpow_div` with exponent `(c-d)/(k+1)`, so the log weight is absorbed
  into an arbitrarily small power.
- `hasDerivAt_vonMangoldtLogTerm`, **`hasDerivAt_vonMangoldtLogSeries`**,
  **`iteratedDeriv_vonMangoldtLogSeries`** — termwise differentiation of that series on
  `(c, infinity)`, giving `(d/ds)^j = (-1)^j` times the next log weight.
- `hasDerivAt_realZetaSeries`, **`deriv_log_realZetaSeries`** — the single arithmetic input, the
  order-one link `(log zeta)' (s) = - sum_m Lambda m m^(-s)`.  This is the only place where the
  complex `zeta` is used, through `LSeries_vonMangoldt_eq_deriv_riemannZeta_div` and
  `HasDerivAt.comp_ofReal`.
- **`iteratedDeriv_log_realZetaSeries`**, **`zipfCumulant_eq_vonMangoldtLogSeries`** — equation
  `(12)`: `(-1)^r (d/da)^r log (zeta (a+1)) = sum_m Lambda m (log m)^(r-1) m^(-(a+1))`.
- **`vonMangoldtLogSeries_pos`**, **`zipfCumulant_pos`** — every Zipf cumulant is strictly
  positive, the `m = 2` term already forcing it.  This is the card's all-order prime sign
  alignment, in probability-law form.
- **`hasSum_gammaZipfMixture`** — equation `(10)`: mixing the scaled Gamma densities against the
  Zipf weights reproduces the Bose density `t^a/((exp t - 1) M a)` exactly.  The mixture identity
  is the same geometric expansion of the Bose kernel that evaluates the Mellin coordinate.

### Scope of the formalization

`(10)` is formalized as the **density** identity — the Zipf-weighted mixture of scaled Gamma
densities sums to the Bose density — not as a measure-level statement about the law of a quotient
of independent random variables.  That density identity is the whole content used by `(11)` and
`(12)`; promoting it to a statement about `ProbabilityTheory` measures would need a quotient
change-of-variables that adds nothing to the cumulant identities.

Likewise `kappa_r` is the exponential-family definition `(3)`, `kappa_r a = (d/da)^r log (M a)`,
which is how `(5)`, `(6)` and `(11)` use it; the equivalent characterization as the `r`-th cumulant
of `log t` under `mu_a` is not separately formalized.

## Log

- 2026-07-31 — Formalized the Mellin coordinate layer.  The interchange in `(1)` did not need a
  hand-rolled Tonelli argument: mathlib's `hasSum_mellin` takes exactly the geometric expansion of
  the Bose kernel plus summability of the Dirichlet coefficients and returns the Mellin transform
  as a Gamma-weighted Dirichlet series.  `(4)` reduces to Legendre duplication once both sides are
  recognized as casts of positive reals.  The strict log-concavity `(8)`–`(9)` is exactly the
  inequality `exp t > 1 + t` after the score is written through the growth factor.  The card's
  order-fourteen conjecture is no longer live: the sign is positive, by the sibling card.
- 2026-07-31 — Jet and cumulant layer formalized, closing the card.  The smoothness of `Gamma` and
  `zeta` on the real ray is not in mathlib and was built from holomorphy
  (`contDiffAt_re_comp_ofReal`).  `(5)`/`(6)` are then the logarithm of `(4)` differentiated with
  `iteratedDeriv_add`, the affine term surviving only at order one.  `(11)` is the same additivity
  applied to `log M = log Gamma + log zeta`.  For `(12)` only the order-one arithmetic link needed
  the complex `zeta`; all higher orders are real termwise differentiation of the von Mangoldt
  series with the `log_le_rpow_div` majorant, and positivity is the `m = 2` term.  `(10)` turned
  out to be the same geometric expansion as `(1)`: the Gamma/Zipf mixture density collapses to the
  Bose density because `m^(-(a+1)) * m * m^a = 1`.

