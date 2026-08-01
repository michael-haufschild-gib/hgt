# Theta-cusp calibrated power-reciprocal first-moment law

- **ID:** `theta-cusp-calibrated-power-reciprocal-first-moment-law`
- **Stage:** 2-fully-proven
- **Type:** `THEOREM (paper)` · `[PROVED HERE]` · `[CORPUS-NOVEL EXACT SYNTHESIS]`
- **Source:** Lean theorem bodies in
  `ThetaCuspCassiniMarkovBoundaryTransport.lean`,
  `ThetaCuspLikelihoodModularSeam.lean`,
  `PrimeArchThetaSourceAtomDomination.lean`,
  `ThetaCuspLikelihoodAtomicNondivisibility.lean`, and
  `XiOrderFourteenCornerSourceExclusion.lean`
- **Lean:**
  `formal/GaloisForLFunctions/RHTower/ThetaCuspCalibratedPowerReciprocalMomentLaw.lean`
- **Statement:** Zeroth-mass calibration cannot repair the raw reciprocal-gap Cassini carrier:
  its first moment exceeds the canonical first source moment by more than
  `(19413 / 160000) * normalizedPrimeArchMoment 0`.  There is nevertheless a unique
  source-selected power exponent `alpha > 1` for which the same positive spectral carrier,
  pushed through `t ↦ t^(-alpha)`, matches both source moments of degrees zero and one.

## Goal

Falsify the explicit fixed reciprocal map in the strongest available low-degree way, then retain
the closest non-trivial source-built positive carrier instead of retiring the whole
theta--Cassini route.

This card does not prove RH.  It changes the exact open core: the fixed exponent `alpha = 1` is
impossible, while a unique exponent `alpha_* > 1` solves the complete mass-and-barycenter
calibration problem.  Moment matching from degree two onward remains open.

## Gates

- [x] 0 → 1 in-progress: explicit source measure, falsifiable degree-one prediction, and
  corpus-only proof strategy
- [x] 1 → 2 fully-proven: dependency-closed paper proof below; `[PROVED HERE]`
- [x] 2 → 3 formalized: Lean quantitative mismatch, no-go, and power-reciprocal survivor
- [ ] 3 → 4 publication-ready: standalone theorem/proof/Lean certificate and independent
  novelty review

## Definitions

Write

```text
B0 = thetaCuspLikelihoodCoordinate 0,
nu = thetaCuspHigherLikelihoodTiltedMeasure B0,
T  = nu(R),
m0 = normalizedPrimeArchMoment 0,
m1 = normalizedPrimeArchMoment 1.
```

The existing calibrated reciprocal candidate is

```text
mu_1 = (m0 / T) * (t ↦ t^(-1))_* nu.
```

All quotients in this card are ordinary real quotients; positivity and finiteness of `T` are
already proved in Lean.

For `alpha ≥ 0`, define the normalized negative-power profile and its calibrated pushforward by

```text
F(alpha) = (1 / T) * integral t^(-alpha) dnu(t),
mu_alpha = (m0 / T) * (t ↦ t^(-alpha))_* nu.
```

## Paper proof: quantitative degree-one obstruction

### 1. Exact seam mass ceiling

The modular-seam extension theorem identifies the degree-zero tilted spectral moment with the
actual higher-to-first theta source ratio at `x = 0`:

```text
T = (thetaCuspFullSource 0 - thetaCuspSourceTerm 0 1)
      / thetaCuspSourceTerm 0 1.
```

The first source term at zero is positive.  The corpus's pointwise higher-atom domination,
evaluated at zero and divided by that positive first term, therefore gives

```text
0 < T ≤ thetaCuspHigherAtomDominationWeight ≤ 8 / 2997.       (1)
```

No numerical integration or zero table enters this estimate.

### 2. Exact first charged atom

The fixed higher spectral measure has its first atom at square gap `3`.  Exponential tilting at
`B0 = pi - 3/2` gives

```text
nu({3})
 = 16 * exp(-3*pi).                                           (2)
```

Indeed, the untilted atomic weight is `16 exp(-9/2)` and the tilt contributes
`exp(-3(pi - 3/2))`; their product is (2).

The proved elementary exponential floor

```text
1 / 24 < exp(-pi)
```

and `exp(-3*pi) = exp(-pi)^3` imply

```text
1 / 864 < nu({3}).                                            (3)
```

### 3. Reciprocal barycenter floor

The reciprocal pushforward charges `{1/3}` with mass `nu({3})`.  Calibration multiplies this
mass by `m0/T`.  Since the calibrated carrier is nonnegative and supported in `[0,1/3]`,

```text
integral x dmu_1(x)
  ≥ (1/3) * mu_1({1/3})
  = (m0 / (3*T)) * nu({3}).
```

Using `m0 > 0`, (1), and (3),

```text
integral x dmu_1(x)
  > m0 * (1/3) * (1/864) / (8/2997)
  = (37/256) * m0.                                           (4)
```

### 4. Canonical first-moment ceiling

The exact Xi/theta recurrence in the corpus is

```text
m1 = m0^2 / 2 - thetaCuspNormalizedEvenMoment 2 / 6.
```

The subtracted normalized theta moment is strictly positive, so

```text
m1 < m0^2 / 2.
```

The independently proved source bound `m0 < 29/625`, together with `m0 > 0`, yields

```text
m1 < (29/1250) * m0.                                        (5)
```

Finally,

```text
37/256 - 29/1250 = 19413/160000.
```

Combining (4) and (5) proves the quantitative mismatch

```text
m1 + (19413/160000) * m0 < integral x dmu_1(x).              (6)
```

Consequently
`ThetaCuspCassiniCalibratedReciprocalPositiveMomentMatching` is false already at `k = 1`.
This kills only the source-normalized fixed reciprocal pushforward, not the
theta--Cassini compact-Markov target.

## Positive survivor: unique source-selected exponent

The same measure `nu` is carried by `[3,∞)` and has positive finite mass.  Hence, for
`alpha ≥ 0`:

1. `0 < F(alpha) ≤ 3^(-alpha) ≤ 1`;
2. `F` is continuous by dominated convergence, using the constant integrable majorant `1`;
3. `F` is strictly decreasing, since `t^(-beta) < t^(-alpha)` for
   `3 ≤ t` and `alpha < beta`, on a set of positive `nu`-mass;
4. `F(0) = 1` and `F(alpha) → 0` as `alpha → ∞`, by the bound in item 1.

The canonical ratio is strictly inside this range:

```text
0 < m1/m0 < 29/1250 < 37/256 < F(1).                        (7)
```

The last inequality is exactly the unscaled content of (4).  Continuity and decay give an
`alpha_* > 1` with

```text
F(alpha_*) = m1/m0.
```

Strict decrease makes `alpha_*` unique.  Therefore `mu_(alpha_*)` is a finite positive measure
with

```text
mu_(alpha_*)(R)        = m0,
integral x dmu_(alpha_*) = m1.
```

Because `alpha_* > 1` and `t ≥ 3`, its support lies in
`[0, 3^(-alpha_*)] ⊂ [0,1/3)`, safely inside the compact-Markov aperture `1/2`.

This is the strongest positive survivor exposed by the obstruction: fixed reciprocal geometry is
too coarse, but the source itself selects one and only one power-reciprocal geometry matching its
mass and barycenter.  The next honest falsification/proof target is degree two:

```text
normalizedPrimeArchMoment 2
  ?= integral x^2 dmu_(alpha_*)(x).
```

## No-go closure

- **Exact killing mechanism:** degree-one quantitative mismatch (6) for the existing
  `alpha = 1` calibrated reciprocal carrier.
- **Strongest positive survivor:** unique `alpha_* > 1` matching degrees zero and one, with
  positive compact support strictly below `1/3`.
- **New insight:** total-mass normalization and reciprocal-map selection are independent source
  constraints.  A scalar can satisfy degree zero only; the first moment forces a geometric
  exponent.  The open Cassini construction should begin at degree two after solving this
  two-parameter calibration exactly.
- **Status:** paper proof and unconditional Lean formalization dependency-closed.

## Lean formalization

Lean defines a globally measurable positive extension of `t ↦ t^(-alpha)` and proves that it is
literally the real power on the carrier's positive support.  Generic finite-measure infrastructure
then proves, for every measure carried by `[c,∞)` with `c > 1`, positivity, continuity on
`[0,∞)`, strict decrease, the sharp bound by `c^(-alpha)`, normalization at zero, decay to zero,
and existence and uniqueness of every target exponent below the value at one.

For the theta carrier, Lean proves

```text
37/256 < F(1),
normalizedPrimeArchMoment 1 / normalizedPrimeArchMoment 0 < F(1),
```

and obtains a unique source-selected exponent `alpha_* > 1`.  The calibrated pushforward at this
exponent has exact mass `normalizedPrimeArchMoment 0`, exact first moment
`normalizedPrimeArchMoment 1`, and almost-everywhere support in the strict interval `(0,1/3)`.
For the fixed reciprocal exponent, Lean proves the literal quantitative obstruction

```text
normalizedPrimeArchMoment 1
  + (19413/160000) * normalizedPrimeArchMoment 0
  < integral x dmu_1(x).
```

`#print axioms` on the quantitative obstruction, unique-exponent theorem, calibrated moment
capstone, support theorem, and generic existence theorem reports only `propext`,
`Classical.choice`, and `Quot.sound`.  Direct source check and
`lake build GaloisForLFunctions.RHTower.ThetaCuspCalibratedPowerReciprocalMomentLaw` pass; the
module is imported by `formal/GaloisForLFunctions/RHTower.lean`.

## Novelty audit

Repository-wide searches found no prior degree-one mismatch theorem, no `37/256` barycenter
floor, and no source-selected power exponent for this Cassini likelihood measure.

Post-proof external searches targeted combinations of Riemann Xi, Jacobi theta probability laws,
Stieltjes/Markov moment representations, reciprocal square-gap measures, and power-reciprocal
pushforwards.  Closest sources were:

- Biane--Pitman--Yor, *Probability laws related to the Jacobi theta and Riemann zeta function and
  Brownian excursions*, arXiv:math/9912170, which studies theta/zeta probability laws built from
  sums of independent exponentials, not this tilted square-gap pushforward or moment mismatch.
- Griffin--Ono--Rolen--Thorner--Tripp--Wagner, *Jensen Polynomials for the Riemann Xi Function*,
  arXiv:1910.01227, which studies hyperbolicity of Xi Jensen polynomials, not positive
  reciprocal-gap carriers.
- Shi, *Real-rooted Pólya-like approximations to the Riemann Xi-function*,
  arXiv:1502.06844, which modifies Fourier kernels to preserve real-rootedness, not a calibrated
  Markov moment measure.

No exact collision was found.  Claim remains `[NOVELTY-UNVERIFIED]` in the external-priority
sense; the precise result is new relative to the repository and to the targeted literature
search.

## Log

- 2026-07-23 — Lean-corpus theorem bodies exposed exact mass ceiling, charged atom, and source
  recurrence; paper proof and positive survivor completed without computation.
