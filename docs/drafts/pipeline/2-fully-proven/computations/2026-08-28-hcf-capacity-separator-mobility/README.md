# HCF capacity, separator, and gamma-cell mobility reconnaissance

Date: 2026-08-28

## Status and boundary

Numerical reconnaissance only. Nothing here is a premise, oracle, certificate, or imported datum for a Lean theorem. Results may kill a route or motivate a conjecture; any survivor must receive an independent paper proof before formalisation.

Main conclusion: computations do **not** produce the missing zero-independent source covariance. They narrow HCF research in three useful ways:

1. Full infinite-lattice receiver capacity appears to improve the three-centre threshold only from `0.3436686391` to `0.3820539915`; more finite-centre optimisation is low-value and does not touch the current source bottleneck.
2. Signed scalar transverse mixtures obtain an off-diagonal minorant only outside an explicit collision radius, with rapidly growing coefficient norm and negative lobe. Without a zero-spacing input they are not a uniform HCF source statistic.
3. Fixed finite-degree gamma-cell mobility contributes `O(T)` off-line zeros against zeta's `T log T` count. It is a severe finite-height falsifier but cannot impose an asymptotic 25% ceiling. An asymptotic structural adversary needs `N(T)`-scale mobility.

## Corpus grounding

Models were selected with `scripts/formal_tools.py research`, not invented from an external surrogate. Relevant corpus results:

- `formal/GaloisForLFunctions/RHTower/HedenmalmCriticalFeatureHolomorphicSectorCoercivity.lean`: critical feature `2 / (1 + (z - t)^2)`.
- `formal/GaloisForLFunctions/RHTower/HedenmalmCriticalFeatureThreeCenterSharpQuantum.lean`: current three-centre threshold `1452 / 4225`.
- `formal/GaloisForLFunctions/RHTower/HedenmalmSubmicroscopicScalarDiagonalCovarianceNoGo.lean`: universal continuous scalar close-pair obstruction.
- `formal/GaloisForLFunctions/RHTower/XiWardCubicPositiveShiftDampedDiagonalSeparator.lean`: Ward damped radial mask.
- `formal/GaloisForLFunctions/RHTower/XiWardCubicPositiveShiftDampedDiagonalSeparatorNoGo.lean`: entire scalar landing obstruction.
- `formal/GaloisForLFunctions/RHTower/XiThinStripExponentialEulerGaugeInvariance.lean`: finite entire-gauge contour invariance.
- `formal/GaloisForLFunctions/RHTower/DegreeZeroNonrealOffline.lean`: exact off-line quartic factor.
- `formal/GaloisForLFunctions/RHTower/GammaCellNonrealMobility.lean`: gamma-cell membership and mobility.

## Run and verification

RunPod host exposed 128 CPUs. Full sweep used 64 process workers, Python 3.12.3, NumPy 2.1.2, SciPy 1.18.1, and mpmath 1.3.0. Wall time: 5.16 seconds.

Workload:

- 405 separator linear programs;
- 200,000-point post-solve validation per successful LP;
- 2,049-height lattice profile plus global differential-evolution search;
- gamma-cell counts and lattice energies through `T = 10^8`.

Downloaded artifacts pass `shasum -a 256 -c SHA256SUMS`. Independent local checks found:

- 4,000,001-term half-cell lattice sum differs from closed candidate by `1.78e-15`, with omitted-tail bound `3.34e-19`;
- separate 1,000,000-point separator grids reproduce reported extrema;
- direct substitution into the DZO quartic at three ordinates on both off-line sequences has maximum floating residual `3.54e-12`.

## Experiment A: full infinite-lattice HCF capacity

Computed

```text
E(x,y) = sum_{k in Z} |2 / (1 + (x + i y - k)^2)|^2,  |y| < 1/2.
```

The standard lattice identity used for evaluation was

```text
S_a(x) = (pi/a) sinh(2 pi a) / (cosh(2 pi a) - cos(2 pi x)),
E(x,y) = (S_{1-y}(x) - S_{1+y}(x)) / y,
```

with the derivative limit at `y = 0` evaluated at high precision.

Global search and the complete sampled `y` profile both selected `(x,y) = (1/2,0)`. Candidate minimum:

```text
2 pi tanh(pi) - 2 pi^2 sech(pi)^2
= 6.1128638634994589523095190379093258326336...
```

Consequent candidate receiver threshold after division by 16:

```text
full lattice:  0.38205399146871616
three centres: 1452/4225 = 0.34366863905325445
gain:          0.03838535241546170
```

Numerical Hessian diagonal at the candidate is positive (`6.6541`, `9.3950`). Across the sampled strip the minimized energy rises to `7.3372` near `|y| = 1/2`.

**Research consequence.** Conjecture a sharp analytic lattice theorem with the displayed minimum. Prove it independently from the closed formula if useful. Do not spend more time tuning finite centre sets: remaining receiver gain is small, and even a proof would not construct the missing source-only covariance. Existing `4/25` and `21/100` source targets already lie below the three-centre capacity.

## Experiment B: scalar separator phase diagram

Optimised normalized signed mixtures

```text
K(d) = sum_j w_j eps_j^2 / (d^2 + eps_j^2),
sum_j w_j = 1,
sum_j |w_j| <= B,
```

over 7, 11, and 15 logarithmic scales from `1/64` to `64`. Objective was minimum sampled `sup_{d >= delta} K(d)`, followed lexicographically by minimum coefficient `L1` norm. Every solution was rechecked on a denser grid.

Smallest sampled exclusion radius with validated supremum at most `1e-8`:

| L1 budget | radius `delta` | attained L1 | negative trough |
|---:|---:|---:|---:|
| 1 | none on sampled range | 1 | positive kernel |
| 2 or 4 | `0.0316228` | `1.48828` | `-0.243872` |
| 8, 16, or 32 | `0.01` | `5.88281` | `-2.43999` |
| 64, 128, or 256 | `0.00316228` | `49.8281` | `-24.4019` |

Increasing scale count from 7 to 15 did not improve these boundaries: optimizers selected only the smallest and largest scales. This exposes an exact two-endpoint candidate worth proving independently. For endpoints `0 < a < b`, the normalized mixture whose zero is `delta` has

```text
K(d) = a^2 b^2 (1 - d^2/delta^2)
       / ((d^2 + a^2)(d^2 + b^2)),
```

so it is positive inside the collision radius and negative outside. Its coefficient norm scales approximately as `1 + 2 a^2/delta^2` when `b` is large. This algebra explains the observed instability; numerical optimality over all signed mixtures remains unproved.

Ward comparison reinforces the same pivot. Ward mask reaches levels `0.1`, `0.5`, and `0.9` at scaled separations `0.00640`, `0.04360`, and `0.15433`; the single antisymmetric Cauchy mask needs `0.3333`, `1`, and `3`. Ward is a much sharper collision detector, but corpus no-go results block its entire scalar landing.

The real-shift kernel `1/(1-d^2)` also exhibits the expected two-sided pole growth, about `+1/(2h)` and `-1/(2h)` at `d=1-h` and `d=1+h`. Values reach magnitude `5.0e13` at `h=1e-14`.

**Research consequence.** Retire scalar signed-mixture sharpening as a uniform route unless paired with a proved spacing/repulsion estimate. Prioritise a signed **matrix** covariance or arithmetic source mechanism whose pair cancellation survives arbitrarily close ordinates. Meromorphic real shifts additionally require pole-safe contour, principal-value, or matrix cancellation before scalarisation.

## Experiment C: degree-zero gamma-cell mobility

Used corpus quartic

```text
D(s) = 1 + 40 * 16^(-2s) + 256 * 16^(-4s).
```

Its two positive-ordinate off-line sequences have real parts `3/8`, `5/8` and ordinates

```text
t_n = (2n+1) pi / (8 log 2).
```

Combined positive-zero density is `8 log(2)/pi = 1.7650848012` per unit height. Their mean infinite-lattice HCF energy converges to the equimeasure value

```text
128 pi / 63 = 6.382918407293548...
```

Using only the Riemann--von Mangoldt main term as a denominator proxy, the off-line fraction in `zeta * D` decreases from `0.8585` at `T=10^2` to `0.4158` at `T=10^8`. This is not an actual zeta-zero count and assumes the zeta factor contributes line zeros for the proxy interpretation.

Asymptotically,

```text
(N_D(T) / N_zeta,main(T)) log T -> 16 log 2 = 11.09035488896,
```

so every fixed power of a fixed DZO factor contributes `o(N_zeta(T))`. Main-term proxy crossover below 25% off-line fraction occurs only around `4.81e15`, explaining why finite-height experiments look hostile while the asymptotic obstruction vanishes.

**Research consequence.** Retire fixed finite-degree DZO factors as asymptotic 75%-ceiling adversaries. Keep them as finite-height and generic-invariance falsifiers. A genuine asymptotic obstruction must supply `N(T)`-scale mobility: degree/source complexity growing like `log T`, or a fixed admissible source with `T log T` off-line density.

## Route decision

Highest-value next work remains source-side, not receiver-side:

1. Search corpus for matrix-valued or signed sesquilinear source covariances that cancel close-pair contributions before scalarisation.
2. Require zero independence at construction time and an explicit-formula reduction to pole/Gamma/von-Mangoldt data.
3. Test any candidate against an `N(T)`-scale mobility adversary, not merely a fixed DZO factor.
4. Only then target the analytic budget `<= 21 N(T)/100 + o(N(T))`, with `4 N(T)/25 + o(N(T))` as stronger goal.

## Artifacts

- `run_experiments.py`: multicore reproducible driver.
- `results.json`: constants, optimiser outputs, checks, environment, and selected LP witnesses.
- `separator_phase.csv`: all 405 LP outcomes.
- `lattice_y_profile.csv`: strip profile.
- `mobility_height_profile.csv`: height sweep.
- `SHA256SUMS`: hashes of downloaded result files.

