# Uniform finite theta metric on growing physical apertures

- **ID:** CDG-LOG-APERTURE-METRIC
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Source:** Conjugate-Diagonal Geometry questions 2 and 10; finite theta readings.
- **Statement:** One prescribed finite arithmetic reading approximates all compact C² tests in a growing logarithmic aperture, with an error homogeneous in their explicit source norm and uniform in moment order after normalization.
- **Count:** Unaccepted. Strengthening of the finite-theta candidate, not a separate counted contribution.

## Goal

Fixed-test convergence does not justify choosing a test after the height or
source stage is fixed. The target is uniformity over the entire normalized
test class, with physical support growing like log height. This permits
adaptive tests in that class. It does not assert isolation of individual
zeros, a zero-spacing lower bound, selective positivity, or RH.

## Exact estimate

Use the finite reading `Q_n(f,L,j)` and prescribed integer cutoff/regulator
from `../3-formalized/finite-theta-collided-readings.md`. Set

```
S(f) = 4 (integral |f| + integral |f''|),
E_n = exp(-n^4 + 68 n^2 + 66).
```

Proved: a constant B>=0 independent of f, a, j, L, tau and n satisfies

```
4^(-j) |Q_n(twist_tau f,L,j) - D_j(twist_tau f,L)|
 <= S(f)^2 [B E_n + 40 sourceReferenceTail(n)]
 <= S(f)^2 [B E_n + (640/n)(C_xi + log(n+4))]
```

for every n>=1, a>=0, compact C² test supported in [-a,a], natural j,
and real L,tau with

```
|tau| <= n/2,
a + j|L| <= 2 log(n+1).
```

The source norm is computed from f, not an assumed analytic bound. The
support and parameter inequalities specify the tested family. The regulator
and integer cutoff are unchanged across this entire family. An equivalent
uniform-convergence consequence restricts to S(f)<=1 and puts the threshold
N before the quantifiers for f,a,j,L,tau.

## Gates

- [x] Precise family and proposed error identified from existing source estimates.
- [x] Complete paper proof, including every finite-source dependency.
- [x] Exact Lean endpoint and transitive axiom audit; individual leaf checks only.
- [ ] Novelty and significance audit of the combined finite-source contribution.

## Approach

The existing `norm_paperFT_le_decay` gives

```
|F_f(s)| <= S(f) exp(a |Re(s)-1/2|)/(1+|Im(s)|)^2.
```

On the actual zero strip, its square costs exp(a), not the coarser
exp(a^2+a) from a whole-plane control weight. The depth kernel costs
`2^j exp(j|L|)`. The joint aperture inequality therefore pays both costs
by `(n+1)^2`, while the moving ordinate comparison and fourth-order decay
leave `40 S(f)^2 2^j sourceReferenceTail(n)`. Division by `4^j` removes
the order factor uniformly.

For the local current use the Gaussian envelope
`A = S(f) exp(a^2+a)`. The existing Laplacian estimate then has factor
`4^(j+1) S(f)^2 exp(2a^2+2a)`. Since
`a <= 2log(n+1) <= 2n`, the remaining exponential is at most
`exp(12n^2+4)`. Multiplication by the checked quartic current envelope
gives the displayed E_n. The finite-source potential constant and actual
xi logarithmic-square constant are independent of the test and its support.

The proof exposes these constants before taking existential quantifiers over
the moment order and test, proves the sharp strip estimate, and assembles
the actual finite reading. Both the fixed-test chain and the stronger family
endpoint pass their individual Lean checks.

## Corpus and novelty audit

Read `UniversalSourceWeight`, `SourceTransformGrowth`,
`MovingSourceTailControl`, `MovingSourceTail`, `ExplicitSourceMetric`,
and `ExplicitThetaErrorCertificate` in full or at the exact used statements.
They provide fixed-test/fixed-order convergence and the exposed factors
used above, but not the proposed quantifier order.

The search also surfaced `HTGeometry/SchwartzLogApertureCompactDecay.lean`.
Its complete leaf was read: it treats compact families at a fixed aperture
and a remote-quartet defect, rather than the present growing-aperture
arithmetic metric. No conclusion of novelty follows from this comparison.
The finite amplitudes and regularized-current mechanism remain known
inputs, as documented on the parent finite-theta card.

Also compared the statements (GC5)–(GC6) in van Hemert's
[October 2026 manuscript](https://raw.githubusercontent.com/LeonardSEO/riemann-xi-zero-detection/main/paper/paper.tex):
these are uniform operator/energy bounds for completed Möbius–gamma fields.
They do not identify the current-weighted collided metric in their statements.
This distinction does not establish novelty of the present conjecture.

## Calibration

The reading is positive on the conjugate diagonal and has no successor
charge or odd-sector sign law. A planted off-line divisor packet contributes
positive mass to this mechanism. Logarithmic physical aperture permits
Fourier tests on the inverse-logarithmic scale, but a separating test can
have a large source norm; the homogeneous error pays that norm. No zero
isolation, capacity inequality, or selective fibre identification follows
merely from this uniformity.

## Lean verification

`SourceTestApertureBounds` and `SourceApertureMovingTail` pass their scratch
and main dependency checks. The latter's tail endpoint has only `propext`,
`Classical.choice`, and `Quot.sound` in its transitive axiom closure.

`FiniteThetaApertureMetric` passes scratch verification (29164), including:

- `exists_finiteThetaSource_aperture_error_bound`;
- `exists_finiteThetaSource_aperture_logarithmic_bound`;
- `finiteThetaSource_uniform_test_aperture_moments`.

All three closures are standard-only. Main source-only final audit 26873
passes. The programme umbrella imports the leaf; the umbrella was not compiled.
The [polynomial-prefix card](../1-in-progress/polynomial-prefix-collided-metric.md) develops a stronger schedule for this same
candidate. No contribution is accepted by counting these helper modules
or rate statements separately.
