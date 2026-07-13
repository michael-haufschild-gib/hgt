# Zeta Fisher low-temperature prime-gap curvature

- **ID:** `zeta-fisher-low-temperature-prime-gap-curvature`
- **Stage:** 2-fully-proven / Lean analytic core formalized / needs scientific-novelty audit
- **Type:** CANDIDATE THEOREM / QUANTUM-GRAVITY SUPERSPACE GEOMETRY
- **Scientific status:** `[NOVELTY UNVERIFIED]`
- **Source:** the globally negative zeta Fisher superspace and its Euler prime-power dispersion
  formula; disjoint from RHTower Routes A--D
- **Statement:** The zero-temperature end of the zeta Fisher superspace is a finite-distance
  curvature singularity whose exact exponential rate and leading coefficient are determined by
  the first two prime-power energies, `log 2` and `log 3`.

## Goal

Classify the end `beta -> infinity` of

```text
g_beta = M_2(beta) (d beta^2+d tau^2),
Scal(beta)=-(M_2 M_4-M_3^2)/M_2^3,
```

where

```text
M_j(beta)=sum_p sum_(k>=1) (k log p)^j p^(-k beta)/k.
```

The critical end `beta -> 1+` is already asymptotically Poincare with scalar curvature `-2`.
The opposite end has not been classified.

## Exact target

Prove

```text
lim_(beta->infinity) 2^beta M_j(beta) = (log 2)^j,       (1)

lim_(beta->infinity) 6^beta (M_2 M_4-M_3^2)
  = (log 2)^2 (log 3)^2 (log(3/2))^2,                    (2)

lim_(beta->infinity) (3/4)^beta (-Scal(beta))
  = (log 3)^2 (log(3/2))^2/(log 2)^4.                    (3)
```

Consequently

```text
Scal(beta) -> -infinity,
log(-Scal(beta))/beta -> log(4/3).                        (4)
```

Also prove that the radial distance to infinity is finite and

```text
integral_beta^infinity sqrt(M_2(u)) du
  ~ 2 * 2^(-beta/2).                                      (5)
```

## Approach

Use the injective prime-power parametrization `n=p^k`.  After scaling by `2^beta`, dominated
convergence isolates the unique ground mode `n=2`, proving `(1)`.  Use the exact pairwise-dispersion
identity

```text
2(M_2 M_4-M_3^2)
 = sum_(a,b) w_a w_b x_a^2 x_b^2 (x_a-x_b)^2.
```

Diagonal terms vanish.  Among distinct prime powers, the minimum product is `2*3=6`, attained only
by the ordered pairs `(2,3)` and `(3,2)`; every other pair has product at least `8`.  Scaling by
`6^beta` and dominated convergence therefore proves `(2)`.  Equation `(3)` is the quotient of `(2)`
by the cube of `(1)` at `j=2`; `(4)` and `(5)` follow by elementary asymptotic calculus.

## General two-level curvature law `[PROVED HERE]`

Let a countable positive energy spectrum have

```text
0<E_1<E_2<E_3<=...,
w_i(beta)=c_i exp(-beta E_i),  c_i>0,
M_j(beta)=sum_i w_i(beta) E_i^j.
```

Assume the spectrum is discrete at its bottom, the first two levels are unique, and the moments
through order four admit a summable low-temperature majorant.  Put

```text
D=M_2 M_4-M_3^2,
R=-D/M_2^3.
```

Then

```text
M_j(beta) ~ c_1 E_1^j exp(-beta E_1),
D(beta) ~ c_1 c_2 E_1^2 E_2^2 (E_2-E_1)^2
          * exp(-beta(E_1+E_2)),

R(beta) ~ -(c_2/c_1^2) * E_2^2(E_2-E_1)^2/E_1^4
          * exp(beta(2E_1-E_2)).                       (6)
```

Consequently the low-temperature curvature has a sharp trichotomy:

```text
E_2<2E_1  => R -> -infinity,
E_2=2E_1  => R -> a finite negative constant,
E_2>2E_1  => R -> 0 from below.                         (7)
```

### Proof

After multiplication by `exp(beta E_1)`, dominated convergence kills every energy above `E_1`
and retains the unique ground term, proving the first line of `(6)`.

The exact dispersion identity is

```text
2D=sum_(i,l) w_i w_l E_i^2 E_l^2(E_i-E_l)^2.           (8)
```

Every diagonal term vanishes.  Among off-diagonal ordered pairs the least total energy is
`E_1+E_2`, attained only by `(1,2)` and `(2,1)`.  Multiply `(8)` by
`exp(beta(E_1+E_2))` and apply dominated convergence.  The two surviving ordered terms are equal;
the factor two in `(8)` cancels them, giving the second line of `(6)`.  Dividing by the cube of the
first asymptotic at `j=2` gives the third line.  The sign trichotomy `(7)` follows from the exponent
`2E_1-E_2`.  QED.

## Euler prime-power specialization `[PROVED HERE]`

Index the spectrum by `a=(p,k)` with `k>=1` and set

```text
n_a=p^k,
E_a=log n_a,
c_a=1/k.
```

Unique factorization makes `a |-> n_a` injective.  The unique first two levels are

```text
n_1=2, E_1=log 2, c_1=1,
n_2=3, E_2=log 3, c_2=1.
```

For `(1)`, write

```text
2^beta M_j(beta)
 = sum_a c_a (log n_a)^j (2/n_a)^beta.                (9)
```

For `beta>=2`, every summand is bounded by

```text
4 (log n_a)^j/n_a^2.
```

This is summable over prime powers because the parametrization is injective and
`sum_(n>=2)(log n)^j/n^2` converges.  Pointwise, every term except `n_a=2` tends to zero.  Dominated
convergence proves `(1)`.

For `(2)`, multiply `(8)` by `6^beta`.  Apart from the zero diagonal, distinct prime powers satisfy

```text
n_a n_b>=6,
n_a n_b=6 iff (n_a,n_b)=(2,3) or (3,2).               (10)
```

For `beta>=2`, the absolute scaled summand is bounded by

```text
36 c_a c_b E_a^2 E_b^2(E_a-E_b)^2/(n_a^2 n_b^2)
 <=72[(E_a^4/n_a^2)(E_b^2/n_b^2)
      +(E_a^2/n_a^2)(E_b^4/n_b^2)].                   (11)
```

The right side is summable on the product index set by factorization of the logarithmically
weighted `n^-2` series.  Dominated convergence and `(10)` leave precisely the two ordered pairs
`(2,3)` and `(3,2)`.  Dividing by the factor two in `(8)` proves `(2)`.

Since `log 3<2 log 2` is equivalent to `3<4`, the divergent branch of `(7)` applies.  Substitution
in `(6)` gives `(3)` and `(4)` with

```text
C_23=(log 3)^2(log(3/2))^2/(log 2)^4>0.               (12)
```

## Metric completeness at the cold end `[PROVED HERE]`

Equation `(1)` at `j=2` gives

```text
sqrt(M_2(beta)) ~ (log 2) 2^(-beta/2).                (13)
```

For any `epsilon>0`, `(13)` bounds the integrand for all sufficiently large `u` between
`(1-epsilon)log(2)2^(-u/2)` and `(1+epsilon)log(2)2^(-u/2)`.  Integrating the two exponentials from
`beta` to infinity yields

```text
(1-epsilon) 2*2^(-beta/2)
 <= integral_beta^infinity sqrt(M_2(u))du
 <= (1+epsilon) 2*2^(-beta/2).
```

Letting `epsilon` tend to zero proves `(5)`.  Hence `beta=infinity` lies at finite metric distance,
while its scalar curvature diverges to negative infinity.  In contrast, `beta=1` is an
infinite-distance asymptotically Poincare end with scalar curvature tending to `-2`.

The zeta Fisher superspace therefore has two inequivalent geometric ends:

```text
critical/clock end beta->1+: complete, asymptotically AdS2/Poincare;
ground-prime end beta->infinity: incomplete, finite-distance curvature singularity.
```

## Lean formalization `[FORMALIZED CORE]`

The universal countable-spectrum theorem and the actual Euler specialization are formalized in:

```text
formal/GaloisForLFunctions/RHTower/LowTemperatureCurvature.lean
formal/GaloisForLFunctions/RHTower/EulerFisherLowTemperature.lean
formal/GaloisForLFunctions/RHTower/EulerFisherColdEndDistance.lean
```

Lean proves without new axioms:

```text
lowTemperatureMoment_tendsto
lowTemperaturePairDispersion_tendsto
lowTemperatureCurvatureProfile_tendsto_atBot
lowTemperatureCurvatureProfile_critical
lowTemperatureCurvatureProfile_tendsto_zero

eulerPrimePowerMoment_scaled_tendsto
eulerPrimePowerMoment_det_scaled_tendsto
eulerFisherScalarCurvature_neg_scaled_tendsto
eulerFisherScalarCurvature_tendsto_atBot
eulerFisherScalarCurvature_log_rate_tendsto

tendsto_expMul_tail_integral
continuousOn_eulerConformalScale
eulerColdEndSqrt_asymptotic
eulerColdEndRadialDistance_tendsto
```

Thus `(1)`, `(2)`, `(3)`, and all of `(4)` are formalized for the actual Euler prime-power
spectrum.  The radial-distance asymptotic `(5)` is now formalized as
`eulerColdEndRadialDistance_tendsto`: `2 ^ (β/2) · ∫_{u>β} √(M₂ u) du → 2`, where the conformal
scale `M₂` is the second Euler prime-power moment.  Its analytic core is the reusable
`tendsto_expMul_tail_integral` (for `c > 0`, `exp(c·u)·g(u) → L` forces
`exp(c·β)·∫_{u>β} g → L/c`), together with `continuousOn_eulerConformalScale` (Weierstrass
`M`-test continuity of `M₂` on every tail `β > 1`) and `eulerColdEndSqrt_asymptotic` (the
square-root ground selection `exp((log 2 / 2)·u)·√(M₂ u) → log 2`).  Focused builds and the
repository formal lint pass.  The theorem family uses only the standard Mathlib axioms `propext`,
`Classical.choice`, and `Quot.sound`.

Formalization audit (needs-audit pass): the analytic core above formalizes the low-temperature limits.
The **exact** finite-sum dispersion identity underlying them — stated in the Approach as
`2(M₂M₄ − M₃²) = ∑_{a,b} w_a w_b x_a² x_b² (x_a − x_b)²`, previously used only inside the
dominated-convergence limit for infinite spectra — is now formalized as a standalone algebraic theorem
over an arbitrary commutative ring in
`formal/GaloisForLFunctions/RHTower/LowTemperatureDispersionIdentity.lean`:
`ZetaFisher.two_mul_dispersion` (the exact symmetrization identity) and `ZetaFisher.dispersion_nonneg`
(its manifest nonnegativity `M₂M₄ − M₃² ≥ 0` for nonnegative weights, each summand a product of a
weight product with a perfect square).  Both are axiom-clean (`propext, Classical.choice, Quot.sound`).

## Carrier verdict after the finite-Gamma boundary law

The finite archimedean Gamma-product theorem supplies one upper projective valuation direction,
whereas this theorem shows that the ordinary cold scalar geometry retains only the first two
prime-power levels.  Combined with the one-point quotient on every fixed-divisor regular-germ
fibre, the positive requirement is:

```text
an RH-sensitive superspace carrier must remain nontrivial after
  (i) fixed-divisor Euler-orbit closure,
  (ii) finite-Gamma projectivization, and
  (iii) bottom-two-level Boltzmann selection.
```

Consequently the carrier must be a pointed global incidence object with unbounded prime-phase
rank, archimedean transport, and distinguished divisor/trace moments.  The Fisher scalar curvature
is a geometric diagnostic of the clock end, not that carrier itself.  This does not reopen any of
Routes A--D.

## Anti-theatre attack

- The theorem does not constrain zeta zeros and is not an RH reformulation.
- It is not the existing Poincare-boundary result: the two ends have opposite completeness and
  curvature behavior.
- It is not visible from the dominant prime `2` alone, because a one-energy Fisher spectrum has
  zero curvature.  The prime `3` is load-bearing.
- `[PARENT-THEORY RISK]` A general low-temperature thermodynamic-curvature theorem may imply the
  result.  The exact rate, coefficient, completeness dichotomy, and zeta specialization require a
  literature audit after proof.

## Gates

- [x] 0 -> 1: exact scaled limits, source-pure mechanism, and falsification tests stated
- [x] 1 -> 2: complete paper proof with dominated-convergence majorants
- [x] 2 -> 3 core: universal two-level law, actual Euler scaled limits, curvature coefficient,
  curvature divergence, logarithmic rate, and axiom audit completed in Lean
- [x] 2 -> 3 completion: radial-distance asymptotic formalized as `eulerColdEndRadialDistance_tendsto`
  (axiom audit: `propext`, `Classical.choice`, `Quot.sound` only)
- [ ] 3 -> 4: primary-source novelty audit and standalone exposition
