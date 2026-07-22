# Möbius additive-triangle subpower RH criterion

- **ID:** `mobius-additive-triangle-subpower-rh-criterion`
- **Stage:** 1-in-progress
- **Type:** CANDIDATE THEOREM
- **Source:** Möbius additive triangle / Mellin continuation wall
- **Statement:** A one-sided `T(N)=O_epsilon(N^(1+epsilon))` family implies all strict
  half-power Möbius--Laplace bounds and RH.

## Goal

Replace the fixed linear-polylog source estimate by its weaker subpower closure.  This removes the
uniform critical-zero multiplicity cap and asks only for the near-linear exponent naturally needed
to make the Mellin transform analytic at each separate point of `Re(s)>1/2`.

Write

```text
T(N) = sum_(m+n<=N) mu(m)mu(n).
```

Assume

```text
for every epsilon>0, there is C_epsilon>=0 such that
T(N) <= C_epsilon (N+1)^(1+epsilon).                 (SP1)
```

Only an upper bound is required.

## Gates

- [x] 0 -> 1 in-progress: source-pure statement, attack, and hostile audit
- [x] paper bridge `(SP1) -> all b>1/2 power bounds -> RH`
- [ ] formalize the all-strict-half-power Mellin consumer
- [ ] formalize the real-power Abel estimate
- [ ] prove `(SP1)` unconditionally

## Dependency-closed paper proof

The exact formalized Abel identity is

```text
Phi(x)^2 = (1-exp(-x)) sum_(N>=0) T(N) exp(-Nx),     (SP2)
```

and its left side is real and nonnegative.  Fix `b>1/2` and put `epsilon=2b-1>0`.  From `(SP1)`,
positive Abel weights, and `1-exp(-x)<=x`,

```text
|Phi(x)|^2
 <= C_epsilon x sum_(N>=0) (N+1)^(1+epsilon) exp(-Nx). (SP3)
```

For `0<x<=1`, set `y=(N+1)x`.  Since

```text
(N+1)^(1+epsilon) exp(-Nx)
 = x^(-epsilon) (N+1) y^epsilon exp(x-y)
 <= e K_epsilon x^(-epsilon) (N+1) exp(-y/2),       (SP4)
```

where `K_epsilon=sup_(y>=0) y^epsilon exp(-y/2)<infinity`, the differentiated geometric series and
`1-exp(-x/2)>=x/4` give

```text
sum_(N>=0) (N+1)^(1+epsilon) exp(-Nx)
 <= 16 e K_epsilon x^(-2-epsilon).                  (SP5)
```

Thus `|Phi(x)|^2=O(x^(-1-epsilon))=O(x^(-2b))`, hence

```text
Phi(x)=O(x^(-b)) for every b>1/2.                    (SP6)
```

At a Mellin point with `Re(s)>1/2`, choose `b` strictly between `1/2` and `Re(s)`.  `(SP6)` gives
local Mellin convergence and analyticity there.  The existing denominator-free identity theorem
then supplies the continuation wall, and the continuation wall implies RH.  `[PROVED HERE]`

## Hostile audit

1. `(SP1)` is not known unconditionally; no RH claim is made.
2. PNT-level cancellation gives only `o(N^2)`, not `N^(1+epsilon)` for every epsilon.
3. Fixed-shift or logarithmically averaged Chowla does not control the full growing-shift triangle
   at this scale.
4. The theorem is strictly weaker than every fixed linear-polylog estimate: constants may depend
   on `epsilon`, and no uniform logarithmic loss or zero-multiplicity cap follows.
5. The source remains one-sided.  Negative values of `T(N)` help and are never replaced by absolute
   values.

## Scientific delta

Targeted corpus and literature searches found neither the additive-triangle interface nor this
subpower closure.  The Abel/Mellin mechanism is classical, so current classification is
`[CANDIDATE NEW SCIENTIFIC KNOWLEDGE] [NEW TO CORPUS] [NOVELTY UNVERIFIED]`.  Relevant neighboring
work on additive convolution with absolutely convergent Ramanujan expansions does not cover
Möbius self-convolution or `(SP1)`.

## No-go closure

- **Exact killing theorem/mechanism:** none; arithmetic endpoint `(SP1)` remains open.
- **Strongest positive survivor:** dependency-closed subpower-to-RH theorem `(SP1)`--`(SP6)`.
- **New insight:** RH requires near-linear one-sided triangle growth only in the `N^(1+o(1))`
  sense; fixed logarithmic degree is needed solely for uniform boundary multiplicity information.
- **Status:** paper-proved bridge; analytic Lean consumer and real-power Abel formalization pending.

## Log

- 2026-07-22 -- extracted weaker subpower source threshold from the fixed-polylog bridge and
  completed paper proof.

## Lean milestone: analytic consumer

Formal module:

```text
formal/GaloisForLFunctions/RHTower/MobiusLaplaceSubpowerCriterion.lean
```

Verified declarations:

- `MobiusDiscreteLaplaceAllStrictHalfPowerDecay`;
- `analyticOnNhd_mellin_mobiusDiscreteLaplaceTransform_of_allStrictHalfPower`;
- `mobiusLaplaceMellinContinuationWall_of_allStrictHalfPower`;
- `mobiusDiscreteLaplaceAllStrictHalfPowerDecay_implies_riemannHypothesis`.

Targeted verification passed with no diagnostics:

```text
lake env lean GaloisForLFunctions/RHTower/MobiusLaplaceSubpowerCriterion.lean
```

The remaining formal obligation is exactly the real-power Abel estimate `(SP1) -> (SP6)`; the
Mellin identity and RH consumer are dependency-closed in Lean.

- 2026-07-22 -- formalized all-strict-half-power analyticity, continuation wall, and RH consumer.

## Lean milestone: dependency-closed subpower source bridge

Formal module:

```text
formal/GaloisForLFunctions/RHTower/MobiusLaplaceAdditiveTriangleSubpower.lean
```

Verified declarations:

- `summable_natSucc_rpow_exp_neg_and_tsum_le`: explicit Gamma bound for every nonnegative real
  exponential moment;
- `MobiusAdditiveTriangleSubpowerUpperBound`;
- `norm_sq_mobiusDiscreteLaplaceTransform_le_of_additiveTriangleSubpowerUpperBound`;
- `mobiusAdditiveTriangleSubpowerUpperBound_implies_allStrictHalfPowerDecay`;
- `mobiusAdditiveTriangleSubpowerUpperBound_implies_riemannHypothesis`.

The formal proof sharpens `(SP4)`--`(SP5)` by direct sum--integral comparison:

```text
sum_(N>=0) (N+1)^r exp(-Nx)
 <= 1 + exp(x) 2^r x^(-r-1) Gamma(r+1).
```

Targeted verification passed. Analytic bridge is now dependency-closed in Lean. Only remaining
endpoint is unconditional arithmetic proof of `(SP1)`; RH is not yet proved.

- 2026-07-22 -- formalized real-power Abel moment and full `N^(1+o(1))` triangle-to-RH bridge.

## Binary-Chowla decomposition and literature boundary

Write the cumulative triangle as ordered pairs. Coordinate exchange gives the exact decomposition

```text
T(N) = D(N) + 2 O(N),
```

where `D(N)` is the equal-coordinate sum and `O(N)` is one strict-order half. Equivalently, after
putting `h=n-m>0`, `O(N)` is the aggregate of binary Möbius correlations over
`2m+h<=N`. The diagonal has at most one term per antidiagonal and therefore

```text
|D(N)| <= N+1.                                               (SP7)
```

Consequently the exact arithmetic core is only

```text
for every epsilon>0, O(N) <= C_epsilon (N+1)^(1+epsilon).     (SP8)
```

No absolute value or lower bound is required. `(SP7)` and `(SP8)` imply `(SP1)`, hence RH.

Targeted literature audit found a sharp boundary. Banks--Shparlinski, *Multiple sums with the
Möbius function* (arXiv:2506.08787), proves strong ternary estimates but explicitly states binary
analogues remain out of reach. Misra--Saha--Sharma (arXiv:2502.08305v2) treats additive
convolutions under absolutely convergent Ramanujan expansions, a hypothesis unavailable for
Möbius. Huxley--Watt (arXiv:1807.05890) studies multiplicative-hyperbola Mertens quadratic forms,
not this additive half-triangle. El Abdalaoui--Ye (arXiv:1504.00950v2) proves qualitative Cesàro
decay for self-correlations, but no square-root-scale rate. Thus neither PNT/Davenport bounds nor
current averaged-Chowla technology supplies `(SP8)`.

Earlier literature contains a claimed implication from qualitative Liouville Chowla to RH
(El Abdalaoui, arXiv:1609.03435v2), while Karagulyan, *Colloquium Mathematicum* 157 (2019),
shows abstract Chowla/Sarnak properties do not imply an abstract RH property and highlights the
role of multiplicativity. The theorem here neither relies on nor validates that disputed qualitative
implication: `(SP8)` is an explicit quantitative, growing-shift aggregate at square-root scale, and
its Abel-to-Mellin proof is formalized dependency-closed. Novelty classification therefore remains
`NOVELTY UNVERIFIED`, not a claim that all Chowla-to-RH connections are new.

Formal module:

```text
formal/GaloisForLFunctions/RHTower/MobiusAdditiveTriangleChowlaFrontier.lean
```

Verified declarations include the exact diagonal/off-diagonal split, unconditional linear diagonal
bound, `(SP8) -> (SP1)`, and `(SP8) -> RH`.

The fixed-degree refinement is also formalized. If for one `q>=0`

```text
O(N) <= C (N+1) log(N+2)^(2q),
```

then RH holds and every critical-line zeta zero has multiplicity at most `q+1`. The diagonal is
absorbed without changing logarithmic degree by the fixed factor `log(2)^(-2q)`. This identifies
zero multiplicity as the analytic shadow of quantitative aggregated binary-Chowla loss.

Classification: `[CANDIDATE NEW SCIENTIFIC KNOWLEDGE] [NEW TO CORPUS] [NOVELTY UNVERIFIED]`.
The endpoint is now identified as one-sided optimal-scale aggregated binary Chowla cancellation,
not ordinary Mertens/PNT cancellation.

## Positive survivor: second-Cesàro Mertens self-convolution equivalence — 2026-07-22

The first-cumulative source `T(N)=O_ε(N^(1+ε))` is stronger than needed. Define

`U(N)=sum_{k≤N} T(k)`.

Formal power-series coefficient extraction gives the exact identity

`U(N)=sum_{a+b=N} M(a)M(b)`.

A second Abel summation gives

`Phi(x)^2=(1-exp(-x))^2 sum_N U(N)exp(-Nx)`.

Therefore the one-sided family `U(N)≤C_ε(N+1)^(2+ε)` implies every strict half-power bound for
`Phi`, hence RH. Conversely RH gives `M(N)=O_δ(N^(1/2+δ))` for every `δ>0`, and the exact
self-convolution plus triangle inequality gives the absolute `U(N)=O_ε(N^(2+ε))` family. Thus this
second-Cesàro condition is paper-equivalent to RH, while the earlier binary-Chowla source is only a
strong sufficient condition.

Status: `[CANDIDATE NEW SCIENTIFIC KNOWLEDGE] [NOVELTY UNVERIFIED]`; full paper proof and literature
audit are in
`../3-formalized/needs-audit/mobius-mertens-self-convolution-rh-equivalence.md`. The finite identity,
double-Abel bridge, Gamma estimate, source transfer, and RH implication are formalized in
`MobiusMertensSelfConvolutionCriterion.lean`. Unconditional source closure remains exactly RH-level,
not a binary-Chowla-strength overconstraint.

- 2026-07-22 -- isolated and formalized binary-Chowla off-diagonal core and proved its RH bridge.

## Hostile no-go: first-moment/PNT information cannot close the source

The fold identity

```text
T(N) = sum_(m<=N) mu(m) M(N-m)
```

shows why inserting only `M(x)=o(x)` and taking absolute values yields at best `o(N^2)`. This is
not a technical loss that can be removed for arbitrary bounded sequences from first-moment data.
Take `a(n)=1` on primes and zero otherwise. Then

```text
A(N)=sum_(n<=N) a(n)=pi(N)=o(N),
sum_(m+n<=N) a(m)a(n) >= pi(N/2)^2 ~ N^2/(4 log(N/2)^2).
```

Thus bounded coefficients plus PNT-strength `o(N)` partial sums do not imply any
`N^(1+epsilon)` triangle bound for `epsilon<1`. Any valid proof of `(SP1)` must use specifically
signed two-point Möbius structure, not only a black-box Mertens estimate. Strongest positive survivor
is `(SP8)`: one-sided optimal-scale aggregated binary-Chowla cancellation.

Classification: `[CLASSICAL CONSEQUENCE] [NEW TO CORPUS]`. This no-go does not rule out a
Möbius-specific bilinear argument.

- 2026-07-22 -- ruled out first-moment/PNT-only closure by sparse prime-indicator countermodel.

## Positive-energy reformulation and its exact loss

Finite coordinate reversal splits the Mertens vector into palindromic and antipalindromic
components with energies `P(N), A(N) >= 0`.  Exact polarization gives

```text
U(N) = P(N) - A(N),
P(N) + A(N) = sum_(a<=N) M(a)^2.
```

Hence the positive all-epsilon estimate `P(N)=O_epsilon(N^(2+epsilon))` implies RH.  Under
Littlewood it is equivalent to RH.  Generic Cauchy--Schwarz discards `A` and replaces the signed
excess by total Mertens energy; this is the exact place Hilbert-space positivity overpays.  Lean
formalization and audit are recorded in
`../3-formalized/not_new_scientific_knowledge/mobius-mertens-reversal-energy-rh-criterion.md`.

Classification: `[BRIDGE] [NOT NEW SCIENTIFIC KNOWLEDGE]`.

## Square-dilation/Liouville escape closed

The Möbius--Liouville square-divisor transform multiplies Mellin data by `zeta(2s)`.  On
`Re(s)>1/2`, this factor is analytic and nowhere zero.  A generic theorem now proves that twisting
the Möbius continuation wall by any analytic unit preserves it exactly; specializing gives

```text
Liouville square-dilation wall <-> Möbius wall <-> RH.
```

Conditional convergence of `sum mu(d)/d` at the boundary therefore changes only representation,
not open-half-plane continuation.  Full paper and Lean certificates are in
`../3-formalized/not_new_scientific_knowledge/mobius-liouville-square-dilation-wall-preservation.md`.

Classification: `[BRIDGE] [CIRCULAR AS SOURCE] [NOT NEW SCIENTIFIC KNOWLEDGE]`.

## Remaining source core

Every completed route now lands on the same quantitative statement: prove signed excess

```text
sum_(a+b=N) M(a)M(b) <= C_epsilon (N+1)^(2+epsilon)
```

for every `epsilon>0`, without replacing it by total energy and without applying an invertible
Mellin multiplier.  PNT/first-moment input, absolute renewal contraction, finite algebraic
Hurwitz atlases, and square dilation are all rigorously excluded as independent source mechanisms.

## Critical prime-removal cascade closed in every positive multiplier norm — 2026-07-22

For finite prime set `P`, rough Möbius Laplace transforms satisfy exact recurrence

```text
F_P(x)=F_(P union {p})(x)-F_(P union {p})(p*x).
```

Critical logarithmic profiles therefore add local factors
`I-p^(-1/2)U_(log p)`.  Individual factors are invertible, but cofinal positive-norm control fails
sharply.  For terminal window `W_Y={p:Y/3<p<=Y}` and moving frequency `t_Y=pi/logY`, every local
phase lies in `[2pi/3,pi]` once `Y>=27`.  Lean proves

```text
(1+1/sqrt(Y))^(#W_Y) <= |product_(p in W_Y)
  (1-p^(-1/2-it_Y))|^2,

(1+1/sqrt(Y))^(#W_Y) <= product_(p in W_Y)(1-p^(-1/2))^(-1),
```

together with the exact Chebyshev window-cardinality budget.  Since `#W_Y >> Y/logY`, both
forward resonant and inverse zero-frequency blocks grow at least
`exp(c*sqrt(Y)/logY)`.  The bad frequency tends to zero, so fixed positive Gamma damping cannot
remove it.

This excludes prime ordering, primewise Neumann inversion, absolute Fourier bounds,
translation-invariant `L2` multiplier bounds, and fixed positive archimedean weights as source
providers.  Surviving route must cancel terminal block before any positive norm or use a
source-defined, non-translation-invariant low-frequency renormalization.  Paper proof, literature
audit, exact physical Hardy--Titchmarsh connector, Lean theorem, build, and axiom audit are in
`../3-formalized/needs-audit/mobius-critical-prime-block-resonance-wall.md` and
`MobiusCriticalPrimeBlockResonance.lean`.

Classification: `[FORMALIZED NO-GO] [CANDIDATE NEW FORMULATION] [NOVELTY NOT CERTIFIED]`.

## Gamma--Hankel localization closes ordinary height averaging — 2026-07-22

For a finite Dirichlet polynomial `P_N(s)=sum_(n<=N)a_n n^(-s)` and its Laplace pencil
`F_N(x)=sum_(n<=N)a_n exp(-nx)`, exact Gamma Fourier/Mellin localization gives

```text
integral_R |Gamma(sigma+it)P_N(sigma+it)|^2 dt
 = 2pi Gamma(2sigma) sum_(m,n<=N) a_m a_n/(m+n)^(2sigma)
 = 2pi integral_0^infinity x^(2sigma-1)|F_N(x)|^2 dx.
```

Thus Gamma damping does not turn logarithmic modes into orthogonal channels. It produces the
positive Hankel kernel `(m+n)^(-2sigma)` and retains every signed additive cross correlation.
Specializing `a_n=mu(n)` recovers the additive-convolution Dirichlet series

```text
Gamma(2sigma) sum_k c(k)/k^(2sigma),
c(k)=sum_(m+n=k)mu(m)mu(n).
```

The full condition

```text
integral_0^infinity x^(2sigma-1)|Phi(x)|^2 dx < infinity
for every sigma>1/2
```

is paper-equivalent to RH: Cauchy--Schwarz gives Mellin convergence and locally uniform
holomorphy on `Re(s)>1/2`; RH gives the energy by choosing a strict half-power exponent below
`sigma`. Long-height Bohr mean, Hilbert-matrix boundedness, and compact synthesis cannot supply
this cofinal energy. Remaining source is uniform control of signed off-diagonal Möbius Hankel
covariance before taking the positive norm.

Lean now proves the finite weighted Laplace/Hankel identity and quadratic-form nonnegativity for
arbitrary real coefficients, plus the exact Möbius specialization. Full proof, hostile audit,
literature boundary, and formal certificate are in
`../3-formalized/needs-audit/mobius-laplace-gamma-hankel-localization-wall.md` and
`MobiusLaplaceGammaHankelWall.lean`.

Classification: `[NEW TO CORPUS] [NOVELTY UNVERIFIED] [NOT AN UNCONDITIONAL RH PROOF]`.
